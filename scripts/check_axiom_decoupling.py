#!/usr/bin/env python3
"""检查实际生产声明的精确传递公理集合，不重新证明枚举样例。

边界由同目录 axiom_decoupling_bounds.json 显式记录并审查。
声明类型的独立前后比较见本轮公理解耦验证报告。
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


def lean_name(name):
    parts = name.split('.')
    # 私有声明的数字组件不能直接放入 Lean 名称引号。
    if not any(part.isascii() and part.isdigit() for part in parts):
        return '`' + name
    result = 'Lean.Name.anonymous'
    for part in parts:
        if part.isascii() and part.isdigit():
            result = f'(Lean.Name.num {result} {int(part)})'
        else:
            result = f'(Lean.Name.str {result} {json.dumps(part, ensure_ascii=False)})'
    return result


def names(xs):
    return '#[' + ', '.join(lean_name(x) for x in xs) + ']'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--bounds', type=Path, default=Path(__file__).with_name('axiom_decoupling_bounds.json'))
    p.add_argument('--skip-build', action='store_true', help='Requires already verified matching .olean files')
    p.add_argument('--emit', type=Path, help='Only write the generated Lean check for independent execution')
    args = p.parse_args()
    spec = json.loads(args.bounds.read_text())
    modules, bounds = spec['modules'], spec['bounds']
    if not modules or not bounds:
        raise SystemExit('Empty module list or declaration-bound list')
    entries = '#[' + ', '.join(f'({lean_name(n)}, {names(ax)})' for n, ax in bounds.items()) + ']'
    source = 'import Lean\n' + ''.join('import ' + m + '\n' for m in modules) + f'''
open Lean
private def rawAxioms (env : Environment) (root : Name) : Except Name (Array Name) := Id.run do
  let env := env.setExporting false
  let mut queue : Array Name := #[root]
  let mut seen : NameSet := NameSet.empty
  let mut result : NameSet := NameSet.empty
  let mut index := 0
  while index < queue.size do
    let name := queue[index]!
    index := index + 1
    if seen.contains name then continue
    seen := seen.insert name
    let some c := env.checked.get.find? name | return .error name
    if c.isAxiom then result := result.insert name
    let mut deps := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
    if let .inductInfo v := c then deps := deps ++ v.ctors.toArray
    if let .recInfo v := c then
      for rule in v.rules do deps := deps.push rule.ctor ++ rule.rhs.getUsedConstants
    for dependency in deps do
      unless seen.contains dependency do queue := queue.push dependency
  return .ok (result.toArray.qsort Name.lt)
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let modules : Array Lean.Name := {names(modules)}
  let permitted : Array Lean.Name := #[`propext, `Quot.sound, `Classical.choice]
  let mut seen : Nat := 0
  let mut count : Nat := 0
  for i in [0 : env.header.moduleNames.size] do
    unless modules.contains env.header.moduleNames[i]! do continue
    seen := seen + 1
    for c in env.header.moduleData[i]!.constants do
      count := count + 1
      match c with
      | .axiomInfo _ => throwError "Unexpected project axiom: {{c.name}}"
      | _ => pure ()
      if c.isUnsafe then throwError "Unsafe declaration: {{c.name}}"
      if Lean.isNoncomputable env c.name then
        throwError "Noncomputable declaration: {{c.name}}"
      for ax in ← Lean.collectAxioms c.name do
        unless permitted.contains ax do
          throwError "Unexpected transitive axiom: {{c.name}} → {{ax}}"
      let raw ← match rawAxioms env c.name with
        | .ok result => pure result
        | .error missing => throwError "Raw audit missing constant: {{missing}}"
      for ax in raw do
        unless permitted.contains ax do
          throwError "Unexpected raw transitive axiom: {{c.name}} → {{ax}}"
  unless seen == modules.size do throwError "Module coverage mismatch: {{seen}} of {{modules.size}}"
  let bounds : Array (Lean.Name × Array Lean.Name) := {entries}
  for (name, expected) in bounds do
    unless env.contains name do throwError "Missing production declaration: {{name}}"
    let actual ← Lean.collectAxioms name
    let raw ← match rawAxioms env name with
      | .ok result => pure result
      | .error missing => throwError "Raw audit missing constant: {{missing}}"
    unless raw.size == expected.size && raw.all expected.contains do
      throwError "Raw axiom set changed for {{name}}: expected {{expected}}, got {{raw}} (cached {{actual}})"
    unless actual.all raw.contains do
      throwError "Cached axioms exceed raw set for {{name}}: cached {{actual}}, raw {{raw}}; rebuild dependencies"
    if actual.size < raw.size then
      Lean.logInfo m!"AXIOM_CACHED_UNDERCOUNT: {{name}}; cached {{actual}}; raw {{raw}}"
    Lean.logInfo m!"AXIOM_EXACT: {{name}}; cached {{actual}}; raw {{raw}}"
  Lean.logInfo m!"AXIOM_DECOUPLING_PASS: {{seen}} modules, {{count}} declarations, {{bounds.size}} exact endpoints"
'''
    if args.emit:
        args.emit.write_text(source)
        return 0
    env = {**os.environ, 'LEAN_NUM_THREADS': '1'}
    if not args.skip_build:
        result = subprocess.run(['lake', '--wfail', 'build', *modules], cwd=args.repo, env=env)
        if result.returncode:
            return result.returncode
    result = subprocess.run(['lake', 'env', 'lean', '--stdin'], cwd=args.repo, env=env,
                            input=source, text=True)
    return result.returncode

if __name__ == '__main__':
    sys.exit(main())
