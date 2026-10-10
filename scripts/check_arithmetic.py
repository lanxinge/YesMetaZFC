"""构建全部算术模块（含可选模块），审计公理及数据构造边界。

这不是数学语义审查。自动生成的 recursor 和私有声明不单独枚举，
但它们作为公开声明的传递依赖仍由 Lean 的公理检查覆盖。
另按声明所属模块检查全部声明（含私有／生成声明），禁止 noncomputable
及自定义公理。结合正常编译，阻止从经典存在证明选择 Type 数据；
Prop 证明仍允许经典推理，不把这一检查冒充为 ZF 内部解释定理。
"""
from pathlib import Path
import hashlib
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ENTRY = ["YesMetaZFC.Logic.Arithmetic", "YesMetaZFC.Model.Arithmetic"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

# 不靠名字前缀猜测声明归属：私有声明与改用其他命名空间的声明也必须覆盖。
DATA_GUARD = r'''
run_cmd do
  let env ← Lean.getEnv
  let mut modules : Nat := 0
  let mut declarations : Nat := 0
  for i in [0 : env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    unless (`YesMetaZFC.Logic.Arithmetic).isPrefixOf moduleName ||
        (`YesMetaZFC.Model.Arithmetic).isPrefixOf moduleName do
      continue
    modules := modules + 1
    let data := env.header.moduleData[i]!
    for c in data.constants do
      declarations := declarations + 1
      if Lean.isNoncomputable env c.name then
        throwError "算术声明不可标记 noncomputable: {c.name}"
      match c with
      | .axiomInfo _ => throwError "算术模块不可新增公理: {c.name}"
      | _ => pure ()
  Lean.logInfo m!"DATA_GUARD_PASS: {modules} modules, {declarations} declarations"
'''


def imports(path):
    return re.findall(r"^import\s+(\S+)", path.read_text(encoding="utf-8-sig"), re.M)


def closure(entry):
    seen, pending = set(), list(entry)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        if path.exists():
            pending.extend(imports(path))
    return seen


def main():
    files = sorted([ROOT / (m.replace(".", "/") + ".lean") for m in ENTRY] +
                   [p for m in ENTRY for p in (ROOT / m.replace(".", "/")).rglob("*.lean")])
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    declarations = []
    for path in files:
        source = path.read_text(encoding="utf-8-sig")
        namespaces = re.findall(r"^namespace\s+(\S+)", source, re.M)
        names = re.findall(r"^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?(?:theorem|def|abbrev|inductive)\s+(\S+)",
                           source, re.M)
        if names and len(namespaces) != 1:
            raise ValueError(f"需要更新声明枚举器的命名空间处理: {path}")
        declarations.extend(namespaces[0] + "." + name for name in names)
    if not declarations or len(declarations) != len(set(declarations)):
        raise ValueError("公开声明列表为空或重复")
    modules = [p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".") for p in files]
    dependencies = closure(modules)
    forbidden = [m for m in dependencies if m.startswith((
        "Mathlib", "BMSConstructibleBridge", "YesMetaZFC.BMS", "ConstructibleUniverse",
        "YesMetaZFC.SetTheory", "YesMetaZFC.Model.ZFC", "YesMetaZFC.Model.SmallGraph"))]
    logic = [m for m in modules if m.startswith("YesMetaZFC.Logic.")]
    forbidden += [m for m in closure(logic) if m.startswith("YesMetaZFC.Model.")]
    if forbidden:
        raise ValueError(f"算术分层依赖越界: {sorted(set(forbidden))}")
    build = subprocess.run(["lake", "--wfail", "build", *modules], cwd=ROOT,
                           env={**os.environ, "LEAN_NUM_THREADS": "1"})
    if build.returncode:
        return build.returncode
    commands = "\n".join(["import Lean"] + ["import " + m for m in modules] +
                         [DATA_GUARD] + ["#print axioms " + name for name in declarations]) + "\n"
    result = subprocess.run(["lake", "env", "lean", "--stdin"], input=commands,
                            cwd=ROOT, capture_output=True, encoding="utf-8", errors="replace")
    log = result.stdout + result.stderr
    print(log, end="")
    reported = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", log)
    used = {a.strip() for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log, re.S)
            for a in group.split(",") if a.strip()}
    missing = set(declarations) - set(reported)
    guarded = re.findall(r"DATA_GUARD_PASS: (\d+) modules, (\d+) declarations", log)
    guard_ok = len(guarded) == 1 and int(guarded[0][0]) == len(modules)
    changed = [str(p.relative_to(ROOT)) for p in files
               if hashlib.sha256(p.read_bytes()).hexdigest() != before[p]]
    if result.returncode or not guard_ok or missing or used - ALLOWED or changed:
        print(f"FAIL: exit={result.returncode}, missing={sorted(missing)}, "
              f"data_guard={guard_ok}, unexpected={sorted(used - ALLOWED)}, changed={changed}", file=sys.stderr)
        return 1
    print(f"PASS: {len(files)} files, {len(declarations)} declarations; axioms={sorted(used)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
