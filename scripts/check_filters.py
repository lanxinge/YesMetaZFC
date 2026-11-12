"""核验滤子、内部 ZF 切割及林登鲍姆代数的构建与公理边界。

检查实际生产声明（含私有及自动生成声明），不使用枚举数学样本。
Prop 证明允许经典逻辑；禁止新增公理和 noncomputable 数据声明。
另对指定的构造性端点排除 Classical.choice，不能据此把宿主结果冒充内部结果。
"""
from pathlib import Path
import hashlib
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    'YesMetaZFC.Model.Boolean.Filter',
    'YesMetaZFC.Model.Boolean.Completion',
    'YesMetaZFC.Model.Boolean.Ultrafilter',
    'YesMetaZFC.Logic.FirstOrder.Lindenbaum',
    'YesMetaZFC.SetTheory.Filter',
    'YesMetaZFC.SetTheory.Filter.Tarski',
    'YesMetaZFC.SetTheory.Filter.Internal',
    'YesMetaZFC.SetTheory.Filter.Extension',
    'YesMetaZFC.SetTheory.Boolean.Completion',
    'YesMetaZFC.SetTheory.Boolean.Algebra',
    'YesMetaZFC.SetTheory.Boolean.Filter',
    'YesMetaZFC.SetTheory.Separation',
    'YesMetaZFC.SetTheory.SetConstruction',
]
CHOICE_FREE = [
    "YesMetaZFC.Model.Boolean.BA_alg.Cut_l.algebra_l",
    "YesMetaZFC.Model.Boolean.BA_alg.Cut_l.dense_sup_l",
    "YesMetaZFC.Logic.FirstOrder.Lindenbaum.algebra_m",
    "YesMetaZFC.Logic.FirstOrder.Lindenbaum.theory_filter_m",
    "YesMetaZFC.SetTheory.FilterZF.generated_exists_d",
    "YesMetaZFC.SetTheory.BooleanZF.boolean_completion_exists_d",
    "YesMetaZFC.SetTheory.BooleanZF.principal_imp_d",
    "YesMetaZFC.SetTheory.BooleanZF.generated_filter_exists_d",
    "YesMetaZFC.SetTheory.BooleanZF.generated_ideal_exists_d",
]
# 当前生产句子的闭合性由内核检查；不再允许原有 native_decide 公理。
BASELINE = []


def names(values):
    return "#[" + ", ".join("`" + value for value in values) + "]"


def main(modules=MODULES, choice_free=CHOICE_FREE, baseline=BASELINE,
         label="FILTER_GUARD_PASS", axiom_bounds=None):
    """复用声明级审计；各数学切片显式传入模块及其可信边界。"""
    files = [ROOT / (m.replace(".", "/") + ".lean") for m in modules]
    hashes = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    env = {**os.environ, "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "1")}
    # 与全源构建入口相同：分批保持全部目标，避免 Windows 命令行长度限制。
    for start in range(0, len(modules), 128):
        result = subprocess.run(["lake", "--wfail", "build", *modules[start:start + 128]], cwd=ROOT, env=env)
        if result.returncode:
            return result.returncode
    # 同一模块可包含不同理论强度的端点，逐声明另给更窄的可信边界。
    bounds = "#[" + ", ".join(
        f"(`{name}, {names(bound + ['propext', 'Quot.sound', 'Classical.choice'])})"
        for name, bound in (axiom_bounds or {}).items()) + "]"
    # 名称表分别编译，避免大型审计闭包内的数组初始化触发代码生成器递归上限。
    guard = f'''
@[noinline] private def guard_selected_l : Array Lean.Name := {names(modules)}
@[noinline] private def guard_allowed_l : Array Lean.Name := {names(baseline + ["propext", "Quot.sound", "Classical.choice"])}
@[noinline] private def guard_strict_l : Array Lean.Name := {names(choice_free)}
@[noinline] private def guard_bounds_l : Array (Lean.Name × Array Lean.Name) := {bounds}

run_cmd do
  let env ← Lean.getEnv
  let selected := guard_selected_l
  let allowed := guard_allowed_l
  let mut count : Nat := 0
  let mut modules : Nat := 0
  for i in [0 : env.header.moduleNames.size] do
    unless selected.contains env.header.moduleNames[i]! do continue
    modules := modules + 1
    for c in env.header.moduleData[i]!.constants do
      count := count + 1
      if Lean.isNoncomputable env c.name then
        throwError "不可计算数据声明: {{c.name}}"
      match c with
      | .axiomInfo _ => throwError "模块新增公理: {{c.name}}"
      | _ => pure ()
      for a in ← Lean.collectAxioms c.name do
        unless allowed.contains a do throwError "未知公理: {{c.name}} → {{a}}"
  unless modules == selected.size do throwError "审计模块遗漏: {{modules}}"
  let strict := guard_strict_l
  for n in strict do
    unless env.contains n do throwError "审计端点不存在: {{n}}"
    let axioms ← Lean.collectAxioms n
    if axioms.contains `Classical.choice then throwError "构造性端点退化: {{n}}"
    Lean.logInfo m!"CHOICE_FREE: {{n}}; {{axioms}}"
  let bounds := guard_bounds_l
  for (n, bound) in bounds do
    unless env.contains n do throwError "审计端点不存在: {{n}}"
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless bound.contains a do throwError "端点超出公理边界: {{n}} → {{a}}"
    Lean.logInfo m!"AXIOM_BOUND: {{n}}; {{axioms}}"
  Lean.logInfo m!"{label}: {{modules}} modules, {{count}} declarations"
'''
    source = "import Lean\n" + "\n".join("import " + m for m in modules) + "\n" + guard
    result = subprocess.run(["lake", "env", "lean", "--stdin"], input=source,
                            cwd=ROOT, env=env, capture_output=True, encoding="utf-8", errors="replace")
    print(result.stdout + result.stderr, end="")
    changed = [str(p.relative_to(ROOT)) for p in files
               if hashlib.sha256(p.read_bytes()).hexdigest() != hashes[p]]
    if result.returncode or label + ":" not in result.stdout or changed:
        print(f"FAIL: exit={result.returncode}, changed={changed}", file=sys.stderr)
        return 1
    print("PASS: no new axioms or noncomputable data; all strict endpoints remain choice-free")
    return 0


if __name__ == "__main__":
    sys.exit(main())
