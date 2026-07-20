import Lean

/-!
# `prove_auto` 宿主保守规约核

本模块只负责上下文无关的 β/ι/ζ/投影规约。它不读取 `prove_auto_norm` 注册规则，
不执行命题前提消解，不改写局部假设或目标，也不调用任何 provider。

规约器把 Lean simplifier 当作不可信的 proof producer：只接受没有实际使用声明的
结果，并核验普通 Lean `Eq` 证明。规则正规化、相继式分解和 checked 事务位于独立
模块，不再通过本文件暴露旧执行接口。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization
namespace ConservativeReduction

open Lean Meta

/-- 单次保守规约的资源护栏。 -/
structure Config where
  maxSteps : Nat := 512
deriving Repr, Inhabited

/-- 一个已经核验等式证明、且没有消费注册声明的规约结果。 -/
structure Result where
  source : Expr
  normal : Expr
  proof : Expr
  changed : Bool := false
deriving Inhabited

private def simpContext (maxSteps : Nat) : MetaM Simp.Context := do
  Simp.mkContext
    (config := {
      maxSteps := Nat.max 1 maxSteps
      maxDischargeDepth := 0
      contextual := false
      memoize := true
      failIfUnchanged := false
      autoUnfold := false
      beta := true
      iota := true
      zeta := true
      zetaDelta := false
      proj := true
      index := true
    })
    (simpTheorems := #[{}])
    (congrTheorems := ← getSimpCongrTheorems)

/-- 核验规约结果的路径端点和普通 Lean 等式证明。 -/
def Result.validate (result : Result) : MetaM Unit := do
  if result.source.hasMVar || result.normal.hasMVar || result.proof.hasMVar then
    throwError "conservative reduction retained an unresolved metavariable"
  unless result.changed == (result.source != result.normal) do
    throwError "conservative reduction changed flag disagrees with its endpoints"
  let expected ← mkEq result.source result.normal
  let proofType ← inferType result.proof
  unless ← isDefEq proofType expected do
    throwError "conservative reduction proof does not connect its endpoints"

/--
把稳定表达式规约到 β/ι/ζ/投影固定点。

函数保存并恢复内部 Meta 状态；返回证明已经实例化，不携带搜索期间创建的 metavariable。
任何全局 simp 声明的实际使用都会使规约失败。
-/
def reduce (source : Expr) (config : Config := {}) : MetaM Result := do
  let savedState ← saveState
  try
    let source ← instantiateMVars source
    if source.hasMVar then
      throwError "conservative reduction refused a source with unresolved metavariables"
    let context ← simpContext config.maxSteps
    let (simpResult, simpStats) ← simp source context
    unless simpStats.usedTheorems.toArray.isEmpty do
      throwError "conservative reduction unexpectedly used a global declaration"
    let normal ← instantiateMVars simpResult.expr
    let proof ←
      match simpResult.proof? with
      | some proof => instantiateMVars proof
      | none => mkEqRefl source
    let result : Result := {
      source
      normal
      proof
      changed := source != normal
    }
    result.validate
    savedState.restore
    return result
  catch error =>
    savedState.restore
    throw error

end ConservativeReduction
end HostNormalization
end Automation
end YesMetaZFC
