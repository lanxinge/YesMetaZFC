import Lean
import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier

/-!
# `Derives` 的类型化全称闭包

自由变量上下文已经记录变量排序与次序；理论又只包含句子。因此全称闭包只需逐层
消去 free 上下文顶部变量，不再需要自然数编号、新鲜性扫描或闭理论注册表。
-/

namespace YesMetaZFC
namespace Tactic
namespace DerivesClosure

open Lean Elab Tactic Meta
open Logic FirstOrder

universe u v w

/-- 空局部上下文中的开放证明可关闭其 free 上下文顶部变量。 -/
theorem forall_intro_empty {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {body : OpenFormula σ (sort :: free)}
    (hBody : Derives T ([] : Context σ (sort :: free)) body) :
    Derives T ([] : Context σ free) (body.forallFreeTop sort) := by
  simpa [FreshVariable.extendContext] using
    (Derives.forall_intro
      (T := T) (Γ := ([] : Context σ free)) hBody)

private def finalize_proof
    (goal : MVarId) (target proof : Expr) : MetaM Bool := do
  let proof ← instantiateMVars proof
  let proofType ← inferType proof
  let hMatches ← withoutModifyingState do
    withTransparency .reducible <| isDefEq proofType target
  unless hMatches do
    return false
  let _ ← withTransparency .reducible <| isDefEq proofType target
  let proof ← instantiateMVars proof
  unless (← getMVarsNoDelayed proof).isEmpty do
    return false
  goal.assign proof
  return true

private partial def close_to_target
    (goal : MVarId) (target proof : Expr) : MetaM Bool := do
  if ← finalize_proof goal target proof then
    return true
  let weakeningState ← saveState
  try
    let weakened ← mkAppM ``Logic.FirstOrder.Derives.of_empty #[proof]
    if ← finalize_proof goal target weakened then
      return true
    weakeningState.restore
  catch _ =>
    weakeningState.restore
  try
    let closed ← mkAppM ``forall_intro_empty #[proof]
    close_to_target goal target closed
  catch _ =>
    return false

private unsafe def run_derive_close
    (proofSyntax : TSyntax `term) : TacticM Unit := do
  let savedState ← saveState
  let goal ← getMainGoal
  let target ← withMainContext <|
    instantiateMVars (← getMainTarget)
  try
    let proof ← withMainContext <|
      instantiateMVars
        (← elabTermForApply proofSyntax (mayPostpone := false))
    if ← withMainContext <|
        close_to_target goal target proof then
      replaceMainGoal []
      return
    throwErrorAt proofSyntax
      "derive_close 无法由给定证明逐层关闭 free 上下文以得到目标"
  catch error =>
    savedState.restore
    throw error

/-- 按证明类型中的 free 上下文逐层关闭规范顶部变量。 -/
syntax (name := deriveClose)
  "derive_close" " using " term : tactic

@[tactic deriveClose] unsafe def eval_derive_close : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| derive_close using $proof:term) =>
        run_derive_close proof
    | _ =>
        throwUnsupportedSyntax

end DerivesClosure
end Tactic
end YesMetaZFC
