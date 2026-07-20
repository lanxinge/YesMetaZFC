import Lean

/-!
# `prove_auto` 宿主相继式核心

本层放置不依赖具体搜索器的宿主相继式规则。规则实现可以失败，但成功时必须直接
构造 Lean proof，并由当前目标的 metavariable assignment 接受内核检查。
-/

namespace YesMetaZFC
namespace Automation
namespace HostSequent

open Lean Meta

/-- 当前局部上下文中的单结论宿主相继式。 -/
structure LocalSequent where
  goal : MVarId
  resources : Array FVarId := #[]

/-- 初始规则 `Γ, A ⊢ A` 的当前叶证明槽位。 -/
structure InitialRuleStep where
  resource : FVarId

/-- 定义等价探测不得向相继式后续规则泄漏临时赋值。 -/
private def expressionsDefEq
    (left right : Expr) : MetaM Bool := do
  let savedState ← saveState
  let result ← isDefEqGuarded left right
  savedState.restore
  return result

/--
按稳定资源顺序准入初始规则。

只接受当前目标上下文中的、无 metavariable 的 Prop proof。返回的 FVar 只允许在当前
叶立即消费，不得跨相继式分支或上下文缓存。
-/
def admitInitialRule
    (sequent : LocalSequent) : MetaM (Option InitialRuleStep) :=
  sequent.goal.withContext do
    let declaration ← sequent.goal.getDecl
    let target ← instantiateMVars declaration.type
    if target.hasMVar then
      return none
    for resource in sequent.resources do
      unless declaration.lctx.contains resource do
        continue
      let proposition ← instantiateMVars (← resource.getType)
      if proposition.hasMVar || !(← isProp proposition) then
        continue
      if ← expressionsDefEq proposition target then
        return some { resource }
    return none

/-- 在当前叶执行已经准入的初始规则。 -/
def applyInitialRule
    (sequent : LocalSequent) (step : InitialRuleStep) : MetaM Unit :=
  sequent.goal.withContext do
    let declaration ← sequent.goal.getDecl
    unless declaration.lctx.contains step.resource do
      throwError
        "prove_auto sequent initial rule received a stale proof resource \
        `{step.resource.name}`"
    let target ← instantiateMVars declaration.type
    let proposition ← instantiateMVars (← step.resource.getType)
    if target.hasMVar || proposition.hasMVar || !(← isProp proposition) then
      throwError
        "prove_auto sequent initial rule requires stable proposition resources"
    unless ← expressionsDefEq proposition target do
      throwError
        "prove_auto sequent initial rule resource no longer matches its conclusion"
    sequent.goal.assign (mkFVar step.resource)

/-- 尝试以初始规则闭合当前宿主相继式。 -/
def tryInitialRule
    (sequent : LocalSequent) : MetaM (Option InitialRuleStep) := do
  let some step ← admitInitialRule sequent
    | return none
  applyInitialRule sequent step
  return some step

end HostSequent
end Automation
end YesMetaZFC
