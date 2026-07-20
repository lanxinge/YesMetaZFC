import YesMetaZFC.SetTheory.Definitional.DeepRflAttr
import YesMetaZFC.SetTheory.Definitional.Theory

/-!
# 新核受控定义约化

`deep_rfl` 只使用专用 simp 集约化新核语义。原子定义体、保守性桥和审计展开不会进入
该集合，因此遇到原子时最多约化到原生 `Interpretation.atom`。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional

open Lean Meta Elab Tactic

attribute [deep_rfl]
  Env.push
  Term.bind
  Term.rename
  Term.weaken
  Formula.bind
  Term.eval
  TermVector.eval
  Semantics.satisfies
  Structure.SatisfiesSentence

/--
只沿 `[deep_rfl]` 白名单执行的项目专用反身性战术。

该战术不调用普通 `rfl`，避免在失败路径上触发定义原子体的全透明展开。
-/
syntax (name := deepRfl) "deep_rfl" : tactic

private def isForbiddenFormulaReduction (formula : Expr) : Bool :=
  (formula.find? fun expression =>
    expression.isConstOf ``Definitions.body ||
      expression.isConstOf ``Kernel.atom_iff ||
      expression.isConstOf
        `YesMetaZFC.SetTheory.Definitional.Audit.Formula.expand).isSome

private def replaceLastArgument (expression : Expr) (arguments : Array Expr)
    (replacement : Expr) : Expr :=
  mkAppN expression.getAppFn
    (arguments.set! (arguments.size - 1) replacement)

private def replaceLastTwoArguments (expression : Expr)
    (arguments : Array Expr) (left right : Expr) : Expr :=
  mkAppN expression.getAppFn <|
    (arguments.set! (arguments.size - 2) left).set!
      (arguments.size - 1) right

private def isSatisfiesApp (expression : Expr) : Bool :=
  expression.isAppOf ``Semantics.satisfies ||
    expression.getAppFn.constName? ==
      some `YesMetaZFC.SetTheory.Definitional.Project.Formula.satisfies

/-- 只展开公式 AST 的逻辑骨架，遇到定义原子和审计入口立即停止。 -/
private partial def exposeFormulaSpine (formula : Expr) : MetaM Expr := do
  if isForbiddenFormulaReduction formula then
    return formula
  let exposed ← withTransparency .all <| whnf formula
  if isForbiddenFormulaReduction exposed then
    return formula
  let arguments := exposed.getAppArgs
  if exposed.isAppOf ``Formula.neg ||
      exposed.isAppOf ``Formula.forallE ||
      exposed.isAppOf ``Formula.existsE then
    let body ← exposeFormulaSpine arguments.back!
    return replaceLastArgument exposed arguments body
  if exposed.isAppOf ``Formula.conj ||
      exposed.isAppOf ``Formula.disj ||
      exposed.isAppOf ``Formula.imp ||
      exposed.isAppOf ``Formula.iff then
    let left ← exposeFormulaSpine arguments[arguments.size - 2]!
    let right ← exposeFormulaSpine arguments.back!
    return replaceLastTwoArguments exposed arguments left right
  return exposed

/-- 只修改 `satisfies` 的公式参数，不对目标其余部分做全透明约化。 -/
private def exposeSatisfiesFormulas (target : Expr) : MetaM Expr :=
  transform target (pre := fun expression => do
    unless isSatisfiesApp expression do
      return .continue
    let arguments := expression.getAppArgs
    if arguments.isEmpty then
      return .continue
    let formula := arguments.back!
    let exposed ← exposeFormulaSpine formula
    if exposed == formula then
      return .continue
    return .done (replaceLastArgument expression arguments exposed))

private def exposeGoal (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let target ← goal.getType
    let exposed ← exposeSatisfiesFormulas target
    if exposed == target then
      return goal
    goal.replaceTargetDefEq exposed

elab_rules : tactic
  | `(tactic| deep_rfl) => do
      liftMetaTactic fun goal => do
        return [← exposeGoal goal]
      evalTactic (← `(tactic| (simp only [deep_rfl]) <;> done))

end Definitional
end SetTheory
end YesMetaZFC
