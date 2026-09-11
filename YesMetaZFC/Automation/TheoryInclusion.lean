import Lean
import YesMetaZFC.Logic.Theory.Basic

/-!
# 理论并的结构性包含

只沿理论定义的并、插入和别名寻找包含路径，不展开闭句正文，也不搜索数学推导。
生成的证明仅使用假设、析取引入与消去，由普通 Lean 内核检查。
-/
namespace YesMetaZFC.Automation.TheoryInclusion
open Lean Meta Elab Tactic Command

private def unfoldTheory? (sentence type : Expr) : MetaM (Option Expr) := do
  if type.getAppArgs.back? == some sentence then
    delta? type
  else
    return none

private partial def inject? (sentence source proof target : Expr) :
    StateT (Std.HashSet Expr) MetaM (Option Expr) := do
  if (← get).contains target then return none
  if ← withReducible <| isDefEq source target then return some proof
  modify (·.insert target)
  if target.isAppOfArity ``Or 2 then
    let left := target.getArg! 0
    let right := target.getArg! 1
    if let some result ← inject? sentence source proof left then
      return some (mkApp3 (mkConst ``Or.inl) left right result)
    if let some result ← inject? sentence source proof right then
      return some (mkApp3 (mkConst ``Or.inr) left right result)
  else if let some expanded ← unfoldTheory? sentence target then
    return ← inject? sentence source proof expanded
  return none

private partial def include? (sentence source proof target : Expr) : MetaM (Option Expr) := do
  if let some result ← (inject? sentence source proof target).run' {} then
    return some result
  if source.isAppOfArity ``Or 2 then
    let left := source.getArg! 0
    let right := source.getArg! 1
    return ← withLocalDeclD `hLeft left fun hLeft => do
      let some pLeft ← include? sentence left hLeft target | return none
      withLocalDeclD `hRight right fun hRight => do
        let some pRight ← include? sentence right hRight target | return none
        return some (← mkAppM ``Or.elim #[proof,
          ← mkLambdaFVars #[hLeft] pLeft, ← mkLambdaFVars #[hRight] pRight])
  else if source.isConstOf ``False then
    return some (← mkFalseElim target proof)
  else if let some expanded ← unfoldTheory? sentence source then
    return ← include? sentence expanded proof target
  return none

/-- 核验当前理论成员或包含目标；仅处理理论的结构性包含。 -/
elab "theory_inclusion" : tactic => do
  liftMetaTactic1 fun goal => goal.withContext do
    let goal ← if (← goal.getType).isAppOf ``Logic.FirstOrder.Theory.Extends then
      goal.change (← whnf (← goal.getType))
    else pure goal
    let (_, goal) ← goal.intros
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      if target.hasExprMVar then
        throwError "theory_inclusion 要求先确定目标理论；可用 show Theory.Extends 指定边界"
      for decl in ← getLCtx do
        if !decl.isImplementationDetail && (← isProp decl.type) then
          let source := decl.type
          if let some sentence := source.getAppArgs.back? then
            if let some proof ← include? sentence source decl.toExpr target then
              goal.assign proof
              return none
      throwError "theory_inclusion 未找到理论定义中的包含路径"

/-- 在理论组合边界声明包含合同，保留普通定理及命名参数。 -/
syntax (name := deriveTheorySubset) (docComment)? ("private ")?
  "derive_theory_subset " ident " ⊆ " ident (" => " ident)? : command

elab_rules : command
  | `($[$doc:docComment]? $[private%$priv]? derive_theory_subset $weak:ident ⊆ $strong:ident $[=> $name:ident]?) => do
      let name := name.getD <| mkIdent <| Name.mkSimple
        (weak.getId.getString! ++ "_subset_" ++ strong.getId.getString!)
      let sentence := mkIdent `sentence
      let hypothesis := mkIdent `hSentence
      elabCommand (← `($[$doc:docComment]? $[private%$priv]? theorem $name
        {$sentence} ($hypothesis : $weak $sentence) : $strong $sentence := by theory_inclusion))

end YesMetaZFC.Automation.TheoryInclusion
