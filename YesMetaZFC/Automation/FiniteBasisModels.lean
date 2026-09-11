import Lean
import YesMetaZFC.Model.ZFC.FiniteAxiomModels

/-! # 有限公理基的模型装配

调用者提供真实的闭句语义或已验证子基；只读取基的并、插入、同余和别名结构。
共享子基缓存为普通内核定理，避免展开巨大公理列表或重复复制模型证明。
-/
namespace YesMetaZFC.Automation.FiniteBasisModels
open Lean Meta Elab Tactic
open Logic.FirstOrder Logic.FirstOrder.FormalSystem.ProofT

private structure Facts where
  sentences : Std.HashMap Expr Expr := {}
  bases : Std.HashMap Expr Expr := {}

private partial def addSentence (formula proof : Expr) (facts : Facts) : MetaM Facts := do
  let facts := { facts with sentences := facts.sentences.insert formula proof }
  if formula.isAppOf ``Formula.conj then
    let facts ← addSentence (formula.getRevArg! 1) (← mkAppM ``And.left #[proof]) facts
    addSentence (formula.getRevArg! 0) (← mkAppM ``And.right #[proof]) facts
  else pure facts

private partial def sentenceProof (facts : Facts) (formula : Expr) : MetaM Expr := do
  if let some proof := facts.sentences[formula]? then return proof
  if formula.isAppOf ``Formula.conj then
    return ← mkAppM ``And.intro #[← sentenceProof facts (formula.getRevArg! 1),
      ← sentenceProof facts (formula.getRevArg! 0)]
  if let some expanded ← delta? formula then return ← sentenceProof facts expanded
  throwError "finite_basis_models 缺少闭句的语义证据：{formula.getAppFn}"

private partial def basisProof (model : Expr) (facts : Facts) (basis : Expr) :
    StateT (Std.HashMap Expr Expr) MetaM Expr := do
  if let some proof := (← get)[basis]? then return proof
  let proof ← if let some proof := facts.bases[basis]? then pure proof
    else if basis.isAppOf ``FiniteAxiomBasis.singleton then
      mkAppOptM ``FiniteAxiomBasis.singleton_models #[some model, some (basis.getArg! 0),
        some (← sentenceProof facts (basis.getArg! 0))]
    else if basis.isAppOf ``FiniteAxiomBasis.insert then
      mkAppOptM ``FiniteAxiomBasis.insert_models #[none, some (basis.getRevArg! 0),
        some (basis.getArg! 0), some model, some (← sentenceProof facts (basis.getArg! 0)),
        some (← basisProof model facts (basis.getRevArg! 0))]
    else if basis.isAppOf ``FiniteAxiomBasis.union then
      mkAppM ``FiniteAxiomBasis.union_models #[← basisProof model facts (basis.getRevArg! 1),
        ← basisProof model facts (basis.getRevArg! 0)]
    else if basis.isAppOf ``FiniteAxiomBasis.congr then
      basisProof model facts (basis.getRevArg! 1)
    else if let some expanded ← delta? basis then
      basisProof model facts expanded
    else throwError "finite_basis_models 无法识别公理基：{basis.getAppFn}"
  let proof ← if basis.isConst then
      let type ← mkAppM ``Theory.Models #[model, ← mkAppM ``FiniteAxiomBasis.theory #[basis]]
      mkAuxTheorem type proof
    else pure proof
  modify (·.insert basis proof)
  return proof

/-- 仅装配指定证据，不搜索公理、不增加模型假设。 -/
elab "finite_basis_models" "[" terms:term,* "]" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOf ``Theory.Models &&
        (target.getRevArg! 0).isAppOf ``FiniteAxiomBasis.theory do
      throwError "finite_basis_models 要求显式的有限公理基模型目标"
    let model := target.getRevArg! 1
    let basis := (target.getRevArg! 0).getRevArg! 0
    let mut facts : Facts := {}
    for term in terms.getElems do
      let proof ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      let type ← instantiateMVars (← inferType proof)
      unless !proof.hasExprMVar && !proof.hasSorry &&
          (type.isAppOf ``Theory.Models || type.isAppOf ``Formula.satisfies) do
        throwErrorAt term "请提供已完成的闭句语义或有限公理基模型证据"
      unless ← withReducible <| isDefEq (type.getArg! 1) model do
        throwErrorAt term "语义证据必须使用目标中的同一模型"
      if type.isAppOf ``Formula.satisfies then
        facts ← addSentence (type.getRevArg! 0) proof facts
      else
        let theory := type.getRevArg! 0
        unless theory.isAppOf ``FiniteAxiomBasis.theory do
          throwErrorAt term "模型证据必须注明有限公理基"
        facts := { facts with bases := facts.bases.insert (theory.getRevArg! 0) proof }
    let proof ← (basisProof model facts basis).run' {}
    goal.assign proof
    replaceMainGoal []

end YesMetaZFC.Automation.FiniteBasisModels
