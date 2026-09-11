import YesMetaZFC.Model.ZFC.Pure.PureStageBase
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalSetTheory

/-! # 第一轮二十个关系符号的实际纯定义

按原定义的依赖顺序编译，不用名称近似替换数学条件。最终图方程逐项由内核确认，
再由通用翻译正确性在实际阶段模型中证明原定义对任意对象参数成立。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundOneRelations
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x

inductive Primitive : Nonlogical.BasicSetTheory.RelationSymbol → Type where
  | isEquivalenceRelation : Primitive .isEquivalenceRelation
  | isInjective : Primitive .isInjective
  | isSurjective : Primitive .isSurjective
  | isBijection : Primitive .isBijection
  | isTransitiveSet : Primitive .isTransitiveSet
  | isLinearOrder : Primitive .isLinearOrder
  | isOrderIsomorphism : Primitive .isOrderIsomorphism
  | isOrderIsomorphic : Primitive .isOrderIsomorphic
  | isOrderEmbedding : Primitive .isOrderEmbedding
  | isOrderEmbeddable : Primitive .isOrderEmbeddable
  | isNaturalDiscreteLinearOrder : Primitive .isNaturalDiscreteLinearOrder
  | isWellOrder : Primitive .isWellOrder
  | isFinite : Primitive .isFinite
  | isEquinumerous : Primitive .isEquinumerous
  | cardinalityLeq : Primitive .cardinalityLeq
  | cardinalityStrictLess : Primitive .cardinalityStrictLess
  | isDedekindFinite : Primitive .isDedekindFinite
  | isInductiveSet : Primitive .isInductiveSet
  | isUnboundedSubset : Primitive .isUnboundedSubset
  | isBoundedSubset : Primitive .isBoundedSubset

def condition {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol) :
    Formula Nonlogical.BasicSetTheory.signature [] (Nonlogical.BasicSetTheory.signature.relDomain symbol) :=
  match primitive with
  | .isEquivalenceRelation => Nonlogical.BasicSetTheory.is_equivalence_relation_condition (.fvar .here)
  | .isInjective => Nonlogical.BasicSetTheory.is_injective_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  | .isSurjective => Nonlogical.BasicSetTheory.is_surjective_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  | .isBijection => Nonlogical.BasicSetTheory.is_bijection_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  | .isTransitiveSet => Nonlogical.BasicSetTheory.is_transitive_set_condition (.fvar .here)
  | .isLinearOrder => Nonlogical.BasicSetTheory.is_linear_order_condition (.fvar .here) (.fvar (.there .here))
  | .isOrderIsomorphism => Nonlogical.BasicSetTheory.is_order_isomorphism_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
  | .isOrderIsomorphic => Nonlogical.BasicSetTheory.is_order_isomorphic_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
  | .isOrderEmbedding => Nonlogical.BasicSetTheory.is_order_embedding_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
  | .isOrderEmbeddable => Nonlogical.BasicSetTheory.is_order_embeddable_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
  | .isNaturalDiscreteLinearOrder => Nonlogical.BasicSetTheory.is_natural_discrete_linear_order_condition (.fvar .here) (.fvar (.there .here))
  | .isWellOrder => Nonlogical.BasicSetTheory.well_order_condition (.fvar .here) (.fvar (.there .here))
  | .isFinite => Nonlogical.BasicSetTheory.is_finite_condition (.fvar .here)
  | .isEquinumerous => Nonlogical.BasicSetTheory.is_equinumerous_condition (.fvar .here) (.fvar (.there .here))
  | .cardinalityLeq => Nonlogical.BasicSetTheory.cardinality_leq_condition (.fvar .here) (.fvar (.there .here))
  | .cardinalityStrictLess => Nonlogical.BasicSetTheory.cardinality_strict_less_condition (.fvar .here) (.fvar (.there .here))
  | .isDedekindFinite => Nonlogical.BasicSetTheory.is_dedekind_finite_condition (.fvar .here)
  | .isInductiveSet => Nonlogical.BasicSetTheory.is_inductive_set_condition (.fvar .here)
  | .isUnboundedSubset => Nonlogical.BasicSetTheory.unbounded_subset_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  | .isBoundedSubset => Nonlogical.BasicSetTheory.bounded_subset_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

/-- 已完成的关系集合，用于排除临时假值分支。 -/
def relationCovered : Nonlogical.BasicSetTheory.RelationSymbol → Bool
  | .membership | .subset | .isOrderedPair | .isRelation | .isFunction | .isMapping
  | .isEquivalenceRelation
  | .isInjective
  | .isSurjective
  | .isBijection
  | .isTransitiveSet
  | .isLinearOrder
  | .isOrderIsomorphism
  | .isOrderIsomorphic
  | .isOrderEmbedding
  | .isOrderEmbeddable
  | .isNaturalDiscreteLinearOrder
  | .isWellOrder
  | .isFinite
  | .isEquinumerous
  | .cardinalityLeq
  | .cardinalityStrictLess
  | .isDedekindFinite
  | .isInductiveSet
  | .isUnboundedSubset
  | .isBoundedSubset => true
  | _ => false

/-- 每个原正文仅使用已完成函数与关系，临时分支没有进入本轮成果。 -/
theorem dependencies_covered {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol) :
    formulaCovered PureStageBase.functionCovered relationCovered (condition primitive) = true := by
  cases primitive <;> rfl

private def stage1 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isEquivalenceRelation => openFormula PureStageBase.interpretation (condition .isEquivalenceRelation)
    | symbol => PureStageBase.interpretation.relation symbol }

private def stage2 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isInjective => openFormula stage1 (condition .isInjective)
    | symbol => stage1.relation symbol }

private def stage3 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isSurjective => openFormula stage2 (condition .isSurjective)
    | symbol => stage2.relation symbol }

private def stage4 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isBijection => openFormula stage3 (condition .isBijection)
    | symbol => stage3.relation symbol }

private def stage5 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isTransitiveSet => openFormula stage4 (condition .isTransitiveSet)
    | symbol => stage4.relation symbol }

private def stage6 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isLinearOrder => openFormula stage5 (condition .isLinearOrder)
    | symbol => stage5.relation symbol }

private def stage7 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isOrderIsomorphism => openFormula stage6 (condition .isOrderIsomorphism)
    | symbol => stage6.relation symbol }

private def stage8 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isOrderIsomorphic => openFormula stage7 (condition .isOrderIsomorphic)
    | symbol => stage7.relation symbol }

private def stage9 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isOrderEmbedding => openFormula stage8 (condition .isOrderEmbedding)
    | symbol => stage8.relation symbol }

private def stage10 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isOrderEmbeddable => openFormula stage9 (condition .isOrderEmbeddable)
    | symbol => stage9.relation symbol }

private def stage11 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isNaturalDiscreteLinearOrder => openFormula stage10 (condition .isNaturalDiscreteLinearOrder)
    | symbol => stage10.relation symbol }

private def stage12 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isWellOrder => openFormula stage11 (condition .isWellOrder)
    | symbol => stage11.relation symbol }

private def stage13 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isFinite => openFormula stage12 (condition .isFinite)
    | symbol => stage12.relation symbol }

private def stage14 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isEquinumerous => openFormula stage13 (condition .isEquinumerous)
    | symbol => stage13.relation symbol }

private def stage15 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .cardinalityLeq => openFormula stage14 (condition .cardinalityLeq)
    | symbol => stage14.relation symbol }

private def stage16 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .cardinalityStrictLess => openFormula stage15 (condition .cardinalityStrictLess)
    | symbol => stage15.relation symbol }

private def stage17 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isDedekindFinite => openFormula stage16 (condition .isDedekindFinite)
    | symbol => stage16.relation symbol }

private def stage18 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isInductiveSet => openFormula stage17 (condition .isInductiveSet)
    | symbol => stage17.relation symbol }

private def stage19 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isUnboundedSubset => openFormula stage18 (condition .isUnboundedSubset)
    | symbol => stage18.relation symbol }

private def stage20 : Interpretation Nonlogical.BasicSetTheory.signature ℒ :=
  { sort := fun _ => setSort, function := PureStageBase.functionGraph, relation := fun symbol => match symbol with
    | .isBoundedSubset => openFormula stage19 (condition .isBoundedSubset)
    | symbol => stage19.relation symbol }

def interpretation : Interpretation Nonlogical.BasicSetTheory.signature ℒ := stage20

def graph {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (_ : Primitive symbol) :
    Formula ℒ [] ((Nonlogical.BasicSetTheory.signature.relDomain symbol).map (fun _ => setSort)) :=
  interpretation.relation symbol

/-- 后续步骤没有改变正文所用的前置定义，因此最终解释仍精确展开原正文。 -/
theorem graph_equation {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (condition primitive) := by
  cases primitive <;> rfl

theorem functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional interpretation ℳ := by
  intro symbol args
  have hMap : mapValues interpretation args = mapValues PureStageBase.interpretation args := by
    generalize hSorts : Nonlogical.BasicSetTheory.signature.funcDomain symbol = sorts at args
    clear hSorts
    induction args with
    | nil => rfl
    | cons head tail ih => exact congrArg (Values.cons head) ih
  change ∃ output, (PureStageBase.functionGraph symbol).satisfies
      (templateEnv (.cons output (mapValues interpretation args))) ∧
    ∀ other, (PureStageBase.functionGraph symbol).satisfies
      (templateEnv (.cons other (mapValues interpretation args))) → other = output
  rw [hMap]
  exact PureStageBase.functional hℳ symbol args

/-- 这是具体阶段扩张中的原定义，不把定义公理或未填的模型实现合同作为前提。 -/
theorem definition_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol)
    (args : Values (expansion (functional hℳ)).model.Carrier (Nonlogical.BasicSetTheory.signature.relDomain symbol)) :
    (expansion (functional hℳ)).relation symbol args ↔ (condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion (functional hℳ)) (expansion_realizes (functional hℳ))
    symbol (condition primitive) (graph_equation primitive) args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundOneRelations
