import YesMetaZFC.Model.Interpretation.ModelClosure
import YesMetaZFC.Model.ZFC.Pure.PureFinalTransfer
import YesMetaZFC.Model.ZFC.Pure.PureRoundTwoSpecifications

/-! # 最终扩张中的非递归关系定义闭句

消费原阶段的逐参数关系方程，以原参数顺序闭合，再经覆盖定理传到最终扩张。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalRelations
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem is_equivalence_relation (hℳ : Theory.Models ℳ theory) :
    is_equivalence_relation_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isEquivalenceRelation (.cons a .nil)

theorem is_injective (hℳ : Theory.Models ℳ theory) :
    is_injective_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isInjective (.cons a (.cons b (.cons c .nil)))

theorem is_surjective (hℳ : Theory.Models ℳ theory) :
    is_surjective_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isSurjective (.cons a (.cons b (.cons c .nil)))

theorem is_bijection (hℳ : Theory.Models ℳ theory) :
    is_bijection_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isBijection (.cons a (.cons b (.cons c .nil)))

theorem is_transitive_set (hℳ : Theory.Models ℳ theory) :
    is_transitive_set_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isTransitiveSet (.cons a .nil)

theorem is_linear_order (hℳ : Theory.Models ℳ theory) :
    is_linear_order_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isLinearOrder (.cons a (.cons b .nil))

theorem is_order_isomorphism (hℳ : Theory.Models ℳ theory) :
    is_order_isomorphism_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro e d c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isOrderIsomorphism (.cons a (.cons b (.cons c (.cons d (.cons e .nil)))))

theorem is_order_isomorphic (hℳ : Theory.Models ℳ theory) :
    is_order_isomorphic_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro d c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isOrderIsomorphic (.cons a (.cons b (.cons c (.cons d .nil))))

theorem is_order_embedding (hℳ : Theory.Models ℳ theory) :
    is_order_embedding_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro e d c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isOrderEmbedding (.cons a (.cons b (.cons c (.cons d (.cons e .nil)))))

theorem is_order_embeddable (hℳ : Theory.Models ℳ theory) :
    is_order_embeddable_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro d c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isOrderEmbeddable (.cons a (.cons b (.cons c (.cons d .nil))))

theorem is_natural_discrete_linear_order (hℳ : Theory.Models ℳ theory) :
    is_natural_discrete_linear_order_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isNaturalDiscreteLinearOrder (.cons a (.cons b .nil))

theorem well_order (hℳ : Theory.Models ℳ theory) :
    well_order_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isWellOrder (.cons a (.cons b .nil))

theorem is_finite (hℳ : Theory.Models ℳ theory) :
    is_finite_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isFinite (.cons a .nil)

theorem is_equinumerous (hℳ : Theory.Models ℳ theory) :
    is_equinumerous_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isEquinumerous (.cons a (.cons b .nil))

theorem cardinality_leq (hℳ : Theory.Models ℳ theory) :
    cardinality_leq_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .cardinalityLeq (.cons a (.cons b .nil))

theorem cardinality_strict_less (hℳ : Theory.Models ℳ theory) :
    cardinality_strict_less_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .cardinalityStrictLess (.cons a (.cons b .nil))

theorem is_dedekind_finite (hℳ : Theory.Models ℳ theory) :
    is_dedekind_finite_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isDedekindFinite (.cons a .nil)

theorem is_inductive_set (hℳ : Theory.Models ℳ theory) :
    is_inductive_set_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isInductiveSet (.cons a .nil)

theorem unbounded_subset (hℳ : Theory.Models ℳ theory) :
    unbounded_subset_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isUnboundedSubset (.cons a (.cons b (.cons c .nil)))

theorem bounded_subset (hℳ : Theory.Models ℳ theory) :
    bounded_subset_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro c b a
  exact PureRoundTwoSpecifications.round_one_definition hℳ .isBoundedSubset (.cons a (.cons b (.cons c .nil)))

theorem is_infinite (hℳ : Theory.Models ℳ theory) :
    is_infinite_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.natural_definition hℳ .isInfinite (.cons a .nil)

theorem is_countable (hℳ : Theory.Models ℳ theory) :
    is_countable_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.natural_definition hℳ .isCountable (.cons a .nil)

theorem is_uncountable (hℳ : Theory.Models ℳ theory) :
    is_uncountable_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.natural_definition hℳ .isUncountable (.cons a .nil)

theorem is_countably_infinite (hℳ : Theory.Models ℳ theory) :
    is_countably_infinite_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro a
  exact PureRoundTwoSpecifications.natural_definition hℳ .isCountablyInfinite (.cons a .nil)

theorem omega_pair_less (hℳ : Theory.Models ℳ theory) :
    omega_pair_less_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.natural_definition hℳ .omegaPairLess (.cons a (.cons b .nil))

theorem hereditarily_finite (hℳ : Theory.Models ℳ theory) :
    hereditarily_finite_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_values
  intro args
  exact PureRoundTwoSpecifications.hereditary_definition hℳ (templateEnv args) (.fvar .here)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalRelations
