import YesMetaZFC.Model.ZFC.Pure.PureFinalArithmetic
import YesMetaZFC.Model.ZFC.Pure.PureRoundTwoSpecifications

/-! # 第二轮集合构造的原定义闭句

逐一保留原 guard，并以已有任意输出规格关闭自由参数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalConstructions
open PureModel Nonlogical.BasicSetTheory FormalSystem PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem finite_subset_collection (hℳ : Theory.Models ℳ theory) :
    finite_subset_collection_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.bounded_specification hℳ .finiteSubsetCollection (.cons a .nil) b

theorem power_set_bijection (hℳ : Theory.Models ℳ theory) :
    power_set_bijection_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  intro _
  exact PureRoundTwoSpecifications.bounded_specification hℳ .powerSetBijection (.cons a .nil) b

theorem index_order (hℳ : Theory.Models ℳ theory) :
    index_order_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro e d c b a
  intro _
  exact PureRoundTwoSpecifications.bounded_specification hℳ .indexOrder (.cons a (.cons b (.cons c (.cons d .nil)))) e

theorem finite_sequence_space (hℳ : Theory.Models ℳ theory) :
    finite_sequence_space_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  intro _
  exact PureRoundTwoSpecifications.finite_sequence_specification hℳ a b

theorem nonempty_finite_sequence_space (hℳ : Theory.Models ℳ theory) :
    nonempty_finite_sequence_space_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  intro _
  exact PureRoundTwoSpecifications.filter_specification hℳ .nonemptyFiniteSequenceSpace (.cons a .nil) b

theorem recursive_sequence_space (hℳ : Theory.Models ℳ theory) :
    recursive_sequence_space_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro d c b a
  intro _
  exact PureRoundTwoSpecifications.filter_specification hℳ .recursiveSequenceSpace (.cons a (.cons b (.cons c .nil))) d

theorem omega_recursive_sequence (hℳ : Theory.Models ℳ theory) :
    omega_recursive_sequence_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro d c b a
  intro _
  exact PureRoundTwoSpecifications.omega_specification hℳ a b c d

theorem transitive_closure (hℳ : Theory.Models ℳ theory) :
    transitive_closure_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoSpecifications.closure_specification hℳ a b

theorem natural_order_type (hℳ : Theory.Models ℳ theory) :
    natural_order_type_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro c b a
  exact PureRoundTwoStage.order_type_definition hℳ a b c

theorem natural_subset_type (hℳ : Theory.Models ℳ theory) :
    natural_subset_type_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoStage.subset_type_definition hℳ a b

theorem finite_sequence_concatenation (hℳ : Theory.Models ℳ theory) :
    finite_sequence_concatenation_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro c b a
  exact PureRoundTwoStage.concatenation_definition hℳ a b c

theorem finite_sequence_flatten (hℳ : Theory.Models ℳ theory) :
    finite_sequence_flatten_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro b a
  exact PureRoundTwoStage.flatten_definition hℳ a b

theorem minimum_difference (hℳ : Theory.Models ℳ theory) :
    minimum_difference_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro f e d c b a
  exact PureRoundTwoSpecifications.minimum_definition hℳ
    (.cons f (.cons a (.cons b (.cons c (.cons d (.cons e .nil))))))


theorem old_omega (hℳ : Theory.Models ℳ theory) :
    (PureRoundTwoStage.expansion hℳ).function .omega .nil = PureNaturalInduction.omega hℳ :=
  (functionFromRoundTwo hℳ .omega rfl .nil).symm.trans (PureFinalArithmetic.omega_final hℳ)

theorem natural_addition (hℳ : Theory.Models ℳ theory) :
    natural_addition_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro output right left
  rintro ⟨hLeft, hRight⟩
  change membership ℳ left ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hLeft
  change membership ℳ right ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hRight
  rw [old_omega] at hLeft hRight
  exact PureRoundTwoSpecifications.arithmetic_specification hℳ .addition hLeft hRight output

theorem natural_multiplication (hℳ : Theory.Models ℳ theory) :
    natural_multiplication_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro output right left
  rintro ⟨hLeft, hRight⟩
  change membership ℳ left ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hLeft
  change membership ℳ right ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hRight
  rw [old_omega] at hLeft hRight
  exact PureRoundTwoSpecifications.arithmetic_specification hℳ .multiplication hLeft hRight output

theorem natural_exponentiation (hℳ : Theory.Models ℳ theory) :
    natural_exponentiation_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro output right left
  rintro ⟨hLeft, hRight⟩
  change membership ℳ left ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hLeft
  change membership ℳ right ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hRight
  rw [old_omega] at hLeft hRight
  exact PureRoundTwoSpecifications.arithmetic_specification hℳ .exponentiation hLeft hRight output

theorem natural_difference (hℳ : Theory.Models ℳ theory) :
    natural_difference_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro output right left
  rintro ⟨hLeft, hRight⟩
  change membership ℳ left ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hLeft
  change membership ℳ right ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hRight
  rw [old_omega] at hLeft hRight
  exact PureRoundTwoSpecifications.difference_specification hℳ hLeft hRight output

theorem godel_pairing (hℳ : Theory.Models ℳ theory) :
    godel_pairing_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro output right left
  rintro ⟨hLeft, hRight⟩
  change membership ℳ left ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hLeft
  change membership ℳ right ((PureRoundTwoStage.expansion hℳ).function .omega .nil) at hRight
  rw [old_omega] at hLeft hRight
  exact PureRoundTwoSpecifications.godel_specification hℳ hLeft hRight output

theorem finite_hierarchy (hℳ : Theory.Models ℳ theory) :
    finite_hierarchy_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  exact PureRoundTwoSpecifications.hierarchy_specification hℳ

theorem finite_universe (hℳ : Theory.Models ℳ theory) :
    finite_universe_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  exact (PureRoundTwoSpecifications.universe_specification hℳ _).mp rfl


end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalConstructions
