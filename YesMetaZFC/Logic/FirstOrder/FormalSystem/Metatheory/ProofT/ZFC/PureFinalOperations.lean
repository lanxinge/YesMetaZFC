import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRoundOneSpecifications
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalCollections

/-! # 关系逆、复合、隶属关系、映像与对称差的原闭句 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalOperations
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer PureFinalBasic PureFinalPairs PureFinalMappings PureFinalCollections
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}
abbrev dom (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) := 𝒩.funcInterp .domain (.cons a .nil)
abbrev ran (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) := 𝒩.funcInterp .range (.cons a .nil)

theorem cartesian_value (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    ∀ element, membership ℳ element (prod (E hℳ).model a b) ↔
      ∃ left, membership ℳ left a ∧ ∃ right, membership ℳ right b ∧ PureKuratowski.Code ℳ element left right :=
  (PureMappingDefinitions.cartesian_correct _ a b).mp (cartesian_graph hℳ a b)

theorem converse_semantics (𝒩 : Structure.{0,0,0,x} S) (a output : 𝒩.Carrier s) :
    (relation_converse_spec (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element (prod 𝒩 (ran 𝒩 a) (dom 𝒩 a)) ∧
        ∃ original, Mem 𝒩 original a ∧ element = 𝒩.funcInterp .orderedPairReverse (.cons original .nil) := by
  simp only [relation_converse_spec, membership_specification, relation_converse_member_condition,
    relation_converse_graph_condition, Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem composition_semantics (𝒩 : Structure.{0,0,0,x} S) (a b output : 𝒩.Carrier s) :
    (relation_composition_spec (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element (prod 𝒩 (dom 𝒩 a) (ran 𝒩 b)) ∧
        ∃ middle, Mem 𝒩 (opair 𝒩 (projection 𝒩 .domain element) middle) a ∧
          Mem 𝒩 (opair 𝒩 middle (projection 𝒩 .range element)) b := by
  simp only [relation_composition_spec, membership_specification, relation_composition_member_condition,
    relation_composition_graph_condition, Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem membership_semantics (𝒩 : Structure.{0,0,0,x} S) (a output : 𝒩.Carrier s) :
    (membership_relation_spec (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element (prod 𝒩 a a) ∧
        ∃ left right, element = opair 𝒩 left right ∧ Mem 𝒩 left right := by
  simp only [membership_relation_spec, membership_specification, membership_relation_member_condition,
    membership_relation_graph_condition, Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem image_semantics (𝒩 : Structure.{0,0,0,x} S) (function subset target output : 𝒩.Carrier s) :
    (image_spec (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons target (.cons subset (.cons function .nil)))) : Env 𝒩 [] [s,s,s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element target ∧
        ∃ input, Mem 𝒩 input subset ∧ Mem 𝒩 (opair 𝒩 input element) function := by
  simp only [image_spec, membership_specification, relation_image_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem symmetric_semantics (𝒩 : Structure.{0,0,0,x} S) (a b output : 𝒩.Carrier s) :
    (symmetric_difference_spec (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element (binUnion 𝒩 a b) ∧
        ((Mem 𝒩 element a ∧ ¬ Mem 𝒩 element b) ∨ (Mem 𝒩 element b ∧ ¬ Mem 𝒩 element a)) := by
  simp only [symmetric_difference_spec, membership_specification, symmetric_difference_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem converse (hℳ : Theory.Models ℳ theory) :
    relation_converse_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output a
  intro hRelation
  apply ((PureCompletedStage.realizes hℳ).function .relationConverse (.cons a .nil) output).symm.trans
  apply (PureRoundOneSpecifications.converse_spec hℳ output a _ _ _ ((relation_predicate hℳ a).mp hRelation)
    (domain_value hℳ a) (range_value hℳ a)
    (cartesian_value hℳ (ran (E hℳ).model a) (dom (E hℳ).model a))).trans
  apply Iff.trans ?_ (converse_semantics (E hℳ).model a output).symm
  exact forall_congr' (fun element => iff_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr (fun original => and_congr Iff.rfl
      ((PureCompletedStage.realizes hℳ).function .orderedPairReverse (.cons original .nil) element)))))

theorem composition (hℳ : Theory.Models ℳ theory) :
    relation_composition_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output b a
  intro _
  apply ((PureCompletedStage.realizes hℳ).function .relationComposition (.cons b (.cons a .nil)) output).symm.trans
  apply (PureRoundOneSpecifications.composition_spec hℳ output a b _ _ _ (domain_value hℳ a) (range_value hℳ b)
    (cartesian_value hℳ (dom (E hℳ).model a) (ran (E hℳ).model b))).trans
  apply Iff.trans ?_ (composition_semantics (E hℳ).model a b output).symm
  apply forall_congr'
  intro element
  apply iff_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨left, right, hLeft, hRight, middle, hFirst, hSecond⟩
    have hLeftEq := (projection_value hℳ .domain element left).mp hLeft
    have hRightEq := (projection_value hℳ .range element right).mp hRight
    subst left; subst right
    exact ⟨middle, (pair_member hℳ _ _ a).mpr hFirst, (pair_member hℳ _ _ b).mpr hSecond⟩
  · rintro ⟨middle, hFirst, hSecond⟩
    exact ⟨_, _, (projection_value hℳ .domain element _).mpr rfl,
      (projection_value hℳ .range element _).mpr rfl, middle,
      (pair_member hℳ _ _ a).mp hFirst, (pair_member hℳ _ _ b).mp hSecond⟩

theorem membership_relation (hℳ : Theory.Models ℳ theory) :
    membership_relation_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output a
  intro _
  apply ((PureCompletedStage.realizes hℳ).function .membershipRelation (.cons a .nil) output).symm.trans
  apply (PureRoundOneSpecifications.membership_spec hℳ output a _ (cartesian_value hℳ a a)).trans
  apply Iff.trans ?_ (membership_semantics (E hℳ).model a output).symm
  exact forall_congr' (fun element => iff_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr (fun left => exists_congr (fun right =>
      and_congr (ordered_value hℳ left right element).symm Iff.rfl)))))

theorem image (hℳ : Theory.Models ℳ theory) :
    image_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output subset target source function
  intro hMapping hSubset
  apply ((PureCompletedStage.realizes hℳ).function .image (.cons function (.cons subset .nil)) output).symm.trans
  apply (PureRoundOneSpecifications.image_spec hℳ output function source target subset
    ((mapping_predicate hℳ function source target).mp hMapping) ((subset_value hℳ subset source).mp hSubset)).trans
  apply Iff.trans ?_ (image_semantics (E hℳ).model function subset target output).symm
  exact forall_congr' (fun element => iff_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr (fun input => and_congr Iff.rfl (pair_member hℳ input element function).symm))))

theorem symmetric_difference (hℳ : Theory.Models ℳ theory) :
    symmetric_difference_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output b a
  exact ((PureCompletedStage.realizes hℳ).function .symmetricDifference (.cons a (.cons b .nil)) output).symm.trans
    ((PureRoundOneSpecifications.symmetric_difference_spec hℳ output a b _ (binary_union_value hℳ a b)).trans
      (symmetric_semantics (E hℳ).model a b output).symm)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalOperations
