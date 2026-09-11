import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalMappings

/-! # 笛卡尔积、映射收集、恒等与限制的原闭句 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalCollections
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer PureFinalBasic PureFinalPairs PureFinalMappings
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

abbrev prod (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) := 𝒩.funcInterp .cartesianProduct (.cons a (.cons b .nil))
abbrev power (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) := 𝒩.funcInterp .powerSet (.cons a .nil)
abbrev binUnion (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) := 𝒩.funcInterp .binaryUnion (.cons a (.cons b .nil))
abbrev opair (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) := 𝒩.funcInterp .orderedPair (.cons a (.cons b .nil))

theorem cartesian_graph (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    (PureMappingDefinitions.graph .cartesianProduct).satisfies
      (templateEnv (.cons (prod (E hℳ).model a b) (.cons a (.cons b .nil))) : Env ℳ [] [setSort,setSort,setSort]) :=
  ((PureCompletedStage.realizes hℳ).function .cartesianProduct (.cons a (.cons b .nil)) _).mpr rfl

theorem cartesian_semantics (𝒩 : Structure.{0,0,0,x} S) (a b output : 𝒩.Carrier s) :
    (cartesian_product_spec (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element (power 𝒩 (power 𝒩 (binUnion 𝒩 a b))) ∧
        ∃ left right, Mem 𝒩 left a ∧ Mem 𝒩 right b ∧ element = opair 𝒩 left right := by
  simp only [cartesian_product_spec, membership_specification, cartesian_product_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem mapping_collection_semantics (𝒩 : Structure.{0,0,0,x} S) (a b output : 𝒩.Carrier s) :
    (mapping_collection_spec (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element (power 𝒩 (prod 𝒩 a b)) ∧
        𝒩.relInterp .isMapping (.cons element (.cons a (.cons b .nil))) := by
  simp only [mapping_collection_spec, membership_specification, mapping_collection_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem identity_semantics (𝒩 : Structure.{0,0,0,x} S) (a output : 𝒩.Carrier s) :
    (identity_spec (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element (prod 𝒩 a a) ∧
        ∃ input, Mem 𝒩 input a ∧ element = opair 𝒩 input input := by
  simp only [identity_spec, membership_specification, identity_member_condition, identity_graph_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem restriction_semantics (𝒩 : Structure.{0,0,0,x} S) (a b output : 𝒩.Carrier s) :
    (restriction_spec (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element a ∧
        ∃ input value, Mem 𝒩 input b ∧ element = opair 𝒩 input value := by
  simp only [restriction_spec, membership_specification, restriction_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem cartesian_product (hℳ : Theory.Models ℳ theory) :
    cartesian_product_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output b a
  apply ((PureCompletedStage.realizes hℳ).function .cartesianProduct (.cons a (.cons b .nil)) output).symm.trans
  apply (PureMappingSpecifications.cartesian_spec output a b _ _ _ (binary_union_value hℳ a b)
    (power_value hℳ (binUnion (E hℳ).model a b))
    (power_value hℳ (power (E hℳ).model (binUnion (E hℳ).model a b)))).trans
  apply Iff.trans ?_ (cartesian_semantics (E hℳ).model a b output).symm
  apply forall_congr'
  intro element
  apply iff_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨left, hLeft, right, hRight, hCode⟩
    exact ⟨left, right, hLeft, hRight, (ordered_value hℳ left right element).mpr hCode⟩
  · rintro ⟨left, right, hLeft, hRight, hEqual⟩
    exact ⟨left, hLeft, right, hRight, (ordered_value hℳ left right element).mp hEqual⟩

theorem mapping_collection (hℳ : Theory.Models ℳ theory) :
    mapping_collection_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output b a
  apply ((PureCompletedStage.realizes hℳ).function .mappingCollection (.cons a (.cons b .nil)) output).symm.trans
  apply (PureMappingSpecifications.mappingCollection_spec output a b _ _ (cartesian_graph hℳ a b)
    (power_value hℳ (prod (E hℳ).model a b))).trans
  apply Iff.trans ?_ (mapping_collection_semantics (E hℳ).model a b output).symm
  exact forall_congr' (fun element => iff_congr Iff.rfl
    (and_congr Iff.rfl (mapping_predicate hℳ element a b).symm))

theorem identity (hℳ : Theory.Models ℳ theory) :
    identity_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output a
  apply ((PureCompletedStage.realizes hℳ).function .identity (.cons a .nil) output).symm.trans
  apply (PureMappingOperations.identity_spec output a _ (cartesian_graph hℳ a a)).trans
  apply Iff.trans ?_ (identity_semantics (E hℳ).model a output).symm
  exact forall_congr' (fun element => iff_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr (fun input => and_congr Iff.rfl (ordered_value hℳ input input element).symm))))

theorem restriction (hℳ : Theory.Models ℳ theory) :
    restriction_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output subset target source function
  intro _ _
  apply ((PureCompletedStage.realizes hℳ).function .restriction (.cons function (.cons subset .nil)) output).symm.trans
  apply (PureMappingOperations.restriction_correct output function subset).trans
  apply Iff.trans ?_ (restriction_semantics (E hℳ).model function subset output).symm
  exact forall_congr' (fun element => iff_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr (fun input => exists_congr (fun value =>
      and_congr Iff.rfl (ordered_value hℳ input value element).symm)))))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalCollections
