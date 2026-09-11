import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalPairs

/-! # 定义域、值域、函数与映射的原公理 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalMappings
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer PureFinalBasic PureFinalPairs
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

abbrev projection (𝒩 : Structure.{0,0,0,x} S) (coordinate : RelationCoordinate) (a : 𝒩.Carrier s) :=
  match coordinate with
  | .domain => 𝒩.funcInterp .leftProjection (.cons a .nil)
  | .range => 𝒩.funcInterp .rightProjection (.cons a .nil)

theorem projection_value (hℳ : Theory.Models ℳ theory) (coordinate : RelationCoordinate) (a output : Carrier ℳ) :
    (PureCoordinateSpecifications.projectionGraph coordinate).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env ℳ [] [setSort,setSort]) ↔
      output = projection (E hℳ).model coordinate a := by
  cases coordinate
  · exact (PureCompletedStage.realizes hℳ).function .leftProjection (.cons a .nil) output
  · exact (PureCompletedStage.realizes hℳ).function .rightProjection (.cons a .nil) output

theorem domain_value (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    ∀ element, membership ℳ element (F hℳ .domain (.cons a .nil)) ↔
      ∃ value, PureKuratowski.PairMember ℳ element value a :=
  (PureRelationCoordinates.domain_correct _ a).mp
    (((PureCompletedStage.realizes hℳ).function .domain (.cons a .nil) _).mpr rfl)

theorem range_value (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    ∀ element, membership ℳ element (F hℳ .range (.cons a .nil)) ↔
      ∃ input, PureKuratowski.PairMember ℳ input element a :=
  (PureRelationCoordinates.range_correct _ a).mp
    (((PureCompletedStage.realizes hℳ).function .range (.cons a .nil) _).mpr rfl)

theorem mapping_predicate (hℳ : Theory.Models ℳ theory) (function source target : Carrier ℳ) :
    (E hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil))) ↔
      PureMappingDefinitions.IsMapping ℳ function source target :=
  ((PureCompletedStage.realizes hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil)))).symm.trans
    (PureMappingDefinitions.isMapping_correct function source target)

theorem coordinate_semantics (𝒩 : Structure.{0,0,0,x} S) (coordinate : RelationCoordinate) (a output : 𝒩.Carrier s) :
    (relation_coordinate_spec coordinate (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔
        Mem 𝒩 element (𝒩.funcInterp .union (.cons (𝒩.funcInterp .union (.cons a .nil)) .nil)) ∧
          ∃ pair, Mem 𝒩 pair a ∧ element = projection 𝒩 coordinate pair := by
  simp only [relation_coordinate_spec, membership_specification, relation_coordinate_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  cases coordinate <;> rfl

theorem function_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (is_function_condition (.fvar .here)).satisfies
      (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      𝒩.relInterp .isRelation (.cons a .nil) ∧ ∀ input left right,
        (Mem 𝒩 (𝒩.funcInterp .orderedPair (.cons input (.cons left .nil))) a ∧
          Mem 𝒩 (𝒩.funcInterp .orderedPair (.cons input (.cons right .nil))) a) → left = right := by
  simp only [is_function_condition, function_single_valued_condition, function_single_valued_at_input,
    function_single_valued_at_left, function_single_valued_at_values,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem coordinate_specification (hℳ : Theory.Models ℳ theory) (coordinate : RelationCoordinate)
    (a output : Carrier ℳ) (hRelation : PureKuratowski.IsRelation ℳ a) :
    (PureRelationCoordinates.coordinateGraph coordinate).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env ℳ [] [setSort,setSort]) ↔
    (relation_coordinate_spec coordinate (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env (E hℳ).model [] [s,s]) := by
  apply (PureCoordinateSpecifications.coordinate_spec coordinate output a _ _ hRelation
    (union_value hℳ a) (union_value hℳ (F hℳ .union (.cons a .nil)))).trans
  apply Iff.trans ?_ (coordinate_semantics (E hℳ).model coordinate a output).symm
  exact forall_congr' (fun element => iff_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr (fun pair => and_congr Iff.rfl (projection_value hℳ coordinate pair element)))))

theorem domain (hℳ : Theory.Models ℳ theory) :
    domain_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output a
  intro hRelation
  exact ((PureCompletedStage.realizes hℳ).function .domain (.cons a .nil) output).symm.trans
    (coordinate_specification hℳ .domain a output ((relation_predicate hℳ a).mp hRelation))

theorem range (hℳ : Theory.Models ℳ theory) :
    range_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output a
  intro hRelation
  exact ((PureCompletedStage.realizes hℳ).function .range (.cons a .nil) output).symm.trans
    (coordinate_specification hℳ .range a output ((relation_predicate hℳ a).mp hRelation))

theorem is_function (hℳ : Theory.Models ℳ theory) :
    is_function_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  apply (function_predicate hℳ a).trans
  apply Iff.trans ?_ (function_semantics (E hℳ).model a).symm
  constructor
  · intro h
    exact ⟨(relation_predicate hℳ a).mpr h.1, fun input left right hs =>
      h.2 input left right ((pair_member hℳ input left a).mp hs.1) ((pair_member hℳ input right a).mp hs.2)⟩
  · intro h
    exact ⟨(relation_predicate hℳ a).mp h.1, fun input left right hl hr =>
      h.2 input left right ⟨(pair_member hℳ input left a).mpr hl, (pair_member hℳ input right a).mpr hr⟩⟩

theorem is_mapping (hℳ : Theory.Models ℳ theory) :
    is_mapping_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro target source function
  apply (mapping_predicate hℳ function source target).trans
  exact (PureMappingDefinitions.mapping_spec hℳ function source target _ _
    (domain_value hℳ function) (range_value hℳ function)).trans
      (and_congr (function_predicate hℳ function).symm
        (and_congr Iff.rfl (subset_value hℳ _ target).symm))

theorem application (hℳ : Theory.Models ℳ theory) :
    function_application_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output input function
  rintro ⟨hFunction, hInput⟩
  exact ((PureCompletedStage.realizes hℳ).function .application (.cons function (.cons input .nil)) output).symm.trans
    ((PureRelationFunctions.application_spec ((function_predicate hℳ function).mp hFunction)
      ((domain_value hℳ function input).mp hInput) output).trans (pair_member hℳ input output function).symm)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalMappings
