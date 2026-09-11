import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalTransfer
import YesMetaZFC.SetTheory.Foundation

/-! # 最终扩张的基础集合规格与原闭句

成员外延性保证所选函数图满足原定义；公式外壳只在抽象源结构上展开。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalBasic
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

abbrev Mem (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) :=
  𝒩.relInterp .membership (.cons a (.cons b .nil))
noncomputable abbrev F (hℳ : Theory.Models ℳ theory) := (E hℳ).function

/-! 任意源结构中的规格语义。 -/
theorem empty_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (empty_set_spec (.fvar .here)).satisfies (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      ∀ element, ¬ Mem 𝒩 element a := by
  simp only [empty_set_spec, membership_specification, empty_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies, not_true_eq_false]
  change (∀ element, Mem 𝒩 element a ↔ False) ↔ _
  simp only [iff_false]

theorem pair_semantics (𝒩 : Structure.{0,0,0,x} S) (a b c : 𝒩.Carrier s) :
    (pair_spec (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∀ element, Mem 𝒩 element c ↔ element = a ∨ element = b := by
  simp only [pair_spec, membership_specification, pair_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem union_semantics (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) :
    (union_spec (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, Mem 𝒩 element b ↔ ∃ member, Mem 𝒩 member a ∧ Mem 𝒩 element member := by
  simp only [union_spec, membership_specification, union_witness_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem subset_semantics (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) :
    (subset_condition (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, Mem 𝒩 element a → Mem 𝒩 element b := by
  simp only [subset_condition, Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem extensionality_semantics (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) :
    (extensionality_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ((∀ element, Mem 𝒩 element a ↔ Mem 𝒩 element b) → a = b) := by
  simp only [extensionality_instance, agreement_to_equality, membership_agreement,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

/-! 实际图与集合值的成员规格。 -/
theorem empty_value (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    a = F hℳ .emptySet .nil ↔ ∀ element, ¬ membership ℳ element a :=
  ((PureCompletedStage.realizes hℳ).function .emptySet .nil a).symm.trans
    (PureFunctionDefinitions.empty_correct a)

theorem pair_value (hℳ : Theory.Models ℳ theory) (a b c : Carrier ℳ) :
    c = F hℳ .unorderedPair (.cons a (.cons b .nil)) ↔
      ∀ element, membership ℳ element c ↔ element = a ∨ element = b :=
  ((PureCompletedStage.realizes hℳ).function .unorderedPair (.cons a (.cons b .nil)) c).symm.trans
    (PureFunctionDefinitions.pair_correct c a b)

theorem singleton_value (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    ∀ element, membership ℳ element (F hℳ .singleton (.cons a .nil)) ↔ element = a :=
  (PureFunctionDefinitions.singleton_correct _ a).mp
    (((PureCompletedStage.realizes hℳ).function .singleton (.cons a .nil) _).mpr rfl)

theorem union_value (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    ∀ element, membership ℳ element (F hℳ .union (.cons a .nil)) ↔
      ∃ member, membership ℳ member a ∧ membership ℳ element member :=
  (PureFunctionDefinitions.union_correct _ a).mp
    (((PureCompletedStage.realizes hℳ).function .union (.cons a .nil) _).mpr rfl)

theorem successor_value (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    ∀ element, membership ℳ element (F hℳ .successor (.cons a .nil)) ↔
      membership ℳ element a ∨ element = a :=
  (PureFunctionDefinitions.successor_correct _ a).mp
    (((PureCompletedStage.realizes hℳ).function .successor (.cons a .nil) _).mpr rfl)

theorem binary_union_value (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    ∀ element, membership ℳ element (F hℳ .binaryUnion (.cons a (.cons b .nil))) ↔
      membership ℳ element a ∨ membership ℳ element b :=
  (PureRelationSetOperations.binaryUnion_correct hℳ _ a b).mp
    (((PureCompletedStage.realizes hℳ).function .binaryUnion (.cons a (.cons b .nil)) _).mpr rfl)

theorem subset_value (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    (E hℳ).relation .subset (.cons a (.cons b .nil)) ↔
      ∀ element, membership ℳ element a → membership ℳ element b :=
  ((PureCompletedStage.realizes hℳ).relation .subset (.cons a (.cons b .nil))).symm.trans
    (PureRelationDefinitions.subset_correct a b)

/-! 原基础闭句。 -/
theorem extensionality_axiom (hℳ : Theory.Models ℳ theory) :
    Nonlogical.BasicSetTheory.extensionality_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro b a
  exact (extensionality_semantics (E hℳ).model a b).mpr (PureModel.extensionality hℳ a b)

theorem empty_set (hℳ : Theory.Models ℳ theory) :
    empty_set_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  exact (empty_value hℳ a).trans (empty_semantics (E hℳ).model a).symm

theorem pairing (hℳ : Theory.Models ℳ theory) :
    pair_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro c b a
  exact (pair_value hℳ a b c).trans (pair_semantics (E hℳ).model a b c).symm

theorem subset (hℳ : Theory.Models ℳ theory) :
    subset_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro b a
  exact (subset_value hℳ a b).trans (subset_semantics (E hℳ).model a b).symm

theorem singleton (hℳ : Theory.Models ℳ theory) :
    singleton_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  apply (pair_value hℳ a a _).mpr
  intro element
  exact (singleton_value hℳ a element).trans ⟨Or.inl, fun h => h.elim id id⟩

theorem binary_union (hℳ : Theory.Models ℳ theory) :
    binary_union_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro b a
  apply PureModel.extensionality hℳ
  intro element
  change membership ℳ element (F hℳ .binaryUnion (.cons a (.cons b .nil))) ↔
    membership ℳ element (F hℳ .union (.cons (F hℳ .unorderedPair (.cons a (.cons b .nil))) .nil))
  rw [binary_union_value, union_value]
  have hPair := (pair_value hℳ a b _).mp rfl
  constructor
  · intro h
    rcases h with h | h
    · exact ⟨a, (hPair a).mpr (Or.inl rfl), h⟩
    · exact ⟨b, (hPair b).mpr (Or.inr rfl), h⟩
  · rintro ⟨member, hMember, hElement⟩
    rcases (hPair member).mp hMember with rfl | rfl
    · exact Or.inl hElement
    · exact Or.inr hElement

theorem successor (hℳ : Theory.Models ℳ theory) :
    successor_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  apply PureModel.extensionality hℳ
  intro element
  change membership ℳ element (F hℳ .successor (.cons a .nil)) ↔
    membership ℳ element (F hℳ .binaryUnion (.cons a (.cons (F hℳ .unorderedPair (.cons a (.cons a .nil))) .nil)))
  rw [successor_value, binary_union_value]
  have hPair := (pair_value hℳ a a _).mp rfl
  rw [hPair]
  exact or_congr Iff.rfl ⟨Or.inl, fun h => h.elim id id⟩


theorem power_graph_correct (output input : Carrier ℳ) :
    (PureFunctionDefinitions.graph .powerSet).satisfies
      (templateEnv (.cons output (.cons input .nil)) : Env ℳ [] [setSort,setSort]) ↔
      ∀ element, membership ℳ element output ↔
        ∀ member, membership ℳ member element → membership ℳ member input := by
  rw [PureFunctionDefinitions.graph, PureFunctionDefinitions.comprehension_correct]
  rfl

theorem power_value (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    ∀ element, membership ℳ element (F hℳ .powerSet (.cons a .nil)) ↔
      ∀ member, membership ℳ member element → membership ℳ member a :=
  (power_graph_correct _ a).mp
    (((PureCompletedStage.realizes hℳ).function .powerSet (.cons a .nil) _).mpr rfl)

theorem pair_exists_semantics (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) :
    (pair_exists (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∃ output, ∀ element, Mem 𝒩 element output ↔ element = a ∨ element = b := by
  simp only [pair_exists, pair_spec, membership_specification, pair_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem union_exists_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (union_exists (.fvar .here)).satisfies
      (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      ∃ output, ∀ element, Mem 𝒩 element output ↔ ∃ member, Mem 𝒩 member a ∧ Mem 𝒩 element member := by
  simp only [union_exists, union_spec, membership_specification, union_witness_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem union_definition_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (union_definition_instance (.fvar .here)).satisfies
      (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      ∀ element, Mem 𝒩 element (𝒩.funcInterp .union (.cons a .nil)) ↔
        ∃ member, Mem 𝒩 member a ∧ Mem 𝒩 element member := by
  simp only [union_definition_instance, union_spec, membership_specification, union_witness_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem power_exists_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (power_set_exists (.fvar .here)).satisfies
      (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      ∃ output, ∀ element, Mem 𝒩 element output ↔
        𝒩.relInterp .subset (.cons element (.cons a .nil)) := by
  simp only [power_set_exists, power_set_spec, membership_specification,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem power_definition_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (power_set_definition_instance (.fvar .here)).satisfies
      (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      ∀ element, Mem 𝒩 element (𝒩.funcInterp .powerSet (.cons a .nil)) ↔
        𝒩.relInterp .subset (.cons element (.cons a .nil)) := by
  simp only [power_set_definition_instance, power_set_spec, membership_specification,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem pairing_exists (hℳ : Theory.Models ℳ theory) :
    pairing_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro b a
  exact (pair_exists_semantics (E hℳ).model a b).mpr (PureModel.pair hℳ a b)

theorem union_exists_axiom (hℳ : Theory.Models ℳ theory) :
    union_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  exact (union_exists_semantics (E hℳ).model a).mpr (PureModel.union hℳ a)

theorem union_definition (hℳ : Theory.Models ℳ theory) :
    union_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  exact (union_definition_semantics (E hℳ).model a).mpr (union_value hℳ a)

theorem power_exists_axiom (hℳ : Theory.Models ℳ theory) :
    power_set_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  apply (power_exists_semantics (E hℳ).model a).mpr
  exact ⟨F hℳ .powerSet (.cons a .nil), fun element =>
    (power_value hℳ a element).trans (subset_value hℳ element a).symm⟩

theorem power_definition (hℳ : Theory.Models ℳ theory) :
    power_set_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  exact (power_definition_semantics (E hℳ).model a).mpr (fun element =>
    (power_value hℳ a element).trans (subset_value hℳ element a).symm)

theorem irreflexivity (hℳ : Theory.Models ℳ theory) :
    membership_irreflexive_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  exact _root_.YesMetaZFC.SetTheory.KP.mem_irrefl_d
    (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ)) a

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalBasic
