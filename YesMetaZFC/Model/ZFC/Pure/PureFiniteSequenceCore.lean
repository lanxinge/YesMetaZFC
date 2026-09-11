import YesMetaZFC.Model.ZFC.Pure.PureOrderSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.FiniteSequenceConcatenation
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison

/-! # 当前扩张中的有限序列与内部长度加法 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteSequenceCore
open PureModel PureNaturalInduction PureOrderSemantics
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable abbrev add (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :=
  (E hℳ).function .naturalAddition (.cons left (.cons right .nil))

def Finite (hℳ : Theory.Models ℳ theory) (function : Carrier ℳ) : Prop :=
  PureKuratowski.IsFunction ℳ function ∧ membership ℳ (domain hℳ function) (omega hℳ)

theorem finite_correct (hℳ : Theory.Models ℳ theory) {bound free : SortContext Nonlogical.BasicSetTheory.signature}
    (env : Env (E hℳ).model bound free) (sequence : Term Nonlogical.BasicSetTheory.signature bound free Nonlogical.BasicSetTheory.SetSort.set) :
    (FormalSystem.finite_sequence_condition sequence).satisfies env ↔ Finite hℳ (sequence.eval env) := by
  change ((E hℳ).relation .isFunction (.cons (sequence.eval env) .nil) ∧
    membership ℳ (domain hℳ (sequence.eval env)) ((E hℳ).function .omega .nil)) ↔ _
  rw [function_correct hℳ,omega_eq hℳ]
  rfl

theorem mapping_self (hℳ : Theory.Models ℳ theory) {function : Carrier ℳ} (hFunction : PureKuratowski.IsFunction ℳ function) :
    PureMappingDefinitions.IsMapping ℳ function (domain hℳ function) (range hℳ function) := by
  refine ⟨hFunction,domain_correct hℳ function,?_⟩
  intro input hInput
  obtain ⟨output,hPair⟩ := (domain_correct hℳ function input).mp hInput
  exact ⟨output,(range_correct hℳ function output).mpr ⟨input,hPair⟩,hPair⟩

theorem pair_correct (hℳ : Theory.Models ℳ theory) {function : Carrier ℳ} (hFunction : PureKuratowski.IsFunction ℳ function) (input output : Carrier ℳ) :
    PureKuratowski.PairMember ℳ input output function ↔ membership ℳ input (domain hℳ function) ∧ output = value hℳ function input := by
  constructor
  · intro hPair
    have hInput := (domain_correct hℳ function input).mpr ⟨output,hPair⟩
    exact ⟨hInput,hFunction.2 input output _ hPair (application_member hℳ (mapping_self hℳ hFunction) hInput)⟩
  · rintro ⟨hInput,hEqual⟩
    exact hEqual.symm ▸ application_member hℳ (mapping_self hℳ hFunction) hInput

theorem function_ext (hℳ : Theory.Models ℳ theory) {first second : Carrier ℳ}
    (hFirst : PureKuratowski.IsFunction ℳ first) (hSecond : PureKuratowski.IsFunction ℳ second)
    (hDomain : domain hℳ first = domain hℳ second)
    (hValues : ∀ input, membership ℳ input (domain hℳ first) → value hℳ first input = value hℳ second input) : first = second := by
  apply _root_.YesMetaZFC.SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (𝕀 := PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1 hFirst.1 hSecond.1
  intro input output
  change PureKuratowski.PairMember ℳ input output first ↔ PureKuratowski.PairMember ℳ input output second
  rw [pair_correct hℳ hFirst,pair_correct hℳ hSecond]
  constructor
  · rintro ⟨hInput,hOutput⟩
    exact ⟨hDomain ▸ hInput,hOutput.trans (hValues input hInput)⟩
  · rintro ⟨hInput,hOutput⟩
    have hIn := hDomain.symm ▸ hInput
    exact ⟨hIn,hOutput.trans (hValues input hIn).symm⟩

theorem mapping_domain (hℳ : Theory.Models ℳ theory) {function source target : Carrier ℳ}
    (hMap : PureMappingDefinitions.IsMapping ℳ function source target) : domain hℳ function = source :=
  extensionality hℳ _ _ (fun input => (domain_correct hℳ function input).trans (hMap.2.1 input).symm)

theorem add_ordinal (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    (Project.FirstOrderSemantics.reduct ℳ).IsOrdinalAddition (PureKuratowskiProject.interpretation hℳ) (add hℳ left right) left right := by
  rw [show add hℳ left right = PureArithmeticStage.arithmetic hℳ .addition left right from
    PureNaturalDifferenceStage.function_from_arithmetic hℳ .naturalAddition rfl _]
  exact PureArithmeticStage.arithmetic_correct hℳ .addition hLeft hRight

theorem add_mem (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) : membership ℳ (add hℳ left right) (omega hℳ) := by
  exact _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_mem_omega (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight (add_ordinal hℳ hLeft hRight)

theorem add_parts (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (input : Carrier ℳ) :
    membership ℳ input (add hℳ left right) ↔ membership ℳ input left ∨
      ∃ index, membership ℳ index right ∧ input = add hℳ left index := by
  apply (_root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_mem_iff (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ)
    ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) right hRight) (add_ordinal hℳ hLeft hRight)).trans
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨index,hIndex,hValue⟩
    have hIndexOmega := (omega_project hℳ).transitive (project_modelsZF hℳ) right hRight index hIndex
    exact ⟨index,hIndex,PureOrdinalArithmetic.ordinal_unique hℳ .addition hLeft hIndexOmega hValue (add_ordinal hℳ hLeft hIndexOmega)⟩
  · rintro ⟨index,hIndex,hEqual⟩
    exact ⟨index,hIndex,hEqual.symm ▸ add_ordinal hℳ hLeft ((omega_project hℳ).transitive (project_modelsZF hℳ) right hRight index hIndex)⟩

theorem add_not_mem_left (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) : ¬ membership ℳ (add hℳ left right) left := by
  intro hLess
  have hOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) left hLeft
  rcases _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_left_eq_or_mem (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ)
    ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) right hRight) (add_ordinal hℳ hLeft hRight) with hEqual | hMember
  · have hSelf : membership ℳ left left := (congrArg (fun x => membership ℳ x left) hEqual).mpr hLess
    exact hOrdinal.wellOrder.linear.irrefl left hSelf hSelf
  · have hSelf := hOrdinal.transitive _ hLess left hMember
    exact hOrdinal.wellOrder.linear.irrefl left hSelf hSelf

theorem add_injective (hℳ : Theory.Models ℳ theory) {left first second : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hFirst : membership ℳ first (omega hℳ)) (hSecond : membership ℳ second (omega hℳ))
    (hEqual : add hℳ left first = add hℳ left second) : first = second :=
  _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_right_injective (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ)
    ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) left hLeft)
    ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) first hFirst)
    ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) second hSecond)
    (hEqual ▸ add_ordinal hℳ hLeft hFirst) (add_ordinal hℳ hLeft hSecond)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteSequenceCore
