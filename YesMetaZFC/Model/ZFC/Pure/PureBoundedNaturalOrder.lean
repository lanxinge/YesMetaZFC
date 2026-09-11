import YesMetaZFC.Model.ZFC.Pure.PureNaturalOrderType

/-! # 有界自然数子集上的自然离散序

最大元由最小严格上界的前驱得到；构造全程使用模型内部的分离与良序。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureBoundedNaturalOrder
open PureModel PureNaturalInduction PureOrderSemantics PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

def upperCondition : Formula ℒ [] [setSort,setSort] := .forallE setSort <|
  .imp (PureRelationDefinitions.mem (.bvar .here) (.fvar (.there .here))) (PureRelationDefinitions.mem (.bvar .here) (.fvar .here))

/-- 有内部自然数上界的任意非空子集有最大元。 -/
theorem greatest_of_bounded (hℳ : Theory.Models ℳ theory) {subset bound : Carrier ℳ}
    (hBound : membership ℳ bound (omega hℳ))
    (hSubset : ∀ input, membership ℳ input subset → membership ℳ input bound)
    (hNonempty : ∃ input, membership ℳ input subset) :
    ∃ greatest, membership ℳ greatest subset ∧ ∀ input, membership ℳ input subset → greatest ≠ input → membership ℳ input greatest := by
  classical
  obtain ⟨uppers,hUppers⟩ := PureSeparation.exists_subset hℳ upperCondition (.cons subset .nil) (omega hℳ)
  have hU (candidate : Carrier ℳ) : membership ℳ candidate uppers ↔ membership ℳ candidate (omega hℳ) ∧
      ∀ input, membership ℳ input subset → membership ℳ input candidate := hUppers candidate
  obtain ⟨least,hLeast,hMinimal⟩ := (omega_project hℳ).membershipWellOrder (project_modelsZF hℳ) |>.least
    uppers (fun input hInput => ((hU input).mp hInput).1) ⟨bound,(hU bound).mpr ⟨hBound,hSubset⟩⟩
  have hLeastData := (hU least).mp hLeast
  have hLeastNonempty : ∃ input, membership ℳ input least := by
    obtain ⟨input,hInput⟩ := hNonempty
    exact ⟨input,hLeastData.2 input hInput⟩
  obtain ⟨previous,hPrevious,hSuccessor⟩ := (omega_project hℳ).exists_predecessor_of_mem_of_nonempty
    (project_modelsZF hℳ) hLeastData.1 hLeastNonempty
  have hEqual := _root_.YesMetaZFC.SetTheory.Structure.SuccessorOf.eq (project_models hℳ).1 hSuccessor (succ_project hℳ previous)
  have hPreviousLeast : membership ℳ previous least := hEqual.symm ▸ (succ_spec hℳ previous previous).mpr (Or.inr rfl)
  have hPreviousNotUpper : ¬ membership ℳ previous uppers := by
    intro hUpper
    have hLeastOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) least hLeastData.1
    rcases hMinimal previous hUpper with hSame | hLess
    · have hSameEq := (project_models hℳ).1.eq_of_same_members least previous hSame
      have hSelf : membership ℳ least least := (congrArg (fun input => membership ℳ input least) hSameEq).mpr hPreviousLeast
      exact hLeastOrdinal.wellOrder.linear.irrefl least hSelf hSelf
    · have hSelf := hLeastOrdinal.transitive previous hPreviousLeast least hLess
      exact hLeastOrdinal.wellOrder.linear.irrefl least hSelf hSelf
  have hWitness : ∃ input, membership ℳ input subset ∧ ¬ membership ℳ input previous := by
    by_cases h : ∃ input, membership ℳ input subset ∧ ¬ membership ℳ input previous
    · exact h
    · apply False.elim
      apply hPreviousNotUpper ((hU previous).mpr ⟨hPrevious,?_⟩)
      intro input hInput
      by_cases hIn : membership ℳ input previous
      · exact hIn
      · exact False.elim (h ⟨input,hInput,hIn⟩)
  obtain ⟨witness,hWitness,hNotPrevious⟩ := hWitness
  have hWitnessSucc : membership ℳ witness (succ hℳ previous) := hEqual ▸ hLeastData.2 witness hWitness
  have hWitnessEqual : witness = previous := ((succ_spec hℳ previous witness).mp hWitnessSucc).resolve_left hNotPrevious
  refine ⟨previous,hWitnessEqual ▸ hWitness,?_⟩
  intro input hInput hNe
  have hInputSucc : membership ℳ input (succ hℳ previous) := hEqual ▸ hLeastData.2 input hInput
  exact ((succ_spec hℳ previous input).mp hInputSucc).resolve_right (Ne.symm hNe)

theorem least_on_subset (hℳ : Theory.Models ℳ theory) {carrier : Carrier ℳ}
    (hSubset : ∀ input, membership ℳ input carrier → membership ℳ input (omega hℳ)) : Extremes (epsilon hℳ carrier) carrier false := by
  intro subset hSubsetCarrier hNonempty
  obtain ⟨least,hLeast,hMinimal⟩ := (omega_project hℳ).membershipWellOrder (project_modelsZF hℳ) |>.least
    subset (fun input hInput => hSubset input (hSubsetCarrier input hInput)) hNonempty
  refine ⟨least,hLeast,fun input hInput hNe => ?_⟩
  apply (epsilon_correct hℳ carrier least input).mpr
  refine ⟨hSubsetCarrier least hLeast,hSubsetCarrier input hInput,?_⟩
  rcases hMinimal input hInput with hSame | hLess
  · exact False.elim (hNe ((project_models hℳ).1.eq_of_same_members least input hSame))
  · exact hLess

theorem natural_order (hℳ : Theory.Models ℳ theory) {carrier bound : Carrier ℳ}
    (hBound : membership ℳ bound (omega hℳ))
    (hSubset : ∀ input, membership ℳ input carrier → membership ℳ input bound) :
    Linear (epsilon hℳ carrier) carrier ∧ Extremes (epsilon hℳ carrier) carrier true ∧ Extremes (epsilon hℳ carrier) carrier false := by
  have hOmegaSubset := fun input hInput => (omega_project hℳ).transitive (project_modelsZF hℳ) bound hBound input (hSubset input hInput)
  refine ⟨epsilon_linear hℳ ((omega_project hℳ).isOrdinal (project_modelsZF hℳ)) hOmegaSubset,?_,least_on_subset hℳ hOmegaSubset⟩
  intro subset hSubsetCarrier hNonempty
  obtain ⟨greatest,hGreatest,hMaximal⟩ := greatest_of_bounded hℳ hBound
    (fun input hInput => hSubset input (hSubsetCarrier input hInput)) hNonempty
  exact ⟨greatest,hGreatest,fun input hInput hNe => (epsilon_correct hℳ carrier input greatest).mpr
    ⟨hSubsetCarrier input hInput,hSubsetCarrier greatest hGreatest,hMaximal input hInput hNe⟩⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureBoundedNaturalOrder
