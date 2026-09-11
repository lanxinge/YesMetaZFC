import YesMetaZFC.Model.ZFC.Pure.PureConcatenationStage

/-! # 展平的内部累积序列

前段为空时取空序列；其余前段取定义域之并作为末项索引，追加族中的对应项。
这个纯公式算子在任意集合输入上全定义，故可直接应用内部超限递归。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFlattenRecursion
open PureModel PureNaturalInduction PureOrderSemantics PureFiniteSequenceCore PureArithmeticSpecifications
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev C (hℳ : Theory.Models ℳ theory) := PureConcatenationStage.expansion hℳ
noncomputable abbrev join (hℳ : Theory.Models ℳ theory) := PureConcatenationStage.concat hℳ
noncomputable abbrev unionValue (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :=
  (C hℳ).function .union (.cons input .nil)

theorem union_value (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) : PureSetIterations.Union input (unionValue hℳ input) := by
  have hGraph := ((PureConcatenationStage.realizes hℳ).function .union (.cons input .nil) _).mpr rfl
  exact (PureFunctionDefinitions.union_correct _ input).mp hGraph

theorem union_succ (hℳ : Theory.Models ℳ theory) {input : Carrier ℳ} (hInput : membership ℳ input (omega hℳ)) :
    unionValue hℳ (succ hℳ input) = input :=
  extensionality hℳ _ _ (fun element => (union_value hℳ _ element).trans (PureNaturalDifference.union_successor hℳ hInput element).symm)

def historyCondition : Formula S [] [s,s,s] :=
  let output : Term S [] [s,s,s] s := .fvar .here
  let history : Term S [] [s,s,s] s := .fvar (.there .here)
  let family : Term S [] [s,s,s] s := .fvar (.there (.there .here))
  let index := ⋃ₘ domₘ(history)
  ((domₘ(history) ≐ₘ ∅ₘ) ∧ₘ (output ≐ₘ ∅ₘ)) ∨ₘ
    ((domₘ(history) ≠ₘ ∅ₘ) ∧ₘ (output ≐ₘ ((history ·ₘ index) ⌢ₘ (family ·ₘ index))))

def History (hℳ : Theory.Models ℳ theory) (family history output : Carrier ℳ) : Prop :=
  (domain hℳ history = zero hℳ ∧ output = zero hℳ) ∨
    (domain hℳ history ≠ zero hℳ ∧ output = join hℳ (value hℳ history (unionValue hℳ (domain hℳ history)))
      (value hℳ family (unionValue hℳ (domain hℳ history))))
def historyPure := openFormula PureConcatenationStage.interpretation historyCondition

theorem history_correct (hℳ : Theory.Models ℳ theory) (family history output : Carrier ℳ) :
    historyPure.satisfies (templateEnv (.cons output (.cons history (.cons family .nil)))) ↔ History hℳ family history output := by
  apply (openFormula_correct (C hℳ) (PureConcatenationStage.realizes hℳ) historyCondition (.cons output (.cons history (.cons family .nil)))).trans
  change (((C hℳ).function .domain (.cons history .nil) = (C hℳ).function .emptySet .nil ∧ output = (C hℳ).function .emptySet .nil) ∨
    ((C hℳ).function .domain (.cons history .nil) ≠ (C hℳ).function .emptySet .nil ∧
      output = join hℳ ((C hℳ).function .application (.cons history (.cons (unionValue hℳ ((C hℳ).function .domain (.cons history .nil))) .nil)))
        ((C hℳ).function .application (.cons family (.cons (unionValue hℳ ((C hℳ).function .domain (.cons history .nil))) .nil))))) ↔ _
  simp only [PureConcatenationStage.domain_eq hℳ,PureConcatenationStage.zero_eq hℳ,PureConcatenationStage.value_eq hℳ]
  rfl

def operator := PureReplacement.schema historyPure
noncomputable abbrev parameters (hℳ : Theory.Models ℳ theory) (family : Carrier ℳ) := PureSeparation.parameterEnv (.cons family .nil) (zero hℳ)

theorem operator_correct (hℳ : Theory.Models ℳ theory) (family history output : Carrier ℳ) :
    operator.denote (parameters hℳ family) history output ↔ History hℳ family history output :=
  (PureReplacement.schema_correct hℳ historyPure (.cons family .nil) history output (zero hℳ)).trans (history_correct hℳ family history output)

theorem operator_functional (hℳ : Theory.Models ℳ theory) (family : Carrier ℳ) :
    (Project.FirstOrderSemantics.reduct ℳ).IsClassFunctionOnTransfiniteSequences (PureKuratowskiProject.interpretation hℳ) (operator.denote (parameters hℳ family)) := by
  classical
  intro history _
  by_cases hZero : domain hℳ history = zero hℳ
  · refine ⟨zero hℳ,(operator_correct hℳ family history _).mpr (Or.inl ⟨hZero,rfl⟩),?_⟩
    intro other hOther
    rcases (operator_correct hℳ family history other).mp hOther with ⟨_,hEqual⟩ | ⟨hNe,_⟩
    · exact hEqual
    · exact False.elim (hNe hZero)
  · refine ⟨join hℳ (value hℳ history (unionValue hℳ (domain hℳ history))) (value hℳ family (unionValue hℳ (domain hℳ history))),
      (operator_correct hℳ family history _).mpr (Or.inr ⟨hZero,rfl⟩),?_⟩
    intro other hOther
    rcases (operator_correct hℳ family history other).mp hOther with ⟨hEqual,_⟩ | ⟨_,hEqual⟩
    · exact False.elim (hZero hEqual)
    · exact hEqual

theorem sequence_domain (hℳ : Theory.Models ℳ theory) {sequence length : Carrier ℳ}
    (hSequence : (Project.FirstOrderSemantics.reduct ℳ).IsSequenceOfLength (PureKuratowskiProject.interpretation hℳ) sequence length) :
    domain hℳ sequence = length :=
  extensionality hℳ _ _ (fun input => (domain_correct hℳ sequence input).trans (hSequence.2.2 input).symm)

def Accumulates (hℳ : Theory.Models ℳ theory) (family accumulator : Carrier ℳ) : Prop :=
  Finite hℳ accumulator ∧ domain hℳ accumulator = succ hℳ (domain hℳ family) ∧
    value hℳ accumulator (zero hℳ) = zero hℳ ∧
      ∀ index, membership ℳ index (domain hℳ family) →
        value hℳ accumulator (succ hℳ index) = join hℳ (value hℳ accumulator index) (value hℳ family index)

/-- 内部递归产生精确长度为族长度后继的累积序列。 -/
theorem accumulator_exists (hℳ : Theory.Models ℳ theory) {family : Carrier ℳ} (hFamily : Finite hℳ family) :
    ∃ accumulator, Accumulates hℳ family accumulator := by
  obtain ⟨accumulator,hAccumulator⟩ := _root_.YesMetaZFC.SetTheory.ZF.recursiveSequence_exists (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (parameters hℳ family) operator (operator_functional hℳ family)
    ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) _ (succ_mem hℳ hFamily.2))
  have hDomain := sequence_domain hℳ hAccumulator.1
  have hFinite : Finite hℳ accumulator := ⟨hAccumulator.1.2.1,hDomain.symm ▸ succ_mem hℳ hFamily.2⟩
  have hPair (index : Carrier ℳ) (hIndex : membership ℳ index (succ hℳ (domain hℳ family))) :
      PureKuratowski.PairMember ℳ index (value hℳ accumulator index) accumulator :=
    application_member hℳ (mapping_self hℳ hFinite.1) (hDomain.symm ▸ hIndex)
  refine ⟨accumulator,hFinite,hDomain,?_,?_⟩
  · have hZero := zero_mem_successor hℳ hFamily.2
    obtain ⟨restricted,hRestricted,hOutput⟩ := hAccumulator.2 (zero hℳ) hZero _ (hPair _ hZero)
    have hRestrictedDomain := sequence_domain hℳ (hAccumulator.1.restriction hZero hRestricted)
    have hHistory := (operator_correct hℳ family restricted _).mp hOutput
    rcases hHistory with ⟨_,hEqual⟩ | ⟨hNe,_⟩
    · exact hEqual
    · exact False.elim (hNe hRestrictedDomain)
  · intro index hIndex
    have hSucc := successor_mem_successor hℳ hFamily.2 hIndex
    have hIndexOmega := (omega_project hℳ).transitive (project_modelsZF hℳ) _ hFamily.2 index hIndex
    obtain ⟨restricted,hRestricted,hOutput⟩ := hAccumulator.2 (succ hℳ index) hSucc _ (hPair _ hSucc)
    have hRestrictedSequence := hAccumulator.1.restriction hSucc hRestricted
    have hRestrictedDomain := sequence_domain hℳ hRestrictedSequence
    have hNonzero : domain hℳ restricted ≠ zero hℳ := by
      intro hEqual
      exact zero_spec hℳ index ((hRestrictedDomain.symm.trans hEqual) ▸ (succ_spec hℳ index index).mpr (Or.inr rfl))
    have hPrevious : unionValue hℳ (domain hℳ restricted) = index := by rw [hRestrictedDomain]; exact union_succ hℳ hIndexOmega
    have hIndexAcc := (succ_spec hℳ (domain hℳ family) index).mpr (Or.inl hIndex)
    have hRestrictedPair := (hRestricted.2 index (value hℳ accumulator index)).mpr ⟨(succ_spec hℳ index index).mpr (Or.inr rfl),hPair index hIndexAcc⟩
    have hValue := (pair_correct hℳ hRestrictedSequence.2.1 index _).mp hRestrictedPair
    rcases (operator_correct hℳ family restricted _).mp hOutput with ⟨hZero,_⟩ | ⟨_,hEqual⟩
    · exact False.elim (hNonzero hZero)
    · rw [hPrevious,← hValue.2] at hEqual
      exact hEqual

theorem dependencies_covered : formulaCovered PureConcatenationStage.functionCovered PureConcatenationStage.relationCovered historyCondition = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFlattenRecursion
