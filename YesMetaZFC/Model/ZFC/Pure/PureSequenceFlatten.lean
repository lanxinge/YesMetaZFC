import YesMetaZFC.Model.ZFC.Pure.PureFlattenRecursion

/-! # 有限序列族展平的纯定义图

内部公式归纳保持各步有限性，并比较任意两个满足原规格的累积序列。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceFlatten
open PureModel PureNaturalInduction PureOrderSemantics PureFiniteSequenceCore PureFlattenRecursion PureArithmeticSpecifications
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

def Family (hℳ : Theory.Models ℳ theory) (family : Carrier ℳ) : Prop :=
  Finite hℳ family ∧ ∀ index, membership ℳ index (domain hℳ family) → Finite hℳ (value hℳ family index)

theorem empty_finite (hℳ : Theory.Models ℳ theory) : Finite hℳ (zero hℳ) := by
  have hSequence := _root_.YesMetaZFC.SetTheory.Structure.IsSequenceOfLength.empty (PureKuratowskiProject.interpretation hℳ) (zero_spec hℳ)
  exact ⟨hSequence.2.1,(sequence_domain hℳ hSequence).symm ▸ zero_mem hℳ⟩

def finiteValuesWithin : Formula S [] [s,s,s] :=
  let index : Term S [] [s,s,s] s := .fvar .here
  let accumulator : Term S [] [s,s,s] s := .fvar (.there .here)
  let length : Term S [] [s,s,s] s := .fvar (.there (.there .here))
  (index ∈ₘ length) ⟶ₘ FormalSystem.finite_sequence_condition (accumulator ·ₘ index)

theorem finite_values_correct (hℳ : Theory.Models ℳ theory) (index accumulator length : Carrier ℳ) :
    (openFormula PureConcatenationStage.interpretation finiteValuesWithin).satisfies
      (templateEnv (.cons index (.cons accumulator (.cons length .nil)))) ↔
        (membership ℳ index length → Finite hℳ (value hℳ accumulator index)) := by
  apply (openFormula_correct (C hℳ) (PureConcatenationStage.realizes hℳ) finiteValuesWithin (.cons index (.cons accumulator (.cons length .nil)))).trans
  change (membership ℳ index length → (FormalSystem.finite_sequence_condition
    (function_application_term (.fvar (.there .here)) (.fvar .here))).satisfies
      (templateEnv (.cons index (.cons accumulator (.cons length .nil))) : Env (C hℳ).model [] [s,s,s])) ↔ _
  rw [PureConcatenationStage.finite_correct hℳ]
  change (membership ℳ index length → Finite hℳ ((C hℳ).function .application (.cons accumulator (.cons index .nil)))) ↔ _
  rw [PureConcatenationStage.value_eq hℳ]

/-- 累积列中每个合法位置的值都是内部有限序列。 -/
theorem accumulator_finite_values (hℳ : Theory.Models ℳ theory) {family accumulator : Carrier ℳ}
    (hFamily : Family hℳ family) (hAccumulator : Accumulates hℳ family accumulator) :
    ∀ index, membership ℳ index (succ hℳ (domain hℳ family)) → Finite hℳ (value hℳ accumulator index) := by
  have hValues := pure_induction hℳ (openFormula PureConcatenationStage.interpretation finiteValuesWithin)
    (.cons accumulator (.cons (succ hℳ (domain hℳ family)) .nil))
    ((finite_values_correct hℳ _ _ _).mpr (fun _ => hAccumulator.2.2.1.symm ▸ empty_finite hℳ))
    (fun index _ hPrevious => (finite_values_correct hℳ _ _ _).mpr (fun hNext => by
      have hIndex := predecessor_mem hℳ hFamily.1.2 hNext
      have hFinite := (finite_values_correct hℳ _ _ _).mp hPrevious ((succ_spec hℳ (domain hℳ family) index).mpr (Or.inl hIndex))
      rw [hAccumulator.2.2.2 index hIndex]
      exact (PureConcatenationStage.concat_correct hℳ hFinite (hFamily.2 index hIndex)).1))
  intro index hIndex
  exact (finite_values_correct hℳ _ _ _).mp (hValues index (input_mem_omega hℳ hFamily.1.2 hIndex)) hIndex

/-- 原递推方程确定整个累积函数图，不要求预先给出公共值域。 -/
theorem accumulator_unique (hℳ : Theory.Models ℳ theory) {family first second : Carrier ℳ}
    (hFamily : Finite hℳ family) (hFirst : Accumulates hℳ family first) (hSecond : Accumulates hℳ family second) : first = second := by
  have hValues : ∀ index, membership ℳ index (omega hℳ) → membership ℳ index (succ hℳ (domain hℳ family)) →
      value hℳ first index = value hℳ second index := by
    apply source_induction hℳ equalValuesWithin (.cons first (.cons second (.cons (succ hℳ (domain hℳ family)) .nil)))
    · exact fun _ => hFirst.2.2.1.trans hSecond.2.2.1.symm
    · intro index _ hPrevious hNext
      change value hℳ first (succ hℳ index) = value hℳ second (succ hℳ index)
      change membership ℳ index (succ hℳ (domain hℳ family)) → value hℳ first index = value hℳ second index at hPrevious
      have hIndex := predecessor_mem hℳ hFamily.2 hNext
      rw [hFirst.2.2.2 index hIndex,hSecond.2.2.2 index hIndex,
        hPrevious ((succ_spec hℳ (domain hℳ family) index).mpr (Or.inl hIndex))]
  apply function_ext hℳ hFirst.1.1 hSecond.1.1 (hFirst.2.1.trans hSecond.2.1.symm)
  intro index hIndex
  have hIn := hFirst.2.1 ▸ hIndex
  exact hValues index (input_mem_omega hℳ hFamily.2 hIn) hIn

def Flattens (hℳ : Theory.Models ℳ theory) (family output : Carrier ℳ) : Prop :=
  Finite hℳ output ∧ ∃ accumulator, Accumulates hℳ family accumulator ∧ output = value hℳ accumulator (domain hℳ family)

theorem exists_flattening (hℳ : Theory.Models ℳ theory) {family : Carrier ℳ} (hFamily : Family hℳ family) :
    ∃ output, Flattens hℳ family output := by
  obtain ⟨accumulator,hAccumulator⟩ := accumulator_exists hℳ hFamily.1
  exact ⟨value hℳ accumulator (domain hℳ family),accumulator_finite_values hℳ hFamily hAccumulator _
    ((succ_spec hℳ (domain hℳ family) (domain hℳ family)).mpr (Or.inr rfl)),accumulator,hAccumulator,rfl⟩

theorem unique (hℳ : Theory.Models ℳ theory) {family first second : Carrier ℳ} (hFamily : Finite hℳ family)
    (hFirst : Flattens hℳ family first) (hSecond : Flattens hℳ family second) : first = second := by
  obtain ⟨_,f,hF,hFirst⟩ := hFirst
  obtain ⟨_,g,hG,hSecond⟩ := hSecond
  rw [hFirst,hSecond,accumulator_unique hℳ hFamily hF hG]

def guard : Formula S [] [s,s] := FormalSystem.finite_sequence_family_condition (.fvar (.there .here))
def specification : Formula S [] [s,s] := FormalSystem.finite_sequence_flatten_spec (.fvar (.there .here)) (.fvar .here)
def body : Formula ℒ [] [setSort,setSort] := openFormula PureConcatenationStage.interpretation (.conj guard specification)
def graph : Formula ℒ [] [setSort,setSort] := _root_.YesMetaZFC.Automation.TotalizedGraph.formula body PureRelationFunctions.emptyFallback

theorem family_correct (hℳ : Theory.Models ℳ theory) {bound free : SortContext S} (env : Env (C hℳ).model bound free)
    (family : Term S bound free s) :
    (FormalSystem.finite_sequence_family_condition family).satisfies env ↔ Family hℳ (family.eval env) := by
  simp only [FormalSystem.finite_sequence_family_condition,Formula.satisfies_forallFreeTop,Formula.satisfies,PureConcatenationStage.finite_correct hℳ,
    membership_formula,domain_term,function_application_term,Term.eval,Arguments.eval,Term.eval_weakenFree,Expansion.model]
  change (Finite hℳ (family.eval env) ∧ ∀ index, membership ℳ index ((C hℳ).function .domain (.cons (family.eval env) .nil)) →
    Finite hℳ ((C hℳ).function .application (.cons (family.eval env) (.cons index .nil)))) ↔ _
  simp only [PureConcatenationStage.domain_eq hℳ,PureConcatenationStage.value_eq hℳ]
  rfl

theorem specification_correct (hℳ : Theory.Models ℳ theory) (family output : Carrier ℳ) :
    specification.satisfies (templateEnv (.cons output (.cons family .nil)) : Env (C hℳ).model [] [s,s]) ↔ Flattens hℳ family output := by
  simp only [specification,FormalSystem.finite_sequence_flatten_spec,FormalSystem.finite_sequence_flatten_step_condition,
    Formula.satisfies_existsFreeTop,Formula.satisfies_forallFreeTop,Formula.satisfies,PureConcatenationStage.finite_correct hℳ]
  change (Finite hℳ output ∧ ∃ accumulator, Finite hℳ accumulator ∧
    (C hℳ).function .domain (.cons accumulator .nil) = (C hℳ).function .successor (.cons ((C hℳ).function .domain (.cons family .nil)) .nil) ∧
      (C hℳ).function .application (.cons accumulator (.cons ((C hℳ).function .emptySet .nil) .nil)) = (C hℳ).function .emptySet .nil ∧
        ∀ index, (membership ℳ index ((C hℳ).function .domain (.cons family .nil)) →
          (C hℳ).function .application (.cons accumulator (.cons ((C hℳ).function .successor (.cons index .nil)) .nil)) =
            join hℳ ((C hℳ).function .application (.cons accumulator (.cons index .nil))) ((C hℳ).function .application (.cons family (.cons index .nil)))) ∧
          output = (C hℳ).function .application (.cons accumulator (.cons ((C hℳ).function .domain (.cons family .nil)) .nil))) ↔ _
  simp only [PureConcatenationStage.domain_eq hℳ,PureConcatenationStage.value_eq hℳ,PureConcatenationStage.zero_eq hℳ,PureConcatenationStage.succ_eq hℳ]
  constructor
  · rintro ⟨hFinite,accumulator,hAcc,hDomain,hZero,hSteps⟩
    exact ⟨hFinite,accumulator,⟨hAcc,hDomain,hZero,fun index hIndex => (hSteps index).1 hIndex⟩,(hSteps (zero hℳ)).2⟩
  · rintro ⟨hFinite,accumulator,⟨hAcc,hDomain,hZero,hSteps⟩,hOutput⟩
    exact ⟨hFinite,accumulator,hAcc,hDomain,hZero,fun index => ⟨hSteps index,hOutput⟩⟩

theorem body_correct (hℳ : Theory.Models ℳ theory) (family output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons family .nil))) ↔ Family hℳ family ∧ Flattens hℳ family output := by
  apply (openFormula_correct (C hℳ) (PureConcatenationStage.realizes hℳ) (.conj guard specification) (.cons output (.cons family .nil))).trans
  exact and_congr (family_correct hℳ _ _) (specification_correct hℳ family output)

theorem exists_body (hℳ : Theory.Models ℳ theory) {family : Carrier ℳ} (hFamily : Family hℳ family) :
    ∃ output, body.satisfies (templateEnv (.cons output (.cons family .nil))) := by
  obtain ⟨output,hOutput⟩ := exists_flattening hℳ hFamily
  exact ⟨output,(body_correct hℳ family output).mpr ⟨hFamily,hOutput⟩⟩

theorem functional (hℳ : Theory.Models ℳ theory) (family : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons family .nil))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons family .nil))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ body (.cons family .nil)
  intro first second hFirst hSecond
  have hF := (body_correct hℳ family first).mp hFirst
  have hS := (body_correct hℳ family second).mp hSecond
  exact unique hℳ hF.1.1 hF.2 hS.2

theorem agrees (hℳ : Theory.Models ℳ theory) {family : Carrier ℳ} (hFamily : Family hℳ family) (output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons family .nil))) ↔
      specification.satisfies (templateEnv (.cons output (.cons family .nil)) : Env (C hℳ).model [] [s,s]) :=
  (PureRelationFunctions.totalized_agrees body (.cons family .nil) (exists_body hℳ hFamily) output).trans
    ((body_correct hℳ family output).trans (Iff.trans ⟨And.right,fun h => ⟨hFamily,h⟩⟩ (specification_correct hℳ family output).symm))

theorem dependencies_covered : formulaCovered PureConcatenationStage.functionCovered PureConcatenationStage.relationCovered (.conj guard specification) = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceFlatten
