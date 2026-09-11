import YesMetaZFC.Model.ZFC.Pure.PureArithmeticStage

/-! # 加乘幂的原自然数规格

替换收集序数算术值列，零步与后继步给出原有限迭代见证；内部迭代唯一性
证明反向规格。加乘交换律只用于适配原正文的迭代参数方向。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticSpecifications
open PureModel PureNaturalInduction PureOrdinalArithmetic PureArithmeticStage
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
abbrev Operation := PureArithmeticRecurrence.Operation
variable {ℳ : Structure.{0,0,0,x} ℒ}

/-- 选择的空集与后继保留内部 ω 的封闭性。 -/
theorem zero_mem (hℳ : Theory.Models ℳ theory) : membership ℳ (zero hℳ) (omega hℳ) := by
  obtain ⟨empty,hEmpty,hMem⟩ := (omega_project hℳ).1.1
  have hEqual : empty = zero hℳ := extensionality hℳ empty (zero hℳ)
    (fun element => iff_of_false (hEmpty element) (zero_spec hℳ element))
  exact hEqual ▸ hMem

theorem succ_mem (hℳ : Theory.Models ℳ theory) {input : Carrier ℳ} (hInput : membership ℳ input (omega hℳ)) :
    membership ℳ (succ hℳ input) (omega hℳ) := by
  obtain ⟨successor,hSuccessor,hMem⟩ := (omega_project hℳ).1.2 input hInput
  have hEqual := _root_.YesMetaZFC.SetTheory.Structure.SuccessorOf.eq (project_models hℳ).1 hSuccessor (succ_project hℳ input)
  exact hEqual ▸ hMem

theorem input_mem_omega (hℳ : Theory.Models ℳ theory) {length input : Carrier ℳ}
    (hLength : membership ℳ length (omega hℳ)) (hInput : membership ℳ input (succ hℳ length)) :
    membership ℳ input (omega hℳ) :=
  (omega_project hℳ).transitive (project_modelsZF hℳ) (succ hℳ length) (succ_mem hℳ hLength) input hInput

theorem zero_mem_successor (hℳ : Theory.Models ℳ theory) {length : Carrier ℳ}
    (hLength : membership ℳ length (omega hℳ)) : membership ℳ (zero hℳ) (succ hℳ length) :=
  _root_.YesMetaZFC.SetTheory.Structure.IsOrdinal.empty_mem_of_nonempty
    (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ))
    ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) _ (succ_mem hℳ hLength))
    ⟨length,(succ_spec hℳ length length).mpr (Or.inr rfl)⟩ (zero_spec hℳ)

theorem successor_mem_successor (hℳ : Theory.Models ℳ theory) {length input : Carrier ℳ}
    (hLength : membership ℳ length (omega hℳ)) (hInput : membership ℳ input length) :
    membership ℳ (succ hℳ input) (succ hℳ length) := by
  have hInputOmega := (omega_project hℳ).transitive (project_modelsZF hℳ) length hLength input hInput
  have hLengthOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) length hLength
  have hSuccOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) _ (succ_mem hℳ hInputOmega)
  have hSubset : (Project.FirstOrderSemantics.reduct ℳ).MemberSubset (succ hℳ input) length := by
    intro member hMember
    rcases (succ_spec hℳ input member).mp hMember with hLess | rfl
    · exact hLengthOrdinal.transitive input hInput member hLess
    · exact hInput
  rcases _root_.YesMetaZFC.SetTheory.Structure.IsOrdinal.trichotomy (project_models hℳ).1 hSuccOrdinal hLengthOrdinal
    (_root_.YesMetaZFC.SetTheory.KP.difference_exists_d (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ)))
    (_root_.YesMetaZFC.SetTheory.KP.intersection_exists_d (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ)) (succ hℳ input) length) with hEqual | hLess | hGreater
  · exact (succ_spec hℳ length _).mpr (Or.inr ((project_models hℳ).1.eq_of_same_members _ _ hEqual))
  · exact (succ_spec hℳ length _).mpr (Or.inl hLess)
  · have hSelf := hSubset length hGreater
    exact False.elim (hLengthOrdinal.wellOrder.linear.irrefl length hSelf hSelf)

theorem ordinal_zero_value (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {base output : Carrier ℳ} (hBase : membership ℳ base (omega hℳ))
    (hOutput : OrdinalValue hℳ operation output base (zero hℳ)) :
    output = PureArithmeticRecurrence.seed hℳ operation base := by
  have hBaseOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) base hBase
  cases operation with
  | addition => exact (_root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_zero_iff
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (zero_spec hℳ)).mp hOutput
  | multiplication =>
    have hEmpty := (_root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_zero_iff
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hBaseOrdinal (zero_spec hℳ)).mp hOutput
    exact extensionality hℳ output (zero hℳ) (fun element => iff_of_false (hEmpty element) (zero_spec hℳ element))
  | exponentiation =>
    have hOne := (_root_.YesMetaZFC.SetTheory.ZF.ordinalExponentiation_zero_iff
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hBaseOrdinal (zero_spec hℳ)).mp hOutput
    exact _root_.YesMetaZFC.SetTheory.Structure.IsOrdinalOne.eq (project_models hℳ).1 hOne
      ⟨zero hℳ,zero_spec hℳ,succ_project hℳ (zero hℳ)⟩

/-- 已收集值列的后继步等于当前扩张中的实际算术步。 -/
theorem ordinal_step_value (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {base input current next : Carrier ℳ} (hBase : membership ℳ base (omega hℳ)) (hInput : membership ℳ input (omega hℳ))
    (hCurrent : OrdinalValue hℳ operation current base input)
    (hNext : OrdinalValue hℳ operation next base (succ hℳ input)) :
    next = PureArithmeticStage.step hℳ operation base base current := by
  have hBaseOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) base hBase
  have hInputOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) input hInput
  have hCurrentOmega := closed hℳ operation hBase hInput hCurrent
  cases operation with
  | addition =>
    obtain ⟨previous,hPrevious,hSuccessor⟩ := (_root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_successor_iff
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hInputOrdinal (succ_project hℳ input)).mp hNext
    have hEqual := ordinal_unique hℳ .addition hBase hInput hPrevious hCurrent
    subst previous
    exact _root_.YesMetaZFC.SetTheory.Structure.SuccessorOf.eq (project_models hℳ).1 hSuccessor (succ_project hℳ current)
  | multiplication =>
    obtain ⟨previous,hPrevious,hSum⟩ := (_root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_successor_iff
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hBaseOrdinal hInputOrdinal (succ_project hℳ input)).mp hNext
    have hEqual := ordinal_unique hℳ .multiplication hBase hInput hPrevious hCurrent
    subst previous
    exact ordinal_unique hℳ .addition hCurrentOmega hBase hSum (arithmetic_correct hℳ .addition hCurrentOmega hBase)
  | exponentiation =>
    obtain ⟨previous,hPrevious,hProduct⟩ := (_root_.YesMetaZFC.SetTheory.ZF.ordinalExponentiation_successor_iff
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hBaseOrdinal hInputOrdinal (succ_project hℳ input)).mp hNext
    have hEqual := ordinal_unique hℳ .exponentiation hBase hInput hPrevious hCurrent
    subst previous
    exact ordinal_unique hℳ .multiplication hCurrentOmega hBase hProduct (arithmetic_correct hℳ .multiplication hCurrentOmega hBase)

def base (operation : Operation) (left right : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition | .multiplication => right
  | .exponentiation => left

/-- 三种原算术规格都有内部有限序列见证。 -/
theorem iteration_exists (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    ∃ sequence, PureArithmeticRecurrence.Iteration hℳ (PureArithmeticRecurrence.length operation left right)
      (PureArithmeticRecurrence.seed hℳ operation right) (PureArithmeticStage.step hℳ operation left right)
      sequence (arithmetic hℳ operation left right) := by
  have hBase : membership ℳ (base operation left right) (omega hℳ) := by cases operation <;> first | exact hRight | exact hLeft
  have hLength : membership ℳ (PureArithmeticRecurrence.length operation left right) (omega hℳ) := by cases operation <;> first | exact hLeft | exact hRight
  obtain ⟨sequence,hMapping,hValues⟩ := sequence_exists hℳ operation hBase hLength
  have hValue {input : Carrier ℳ} (hInput : membership ℳ input (succ hℳ (PureArithmeticRecurrence.length operation left right))) :
      OrdinalValue hℳ operation (value hℳ sequence input) (base operation left right) input :=
    ((hValues input _).mp (application_member hℳ hMapping hInput)).2
  refine ⟨sequence,hMapping,?_,?_,?_⟩
  · have hZero := ordinal_zero_value hℳ operation hBase (hValue (zero_mem_successor hℳ hLength))
    cases operation <;> exact hZero
  · intro input hInput
    have hCurrent := (succ_spec hℳ _ input).mpr (Or.inl hInput)
    have hNext := successor_mem_successor hℳ hLength hInput
    have hStep := ordinal_step_value hℳ operation hBase (input_mem_omega hℳ hLength hCurrent) (hValue hCurrent) (hValue hNext)
    cases operation <;> exact hStep
  · have hLast := hValue ((succ_spec hℳ _ _).mpr (Or.inr rfl))
    have hActual := arithmetic_correct hℳ operation hLeft hRight
    cases operation with
    | addition => exact (_root_.YesMetaZFC.SetTheory.Structure.natural_add_comm (project_modelsZF hℳ)
        (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight hActual hLast).symm
    | multiplication => exact (_root_.YesMetaZFC.SetTheory.Structure.natural_mul_comm (project_modelsZF hℳ)
        (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight hActual hLast).symm
    | exponentiation => exact ordinal_unique hℳ .exponentiation hLeft hRight hLast hActual

/-- 原 guard 下，三个所选函数值逐输出精确满足原规格。 -/
theorem specification_correct (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (output : Carrier ℳ) :
    output = arithmetic hℳ operation left right ↔
      (PureArithmeticRecurrence.specification operation).satisfies
        (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (PureArithmeticStage.expansion hℳ).model [] [PureArithmeticStage.s,PureArithmeticStage.s,PureArithmeticStage.s]) := by
  rw [specification_semantics]
  obtain ⟨sequence,hSequence⟩ := iteration_exists hℳ operation hLeft hRight
  constructor
  · intro hEqual
    subst output
    exact ⟨arithmetic_closed hℳ operation hLeft hRight,sequence,hSequence⟩
  · rintro ⟨_,other,hOther⟩
    have hLength : membership ℳ (PureArithmeticRecurrence.length operation left right) (omega hℳ) := by
      cases operation <;> first | exact hLeft | exact hRight
    exact (PureArithmeticRecurrence.iteration_unique hℳ hLength hOther hSequence).2

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticSpecifications
