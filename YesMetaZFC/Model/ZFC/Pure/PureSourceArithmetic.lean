import YesMetaZFC.Model.ZFC.Pure.PureSourceMappings

/-! # 全部内部自然数上的算术对应

任意原模型的有限递推见证都是同一个纯隶属模型中的集合函数。把两侧递推图
放入已有内部唯一性定理，依次确定加、乘、幂；长度不要求外部标准。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceArithmetic
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
open PureSourceMappings
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}
abbrev Operation := PureArithmeticRecurrence.Operation

def arithmetic (𝒩 : Structure.{0,0,0,x} signature) (operation : Operation) (left right : 𝒩.Carrier .set) :=
  match operation with
  | .addition => sum 𝒩 left right
  | .multiplication => product 𝒩 left right
  | .exponentiation => power 𝒩 left right

def seed (𝒩 : Structure.{0,0,0,x} signature) (operation : Operation) (right : 𝒩.Carrier .set) :=
  match operation with
  | .addition => right
  | .multiplication => z 𝒩
  | .exponentiation => suc 𝒩 (z 𝒩)

def step (𝒩 : Structure.{0,0,0,x} signature) (operation : Operation) (left right current : 𝒩.Carrier .set) :=
  match operation with
  | .addition => suc 𝒩 current
  | .multiplication => sum 𝒩 current right
  | .exponentiation => product 𝒩 current left

def Iteration (𝒩 : Structure.{0,0,0,x} signature) (length initial : 𝒩.Carrier .set)
    (next : 𝒩.Carrier .set → 𝒩.Carrier .set) (sequence output : 𝒩.Carrier .set) : Prop :=
  Mapping 𝒩 sequence (suc 𝒩 length) (w 𝒩) ∧ value 𝒩 sequence (z 𝒩) = initial ∧
    (∀ input, mem 𝒩 input length → value 𝒩 sequence (suc 𝒩 input) = next (value 𝒩 sequence input)) ∧
      value 𝒩 sequence length = output

theorem specification_semantics (operation : Operation) (left right output : 𝒩.Carrier .set) :
    (PureArithmeticRecurrence.specification operation).satisfies
      (templateEnv (.cons output (.cons left (.cons right .nil))) : Env 𝒩 [] [.set,.set,.set]) ↔
    mem 𝒩 output (w 𝒩) ∧ ∃ sequence,
      Iteration 𝒩 (PureArithmeticRecurrence.length (ℳ := PureProjectEmbedding.reduct 𝒩) operation left right) (seed 𝒩 operation right)
        (step 𝒩 operation left right) sequence output := by
  cases operation <;>
    simp only [PureArithmeticRecurrence.specification, natural_addition_spec,
      natural_multiplication_spec, natural_exponentiation_spec,
      natural_addition_bound_graph_condition, natural_multiplication_bound_graph_condition,
      natural_exponentiation_bound_graph_condition, natural_addition_graph_condition,
      natural_multiplication_graph_condition, natural_exponentiation_graph_condition,
      Formula.satisfies_existsFreeTop, Formula.satisfies_forallFreeTop, Formula.satisfies] <;> rfl

theorem specification (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : Operation)
    {left right : 𝒩.Carrier .set} (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩)) :
    mem 𝒩 (arithmetic 𝒩 operation left right) (w 𝒩) ∧ ∃ sequence,
      Iteration 𝒩 (PureArithmeticRecurrence.length (ℳ := PureProjectEmbedding.reduct 𝒩) operation left right) (seed 𝒩 operation right)
        (step 𝒩 operation left right) sequence (arithmetic 𝒩 operation left right) := by
  apply (specification_semantics operation left right _).mp
  cases operation with
  | addition =>
    have h := (intrinsic_zfc_arithmetic_support.addition_definition_instance_derives
      (Γ := []) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar .here : SetOpenTerm [.set,.set,.set])).sound h𝒩
        (templateEnv (.cons (sum 𝒩 left right) (.cons left (.cons right .nil)))) (by intro φ h; cases h)
    exact (h ⟨hLeft,hRight⟩).mp rfl
  | multiplication =>
    have h := (intrinsic_zfc_arithmetic_support.multiplication_definition_instance_derives
      (Γ := []) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar .here : SetOpenTerm [.set,.set,.set])).sound h𝒩
        (templateEnv (.cons (product 𝒩 left right) (.cons left (.cons right .nil)))) (by intro φ h; cases h)
    exact (h ⟨hLeft,hRight⟩).mp rfl
  | exponentiation =>
    have h := (intrinsic_zfc_arithmetic_support.exponentiation_definition_instance_derives
      (Γ := []) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar .here : SetOpenTerm [.set,.set,.set])).sound h𝒩
        (templateEnv (.cons (power 𝒩 left right) (.cons left (.cons right .nil)))) (by intro φ h; cases h)
    exact (h ⟨hLeft,hRight⟩).mp rfl

theorem zero_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    z 𝒩 = PureNaturalInduction.zero (PureZFCModels.reduct_models h𝒩) :=
  (empty_agrees h𝒩).trans (zero_final _)
theorem successor_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (input : 𝒩.Carrier .set) :
    suc 𝒩 input = PureNaturalInduction.succ (PureZFCModels.reduct_models h𝒩) input :=
  (successor_agrees h𝒩 input).trans (succ_final _ _)
theorem omega_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    w 𝒩 = PureNaturalInduction.omega (PureZFCModels.reduct_models h𝒩) :=
  (omega_agrees h𝒩).trans (omega_final _)

/-- 任意原递推图进入同一个纯集合函数唯一性接口。 -/
theorem iteration_project (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {length initial sequence output : 𝒩.Carrier .set} {next : 𝒩.Carrier .set → 𝒩.Carrier .set}
    (hLength : mem 𝒩 length (w 𝒩)) (hIteration : Iteration 𝒩 length initial next sequence output) :
    PureArithmeticRecurrence.Iteration (PureZFCModels.reduct_models h𝒩) length initial next sequence output := by
  let hℳ := PureZFCModels.reduct_models h𝒩
  have hNatural : PureModel.membership (PureProjectEmbedding.reduct 𝒩) length (PureNaturalInduction.omega hℳ) :=
    omega_value h𝒩 ▸ hLength
  have hMapping := mapping_project h𝒩 hIteration.1
  rw [successor_value h𝒩, omega_value h𝒩] at hMapping
  have hValue (input : 𝒩.Carrier .set)
      (hInput : PureModel.membership (PureProjectEmbedding.reduct 𝒩) input (PureNaturalInduction.succ hℳ length)) :
      value 𝒩 sequence input = PureNaturalInduction.value hℳ sequence input :=
    application_value h𝒩 hIteration.1 ((successor_value h𝒩 length).symm ▸ hInput)
  refine ⟨hMapping, ?_, ?_, ?_⟩
  · have hZero := hIteration.2.1
    rw [zero_value h𝒩, hValue _ (PureArithmeticSpecifications.zero_mem_successor hℳ hNatural)] at hZero
    exact hZero
  · intro input hInput
    have hStep := hIteration.2.2.1 input hInput
    rw [successor_value h𝒩 input, hValue _ (PureArithmeticSpecifications.successor_mem_successor hℳ hNatural hInput),
      hValue _ ((PureNaturalInduction.succ_spec hℳ length input).mpr (Or.inl hInput))] at hStep
    exact hStep
  · exact (hValue _ ((PureNaturalInduction.succ_spec hℳ length length).mpr (Or.inr rfl))).symm.trans hIteration.2.2.2

theorem iteration_change_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {length initial sequence output : 𝒩.Carrier .set} {first second : 𝒩.Carrier .set → 𝒩.Carrier .set}
    (hIteration : PureArithmeticRecurrence.Iteration (PureZFCModels.reduct_models h𝒩)
      length initial first sequence output)
    (hStep : ∀ current, mem 𝒩 current (w 𝒩) → first current = second current) :
    PureArithmeticRecurrence.Iteration (PureZFCModels.reduct_models h𝒩) length initial second sequence output := by
  refine ⟨hIteration.1, hIteration.2.1, ?_, hIteration.2.2.2⟩
  intro input hInput
  have hIn := (PureNaturalInduction.succ_spec (PureZFCModels.reduct_models h𝒩) length input).mpr (Or.inl hInput)
  obtain ⟨current, hCurrent, hGraph⟩ := hIteration.1.2.2 input hIn
  have hEqual := hIteration.1.1.2 input _ current
    (PureNaturalInduction.application_member (PureZFCModels.reduct_models h𝒩) hIteration.1 hIn) hGraph
  have hNatural : mem 𝒩 (PureNaturalInduction.value (PureZFCModels.reduct_models h𝒩) sequence input) (w 𝒩) := by
    rw [omega_value h𝒩, hEqual]; exact hCurrent
  exact (hIteration.2.2.1 input hInput).trans (hStep _ hNatural)

/-- 同步有限递推后，算术对应只依赖其自然数后继步的对应。 -/
theorem arithmetic_agrees_of_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : Operation)
    {left right : 𝒩.Carrier .set} (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩))
    (hStep : ∀ current, mem 𝒩 current (w 𝒩) →
      step 𝒩 operation left right current = step (canonical h𝒩) operation left right current) :
    arithmetic 𝒩 operation left right = arithmetic (canonical h𝒩) operation left right := by
  have hCanonical := PureZFCModels.models (PureZFCModels.reduct_models h𝒩)
  have hLeft' : mem (canonical h𝒩) left (w (canonical h𝒩)) := omega_agrees h𝒩 ▸ hLeft
  have hRight' : mem (canonical h𝒩) right (w (canonical h𝒩)) := omega_agrees h𝒩 ▸ hRight
  obtain ⟨_, first, hFirst⟩ := specification h𝒩 operation hLeft hRight
  obtain ⟨_, second, hSecond⟩ := specification hCanonical operation hLeft' hRight'
  have hLength : mem 𝒩 (PureArithmeticRecurrence.length (ℳ := PureProjectEmbedding.reduct 𝒩) operation left right) (w 𝒩) := by
    cases operation
    · exact hLeft
    · exact hLeft
    · exact hRight
  have hFirstPure := iteration_change_step h𝒩 (iteration_project h𝒩 hLength hFirst) hStep
  have hSecondPure := iteration_project hCanonical (omega_agrees h𝒩 ▸ hLength) hSecond
  have hSeed : seed 𝒩 operation right = seed (canonical h𝒩) operation right := by
    cases operation
    · rfl
    · exact empty_agrees h𝒩
    · exact (successor_agrees h𝒩 (z 𝒩)).trans
        (congrArg (suc (canonical h𝒩)) (empty_agrees h𝒩))
  rw [hSeed] at hFirstPure
  exact (PureArithmeticRecurrence.iteration_unique (PureZFCModels.reduct_models h𝒩)
    (omega_value h𝒩 ▸ hLength) hFirstPure hSecondPure).2

theorem addition_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : 𝒩.Carrier .set} (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩)) :
    sum 𝒩 left right = sum (canonical h𝒩) left right :=
  arithmetic_agrees_of_step h𝒩 .addition hLeft hRight (fun current _ => successor_agrees h𝒩 current)

theorem multiplication_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : 𝒩.Carrier .set} (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩)) :
    product 𝒩 left right = product (canonical h𝒩) left right :=
  arithmetic_agrees_of_step h𝒩 .multiplication hLeft hRight (fun _ hCurrent => addition_agrees h𝒩 hCurrent hRight)

theorem exponentiation_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : 𝒩.Carrier .set} (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩)) :
    power 𝒩 left right = power (canonical h𝒩) left right :=
  arithmetic_agrees_of_step h𝒩 .exponentiation hLeft hRight (fun _ hCurrent => multiplication_agrees h𝒩 hCurrent hLeft)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceArithmetic
