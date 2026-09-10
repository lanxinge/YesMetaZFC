import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceArithmetic

/-! # 原模型加乘幂的右参数递推

以既有纯序数算术规格和全部内部自然数对应证明递推式。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceArithmetic
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem arithmetic_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : Operation)
    {left right : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩)) :
    arithmetic 𝒩 operation left right = PureArithmeticStage.arithmetic (PureZFCModels.reduct_models h𝒩) operation left right := by
  cases operation
  · exact (addition_agrees h𝒩 hl hr).trans (add_final _ _ _)
  · exact (multiplication_agrees h𝒩 hl hr).trans (mul_final _ _ _)
  · exact (exponentiation_agrees h𝒩 hl hr).trans (pow_final _ _ _)

theorem seed_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : Operation) (left : 𝒩.Carrier .set) :
    seed 𝒩 operation left = PureArithmeticRecurrence.seed (PureZFCModels.reduct_models h𝒩) operation left := by
  cases operation
  · rfl
  · exact zero_value h𝒩
  · exact (successor_value h𝒩 _).trans (congrArg _ (zero_value h𝒩))

theorem step_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : Operation)
    {left current : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) (hc : mem 𝒩 current (w 𝒩)) :
    step 𝒩 operation left left current =
      PureArithmeticStage.step (PureZFCModels.reduct_models h𝒩) operation left left current := by
  cases operation
  · exact successor_value h𝒩 _
  · exact arithmetic_value h𝒩 .addition hc hl
  · exact arithmetic_value h𝒩 .multiplication hc hl

theorem at_zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : Operation)
    {left : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) :
    arithmetic 𝒩 operation left (z 𝒩) = seed 𝒩 operation left := by
  let hℳ := PureZFCModels.reduct_models h𝒩
  have hl' := (omega_value h𝒩) ▸ hl
  rw [arithmetic_value h𝒩 operation hl (omega_closed h𝒩).1, zero_value h𝒩, seed_value h𝒩]
  exact PureArithmeticSpecifications.ordinal_zero_value hℳ operation hl'
    (PureArithmeticStage.arithmetic_correct hℳ operation hl' (PureArithmeticSpecifications.zero_mem hℳ))

theorem at_successor (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : Operation)
    {left right : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩)) :
    arithmetic 𝒩 operation left (suc 𝒩 right) =
      step 𝒩 operation left left (arithmetic 𝒩 operation left right) := by
  let hℳ := PureZFCModels.reduct_models h𝒩
  have hl' := (omega_value h𝒩) ▸ hl
  have hr' := (omega_value h𝒩) ▸ hr
  rw [arithmetic_value h𝒩 operation hl ((omega_closed h𝒩).2 right hr), successor_value h𝒩,
    step_value h𝒩 operation hl (specification h𝒩 operation hl hr).1, arithmetic_value h𝒩 operation hl hr]
  exact PureArithmeticSpecifications.ordinal_step_value hℳ operation hl' hr'
    (PureArithmeticStage.arithmetic_correct hℳ operation hl' hr')
    (PureArithmeticStage.arithmetic_correct hℳ operation hl' (PureArithmeticSpecifications.succ_mem hℳ hr'))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceArithmetic
