import YesMetaZFC.Model.Arithmetic.Order
import YesMetaZFC.Model.Arithmetic.PA.Cancellation

/-! # 任意 PA 模型中的内部偏序

存在见证遍历模型全数域。只组合已验证的运算规律，不添加宿主序类型类。
-/
namespace YesMetaZFC.Model.Arithmetic.PA
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem le_refl_m (n : num_l ℳ) : le_l n n :=
  ⟨zero_l ℳ, Q.add_zero_m (q_models_m hPA) n⟩

theorem zero_le_m (n : num_l ℳ) : le_l (zero_l ℳ) n := ⟨n, zero_add_m hPA n⟩

theorem le_trans_m {m n p : num_l ℳ} (h₁ : le_l m n) (h₂ : le_l n p) : le_l m p := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨add_l a b, (add_assoc_m hPA m a b).symm.trans
    ((congrArg (fun n => add_l n b) ha).trans hb)⟩

theorem le_antisymm_m {m n : num_l ℳ} (h₁ : le_l m n) (h₂ : le_l n m) : m = n := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have h : add_l a b = zero_l ℳ := add_left_cancel_m hPA m
    ((add_assoc_m hPA m a b).symm.trans ((congrArg (fun n => add_l n b) ha).trans
      (hb.trans (Q.add_zero_m (q_models_m hPA) m).symm)))
  have ha₀ := add_eq_zero_left_m hPA h
  exact (Q.add_zero_m (q_models_m hPA) m).symm.trans
    ((congrArg (add_l m) ha₀.symm).trans ha)

end YesMetaZFC.Model.Arithmetic.PA
