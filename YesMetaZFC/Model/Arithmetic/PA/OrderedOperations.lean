import YesMetaZFC.Model.Arithmetic.PA.LinearOrder

/-! # PA 模型中的运算单调性

保留内部差值见证，直接消费既有分配律和结合律，不引入全局有序环实例。
-/
namespace YesMetaZFC.Model.Arithmetic.PA
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem add_le_add_left_m (p : num_l ℳ) {m n : num_l ℳ} (h : le_l m n) :
    le_l (add_l p m) (add_l p n) := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, (add_assoc_m hPA p m k).trans (congrArg (add_l p) h)⟩

theorem add_lt_add_left_m (p : num_l ℳ) {m n : num_l ℳ} (h : lt_l m n) :
    lt_l (add_l p m) (add_l p n) := by
  change le_l (succ_l (add_l p m)) (add_l p n)
  rw [← Q.add_succ_m (q_models_m hPA) p m]
  exact add_le_add_left_m hPA p h

theorem mul_le_mul_right_m (p : num_l ℳ) {m n : num_l ℳ} (h : le_l m n) :
    le_l (mul_l m p) (mul_l n p) := by
  obtain ⟨k, h⟩ := h
  exact ⟨mul_l k p, (add_mul_m hPA m k p).symm.trans (congrArg (fun m => mul_l m p) h)⟩

theorem zero_lt_m {n : num_l ℳ} (h : n ≠ zero_l ℳ) : lt_l (zero_l ℳ) n := by
  rcases Q.predecessor_m (q_models_m hPA) n with hn | ⟨m, hn⟩
  · exact False.elim (h hn)
  · rw [hn]
    exact (lt_succ_m hPA).mpr (zero_le_m hPA m)

end YesMetaZFC.Model.Arithmetic.PA
