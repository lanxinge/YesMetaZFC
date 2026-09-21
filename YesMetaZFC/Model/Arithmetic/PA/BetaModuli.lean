import YesMetaZFC.Model.Arithmetic.PA.Beta
import YesMetaZFC.Model.Arithmetic.PA.Divisibility
import YesMetaZFC.Model.Arithmetic.PA.Modular

/-! # β 特殊模数之间的可逆性

共同倍数 c 吸收下标差 j-i。直接构造无减法贝祖等式，不引用宿主 gcd 或 CRT。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Beta
open Logic FirstOrder Logic.Arithmetic Model.Arithmetic.Divisibility
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

/-- 每个模数严格超过参数 c，包括 c=0。 -/
theorem parameter_lt_m (c i : num_l ℳ) : lt_l c (modulus_l c i) := by
  apply (lt_succ_m hPA).mpr
  have h := mul_le_mul_right_m hPA c ((succ_le_succ_m hPA).mpr (zero_le_m hPA i))
  simpa only [one_mul_m hPA] using h

theorem inverse_m {n c i j : num_l ℳ} (hc : common_l n c)
    (hij : lt_l i j) (hjn : le_l j n) : Modular.inverse_l (modulus_l c i) (modulus_l c j) := by
  have hQ := q_models_m hPA
  obtain ⟨d, hd⟩ := lt_le_m hPA hij
  have hd₀ : lt_l (zero_l ℳ) d := by
    apply zero_lt_m hPA
    intro h
    rw [h, Q.add_zero_m hQ] at hd
    exact lt_ne_m hPA hij hd
  have hdj : le_l d j := ⟨i, (add_comm_m hPA d i).trans hd⟩
  obtain ⟨e, he⟩ := hc.2 d hd₀ (le_trans_m hPA hdj hjn)
  have hq : succ_l j = add_l (succ_l i) d :=
    (congrArg succ_l hd).symm.trans (succ_add_m hPA i d).symm
  have h₁ (x : num_l ℳ) : add_l (succ_l (zero_l ℳ)) x = succ_l x :=
    (succ_add_m hPA (zero_l ℳ) x).trans (congrArg succ_l (zero_add_m hPA x))
  have hcore : add_l
      (mul_l (mul_l (mul_l (succ_l j) (succ_l j)) e) (modulus_l c i)) (succ_l (zero_l ℳ)) =
      mul_l (add_l (mul_l (mul_l (succ_l i) (succ_l j)) e) (succ_l (zero_l ℳ))) (modulus_l c j) := by
    have h := Modular.modulus_identity_m hPA (succ_l i) d e
    rw [← hq, he] at h
    simpa only [h₁, modulus_l] using h
  apply Modular.of_bezout_m hPA hcore
  · rw [Q.add_succ_m hQ, Q.add_zero_m hQ]
    exact (lt_succ_m hPA).mpr (zero_le_m hPA _)
  · apply (lt_succ_m hPA).mpr
    have h := mul_le_mul_right_m hPA c ((succ_le_succ_m hPA).mpr (zero_le_m hPA j))
    rw [one_mul_m hPA] at h
    exact le_trans_m hPA hc.1 h

end YesMetaZFC.Model.Arithmetic.PA.Beta
