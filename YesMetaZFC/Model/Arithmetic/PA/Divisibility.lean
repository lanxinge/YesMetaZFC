import YesMetaZFC.Model.Arithmetic.Divisibility
import YesMetaZFC.Model.Arithmetic.PA.OrderedOperations

/-! # PA 中内部有限截段的共同倍数

以实际存在公式归纳，不构造宿主阶乘，也不要求内部截段外部有限。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Divisibility
open Logic FirstOrder Logic.Arithmetic Model.Arithmetic.Divisibility
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem dvd_mul_m {d c : num_l ℳ} (h : dvd_l d c) (a : num_l ℳ) : dvd_l d (mul_l c a) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨mul_l k a, (mul_assoc_m hPA d k a).symm.trans (congrArg (fun c => mul_l c a) hk)⟩

theorem exists_m (n : num_l ℳ) : ∃ c, common_l n c := by
  let φ : Formula signature_m [] [.num] := .existsE .num
    (Logic.Arithmetic.Divisibility.common_m (.fvar .here) (.bvar .here))
  have hφ (n : num_l ℳ) : φ.satisfies (Env.empty.pushFree n) ↔ ∃ c, common_l n c := by
    simp only [φ, Formula.satisfies, common_sat_m]
    rfl
  apply induct_m hPA φ Env.empty (fun n => ∃ c, common_l n c) hφ ?_ ?_ n
  · refine ⟨succ_l (zero_l ℳ), (lt_succ_m hPA).mpr (le_refl_m hPA _), ?_⟩
    exact fun d hd hd₀ => False.elim (not_lt_of_le_m hPA hd₀ hd)
  · rintro n ⟨c, hc, hcd⟩
    have h₁ := mul_le_mul_right_m hPA (succ_l n) hc
    rw [one_mul_m hPA] at h₁
    refine ⟨mul_l c (succ_l n),
      le_lt_trans_m hPA (zero_le_m hPA n) h₁, ?_⟩
    intro d hd hdn
    rcases le_cases_m hPA hdn with hdn | hdn
    · exact ⟨c, (congrArg (fun d => mul_l d c) hdn).trans (mul_comm_m hPA _ _)⟩
    · exact dvd_mul_m hPA (hcd d hd ((lt_succ_m hPA).mp hdn)) _

theorem bounded_m (n b : num_l ℳ) : ∃ c, lt_l b c ∧ common_l n c := by
  obtain ⟨c, hc, hcd⟩ := exists_m hPA n
  have hb := mul_le_mul_right_m hPA (succ_l b) hc
  rw [one_mul_m hPA] at hb
  exact ⟨mul_l c (succ_l b), hb, le_lt_trans_m hPA (zero_le_m hPA b) hb,
    fun d hd hdn => dvd_mul_m hPA (hcd d hd hdn) _⟩

end YesMetaZFC.Model.Arithmetic.PA.Divisibility
