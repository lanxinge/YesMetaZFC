import YesMetaZFC.Model.Arithmetic.PA.BetaModuli

/-! # β 编码的前缀不变量

同时保存旧模数整除、未用模数可逆和已读前缀。归纳接口显式要求调用方给出
实际公式的归纳证据，不能直接用于任意外部关系。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Beta
open Logic FirstOrder Logic.Arithmetic Model.Arithmetic.Divisibility
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def prefix_l (H : num_l ℳ → num_l ℳ → Prop) (n c j : num_l ℳ) : Prop :=
  ∃ b M, (∀ i, lt_l i j → dvd_l (modulus_l c i) M) ∧
    (∀ l, lt_l l n → le_l j l → Modular.inverse_l M (modulus_l c l)) ∧
    ∀ i, lt_l i j → ∀ a, H i a → ∃ q, add_l (mul_l q (modulus_l c i)) a = b

variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

private theorem remainder_add_m {d M b a : num_l ℳ} (hD : dvd_l d M)
    (hR : ∃ q, add_l (mul_l q d) a = b) (t : num_l ℳ) :
    ∃ q, add_l (mul_l q d) a = add_l b (mul_l M t) := by
  obtain ⟨r, hr⟩ := hD
  obtain ⟨q, hq⟩ := hR
  refine ⟨add_l q (mul_l r t), ?_⟩
  rw [add_mul_m hPA, add_assoc_m hPA, add_comm_m hPA (mul_l (mul_l r t) d) a,
    ← add_assoc_m hPA, hq]
  apply congrArg (add_l b)
  rw [mul_assoc_m hPA, mul_comm_m hPA t d, ← mul_assoc_m hPA,
    mul_comm_m hPA r d, hr]

theorem prefix_zero_m (H : num_l ℳ → num_l ℳ → Prop) (n c : num_l ℳ) :
    prefix_l H n c (zero_l ℳ) := by
  refine ⟨zero_l ℳ, succ_l (zero_l ℳ), ?_, ?_, ?_⟩
  · exact fun i hi => False.elim (not_lt_of_le_m hPA (zero_le_m hPA i) hi)
  · exact fun l _ _ => Modular.one_m hPA (modulus_l c l)
  · exact fun i hi => False.elim (not_lt_of_le_m hPA (zero_le_m hPA i) hi)

theorem prefix_succ_m {H : num_l ℳ → num_l ℳ → Prop} {n c j : num_l ℳ}
    (hc : common_l n c) (hj : lt_l j n)
    (hH : ∃ a, H j a ∧ ∀ d, H j d → d = a) (hp : prefix_l H n c j) :
    prefix_l H n c (succ_l j) := by
  obtain ⟨b, M, hA, hB, hC⟩ := hp
  obtain ⟨a, _, ha⟩ := hH
  obtain ⟨t, q, hq⟩ := Modular.adjust_m hPA (hB j hj (le_refl_m hPA j))
    ((lt_succ_m hPA).mpr (zero_le_m hPA _)) b a
  refine ⟨add_l b (mul_l M t), mul_l M (modulus_l c j), ?_, ?_, ?_⟩
  · intro i hi
    rcases le_cases_m hPA ((lt_succ_m hPA).mp hi) with hi | hi
    · subst i
      exact ⟨M, mul_comm_m hPA _ _⟩
    · exact Divisibility.dvd_mul_m hPA (hA i hi) _
  · intro l hln hjl
    exact Modular.mul_m hPA (hB l hln (lt_le_m hPA hjl))
      (inverse_m hPA hc hjl (lt_le_m hPA hln))
  · intro i hi d hd
    rcases le_cases_m hPA ((lt_succ_m hPA).mp hi) with hi | hi
    · subst i
      exact ⟨q, (congrArg (add_l (mul_l q (modulus_l c j))) (ha d hd)).trans hq⟩
    · exact remainder_add_m hPA (hA i hi) (hC i hi d hd) t

/-- 数论部分共用；hI 必须由 PA 或 Z₂ 的实际公式归纳填满。 -/
theorem sequence_rule_m (H : num_l ℳ → num_l ℳ → Prop) (n c : num_l ℳ)
    (hc : common_l n c)
    (hH : ∀ i, lt_l i n → ∃ a, H i a ∧ ∀ d, H i d → d = a)
    (hB : ∀ i a, lt_l i n → H i a → lt_l a c)
    (hI : (le_l (zero_l ℳ) n → prefix_l H n c (zero_l ℳ)) →
      (∀ j, (le_l j n → prefix_l H n c j) → le_l (succ_l j) n → prefix_l H n c (succ_l j)) →
      ∀ j, le_l j n → prefix_l H n c j) :
    ∃ b, ∀ i, lt_l i n → ∀ a, graph_l b c i a ↔ H i a := by
  have hp := hI (fun _ => prefix_zero_m hPA H n c)
    (fun j h hj => prefix_succ_m hPA hc hj (hH j hj)
      (h (le_trans_m hPA (le_succ_m hPA j) hj))) n (le_refl_m hPA n)
  obtain ⟨b, _, _, _, hC⟩ := hp
  have hforward (i a : num_l ℳ) (hi : lt_l i n) (ha : H i a) : graph_l b c i a := by
    obtain ⟨q, hq⟩ := hC i hi a ha
    exact ⟨q, hq, lt_trans_m hPA (hB i a hi ha) (parameter_lt_m hPA c i)⟩
  refine ⟨b, fun i hi a => ⟨?_, hforward i a hi⟩⟩
  intro ha
  obtain ⟨d, hd, _⟩ := hH i hi
  exact (unique_m hPA ha (hforward i d hi hd)) ▸ hd

end YesMetaZFC.Model.Arithmetic.PA.Beta
