import YesMetaZFC.Model.Arithmetic.FiniteRange
import YesMetaZFC.Model.Arithmetic.PA.LinearOrder

/-! # PA 中可定义内部有限函数的值域界

只在所需截段假定存在唯一输出。归纳式带有截段上界条件，
不把关系补全为外部函数，不对内部长度使用宿主有限性。
-/
namespace YesMetaZFC.Model.Arithmetic.PA
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

/-- 共同数论论证；对 H 所需的归纳必须由具体公式提供。 -/
theorem bound_rule_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    (H : num_l ℳ → num_l ℳ → Prop) (N : num_l ℳ)
    (hI : (le_l (zero_l ℳ) N → ∃ b, ∀ i a, lt_l i (zero_l ℳ) → H i a → lt_l a b) →
      (∀ n, (le_l n N → ∃ b, ∀ i a, lt_l i n → H i a → lt_l a b) →
        le_l (succ_l n) N → ∃ b, ∀ i a, lt_l i (succ_l n) → H i a → lt_l a b) →
      ∀ n, le_l n N → ∃ b, ∀ i a, lt_l i n → H i a → lt_l a b)
    (hH : ∀ i, lt_l i N → ∃ a, H i a ∧ ∀ c, H i c → c = a) :
    ∃ b, ∀ i a, lt_l i N → H i a → lt_l a b := by
  apply hI ?_ ?_ N (le_refl_m hPA N)
  · exact fun _ => ⟨zero_l ℳ, fun i _ hi _ =>
      False.elim (not_lt_of_le_m hPA (zero_le_m hPA i) hi)⟩
  · intro n hn hN
    obtain ⟨a, _, ha⟩ := hH n hN
    obtain ⟨b, hb⟩ := hn (le_trans_m hPA (le_succ_m hPA n) hN)
    refine ⟨succ_l (add_l b a), ?_⟩
    intro i c hi hc
    rcases le_cases_m hPA ((lt_succ_m hPA).mp hi) with hi | hi
    · subst i
      rw [ha c hc]
      exact (lt_succ_m hPA).mpr ⟨b, add_comm_m hPA a b⟩
    · exact lt_le_trans_m hPA (hb i c hi hc)
        (le_trans_m hPA (show le_l b (add_l b a) from ⟨a, rfl⟩) (le_succ_m hPA _))

theorem bound_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {Δ : SortContext signature_m} (φ : OpenFormula signature_m (.num :: .num :: Δ))
    (η : Env ℳ [] Δ) (N : num_l ℳ)
    (hφ : ∀ i, lt_l i N → ∃ a, φ.satisfies ((η.pushFree i).pushFree a) ∧
      ∀ c, φ.satisfies ((η.pushFree i).pushFree c) → c = a) :
    ∃ b, ∀ i a, lt_l i N → φ.satisfies ((η.pushFree i).pushFree a) → lt_l a b := by
  apply bound_rule_m hPA (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) N ?_ hφ
  intro h₀ h₁
  let ψ : OpenFormula signature_m (.num :: .num :: Δ) :=
    .imp (le_m (.fvar .here) (.fvar (.there .here)))
      (Logic.Arithmetic.FiniteRange.bound_m (Logic.Arithmetic.FiniteRange.insert_m φ) lt_m)
  have hψ (n : num_l ℳ) : ψ.satisfies ((η.pushFree N).pushFree n) ↔
      (le_l n N → ∃ b, ∀ i a, lt_l i n → φ.satisfies ((η.pushFree i).pushFree a) → lt_l a b) := by
    simp only [ψ, Formula.satisfies, le_sat_m,
      FiniteRange.bound_sat_m _ _ _ lt_m lt_l lt_sat_m, FiniteRange.insert_sat_m]
    rfl
  exact induct_m hPA ψ (η.pushFree N)
    (fun n => le_l n N → ∃ b, ∀ i a, lt_l i n → φ.satisfies ((η.pushFree i).pushFree a) → lt_l a b)
    hψ h₀ h₁

end YesMetaZFC.Model.Arithmetic.PA
