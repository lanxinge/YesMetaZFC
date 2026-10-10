import YesMetaZFC.Model.Arithmetic.PA.FiniteRange
import YesMetaZFC.Model.Arithmetic.Z2.Order

/-! # Z₂ 混合参数内部有限函数的值域界

仅复用 PA 数域的序运算；带集合参数的归纳正文由 Z₂ 的实际公式归纳处理。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
universe u

theorem bound_m {ℳ : Structure.{0, 0, 0, u} signature_m} (hZ₂ : Theory.Models ℳ theory_m)
    {Δ : SortContext signature_m} (φ : OpenFormula signature_m (.num :: .num :: Δ))
    (η : Env ℳ [] Δ) (N : num_l ℳ)
    (hφ : ∀ i, lt_l i N → ∃ a, φ.satisfies ((η.pushFree i).pushFree a) ∧
      ∀ c, φ.satisfies ((η.pushFree i).pushFree c) → c = a) :
    ∃ b, ∀ i a, lt_l i N → φ.satisfies ((η.pushFree i).pushFree a) → lt_l a b := by
  apply Arithmetic.PA.bound_rule_m (reduct_models_m hZ₂)
    (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) N ?_ hφ
  intro h₀ h₁
  let ψ : OpenFormula signature_m (.num :: .num :: Δ) :=
    .imp (le_m (.fvar .here) (.fvar (.there .here)))
      (Logic.Arithmetic.FiniteRange.bound_m (Logic.Arithmetic.FiniteRange.insert_m φ) lt_m)
  have hψ (n : num_l ℳ) : ψ.satisfies ((η.pushFree N).pushFree n) ↔
      (le_l n N → ∃ b, ∀ i a, lt_l i n → φ.satisfies ((η.pushFree i).pushFree a) → lt_l a b) := by
    simp only [ψ, Formula.satisfies, le_sat_m,
      Arithmetic.FiniteRange.bound_sat_m _ _ _ lt_m lt_l lt_sat_m, Arithmetic.FiniteRange.insert_sat_m]
    rfl
  exact induct_m hZ₂ ψ (η.pushFree N)
    (fun n => le_l n N → ∃ b, ∀ i a, lt_l i n → φ.satisfies ((η.pushFree i).pushFree a) → lt_l a b)
    hψ h₀ h₁

end YesMetaZFC.Model.Arithmetic.Z2
