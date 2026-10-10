import YesMetaZFC.Logic.Arithmetic.Z2.Beta
import YesMetaZFC.Model.Arithmetic.PA.BetaSequence
import YesMetaZFC.Model.Arithmetic.Z2.FiniteRange

/-! # 混合参数 β 模板与数域约化的语义接线 -/
namespace YesMetaZFC.Model.Arithmetic.Z2.Beta
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
local notation "𝒩" => reduct_m ℳ

theorem modulus_eval_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (c i : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Z2.Beta.modulus_m c i).eval η =
      Arithmetic.PA.Beta.modulus_l (ℳ := 𝒩) (c.eval η) (i.eval η) := rfl

theorem divisor_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (c i M : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Z2.Beta.divisor_m c i M).satisfies η ↔
      Arithmetic.Divisibility.dvd_l (ℳ := 𝒩) (Arithmetic.PA.Beta.modulus_l (c.eval η) (i.eval η)) (M.eval η) := by
  simp only [Logic.Arithmetic.Z2.Beta.divisor_m, Formula.satisfies,
    mul_m, Term.eval, Arguments.eval, Term.eval_weakenBound, modulus_eval_m]
  rfl

theorem inverse_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (c i M : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Z2.Beta.inverse_m c i M).satisfies η ↔
      Arithmetic.PA.Modular.inverse_l (ℳ := 𝒩) (M.eval η) (Arithmetic.PA.Beta.modulus_l (c.eval η) (i.eval η)) := by
  simp only [Logic.Arithmetic.Z2.Beta.inverse_m, Formula.satisfies,
    add_m, mul_m, Term.eval, Arguments.eval, Term.eval_weakenBound, modulus_eval_m]
  rfl

theorem remainder_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c i a : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Z2.Beta.remainder_m b c i a).satisfies η ↔
      ∃ q, Arithmetic.add_l (ℳ := 𝒩) (Arithmetic.mul_l q
        (Arithmetic.PA.Beta.modulus_l (c.eval η) (i.eval η))) (a.eval η) = b.eval η := by
  simp only [Logic.Arithmetic.Z2.Beta.remainder_m, Formula.satisfies,
    add_m, mul_m, Term.eval, Arguments.eval, Term.eval_weakenBound, modulus_eval_m]
  rfl

theorem graph_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c i a : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Z2.Beta.graph_m b c i a).satisfies η ↔
      Arithmetic.PA.Beta.graph_l (ℳ := 𝒩) (b.eval η) (c.eval η) (i.eval η) (a.eval η) := by
  simp only [Logic.Arithmetic.Z2.Beta.graph_m, Formula.satisfies, lt_sat_m,
    add_m, mul_m, Term.eval, Arguments.eval, Term.eval_weakenBound, modulus_eval_m]
  rfl

theorem invariant_sat_m {Δ : SortContext signature_m}
    (φ : OpenFormula signature_m (.num :: .num :: Δ)) (η : Env ℳ [] Δ) (n c j : num_l ℳ) :
    (Logic.Arithmetic.Z2.Beta.invariant_m φ).satisfies (((η.pushFree c).pushFree n).pushFree j) ↔
      (le_l j n → Arithmetic.PA.Beta.prefix_l (ℳ := 𝒩)
        (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) n c j) := by
  simp only [Logic.Arithmetic.Z2.Beta.invariant_m, Formula.satisfies, le_sat_m]
  change (le_l j n → _) ↔ (le_l j n → _)
  apply imp_congr Iff.rfl
  exact Arithmetic.Beta.prefix_sat_m φ η n c j lt_m le_m
    Logic.Arithmetic.Z2.Beta.divisor_m Logic.Arithmetic.Z2.Beta.inverse_m Logic.Arithmetic.Z2.Beta.remainder_m
    lt_l le_l
    (fun c i M => Arithmetic.Divisibility.dvd_l (ℳ := 𝒩) (Arithmetic.PA.Beta.modulus_l c i) M)
    (fun c i M => Arithmetic.PA.Modular.inverse_l (ℳ := 𝒩) M (Arithmetic.PA.Beta.modulus_l c i))
    (fun b c i a => ∃ q, Arithmetic.add_l (ℳ := 𝒩) (Arithmetic.mul_l q (Arithmetic.PA.Beta.modulus_l c i)) a = b)
    lt_sat_m le_sat_m divisor_sat_m inverse_sat_m remainder_sat_m

theorem sequence_m (hZ₂ : Theory.Models ℳ theory_m)
    {Δ : SortContext signature_m} (φ : OpenFormula signature_m (.num :: .num :: Δ))
    (η : Env ℳ [] Δ) (n : num_l ℳ)
    (hφ : ∀ i, lt_l i n → ∃ a, φ.satisfies ((η.pushFree i).pushFree a) ∧
      ∀ d, φ.satisfies ((η.pushFree i).pushFree d) → d = a) :
    ∃ b c, ∀ i, lt_l i n → ∀ a, Arithmetic.PA.Beta.graph_l (ℳ := 𝒩) b c i a ↔
      φ.satisfies ((η.pushFree i).pushFree a) := by
  have hPA := reduct_models_m hZ₂
  obtain ⟨B, hB⟩ := Z2.bound_m hZ₂ φ η n hφ
  obtain ⟨c, hBc, hc⟩ := Arithmetic.PA.Divisibility.bounded_m hPA n B
  obtain ⟨b, hb⟩ := Arithmetic.PA.Beta.sequence_rule_m hPA
    (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) n c hc hφ
    (fun i a hi ha => Arithmetic.PA.lt_trans_m hPA (hB i a hi ha) hBc) (by
      intro h₀ h₁
      exact induct_m hZ₂ (Logic.Arithmetic.Z2.Beta.invariant_m φ) ((η.pushFree c).pushFree n)
        (fun j => le_l j n → Arithmetic.PA.Beta.prefix_l (ℳ := 𝒩)
          (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) n c j)
        (invariant_sat_m φ η n c) h₀ h₁)
  exact ⟨b, c, hb⟩

end YesMetaZFC.Model.Arithmetic.Z2.Beta
