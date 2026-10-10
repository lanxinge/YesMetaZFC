import YesMetaZFC.Logic.Arithmetic.BetaSequence
import YesMetaZFC.Model.Arithmetic.BetaPrefix
import YesMetaZFC.Model.Arithmetic.PA.BetaPrefix
import YesMetaZFC.Model.Arithmetic.PA.FiniteRange

/-! # PA 可定义内部有限函数的 β 编码

归纳正文由实际公式装配，原数参数全部保留；不要求内部截段外的总性。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Beta
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

theorem remainder_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c i a : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Beta.remainder_m b c i a).satisfies η ↔
      ∃ q, add_l (mul_l q (modulus_l (c.eval η) (i.eval η))) (a.eval η) = b.eval η := by
  simp only [Logic.Arithmetic.Beta.remainder_m, Formula.satisfies,
    add_m, mul_m, Term.eval, Arguments.eval, Term.eval_weakenBound, modulus_eval_m]
  rfl

theorem invariant_sat_m {Δ : SortContext signature_m}
    (φ : OpenFormula signature_m (.num :: .num :: Δ)) (η : Env ℳ [] Δ) (n c j : num_l ℳ) :
    (Logic.Arithmetic.Beta.invariant_m φ).satisfies (((η.pushFree c).pushFree n).pushFree j) ↔
      (le_l j n → prefix_l (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) n c j) := by
  simp only [Logic.Arithmetic.Beta.invariant_m, Formula.satisfies, le_sat_m]
  change (le_l j n → _) ↔ (le_l j n → _)
  apply imp_congr Iff.rfl
  exact Arithmetic.Beta.prefix_sat_m φ η n c j lt_m le_m
    (fun c i M => Logic.Arithmetic.Divisibility.dvd_m (Logic.Arithmetic.Beta.modulus_m c i) M)
    (fun c i M => Logic.Arithmetic.Modular.inverse_m M (Logic.Arithmetic.Beta.modulus_m c i))
    Logic.Arithmetic.Beta.remainder_m lt_l le_l
    (fun c i M => Arithmetic.Divisibility.dvd_l (modulus_l c i) M)
    (fun c i M => Modular.inverse_l M (modulus_l c i))
    (fun b c i a => ∃ q, add_l (mul_l q (modulus_l c i)) a = b)
    lt_sat_m le_sat_m
    (fun _ _ _ _ => by rw [Arithmetic.Divisibility.dvd_sat_m, modulus_eval_m])
    (fun _ _ _ _ => by rw [Modular.inverse_sat_m, modulus_eval_m]) remainder_sat_m

theorem sequence_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {Δ : SortContext signature_m} (φ : OpenFormula signature_m (.num :: .num :: Δ))
    (η : Env ℳ [] Δ) (n : num_l ℳ)
    (hφ : ∀ i, lt_l i n → ∃ a, φ.satisfies ((η.pushFree i).pushFree a) ∧
      ∀ d, φ.satisfies ((η.pushFree i).pushFree d) → d = a) :
    ∃ b c, ∀ i, lt_l i n → ∀ a, graph_l b c i a ↔ φ.satisfies ((η.pushFree i).pushFree a) := by
  obtain ⟨B, hB⟩ := PA.bound_m hPA φ η n hφ
  obtain ⟨c, hBc, hc⟩ := Divisibility.bounded_m hPA n B
  obtain ⟨b, hb⟩ := sequence_rule_m hPA (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) n c hc hφ
    (fun i a hi ha => lt_trans_m hPA (hB i a hi ha) hBc) (by
      intro h₀ h₁
      exact induct_m hPA (Logic.Arithmetic.Beta.invariant_m φ) ((η.pushFree c).pushFree n)
        (fun j => le_l j n → prefix_l (fun i a => φ.satisfies ((η.pushFree i).pushFree a)) n c j)
        (invariant_sat_m φ η n c) h₀ h₁)
  exact ⟨b, c, hb⟩

end YesMetaZFC.Model.Arithmetic.PA.Beta
