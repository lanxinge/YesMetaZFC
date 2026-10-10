import YesMetaZFC.Model.Arithmetic.Pairing
import YesMetaZFC.Model.Arithmetic.PA.OrderedOperations

/-! # PA 内部配对的满射性

归纳正文为实际的反解存在公式。后继步沿平方层的两个边移动，
跨层时使用已证后继平方恒等式，不对模型数使用宿主递归。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Pairing
open Logic FirstOrder Logic.Arithmetic Model.Arithmetic.Pairing
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem successor_m (m n p : num_l ℳ) (hp : graph_l m n p) : ∃ a b, graph_l a b (succ_l p) := by
  classical
  have hQ := q_models_m hPA
  by_cases h : lt_l m n
  · obtain rfl := (of_lt_m h).mp hp
    by_cases h₁ : lt_l (succ_l m) n
    · refine ⟨succ_l m, n, ?_⟩
      apply (of_lt_m h₁).mpr
      exact Q.add_succ_m hQ _ _
    · have h₂ : succ_l m = n := le_antisymm_m hPA h (le_of_not_lt_m hPA h₁)
      refine ⟨n, zero_l ℳ, ?_⟩
      rw [of_not_lt_m (not_lt_of_le_m hPA (zero_le_m hPA n)), Q.add_zero_m hQ]
      exact (congrArg (add_l (mul_l n n)) h₂.symm).trans (Q.add_succ_m hQ _ _)
  · obtain rfl := (of_not_lt_m h).mp hp
    by_cases h₁ : lt_l n m
    · refine ⟨m, succ_l n, ?_⟩
      apply (of_not_lt_m (not_lt_of_le_m hPA h₁)).mpr
      exact Q.add_succ_m hQ _ _
    · have h₂ : n = m := le_antisymm_m hPA (le_of_not_lt_m hPA h) (le_of_not_lt_m hPA h₁)
      subst n
      refine ⟨zero_l ℳ, succ_l m, ?_⟩
      have h₃ := (lt_succ_m hPA).mpr (zero_le_m hPA m)
      rw [of_lt_m h₃, Q.add_zero_m hQ]
      exact square_succ_m hPA m

theorem surjective_m (z : num_l ℳ) : ∃ m n, graph_l m n z := by
  let φ : OpenFormula signature_m [.num] := .existsE .num (.existsE .num
    (Logic.Arithmetic.Pairing.graph_m (.bvar (.there .here)) (.bvar .here) (.fvar .here)))
  have hφ (z : num_l ℳ) : φ.satisfies (Env.empty.pushFree z) ↔ ∃ m n, graph_l m n z := by
    simp only [φ, Formula.satisfies, graph_sat_m]
    rfl
  apply induct_m hPA φ Env.empty (fun z => ∃ m n, graph_l m n z) hφ ?_ ?_ z
  · refine ⟨zero_l ℳ, zero_l ℳ, ?_⟩
    simp only [of_not_lt_m (lt_irrefl_m hPA _), Q.mul_zero_m (q_models_m hPA),
      Q.add_zero_m (q_models_m hPA)]
  · rintro z ⟨m, n, hp⟩
    exact successor_m hPA m n z hp

end YesMetaZFC.Model.Arithmetic.PA.Pairing
