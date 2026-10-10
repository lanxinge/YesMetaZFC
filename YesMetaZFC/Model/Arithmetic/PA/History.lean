import YesMetaZFC.Logic.Arithmetic.History
import YesMetaZFC.Model.Arithmetic.PA.BetaExtension

/-! # 任意 PA 模型中的有限计算历史

初值和转移关系与其公式分别传入；最终总性使用实际历史存在公式归纳。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.History
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def graph_l (F : num_l ℳ → num_l ℳ → Prop)
    (G : num_l ℳ → num_l ℳ → num_l ℳ → num_l ℳ → Prop) (x n y : num_l ℳ) : Prop :=
  ∃ b c, (∃ a, F x a ∧ Beta.graph_l b c (zero_l ℳ) a) ∧ Beta.graph_l b c n y ∧
    ∀ i, lt_l i n → ∃ a d, Beta.graph_l b c i a ∧ Beta.graph_l b c (succ_l i) d ∧ G x i a d

variable (F : Logic.Arithmetic.History.binary_m) (G : Logic.Arithmetic.History.quaternary_m)
variable (R : num_l ℳ → num_l ℳ → Prop)
variable (S : num_l ℳ → num_l ℳ → num_l ℳ → num_l ℳ → Prop)
variable (hF : ∀ {Γ Δ} (η : Env ℳ Γ Δ) (x a : Term signature_m Γ Δ .num),
  (F x a).satisfies η ↔ R (x.eval η) (a.eval η))
variable (hG : ∀ {Γ Δ} (η : Env ℳ Γ Δ) (x i a d : Term signature_m Γ Δ .num),
  (G x i a d).satisfies η ↔ S (x.eval η) (i.eval η) (a.eval η) (d.eval η))

include hF hG in
theorem graph_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (x n y : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.History.graph_m F G x n y).satisfies η ↔
      graph_l R S (x.eval η) (n.eval η) (y.eval η) := by
  simp only [Logic.Arithmetic.History.graph_m, Logic.Arithmetic.History.initial_m,
    Logic.Arithmetic.History.steps_m, Logic.Arithmetic.History.transition_m,
    Formula.satisfies, hF, hG, Beta.graph_sat_m, lt_sat_m, Term.eval_weakenBound,
    zero_m, succ_m, Term.eval, Arguments.eval]
  rfl

variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem zero_m {x a : num_l ℳ} (ha : R x a) : graph_l R S x (zero_l ℳ) a := by
  obtain ⟨b, c, hb⟩ := Beta.singleton_m hPA a
  refine ⟨b, c, ⟨a, ha, hb⟩, hb, ?_⟩
  intro i hi
  exact False.elim (not_lt_of_le_m hPA (zero_le_m hPA i) hi)

theorem step_m {x n y z : num_l ℳ} (h : graph_l R S x n y) (hz : S x n y z) :
    graph_l R S x (succ_l n) z := by
  obtain ⟨b, c, ⟨a, hFa, h₀⟩, hn, hS⟩ := h
  obtain ⟨d, e, hz', h⟩ := Beta.extend_m hPA b c (succ_l n) z
  have hns := (lt_succ_m hPA).mpr (le_refl_m hPA n)
  have h₀s := (lt_succ_m hPA).mpr (zero_le_m hPA n)
  refine ⟨d, e, ⟨a, hFa, (h _ h₀s a).mpr h₀⟩, hz', ?_⟩
  intro i hi
  rcases le_cases_m hPA ((lt_succ_m hPA).mp hi) with hEq | hin
  · subst i
    exact ⟨y, z, (h n hns y).mpr hn, hz', hz⟩
  · obtain ⟨a, v, ha, hv, hG⟩ := hS i hin
    exact ⟨a, v, (h i hi a).mpr ha,
      (h (succ_l i) ((lt_succ_m hPA).mpr hin) v).mpr hv, hG⟩

include hF hG in
theorem total_m (hR : ∀ x, ∃ a, R x a) (hS : ∀ x i a, ∃ d, S x i a d) (x n : num_l ℳ) :
    ∃ y, graph_l R S x n y := by
  let φ : OpenFormula signature_m [.num, .num] := .existsE .num
    (Logic.Arithmetic.History.graph_m F G (.fvar (.there .here)) (.fvar .here) (.bvar .here))
  have hφ (n : num_l ℳ) : φ.satisfies ((Env.empty.pushFree x).pushFree n) ↔
      ∃ y, graph_l R S x n y := by
    simp only [φ, Formula.satisfies, graph_sat_m F G R S hF hG]
    rfl
  apply induct_m hPA φ (Env.empty.pushFree x) (fun n => ∃ y, graph_l R S x n y) hφ ?_ ?_ n
  · obtain ⟨a, ha⟩ := hR x
    exact ⟨a, zero_m R S hPA ha⟩
  · rintro i ⟨a, ha⟩
    obtain ⟨d, hd⟩ := hS x i a
    exact ⟨d, step_m R S hPA ha hd⟩

end YesMetaZFC.Model.Arithmetic.PA.History
