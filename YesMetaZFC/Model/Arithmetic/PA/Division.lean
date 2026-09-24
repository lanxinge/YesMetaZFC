import YesMetaZFC.Logic.Arithmetic.Division
import YesMetaZFC.Model.Arithmetic.PA.OrderedOperations

/-! # 任意 PA 模型的带余除法

商、余数、被除数及除数均在模型内部。归纳正文是两个存在数量词
构成的实际图公式，不使用宿主 Nat.div 或模型外部的有限性。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Division
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def graph_l (n d q r : num_l ℳ) : Prop := add_l (mul_l q d) r = n ∧ lt_l r d

theorem graph_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n d q r : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Division.graph_m n d q r).satisfies η ↔
      graph_l (n.eval η) (d.eval η) (q.eval η) (r.eval η) := by
  simp only [Logic.Arithmetic.Division.graph_m, Formula.satisfies, lt_sat_m,
    add_m, mul_m, Term.eval, Arguments.eval]
  rfl

theorem domain_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n d : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Division.domain_m n d).satisfies η ↔
      ∃ q r, graph_l (n.eval η) (d.eval η) q r := by
  simp only [Logic.Arithmetic.Division.domain_m, Formula.satisfies, graph_sat_m,
    Term.eval_weakenBound]
  rfl

theorem exists_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    (n d : num_l ℳ) (hd : d ≠ zero_l ℳ) : ∃ q r, graph_l n d q r := by
  have hQ := q_models_m hPA
  have hd₁ := zero_lt_m hPA hd
  let φ : Formula signature_m [] [.num, .num] := .existsE .num (.existsE .num
    (Logic.Arithmetic.Division.graph_m (.fvar .here) (.fvar (.there .here))
      (.bvar (.there .here)) (.bvar .here)))
  have hφ (n : num_l ℳ) : φ.satisfies ((Env.empty.pushFree d).pushFree n) ↔
      ∃ q r, graph_l n d q r := by
    simp only [φ, Formula.satisfies, graph_sat_m]
    rfl
  apply induct_m hPA φ (Env.empty.pushFree d) (fun n => ∃ q r, graph_l n d q r) hφ ?_ ?_ n
  · refine ⟨zero_l ℳ, zero_l ℳ, ?_, hd₁⟩
    exact (Q.add_zero_m hQ _).trans (zero_mul_m hPA d)
  · intro n hn
    obtain ⟨q, r, h, hr⟩ := hn
    rcases le_cases_m hPA hr with hr | hr
    · refine ⟨succ_l q, zero_l ℳ, ?_, hd₁⟩
      calc
        add_l (mul_l (succ_l q) d) (zero_l ℳ) = mul_l (succ_l q) d := Q.add_zero_m hQ _
        _ = add_l (mul_l q d) d := succ_mul_m hPA q d
        _ = add_l (mul_l q d) (succ_l r) := congrArg (add_l (mul_l q d)) hr.symm
        _ = succ_l (add_l (mul_l q d) r) := Q.add_succ_m hQ _ r
        _ = succ_l n := congrArg succ_l h
    · exact ⟨q, succ_l r, (Q.add_succ_m hQ _ r).trans (congrArg succ_l h), hr⟩

/-- 余数小于除数时，较小商的整段都位于较大商的段之前。 -/
private theorem block_lt_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    (d q r a b : num_l ℳ) (hr : lt_l r d) (hqa : lt_l q a) :
    lt_l (add_l (mul_l q d) r) (add_l (mul_l a d) b) := by
  have h₁ : lt_l (add_l (mul_l q d) r) (mul_l (succ_l q) d) := by
    rw [succ_mul_m hPA]
    exact add_lt_add_left_m hPA _ hr
  have h₂ := mul_le_mul_right_m hPA d hqa
  exact le_trans_m hPA h₁ (le_trans_m hPA h₂ ⟨b, rfl⟩)

theorem unique_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {n d q r a b : num_l ℳ} (hq : graph_l n d q r) (ha : graph_l n d a b) :
    q = a ∧ r = b := by
  have h : add_l (mul_l q d) r = add_l (mul_l a d) b := hq.1.trans ha.1.symm
  have hqa : q = a := by
    rcases le_total_m hPA q a with h₁ | h₁
    · rcases le_cases_m hPA h₁ with h₁ | h₁
      · exact h₁
      · have h₂ := block_lt_m hPA d q r a b hq.2 h₁
        rw [h] at h₂
        exact False.elim (lt_irrefl_m hPA _ h₂)
    · rcases le_cases_m hPA h₁ with h₁ | h₁
      · exact h₁.symm
      · have h₂ := block_lt_m hPA d a b q r ha.2 h₁
        rw [h] at h₂
        exact False.elim (lt_irrefl_m hPA _ h₂)
  subst a
  exact ⟨rfl, add_left_cancel_m hPA _ h⟩

theorem divisor_ne_zero_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {n d q r : num_l ℳ} (h : graph_l n d q r) : d ≠ zero_l ℳ := by
  intro hd
  subst d
  exact not_lt_of_le_m hPA (zero_le_m hPA r) h.2

theorem exists_unique_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    (n d : num_l ℳ) (hd : d ≠ zero_l ℳ) :
    ∃ q r, graph_l n d q r ∧ ∀ a b, graph_l n d a b → a = q ∧ b = r := by
  obtain ⟨q, r, h⟩ := exists_m hPA n d hd
  exact ⟨q, r, h, fun a b h₁ => unique_m hPA h₁ h⟩

end YesMetaZFC.Model.Arithmetic.PA.Division
