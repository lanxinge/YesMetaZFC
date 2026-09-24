import YesMetaZFC.Model.Arithmetic.PA.Order
import YesMetaZFC.Model.Arithmetic.PA.Induction

/-! # 任意 PA 模型中的内部线序

全序性沿带数量词的真实公式归纳。此处是模型结论，不借完整性把它
冒充已经构造的对象推导；数域不要求外部标准或良基。
-/
namespace YesMetaZFC.Model.Arithmetic.PA
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem succ_le_succ_m {m n : num_l ℳ} : le_l (succ_l m) (succ_l n) ↔ le_l m n := by
  constructor
  · rintro ⟨k, h⟩
    exact ⟨k, Q.injective_m (q_models_m hPA) ((succ_add_m hPA m k).symm.trans h)⟩
  · rintro ⟨k, h⟩
    exact ⟨k, (succ_add_m hPA m k).trans (congrArg succ_l h)⟩

theorem lt_succ_m {m n : num_l ℳ} : lt_l m (succ_l n) ↔ le_l m n := succ_le_succ_m hPA

theorem le_succ_m (n : num_l ℳ) : le_l n (succ_l n) :=
  ⟨succ_l (zero_l ℳ), (Q.add_succ_m (q_models_m hPA) n (zero_l ℳ)).trans
    (congrArg succ_l (Q.add_zero_m (q_models_m hPA) n))⟩

theorem lt_le_m {m n : num_l ℳ} (h : lt_l m n) : le_l m n :=
  le_trans_m hPA (le_succ_m hPA m) h

theorem lt_trans_m {m n p : num_l ℳ} (h₁ : lt_l m n) (h₂ : lt_l n p) : lt_l m p :=
  le_trans_m hPA h₁ (lt_le_m hPA h₂)

theorem lt_irrefl_m (n : num_l ℳ) : ¬lt_l n n := by
  rintro ⟨k, h⟩
  have h₁ : add_l n (succ_l k) = add_l n (zero_l ℳ) :=
    (Q.add_succ_m (q_models_m hPA) n k).trans ((succ_add_m hPA n k).symm.trans
      (h.trans (Q.add_zero_m (q_models_m hPA) n).symm))
  exact Q.nonzero_m (q_models_m hPA) k (add_left_cancel_m hPA n h₁)

theorem not_lt_of_le_m {m n : num_l ℳ} (h : le_l n m) : ¬lt_l m n :=
  fun h₁ => lt_irrefl_m hPA m (le_trans_m hPA h₁ h)

theorem le_cases_m {m n : num_l ℳ} (h : le_l m n) : m = n ∨ lt_l m n := by
  obtain ⟨k, h⟩ := h
  rcases Q.predecessor_m (q_models_m hPA) k with hk | ⟨p, hk⟩
  · exact Or.inl ((Q.add_zero_m (q_models_m hPA) m).symm.trans ((congrArg (add_l m) hk.symm).trans h))
  · exact Or.inr ⟨p, (succ_add_m hPA m p).trans
      ((Q.add_succ_m (q_models_m hPA) m p).symm.trans ((congrArg (add_l m) hk.symm).trans h))⟩

theorem le_total_m (m n : num_l ℳ) : le_l m n ∨ le_l n m := by
  let s : Term signature_m [.num] [.num] .num := .fvar .here
  let t : Term signature_m [.num] [.num] .num := .bvar .here
  let φ : Formula signature_m [] [.num] := .forallE .num (.disj (le_m s t) (le_m t s))
  have hφ (m : num_l ℳ) : φ.satisfies (Env.empty.pushFree m) ↔
      ∀ n : num_l ℳ, le_l m n ∨ le_l n m := by
    simp only [φ, Formula.satisfies, le_sat_m]
    rfl
  apply induct_m hPA φ Env.empty (fun m => ∀ n, le_l m n ∨ le_l n m) hφ ?_ ?_ m n
  · exact fun n => Or.inl (zero_le_m hPA n)
  · intro m hm n
    rcases Q.predecessor_m (q_models_m hPA) n with hn | ⟨p, hn⟩
    · subst n
      exact Or.inr (zero_le_m hPA (succ_l m))
    · subst n
      exact (hm p).elim (fun h => Or.inl ((succ_le_succ_m hPA).mpr h))
        (fun h => Or.inr ((succ_le_succ_m hPA).mpr h))

theorem le_of_not_lt_m {m n : num_l ℳ} (h : ¬lt_l m n) : le_l n m := by
  rcases le_total_m hPA m n with h₁ | h₁
  · rcases le_cases_m hPA h₁ with h₁ | h₁
    · rw [h₁]; exact le_refl_m hPA n
    · exact False.elim (h h₁)
  · exact h₁

theorem lt_ne_m {m n : num_l ℳ} (h : lt_l m n) : m ≠ n := by
  intro h₁
  exact lt_irrefl_m hPA n (h₁ ▸ h)

theorem le_lt_trans_m {m n p : num_l ℳ} (h₁ : le_l m n) (h₂ : lt_l n p) : lt_l m p :=
  le_trans_m hPA ((succ_le_succ_m hPA).mpr h₁) h₂

theorem lt_le_trans_m {m n p : num_l ℳ} (h₁ : lt_l m n) (h₂ : le_l n p) : lt_l m p :=
  le_trans_m hPA h₁ h₂

end YesMetaZFC.Model.Arithmetic.PA
