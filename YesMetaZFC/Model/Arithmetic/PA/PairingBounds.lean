import YesMetaZFC.Model.Arithmetic.PA.Pairing

/-! # 平方区间与配对单射性

最大坐标以关系给出；见证仅在命题证明内消去，不选择宿主数值函数。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Pairing
open Logic FirstOrder Logic.Arithmetic Model.Arithmetic.Pairing
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def max_l (m n k : num_l ℳ) : Prop :=
  (lt_l m n ∧ k = n) ∨ (¬lt_l m n ∧ k = m)

variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem interval_m {m n p k : num_l ℳ} (hp : graph_l m n p) (hk : max_l m n k) :
    le_l (mul_l k k) p ∧ lt_l p (mul_l (succ_l k) (succ_l k)) := by
  rcases hk with ⟨h, hk⟩ | ⟨h, hk⟩
  · subst k
    obtain rfl := (of_lt_m h).mp hp
    refine ⟨⟨m, rfl⟩, ?_⟩
    rw [square_succ_m hPA]
    apply (lt_succ_m hPA).mpr
    exact le_trans_m hPA (add_le_add_left_m hPA (mul_l n n) (lt_le_m hPA h)) ⟨n, rfl⟩
  · subst k
    obtain rfl := (of_not_lt_m h).mp hp
    refine ⟨⟨add_l m n, (add_assoc_m hPA (mul_l m m) m n).symm⟩, ?_⟩
    rw [square_succ_m hPA]
    exact (lt_succ_m hPA).mpr
      (add_le_add_left_m hPA (add_l (mul_l m m) m) (le_of_not_lt_m hPA h))

theorem max_eq_m {m n a b p k l : num_l ℳ} (hp : graph_l m n p) (hq : graph_l a b p)
    (hk : max_l m n k) (hl : max_l a b l) : k = l := by
  have h₁ := interval_m hPA hp hk
  have h₂ := interval_m hPA hq hl
  have h₃ (k l : num_l ℳ)
      (hk : lt_l p (mul_l (succ_l k) (succ_l k)))
      (hl : le_l (mul_l l l) p) (h : lt_l k l) : False :=
    lt_irrefl_m hPA p (lt_le_trans_m hPA hk (le_trans_m hPA (square_le_square_m hPA h) hl))
  rcases le_total_m hPA k l with h | h
  · rcases le_cases_m hPA h with h | h
    · exact h
    · exact False.elim (h₃ k l h₁.2 h₂.1 h)
  · rcases le_cases_m hPA h with h | h
    · exact h.symm
    · exact False.elim (h₃ l k h₂.2 h₁.1 h)

theorem injective_m (m n a b : num_l ℳ) {p : num_l ℳ}
    (hp : graph_l m n p) (hq : graph_l a b p) : m = a ∧ n = b := by
  rcases hp with ⟨h₂, hp⟩ | ⟨h₂, hp⟩ <;> rcases hq with ⟨h₃, hq⟩ | ⟨h₃, hq⟩
  · have h₁ := max_eq_m hPA (Or.inl ⟨h₂, hp⟩) (Or.inl ⟨h₃, hq⟩)
      (Or.inl ⟨h₂, rfl⟩) (Or.inl ⟨h₃, rfl⟩)
    subst b
    exact ⟨add_left_cancel_m hPA _ (hp.trans hq.symm), rfl⟩
  · have h₁ := max_eq_m hPA (Or.inl ⟨h₂, hp⟩) (Or.inr ⟨h₃, hq⟩)
      (Or.inl ⟨h₂, rfl⟩) (Or.inr ⟨h₃, rfl⟩)
    subst a
    have h₄ := lt_le_trans_m hPA h₂ (show le_l n (add_l n b) from ⟨b, rfl⟩)
    exact False.elim (lt_ne_m hPA (add_lt_add_left_m hPA (mul_l n n) h₄)
      ((hp.trans hq.symm).trans (add_assoc_m hPA (mul_l n n) n b)))
  · have h₁ := max_eq_m hPA (Or.inr ⟨h₂, hp⟩) (Or.inl ⟨h₃, hq⟩)
      (Or.inr ⟨h₂, rfl⟩) (Or.inl ⟨h₃, rfl⟩)
    subst b
    have h₄ := lt_le_trans_m hPA h₃ (show le_l m (add_l m n) from ⟨n, rfl⟩)
    exact False.elim (lt_ne_m hPA (add_lt_add_left_m hPA (mul_l m m) h₄)
      ((hq.trans hp.symm).trans (add_assoc_m hPA (mul_l m m) m n)))
  · have h₁ := max_eq_m hPA (Or.inr ⟨h₂, hp⟩) (Or.inr ⟨h₃, hq⟩)
      (Or.inr ⟨h₂, rfl⟩) (Or.inr ⟨h₃, rfl⟩)
    subst a
    exact ⟨rfl, add_left_cancel_m hPA _ (hp.trans hq.symm)⟩

theorem exists_unique_m (z : num_l ℳ) :
    ∃ m n, graph_l m n z ∧ ∀ a b, graph_l a b z → a = m ∧ b = n := by
  obtain ⟨m, n, h⟩ := surjective_m hPA z
  exact ⟨m, n, h, fun a b h₁ => injective_m hPA a b m n h₁ h⟩

end YesMetaZFC.Model.Arithmetic.PA.Pairing
