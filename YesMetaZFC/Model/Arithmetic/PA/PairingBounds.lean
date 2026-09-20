import YesMetaZFC.Model.Arithmetic.PA.Pairing

/-! # 平方分层配对的单射性

先证明平方区间界，再证明相等编码有相同最大坐标，最后区分两个分支。
差值与坐标始终在模型内部；不使用宿主平方根或线序类型类。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Pairing
open Logic FirstOrder Logic.Arithmetic Model.Arithmetic.Pairing
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

noncomputable def max_l (m n : num_l ℳ) : num_l ℳ := by
  classical
  exact if lt_l m n then n else m

variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem interval_m (m n : num_l ℳ) :
    le_l (mul_l (max_l m n) (max_l m n)) (value_l m n) ∧
      lt_l (value_l m n) (mul_l (succ_l (max_l m n)) (succ_l (max_l m n))) := by
  classical
  by_cases h : lt_l m n
  · simp only [max_l, value_l, if_pos h]
    refine ⟨⟨m, rfl⟩, ?_⟩
    rw [square_succ_m hPA]
    apply (lt_succ_m hPA).mpr
    exact le_trans_m hPA (add_le_add_left_m hPA (mul_l n n) (lt_le_m hPA h)) ⟨n, rfl⟩
  · simp only [max_l, value_l, if_neg h]
    refine ⟨⟨add_l m n, (add_assoc_m hPA (mul_l m m) m n).symm⟩, ?_⟩
    rw [square_succ_m hPA]
    exact (lt_succ_m hPA).mpr
      (add_le_add_left_m hPA (add_l (mul_l m m) m) (le_of_not_lt_m hPA h))

theorem max_eq_m (m n a b : num_l ℳ) (h : value_l m n = value_l a b) : max_l m n = max_l a b := by
  have h₁ (m n a b : num_l ℳ) (h : value_l m n = value_l a b)
      (h₂ : lt_l (max_l m n) (max_l a b)) : False := by
    have h₃ := le_trans_m hPA (square_le_square_m hPA h₂) (interval_m hPA a b).1
    exact lt_ne_m hPA (lt_le_trans_m hPA (interval_m hPA m n).2 h₃) h
  rcases le_total_m hPA (max_l m n) (max_l a b) with h₂ | h₂
  · rcases le_cases_m hPA h₂ with h₂ | h₂
    · exact h₂
    · exact False.elim (h₁ m n a b h h₂)
  · rcases le_cases_m hPA h₂ with h₂ | h₂
    · exact h₂.symm
    · exact False.elim (h₁ a b m n h.symm h₂)

theorem injective_m (m n a b : num_l ℳ) (h : value_l m n = value_l a b) : m = a ∧ n = b := by
  classical
  have h₁ := max_eq_m hPA m n a b h
  by_cases h₂ : lt_l m n <;> by_cases h₃ : lt_l a b
  · simp only [value_l, if_pos h₂, if_pos h₃] at h
    simp only [max_l, if_pos h₂, if_pos h₃] at h₁
    subst b
    exact ⟨add_left_cancel_m hPA _ h, rfl⟩
  · simp only [value_l, if_pos h₂, if_neg h₃] at h
    simp only [max_l, if_pos h₂, if_neg h₃] at h₁
    subst a
    have h₄ := lt_le_trans_m hPA h₂ (show le_l n (add_l n b) from ⟨b, rfl⟩)
    exact False.elim (lt_ne_m hPA (add_lt_add_left_m hPA (mul_l n n) h₄)
      (h.trans (add_assoc_m hPA (mul_l n n) n b)))
  · simp only [value_l, if_neg h₂, if_pos h₃] at h
    simp only [max_l, if_neg h₂, if_pos h₃] at h₁
    subst b
    have h₄ := lt_le_trans_m hPA h₃ (show le_l m (add_l m n) from ⟨n, rfl⟩)
    exact False.elim (lt_ne_m hPA (add_lt_add_left_m hPA (mul_l m m) h₄)
      (h.symm.trans (add_assoc_m hPA (mul_l m m) m n)))
  · simp only [value_l, if_neg h₂, if_neg h₃] at h
    simp only [max_l, if_neg h₂, if_neg h₃] at h₁
    subst a
    exact ⟨rfl, add_left_cancel_m hPA _ h⟩

theorem exists_unique_m (z : num_l ℳ) :
    ∃ m n, value_l m n = z ∧ ∀ a b, value_l a b = z → a = m ∧ b = n := by
  obtain ⟨m, n, h⟩ := surjective_m hPA z
  exact ⟨m, n, h, fun a b h₁ => injective_m hPA a b m n (h₁.trans h.symm)⟩

end YesMetaZFC.Model.Arithmetic.PA.Pairing
