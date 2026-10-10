import YesMetaZFC.Logic.Arithmetic.Q.Order
import YesMetaZFC.Logic.Arithmetic.PA.Addition
import YesMetaZFC.Logic.Arithmetic.PA.Cancellation

/-! # PA 中可定义序的初步规律

传递性实际合成两个内部差值见证，不要求它们为外部数码。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem zero_le_m (t : Term signature_m [] Δ .num) : Derives T Γ (le_m zero_m t) :=
  le_intro_m t (zero_add_m hPA t)

theorem le_trans_m {s t u : Term signature_m [] Δ .num}
    (h₁ : Derives T Γ (le_m s t)) (h₂ : Derives T Γ (le_m t u)) :
    Derives T Γ (le_m s u) := by
  apply le_elim_m h₁
  rw [le_weaken_m]
  have h₂₁ := Derives.context_weaken_cons (assumption := le_body_m s t)
    (Derives.free_renaming (VariableRenaming.weaken sort_m.num) h₂)
  change Derives T (le_body_m s t :: FreshVariable.extendContext sort_m.num Γ)
    ((le_m t u).weakenFree sort_m.num) at h₂₁
  rw [le_weaken_m] at h₂₁
  apply le_elim_m h₂₁
  rw [le_weaken_m]
  have h₁₁ := Derives.context_weaken_cons
    (assumption := le_body_m (t.weakenFree sort_m.num) (u.weakenFree sort_m.num)) (Derives.free_renaming
    (VariableRenaming.weaken sort_m.num)
    (Derives.assumption (T := T) (Γ := le_body_m s t :: FreshVariable.extendContext sort_m.num Γ)
      List.mem_cons_self))
  apply le_intro_m (add_m (.fvar (.there .here)) (.fvar .here))
  apply Derives.eq_trans (Derives.eq_symm (add_assoc_m hPA _ _ _))
  apply Derives.eq_trans (add_left_congr_m (.fvar .here) h₁₁)
  exact Derives.assumption List.mem_cons_self

theorem le_antisymm_m {s t : Term signature_m [] Δ .num}
    (h₁ : Derives T Γ (le_m s t)) (h₂ : Derives T Γ (le_m t s)) :
    Derives T Γ (.equal s t) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  apply le_elim_m h₁
  have h₂₁ := Derives.context_weaken_cons (assumption := le_body_m s t)
    (Derives.free_renaming (VariableRenaming.weaken sort_m.num) h₂)
  change Derives T (le_body_m s t :: FreshVariable.extendContext sort_m.num Γ)
    ((le_m t s).weakenFree sort_m.num) at h₂₁
  rw [le_weaken_m] at h₂₁
  apply le_elim_m h₂₁
  let s₂ := (s.weakenFree sort_m.num).weakenFree sort_m.num
  let t₂ := (t.weakenFree sort_m.num).weakenFree sort_m.num
  let a : Term signature_m [] (.num :: .num :: Δ) .num := .fvar (.there .here)
  let b : Term signature_m [] (.num :: .num :: Δ) .num := .fvar .here
  let Γ₂ := le_body_m (t.weakenFree sort_m.num) (s.weakenFree sort_m.num) ::
    FreshVariable.extendContext sort_m.num (le_body_m s t :: FreshVariable.extendContext sort_m.num Γ)
  change Derives T Γ₂ (.equal s₂ t₂)
  have h₁₂ :=
    Derives.context_weaken_cons
      (assumption := le_body_m (t.weakenFree sort_m.num) (s.weakenFree sort_m.num))
      (Derives.free_renaming (VariableRenaming.weaken sort_m.num)
      (Derives.assumption (T := T) (Γ := le_body_m s t :: FreshVariable.extendContext sort_m.num Γ)
        List.mem_cons_self))
  change Derives T Γ₂ (.equal (add_m s₂ a) t₂) at h₁₂
  have h₂₂ : Derives T Γ₂ (.equal (add_m t₂ b) s₂) := Derives.assumption List.mem_cons_self
  have h₃ : Derives T Γ₂ (.equal (add_m a b) zero_m) :=
    add_left_cancel_m hPA s₂ (Derives.eq_trans (Derives.eq_symm (add_assoc_m hPA s₂ a b))
      (Derives.eq_trans (add_left_congr_m b h₁₂)
        (Derives.eq_trans h₂₂ (Derives.eq_symm (Q.add_zero_m hQ s₂)))))
  have h₄ := add_eq_zero_left_m hPA h₃
  exact Derives.eq_trans (Derives.eq_symm (Q.add_zero_m hQ s₂))
    (Derives.eq_trans (Derives.eq_symm (add_right_congr_m s₂ h₄)) h₁₂)

end YesMetaZFC.Logic.Arithmetic.PA
