import YesMetaZFC.Logic.Arithmetic.Q.Order
import YesMetaZFC.Logic.Arithmetic.PA.Addition

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

end YesMetaZFC.Logic.Arithmetic.PA
