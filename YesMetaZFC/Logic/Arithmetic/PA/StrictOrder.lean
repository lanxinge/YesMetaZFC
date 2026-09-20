import YesMetaZFC.Logic.Arithmetic.PA.Order

/-! # PA 中后继与严格序

后继保持并反映可定义序；严格序的不可自返性使用加法消去与后继非零，
没有把模型外部的良基性放入前提。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem succ_le_succ_m {s t : Term signature_m [] Δ .num}
    (h : Derives T Γ (le_m s t)) : Derives T Γ (le_m (succ_m s) (succ_m t)) := by
  apply le_elim_m h
  rw [le_weaken_m]
  apply le_intro_m (.fvar .here)
  exact Derives.eq_trans (succ_add_m hPA _ _)
    (succ_congr_m (Derives.assumption List.mem_cons_self))

theorem le_of_succ_le_succ_m {s t : Term signature_m [] Δ .num}
    (h : Derives T Γ (le_m (succ_m s) (succ_m t))) : Derives T Γ (le_m s t) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  apply le_elim_m h
  rw [le_weaken_m]
  apply le_intro_m (.fvar .here)
  apply Derives.imp_elim (Q.injective_m hQ _ _)
  exact Derives.eq_trans (Derives.eq_symm (succ_add_m hPA _ _))
    (Derives.assumption List.mem_cons_self)

theorem lt_le_m {s t : Term signature_m [] Δ .num}
    (h : Derives T Γ (lt_m s t)) : Derives T Γ (le_m s t) :=
  le_trans_m hPA (Q.le_succ_m (fun h => hPA (extends_q_m h)) s) h

theorem lt_trans_m {s t u : Term signature_m [] Δ .num}
    (h₁ : Derives T Γ (lt_m s t)) (h₂ : Derives T Γ (lt_m t u)) :
    Derives T Γ (lt_m s u) := le_trans_m hPA h₁ (lt_le_m hPA h₂)

theorem lt_irrefl_m (t : Term signature_m [] Δ .num) : Derives T Γ (.neg (lt_m t t)) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  apply Derives.neg_intro
  apply le_elim_m (s := succ_m t) (t := t) (Derives.assumption List.mem_cons_self)
  apply Derives.neg_elim (hNegation := Q.nonzero_m hQ (.fvar .here))
  apply add_left_cancel_m hPA (t.weakenFree sort_m.num)
  exact Derives.eq_trans (Q.add_succ_m hQ _ _)
    (Derives.eq_trans (Derives.eq_symm (succ_add_m hPA _ _))
      (Derives.eq_trans (Derives.assumption List.mem_cons_self) (Derives.eq_symm (Q.add_zero_m hQ _))))

end YesMetaZFC.Logic.Arithmetic.PA
