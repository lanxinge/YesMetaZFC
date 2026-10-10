import YesMetaZFC.Logic.Arithmetic.Order
import YesMetaZFC.Logic.Arithmetic.Q.Derivation

/-! # Q 已能证明的序自反性 -/
namespace YesMetaZFC.Logic.Arithmetic.Q
open FirstOrder
set_option autoImplicit false

theorem le_refl_m {T : Theory signature_m} (hQ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives T Γ (le_m t t) :=
  le_intro_m zero_m (add_zero_m hQ t)

theorem le_succ_m {T : Theory signature_m} (hQ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives T Γ (le_m t (succ_m t)) :=
  le_intro_m (succ_m zero_m) (Derives.eq_trans (add_succ_m hQ t zero_m)
    (succ_congr_m (add_zero_m hQ t)))

theorem lt_succ_m {T : Theory signature_m} (hQ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives T Γ (lt_m t (succ_m t)) :=
  le_refl_m hQ (succ_m t)

end YesMetaZFC.Logic.Arithmetic.Q
