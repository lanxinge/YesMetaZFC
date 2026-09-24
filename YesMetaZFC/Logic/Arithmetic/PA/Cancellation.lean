import YesMetaZFC.Logic.Arithmetic.PA.Addition

/-! # PA 中加法的消去律

对共同加数进行真实公式归纳；被消去的等式作为公式内的前提，
而不是把宿主谓词或外部自然数归纳作用于任意模型元素。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem add_right_cancel_m {s t : Term signature_m [] Δ .num}
    (u : Term signature_m [] Δ .num)
    (h : Derives T Γ (.equal (add_m s u) (add_m t u))) :
    Derives T Γ (.equal s t) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let s₁ := s.weakenFree sort_m.num
  let t₁ := t.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .imp (.equal (add_m s₁ (.fvar .here)) (add_m t₁ (.fvar .here))) (.equal s₁ t₁)
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, s₁, t₁, Formula.instantiateFreeTop_imp, Formula.instantiateFreeTop_equal,
      add_m, Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    apply Derives.imp_intro
    exact Derives.eq_trans (Derives.eq_symm (Q.add_zero_m hQ s))
      (Derives.eq_trans (Derives.assumption List.mem_cons_self) (Q.add_zero_m hQ t))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, s₁, t₁, Formula.substituteMapped, add_m,
      Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    apply Derives.imp_intro
    apply Derives.imp_elim (Derives.assumption (formula := φ)
      (List.mem_cons_of_mem _ List.mem_cons_self))
    apply Derives.imp_elim (Q.injective_m hQ _ _)
    exact Derives.eq_trans (Derives.eq_symm (Q.add_succ_m hQ s₁ (.fvar .here)))
      (Derives.eq_trans (Derives.assumption List.mem_cons_self) (Q.add_succ_m hQ t₁ (.fvar .here)))
  have h₂ := induction_term_m hPA h₀ h₁ u
  simp only [φ, s₁, t₁, Formula.instantiateFreeTop_imp, Formula.instantiateFreeTop_equal,
    add_m, Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h₂
  exact Derives.imp_elim h₂ h

theorem add_left_cancel_m (s : Term signature_m [] Δ .num)
    {t u : Term signature_m [] Δ .num}
    (h : Derives T Γ (.equal (add_m s t) (add_m s u))) :
    Derives T Γ (.equal t u) :=
  add_right_cancel_m hPA s (Derives.eq_trans (add_comm_m hPA t s)
    (Derives.eq_trans h (add_comm_m hPA s u)))

/-- 和为零时左加数为零；后继分支由 Q 的非零公理排除。 -/
theorem add_eq_zero_left_m {s t : Term signature_m [] Δ .num}
    (h : Derives T Γ (.equal (add_m s t) zero_m)) : Derives T Γ (.equal s zero_m) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let s₁ := s.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .imp (.equal (add_m s₁ (.fvar .here)) zero_m) (.equal s₁ zero_m)
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, s₁, Formula.instantiateFreeTop_imp, Formula.instantiateFreeTop_equal,
      add_m, Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    apply Derives.imp_intro
    exact Derives.eq_trans (Derives.eq_symm (Q.add_zero_m hQ s))
      (Derives.assumption List.mem_cons_self)
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, s₁, Formula.substituteMapped, add_m,
      Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    apply Derives.imp_intro
    apply Derives.falsum_elim
    exact Derives.neg_elim
      (Derives.eq_trans (Derives.eq_symm (Q.add_succ_m hQ s₁ (.fvar .here)))
        (Derives.assumption List.mem_cons_self)) (Q.nonzero_m hQ _)
  have h₂ := induction_term_m hPA h₀ h₁ t
  simp only [φ, s₁, Formula.instantiateFreeTop_imp, Formula.instantiateFreeTop_equal,
    add_m, Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h₂
  exact Derives.imp_elim h₂ h

theorem add_eq_zero_right_m {s t : Term signature_m [] Δ .num}
    (h : Derives T Γ (.equal (add_m s t) zero_m)) : Derives T Γ (.equal t zero_m) :=
  add_eq_zero_left_m hPA (Derives.eq_trans (add_comm_m hPA t s) h)

end YesMetaZFC.Logic.Arithmetic.PA
