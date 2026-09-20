import YesMetaZFC.Logic.Arithmetic.PA.Induction

/-! # PA 中任意项的加法规律

归纳公式保留原自由参数，局部假设沿新变量弱化。以下均为对象推导，
不是只在标准模型成立的宿主等式，也不要求参数为外部数码。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem succ_add_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (add_m (succ_m s) t) (succ_m (add_m s t))) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let u := s.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (add_m (succ_m u) (.fvar .here)) (succ_m (add_m u (.fvar .here)))
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, u, Formula.instantiateFreeTop_equal, add_m, succ_m,
      Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    exact Derives.eq_trans (Q.add_zero_m hQ (succ_m s))
        (Derives.eq_symm (succ_congr_m (Q.add_zero_m hQ s)))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, u, Formula.substituteMapped,
      add_m, succ_m, Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    exact Derives.eq_trans (Q.add_succ_m hQ (succ_m u) (.fvar .here))
      (Derives.eq_trans (succ_congr_m (Derives.assumption (formula := φ) List.mem_cons_self))
        (Derives.eq_symm (succ_congr_m (Q.add_succ_m hQ u (.fvar .here)))))
  have h := induction_term_m hPA h₀ h₁ t
  simp only [φ, u, Formula.instantiateFreeTop_equal, add_m, succ_m,
    Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h
  exact h

theorem add_comm_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (add_m s t) (add_m t s)) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let u := s.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (add_m u (.fvar .here)) (add_m (.fvar .here) u)
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, u, Formula.instantiateFreeTop_equal, add_m,
      Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    exact Derives.eq_trans (Q.add_zero_m hQ s) (Derives.eq_symm (zero_add_m hPA s))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, u, Formula.substituteMapped,
      add_m, Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    exact Derives.eq_trans (Q.add_succ_m hQ u (.fvar .here))
      (Derives.eq_trans (succ_congr_m (Derives.assumption List.mem_cons_self))
        (Derives.eq_symm (succ_add_m hPA (.fvar .here) u)))
  have h := induction_term_m hPA h₀ h₁ t
  simp only [φ, u, Formula.instantiateFreeTop_equal, add_m,
    Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h
  exact h

theorem add_assoc_m (s t u : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (add_m (add_m s t) u) (add_m s (add_m t u))) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let s₁ := s.weakenFree sort_m.num
  let t₁ := t.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (add_m (add_m s₁ t₁) (.fvar .here)) (add_m s₁ (add_m t₁ (.fvar .here)))
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, s₁, t₁, Formula.instantiateFreeTop_equal, add_m,
      Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    exact Derives.eq_trans (Q.add_zero_m hQ (add_m s t))
      (Derives.eq_symm (add_right_congr_m s (Q.add_zero_m hQ t)))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, s₁, t₁, Formula.substituteMapped,
      add_m, Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    exact Derives.eq_trans (Q.add_succ_m hQ (add_m s₁ t₁) (.fvar .here))
      (Derives.eq_trans (succ_congr_m (Derives.assumption List.mem_cons_self))
        (Derives.eq_symm (Derives.eq_trans
          (add_right_congr_m s₁ (Q.add_succ_m hQ t₁ (.fvar .here)))
          (Q.add_succ_m hQ s₁ (add_m t₁ (.fvar .here))))))
  have h := induction_term_m hPA h₀ h₁ u
  simp only [φ, s₁, t₁, Formula.instantiateFreeTop_equal, add_m,
    Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h
  exact h

/-- 交换末尾两项；只组合已有加法规律，不再进行公式归纳。 -/
theorem add_right_comm_m (s t u : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (add_m (add_m s t) u) (add_m (add_m s u) t)) :=
  Derives.eq_trans (add_assoc_m hPA s t u)
    (Derives.eq_trans (add_right_congr_m s (add_comm_m hPA t u))
      (Derives.eq_symm (add_assoc_m hPA s u t)))

end YesMetaZFC.Logic.Arithmetic.PA
