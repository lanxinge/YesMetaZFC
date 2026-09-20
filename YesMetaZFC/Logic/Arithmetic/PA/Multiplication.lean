import YesMetaZFC.Logic.Arithmetic.PA.Addition

/-! # PA 中任意项的乘法规律

右零律与右后继律已属于 Q。一般规律通过保留自由参数的对象公式归纳证明，
不使用模型完备性，也不要求输入项为外部数码。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem zero_mul_m (t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m zero_m t) zero_m) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (mul_m zero_m (.fvar .here)) zero_m
  change Derives T Γ (φ.instantiateFreeTop t)
  apply induction_term_m hPA (φ := φ)
  · exact Q.mul_zero_m hQ zero_m
  · apply Derives.imp_intro
    exact Derives.eq_trans (Q.mul_succ_m hQ zero_m (.fvar .here))
      (Derives.eq_trans (Q.add_zero_m hQ _)
        (Derives.assumption List.mem_cons_self))

theorem mul_one_m (t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m t (succ_m zero_m)) t) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  exact Derives.eq_trans (Q.mul_succ_m hQ t zero_m)
    (Derives.eq_trans (add_left_congr_m t (Q.mul_zero_m hQ t)) (zero_add_m hPA t))

theorem one_mul_m (t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m (succ_m zero_m) t) t) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (mul_m (succ_m zero_m) (.fvar .here)) (.fvar .here)
  change Derives T Γ (φ.instantiateFreeTop t)
  apply induction_term_m hPA (φ := φ)
  · exact Q.mul_zero_m hQ _
  · apply Derives.imp_intro
    exact Derives.eq_trans (Q.mul_succ_m hQ _ (.fvar .here))
      (Derives.eq_trans (Q.add_succ_m hQ _ zero_m)
        (succ_congr_m (Derives.eq_trans (Q.add_zero_m hQ _)
          (Derives.assumption List.mem_cons_self))))

theorem succ_mul_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m (succ_m s) t) (add_m (mul_m s t) t)) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let u := s.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (mul_m (succ_m u) (.fvar .here)) (add_m (mul_m u (.fvar .here)) (.fvar .here))
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, u, Formula.instantiateFreeTop_equal, mul_m, add_m, succ_m,
      Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    exact Derives.eq_trans (Q.mul_zero_m hQ (succ_m s))
      (Derives.eq_symm (Derives.eq_trans (Q.add_zero_m hQ (mul_m s zero_m))
        (Q.mul_zero_m hQ s)))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, u, Formula.substituteMapped, mul_m, add_m, succ_m,
      Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    apply Derives.eq_trans (Q.mul_succ_m hQ (succ_m u) (.fvar .here))
    apply Derives.eq_trans (add_left_congr_m (succ_m u)
      (Derives.assumption List.mem_cons_self))
    apply Derives.eq_trans (Q.add_succ_m hQ _ u)
    apply Derives.eq_trans (succ_congr_m
      (add_right_comm_m hPA (mul_m u (.fvar .here)) (.fvar .here) u))
    exact Derives.eq_symm (Derives.eq_trans (Q.add_succ_m hQ _ (.fvar .here))
      (succ_congr_m (add_left_congr_m (.fvar .here) (Q.mul_succ_m hQ u (.fvar .here)))))
  have h := induction_term_m hPA h₀ h₁ t
  simp only [φ, u, Formula.instantiateFreeTop_equal, mul_m, add_m, succ_m,
    Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h
  exact h

theorem mul_comm_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m s t) (mul_m t s)) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let u := s.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (mul_m u (.fvar .here)) (mul_m (.fvar .here) u)
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, u, Formula.instantiateFreeTop_equal, mul_m,
      Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    exact Derives.eq_trans (Q.mul_zero_m hQ s) (Derives.eq_symm (zero_mul_m hPA s))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, u, Formula.substituteMapped, mul_m,
      Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    exact Derives.eq_trans (Q.mul_succ_m hQ u (.fvar .here))
      (Derives.eq_trans (add_left_congr_m u (Derives.assumption List.mem_cons_self))
        (Derives.eq_symm (succ_mul_m hPA (.fvar .here) u)))
  have h := induction_term_m hPA h₀ h₁ t
  simp only [φ, u, Formula.instantiateFreeTop_equal, mul_m,
    Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h
  exact h

theorem mul_add_m (s t u : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m s (add_m t u)) (add_m (mul_m s t) (mul_m s u))) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let s₁ := s.weakenFree sort_m.num
  let t₁ := t.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (mul_m s₁ (add_m t₁ (.fvar .here)))
      (add_m (mul_m s₁ t₁) (mul_m s₁ (.fvar .here)))
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, s₁, t₁, Formula.instantiateFreeTop_equal, mul_m, add_m,
      Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    exact Derives.eq_trans (mul_right_congr_m s (Q.add_zero_m hQ t))
      (Derives.eq_symm (Derives.eq_trans
        (add_right_congr_m (mul_m s t) (Q.mul_zero_m hQ s)) (Q.add_zero_m hQ _)))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, s₁, t₁, Formula.substituteMapped, mul_m, add_m,
      Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    apply Derives.eq_trans (mul_right_congr_m s₁ (Q.add_succ_m hQ t₁ (.fvar .here)))
    apply Derives.eq_trans (Q.mul_succ_m hQ s₁ _)
    apply Derives.eq_trans (add_left_congr_m s₁ (Derives.assumption List.mem_cons_self))
    apply Derives.eq_trans (add_assoc_m hPA (mul_m s₁ t₁) (mul_m s₁ (.fvar .here)) s₁)
    exact Derives.eq_symm (add_right_congr_m (mul_m s₁ t₁) (Q.mul_succ_m hQ s₁ (.fvar .here)))
  have h := induction_term_m hPA h₀ h₁ u
  simp only [φ, s₁, t₁, Formula.instantiateFreeTop_equal, mul_m, add_m,
    Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h
  exact h

/-- 乘法对左侧和的分配由交换律与已证分配律组合，不重复归纳。 -/
theorem add_mul_m (s t u : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m (add_m s t) u) (add_m (mul_m s u) (mul_m t u))) := by
  apply Derives.eq_trans (mul_comm_m hPA (add_m s t) u)
  apply Derives.eq_trans (mul_add_m hPA u s t)
  apply Derives.eq_trans (add_left_congr_m (mul_m u t) (mul_comm_m hPA u s))
  exact add_right_congr_m (mul_m s u) (mul_comm_m hPA u t)

theorem mul_assoc_m (s t u : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m (mul_m s t) u) (mul_m s (mul_m t u))) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let s₁ := s.weakenFree sort_m.num
  let t₁ := t.weakenFree sort_m.num
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (mul_m (mul_m s₁ t₁) (.fvar .here)) (mul_m s₁ (mul_m t₁ (.fvar .here)))
  have h₀ : Derives T Γ (φ.instantiateFreeTop zero_m) := by
    simp only [φ, s₁, t₁, Formula.instantiateFreeTop_equal, mul_m,
      Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
      Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree]
    exact Derives.eq_trans (Q.mul_zero_m hQ (mul_m s t))
      (Derives.eq_symm (Derives.eq_trans (mul_right_congr_m s (Q.mul_zero_m hQ t))
        (Q.mul_zero_m hQ s)))
  have h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m)) := by
    apply Derives.imp_intro
    change Derives T (φ :: FreshVariable.extendContext sort_m.num Γ)
      (φ.substituteMapped VariableSubstitution.boundId next_m)
    simp only [φ, s₁, t₁, Formula.substituteMapped, mul_m,
      Term.substituteMapped, Arguments.substituteMapped, next_weaken_m]
    apply Derives.eq_trans (Q.mul_succ_m hQ (mul_m s₁ t₁) (.fvar .here))
    apply Derives.eq_trans (add_left_congr_m (mul_m s₁ t₁) (Derives.assumption List.mem_cons_self))
    exact Derives.eq_symm (Derives.eq_trans
      (mul_right_congr_m s₁ (Q.mul_succ_m hQ t₁ (.fvar .here)))
      (mul_add_m hPA s₁ (mul_m t₁ (.fvar .here)) t₁))
  have h := induction_term_m hPA h₀ h₁ u
  simp only [φ, s₁, t₁, Formula.instantiateFreeTop_equal, mul_m,
    Term.instantiateFreeTop_app, Arguments.instantiateFreeTop_cons,
    Arguments.instantiateFreeTop_nil, Term.instantiateFreeTop_weakenFree] at h
  exact h

end YesMetaZFC.Logic.Arithmetic.PA
