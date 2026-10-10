import YesMetaZFC.Logic.Arithmetic.PA.Axioms
import YesMetaZFC.Logic.Arithmetic.Q.Derivation
import YesMetaZFC.Logic.Arithmetic.Equality
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra

/-! # PA 归纳的算术应用

左零律使用真实对象公式归纳，结论适用于任意项，而非仅外部数码。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA
open FirstOrder
set_option autoImplicit false

/-- 归纳变量取后继时，原自由参数保持不变。 -/
theorem next_weaken_m {Δ : SortContext signature_m}
    (t : Term signature_m [] Δ .num) :
    (t.weakenFree sort_m.num).substituteMapped VariableSubstitution.boundId next_m =
      t.weakenFree sort_m.num := by
  rw [Term.substituteMapped_weakenFree_tail]
  exact Term.substituteMapped_of_renaming (VariableRenaming.weaken sort_m.num) t

/-- 对公式归纳后在任意项处实例化；不限制该项为外部数码。 -/
theorem induction_term_m {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {φ : Formula signature_m [] (.num :: Δ)}
    (h₀ : Derives T Γ (φ.instantiateFreeTop zero_m))
    (h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m))) (t : Term signature_m [] Δ .num) :
    Derives T Γ (φ.instantiateFreeTop t) := by
  simpa only [Formula.forallFreeTop, Formula.instantiateTop_abstractFreeTop] using
    Derives.forall_elim t (induction_rule_m hPA h₀ h₁)

theorem zero_add_m {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (t : Term signature_m [] Δ .num) : Derives T Γ (.equal (add_m zero_m t) t) := by
  have hQ : Theory.Extends T Q.theory_m := fun h => hPA (extends_q_m h)
  let φ : Formula signature_m [] (.num :: Δ) :=
    .equal (add_m zero_m (.fvar .here)) (.fvar .here)
  have h : Derives T Γ (φ.forallFreeTop sort_m.num) := by
    apply induction_rule_m hPA (φ := φ)
    · exact Q.add_zero_m hQ zero_m
    · apply Derives.imp_intro
      exact Derives.eq_trans (Q.add_succ_m hQ zero_m (.fvar .here))
        (succ_congr_m (Derives.assumption List.mem_cons_self))
  change Derives T Γ (φ.instantiateFreeTop t)
  simpa only [Formula.forallFreeTop, Formula.instantiateTop_abstractFreeTop] using
    Derives.forall_elim t h

end YesMetaZFC.Logic.Arithmetic.PA
