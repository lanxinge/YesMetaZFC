import YesMetaZFC.Logic.Arithmetic.Syntax
import YesMetaZFC.Logic.Arithmetic.Equality
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution

/-! # 算术语言中的可定义序

序不是新增关系符号。非严格序的见证是对象数；没有宿主自然数界。
-/
namespace YesMetaZFC.Logic.Arithmetic
open FirstOrder
set_option autoImplicit false

def le_body_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ (.num :: Δ) :=
  .equal (add_m (s.weakenFree sort_m.num) (.fvar .here)) (t.weakenFree sort_m.num)

def le_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := (le_body_m s t).existsFreeTop sort_m.num

def lt_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := le_m (succ_m s) t

theorem le_rename_m {Γ Δ Θ : SortContext signature_m}
    (ρ : VariableRenaming Δ Θ) (s t : Term signature_m Γ Δ .num) :
    (le_m s t).renameFree ρ = le_m (s.renameFree ρ) (t.renameFree ρ) := by
  change ((le_body_m s t).existsFreeTop sort_m.num).renameMapped VariableRenaming.id ρ = _
  rw [Formula.renameMapped_existsFreeTop]
  simp only [le_body_m, Formula.renameMapped, add_m, Term.renameMapped,
    Arguments.renameMapped]
  rw [Term.renameMapped_weakenFree_lift (introduced := sort_m.num) VariableRenaming.id ρ s,
    Term.renameMapped_weakenFree_lift (introduced := sort_m.num) VariableRenaming.id ρ t]
  rfl

theorem le_weaken_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    (le_m s t).weakenFree sort_m.num =
      le_m (s.weakenFree sort_m.num) (t.weakenFree sort_m.num) :=
  le_rename_m (VariableRenaming.weaken sort_m.num) s t

theorem le_intro_m {T : Theory signature_m} {Δ : SortContext signature_m}
    {Γ : Context signature_m Δ} {s t : Term signature_m [] Δ .num}
    (u : Term signature_m [] Δ .num) (h : Derives T Γ (.equal (add_m s u) t)) :
    Derives T Γ (le_m s t) := by
  apply Derives.exists_intro u
  simp only [Formula.instantiateTop_abstractFreeTop,
    le_body_m, Formula.instantiateFreeTop_equal, add_m, Term.instantiateFreeTop_app,
    Arguments.instantiateFreeTop_cons, Arguments.instantiateFreeTop_nil,
    Term.instantiateFreeTop_weakenFree]
  exact h

theorem le_elim_m {T : Theory signature_m} {Δ : SortContext signature_m}
    {Γ : Context signature_m Δ} {s t : Term signature_m [] Δ .num}
    {φ : Formula signature_m [] Δ} (h : Derives T Γ (le_m s t))
    (h₁ : Derives T (le_body_m s t :: FreshVariable.extendContext sort_m.num Γ)
      (φ.weakenFree sort_m.num)) : Derives T Γ φ :=
  Derives.exists_elim h h₁

theorem le_add_m {T : Theory signature_m} {Δ : SortContext signature_m}
    {Γ : Context signature_m Δ} (s t : Term signature_m [] Δ .num) :
    Derives T Γ (le_m s (add_m s t)) := le_intro_m t (Derives.eq_refl _)

end YesMetaZFC.Logic.Arithmetic
