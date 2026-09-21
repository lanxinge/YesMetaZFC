import YesMetaZFC.Model.Arithmetic.PairingProvability
import YesMetaZFC.Model.Arithmetic.PA.Unpairing

/-! # PA 内部反配对的对象推导

正向总性／函数性只需纯逻辑；反向满射性和坐标唯一性使用 PA。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Pairing.Provability
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
variable {T : Theory signature_m} (hPA : Theory.Extends T Logic.Arithmetic.PA.theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem surjective_m (p : Term signature_m [] Δ .num) :
    Derives T Γ (Logic.Arithmetic.Pairing.range_m p) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  exact (Arithmetic.Pairing.range_sat_m η p).mpr (Pairing.surjective_m hℳ (p.eval η))

theorem injective_m (m n a b p : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (Logic.Arithmetic.Pairing.graph_m m n p)
      (.imp (Logic.Arithmetic.Pairing.graph_m a b p) (.conj (.equal m a) (.equal n b)))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Arithmetic.Pairing.graph_sat_m]
  exact fun h₁ h₂ => Pairing.injective_m hℳ _ _ _ _ h₁ h₂

theorem left_total_m (s : Term signature_m [] Δ .num) :
    Derives T Γ (.existsE .num (Logic.Arithmetic.Pairing.left_m (s.weakenBound sort_m.num) (.bvar .here))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Unpairing.left_sat_m, Term.eval_weakenBound, Term.eval]
  obtain ⟨m, n, h⟩ := Pairing.surjective_m hℳ (s.eval η)
  exact ⟨m, n, h⟩

theorem right_total_m (s : Term signature_m [] Δ .num) :
    Derives T Γ (.existsE .num (Logic.Arithmetic.Pairing.right_m (s.weakenBound sort_m.num) (.bvar .here))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Unpairing.right_sat_m, Term.eval_weakenBound, Term.eval]
  obtain ⟨m, n, h⟩ := Pairing.surjective_m hℳ (s.eval η)
  exact ⟨n, m, h⟩

theorem left_functional_m (s t u : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (Logic.Arithmetic.Pairing.left_m s t)
      (.imp (Logic.Arithmetic.Pairing.left_m s u) (.equal t u))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Unpairing.left_sat_m]
  exact fun h₁ h₂ => Unpairing.left_unique_m hℳ h₁ h₂

theorem right_functional_m (s t u : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (Logic.Arithmetic.Pairing.right_m s t)
      (.imp (Logic.Arithmetic.Pairing.right_m s u) (.equal t u))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Unpairing.right_sat_m]
  exact fun h₁ h₂ => Unpairing.right_unique_m hℳ h₁ h₂

end YesMetaZFC.Model.Arithmetic.PA.Pairing.Provability
