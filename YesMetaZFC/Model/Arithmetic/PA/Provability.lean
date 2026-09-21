import YesMetaZFC.Model.Arithmetic.Completeness
import YesMetaZFC.Model.Arithmetic.PA.Division
import YesMetaZFC.Model.Arithmetic.PA.Divisibility
import YesMetaZFC.Model.Arithmetic.PA.Minimum
import YesMetaZFC.Model.Arithmetic.Minimum
import YesMetaZFC.Model.Arithmetic.PA.FiniteRange

/-! # PA 任意模型结论的对象推导

按需导入的完备性消费者；公共结论使用原 Derives，允许 PA 扩张、
任意有限参数及局部上下文。基础 Logic 算术模块不反向导入本层。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Provability
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false

variable {T : Theory signature_m} (hPA : Theory.Extends T Logic.Arithmetic.PA.theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem le_total_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.disj (le_m s t) (le_m t s)) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simpa only [Formula.satisfies, le_sat_m] using PA.le_total_m hℳ (s.eval η) (t.eval η)

theorem division_exists_m (n d : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (.neg (.equal d zero_m)) (Logic.Arithmetic.Division.domain_m n d)) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Division.domain_sat_m]
  exact Division.exists_m hℳ (n.eval η) (d.eval η)

theorem division_unique_m (n d q r a b : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (Logic.Arithmetic.Division.graph_m n d q r)
      (.imp (Logic.Arithmetic.Division.graph_m n d a b) (.conj (.equal q a) (.equal r b)))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Division.graph_sat_m]
  exact fun h₁ h₂ => Division.unique_m hℳ h₁ h₂

theorem division_nonzero_m (n d q r : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (Logic.Arithmetic.Division.graph_m n d q r) (.neg (.equal d zero_m))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Division.graph_sat_m]
  exact Division.divisor_ne_zero_m hℳ

theorem minimum_m (φ : OpenFormula signature_m (.num :: Δ)) :
    Derives T Γ (.imp (φ.existsFreeTop sort_m.num)
      ((Logic.Arithmetic.Minimum.candidate_m φ
        (lt_m (.fvar .here) (.fvar (.there .here)))).existsFreeTop sort_m.num)) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Formula.satisfies_existsFreeTop,
    Minimum.candidate_sat_m, lt_sat_m]
  exact PA.minimum_m hℳ φ η

theorem bound_m (φ : OpenFormula signature_m (.num :: .num :: Δ)) (n : Term signature_m [] Δ .num) :
    Derives T Γ ((Formula.imp (Logic.Arithmetic.FiniteRange.segment_m φ lt_m)
      (Logic.Arithmetic.FiniteRange.bound_m φ lt_m)).instantiateFreeTop n) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  rw [Formula.satisfies_instantiateFreeTop]
  simp only [Formula.satisfies, FiniteRange.segment_sat_m _ _ _ lt_m lt_l lt_sat_m,
    FiniteRange.bound_sat_m _ _ _ lt_m lt_l lt_sat_m]
  exact PA.bound_m hℳ φ η (n.eval η)

theorem common_multiple_m (n b : Term signature_m [] Δ .num) :
    Derives T Γ (Logic.Arithmetic.Divisibility.bounded_m n b) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  rw [Arithmetic.Divisibility.bounded_sat_m]
  exact Divisibility.bounded_m hℳ (n.eval η) (b.eval η)

end YesMetaZFC.Model.Arithmetic.PA.Provability
