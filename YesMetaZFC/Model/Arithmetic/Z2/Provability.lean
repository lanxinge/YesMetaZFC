import YesMetaZFC.Model.Arithmetic.Z2.Completeness
import YesMetaZFC.Model.Arithmetic.Z2.Minimum
import YesMetaZFC.Model.Arithmetic.Minimum
import YesMetaZFC.Model.Arithmetic.Z2.FiniteRange

/-! # Z₂ 混合参数最小化的对象推导

仅在显式导入本模块时使用双排序一阶完备性。集合域不要求为外部幂集。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2.Provability
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false

theorem minimum_m {T : Theory signature_m} (hZ₂ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (φ : OpenFormula signature_m (.num :: Δ)) :
    Derives T Γ (.imp (φ.existsFreeTop sort_m.num)
      ((Logic.Arithmetic.Minimum.candidate_m φ
        (lt_m (.fvar .here) (.fvar (.there .here)))).existsFreeTop sort_m.num)) := by
  apply Derives.theory_weaken hZ₂
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, Formula.satisfies_existsFreeTop,
    Arithmetic.Minimum.candidate_sat_m, lt_sat_m]
  exact Z2.minimum_m hℳ φ η

theorem bound_m {T : Theory signature_m} (hZ₂ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (φ : OpenFormula signature_m (.num :: .num :: Δ)) (n : Term signature_m [] Δ .num) :
    Derives T Γ ((Formula.imp (Logic.Arithmetic.FiniteRange.segment_m φ lt_m)
      (Logic.Arithmetic.FiniteRange.bound_m φ lt_m)).instantiateFreeTop n) := by
  apply Derives.theory_weaken hZ₂
  apply Completeness.derives_m
  intro ℳ hℳ η
  rw [Formula.satisfies_instantiateFreeTop]
  simp only [Formula.satisfies, Arithmetic.FiniteRange.segment_sat_m _ _ _ lt_m lt_l lt_sat_m,
    Arithmetic.FiniteRange.bound_sat_m _ _ _ lt_m lt_l lt_sat_m]
  exact Z2.bound_m hℳ φ η (n.eval η)

end YesMetaZFC.Model.Arithmetic.Z2.Provability
