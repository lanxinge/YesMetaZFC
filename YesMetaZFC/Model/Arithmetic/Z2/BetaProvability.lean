import YesMetaZFC.Model.Arithmetic.Z2.Completeness
import YesMetaZFC.Model.Arithmetic.Z2.Beta
import YesMetaZFC.Model.Arithmetic.Sequence

/-! # Z₂ 混合参数有限函数的 β 编码推导

允许任意混合公式、内部长度项和局部假设；完备性只应用于所有原一阶模型。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2.Beta.Provability
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
variable {T : Theory signature_m} (hZ₂ : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hZ₂

theorem sequence_m (φ : OpenFormula signature_m (.num :: .num :: Δ)) (n : Term signature_m [] Δ .num) :
    Derives T Γ ((Formula.imp (Logic.Arithmetic.FiniteRange.segment_m φ lt_m)
      (Logic.Arithmetic.Sequence.code_m φ lt_m Logic.Arithmetic.Z2.Beta.graph_m)).instantiateFreeTop n) := by
  apply Derives.theory_weaken hZ₂
  apply Completeness.derives_m
  intro ℳ hℳ η
  rw [Formula.satisfies_instantiateFreeTop]
  simp only [Formula.satisfies, Arithmetic.FiniteRange.segment_sat_m _ _ _ lt_m lt_l lt_sat_m,
    Arithmetic.Sequence.code_sat_m _ _ _ lt_m Logic.Arithmetic.Z2.Beta.graph_m
      lt_l (Arithmetic.PA.Beta.graph_l (ℳ := reduct_m ℳ)) lt_sat_m graph_sat_m]
  exact Beta.sequence_m hℳ φ η (n.eval η)

end YesMetaZFC.Model.Arithmetic.Z2.Beta.Provability
