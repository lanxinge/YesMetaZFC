import YesMetaZFC.Logic.Arithmetic.Order

/-! # 带参数最小元的通用公式模板

R 的首槽为被比较的变量，次槽为候选；其余参数与 φ 一致。
模板不预设 R 为序关系，不增加最小化公理。
-/
namespace YesMetaZFC.Logic.Arithmetic.Minimum
open FirstOrder
set_option autoImplicit false
universe u v w

def candidate_m {σ : Signature.{u, v, w}} {s : σ.SortSymbol} {Δ : SortContext σ}
    (φ : OpenFormula σ (s :: Δ)) (R : OpenFormula σ (s :: s :: Δ)) :
    OpenFormula σ (s :: Δ) :=
  .conj φ ((Formula.imp R (.neg (φ.renameFree
    (VariableRenaming.lift (VariableRenaming.weaken s))))).forallFreeTop s)

end YesMetaZFC.Logic.Arithmetic.Minimum
