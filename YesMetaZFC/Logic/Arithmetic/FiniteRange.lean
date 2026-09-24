import YesMetaZFC.Logic.Arithmetic.Order

/-! # 有限值域界的通用公式模板

φ 的首槽为输出，次槽为输入。插入界和截段长度时保留两槽及原参数。
模板自身不假定比较关系为序，也不假定 φ 是函数。
-/
namespace YesMetaZFC.Logic.Arithmetic.FiniteRange
open FirstOrder
set_option autoImplicit false
universe u v w
variable {σ : Signature.{u, v, w}} {s : σ.SortSymbol} {Δ : SortContext σ}

def insert_m (φ : OpenFormula σ (s :: s :: Δ)) : OpenFormula σ (s :: s :: s :: Δ) :=
  φ.renameFree (VariableRenaming.lift (VariableRenaming.lift (VariableRenaming.weaken s)))

def bound_m (φ : OpenFormula σ (s :: s :: Δ))
    (L : ∀ {Θ : SortContext σ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ) :
    OpenFormula σ (s :: Δ) :=
  let ψ : OpenFormula σ (s :: s :: s :: s :: Δ) :=
    .imp (L (.fvar (.there .here)) (.fvar (.there (.there (.there .here)))))
      (.imp (insert_m (insert_m φ)) (L (.fvar .here) (.fvar (.there (.there .here)))))
  ((ψ.forallFreeTop s).forallFreeTop s).existsFreeTop s

/-- 首个自由变量上存在唯一见证，其他参数不动。 -/
def function_m (φ : OpenFormula σ (s :: Δ)) : OpenFormula σ Δ :=
  (Formula.conj φ ((Formula.imp (φ.renameFree (VariableRenaming.lift (VariableRenaming.weaken s)))
    (.equal (.fvar .here) (.fvar (.there .here)))).forallFreeTop s)).existsFreeTop s

def segment_m (φ : OpenFormula σ (s :: s :: Δ))
    (L : ∀ {Θ : SortContext σ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ) :
    OpenFormula σ (s :: Δ) :=
  (Formula.imp (L (.fvar .here) (.fvar (.there .here))) (function_m (insert_m φ))).forallFreeTop s

end YesMetaZFC.Logic.Arithmetic.FiniteRange
