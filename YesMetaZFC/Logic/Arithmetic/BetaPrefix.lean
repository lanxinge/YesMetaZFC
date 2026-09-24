import YesMetaZFC.Logic.Arithmetic.FiniteRange

/-! # β 前缀不变量的通用绑定模板

φ 的槽位为输出、输入、原参数；L/E 为严格／非严格比较，D/V 分别表达
模数整除与模逆，R 表达带指定余数的商等式。本层只装配公式，不假定这些合同成立。
-/
namespace YesMetaZFC.Logic.Arithmetic.Beta
open FirstOrder
set_option autoImplicit false
universe u v w
variable {σ : Signature.{u, v, w}} {s : σ.SortSymbol} {Δ : SortContext σ}

def prefix_m (φ : OpenFormula σ (s :: s :: Δ))
    (L E : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (D V : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (R : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ) :
    OpenFormula σ (s :: s :: s :: Δ) :=
  -- 以下两层正文槽位为 i,M,b,j,n,c,原参数。
  let A : OpenFormula σ (s :: s :: s :: s :: s :: s :: Δ) :=
    .imp (L (.fvar .here) (.fvar (.there (.there (.there .here)))))
      (D (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.fvar (.there .here)))
  let B : OpenFormula σ (s :: s :: s :: s :: s :: s :: Δ) :=
    .imp (L (.fvar .here) (.fvar (.there (.there (.there (.there .here))))))
      (.imp (E (.fvar (.there (.there (.there .here)))) (.fvar .here))
        (V (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.fvar (.there .here))))
  -- 读取正文槽位为 a,i,M,b,j,n,c,原参数；五次插入保持 a、i 及原参数。
  let C : OpenFormula σ (s :: s :: s :: s :: s :: s :: s :: Δ) :=
    .imp (L (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here))))))
      (.imp (FiniteRange.insert_m (FiniteRange.insert_m (FiniteRange.insert_m
        (FiniteRange.insert_m (FiniteRange.insert_m φ)))))
        (R (.fvar (.there (.there (.there .here))))
          (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
          (.fvar (.there .here)) (.fvar .here)))
  ((Formula.conj (A.forallFreeTop s)
    (.conj (B.forallFreeTop s) ((C.forallFreeTop s).forallFreeTop s))).existsFreeTop s).existsFreeTop s

end YesMetaZFC.Logic.Arithmetic.Beta
