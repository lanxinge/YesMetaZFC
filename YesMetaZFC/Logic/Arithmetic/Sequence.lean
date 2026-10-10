import YesMetaZFC.Logic.Arithmetic.FiniteRange

/-! # 有限图编码的通用公式

φ 首槽为输出、次槽为输入；G 的四个参数为 b,c,i,a。模板要求截段内精确等价，
不只要求已知值蕴含一次读取。
-/
namespace YesMetaZFC.Logic.Arithmetic.Sequence
open FirstOrder
set_option autoImplicit false
universe u v w

def code_m {σ : Signature.{u, v, w}} {s : σ.SortSymbol} {Δ : SortContext σ}
    (φ : OpenFormula σ (s :: s :: Δ))
    (L : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (G : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ) :
    OpenFormula σ (s :: Δ) :=
  -- 槽位 a,i,c,b,n,原参数；存在量词最终依次选择 b、c。
  let ψ : OpenFormula σ (s :: s :: s :: s :: s :: Δ) :=
    .imp (L (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here))))))
      (.iff (G (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
        (.fvar (.there .here)) (.fvar .here))
        (FiniteRange.insert_m (FiniteRange.insert_m (FiniteRange.insert_m φ))))
  (((ψ.forallFreeTop s).forallFreeTop s).existsFreeTop s).existsFreeTop s

end YesMetaZFC.Logic.Arithmetic.Sequence
