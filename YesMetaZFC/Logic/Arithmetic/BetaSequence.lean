import YesMetaZFC.Logic.Arithmetic.Beta
import YesMetaZFC.Logic.Arithmetic.BetaPrefix
import YesMetaZFC.Logic.Arithmetic.Divisibility
import YesMetaZFC.Logic.Arithmetic.Modular

/-! # 算术可定义图的 β 编码归纳正文 -/
namespace YesMetaZFC.Logic.Arithmetic.Beta
open FirstOrder
set_option autoImplicit false

def remainder_m {Γ Δ : SortContext signature_m} (b c i a : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (.equal (add_m (mul_m (.bvar .here) ((modulus_m c i).weakenBound sort_m.num))
    (a.weakenBound sort_m.num)) (b.weakenBound sort_m.num))

/-- 自由槽位为 j,n,c,原参数；截段外无需构造前缀。 -/
def invariant_m {Δ : SortContext signature_m} (φ : OpenFormula signature_m (.num :: .num :: Δ)) :
    OpenFormula signature_m (.num :: .num :: .num :: Δ) :=
  .imp (le_m (.fvar .here) (.fvar (.there .here)))
    (prefix_m φ lt_m le_m (fun c i M => Divisibility.dvd_m (modulus_m c i) M)
      (fun c i M => Modular.inverse_m M (modulus_m c i)) remainder_m)

end YesMetaZFC.Logic.Arithmetic.Beta
