import YesMetaZFC.Logic.Arithmetic.Z2.Syntax

/-! # 双排序语言中的数序公式

参数上下文可混合数与数集；差值见证仍为数排序，不编码成宿主数码。
-/
namespace YesMetaZFC.Logic.Arithmetic.Z2
open FirstOrder
set_option autoImplicit false

def le_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  (Formula.equal (add_m (s.weakenFree sort_m.num) (.fvar .here))
    (t.weakenFree sort_m.num)).existsFreeTop sort_m.num

def lt_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := le_m (succ_m s) t

end YesMetaZFC.Logic.Arithmetic.Z2
