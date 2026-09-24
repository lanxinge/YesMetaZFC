import YesMetaZFC.Logic.Arithmetic.Syntax

/-! # 无减法形式的模逆公式 -/
namespace YesMetaZFC.Logic.Arithmetic.Modular
open FirstOrder
set_option autoImplicit false

/-- 存在内部 u、k，使 a*u=1+k*m；不要求调用者提供整环或宿主剩余类。 -/
def inverse_m {Γ Δ : SortContext signature_m} (a m : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num (.existsE .num
  (.equal (mul_m ((a.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)))
    (add_m (succ_m zero_m)
      (mul_m (.bvar .here) ((m.weakenBound sort_m.num).weakenBound sort_m.num)))))

end YesMetaZFC.Logic.Arithmetic.Modular
