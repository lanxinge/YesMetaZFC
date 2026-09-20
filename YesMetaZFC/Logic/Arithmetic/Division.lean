import YesMetaZFC.Logic.Arithmetic.Order

/-! # 带余除法的实际图公式 -/
namespace YesMetaZFC.Logic.Arithmetic.Division
open FirstOrder
set_option autoImplicit false

/-- 参数依次为被除数、除数、商和余数；数序仍是原语言内的缩写。 -/
def graph_m {Γ Δ : SortContext signature_m} (n d q r : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .conj (.equal (add_m (mul_m q d) r) n) (lt_m r d)

end YesMetaZFC.Logic.Arithmetic.Division
