import YesMetaZFC.Logic.Arithmetic.Order

/-! # 带余除法的实际图公式 -/
namespace YesMetaZFC.Logic.Arithmetic.Division
open FirstOrder
set_option autoImplicit false

/-- 参数依次为被除数、除数、商和余数；数序仍是原语言内的缩写。 -/
def graph_m {Γ Δ : SortContext signature_m} (n d q r : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .conj (.equal (add_m (mul_m q d) r) n) (lt_m r d)

/-- 存在内部商和余数；原项在两个新绑定槽下弱化。 -/
def domain_m {Γ Δ : SortContext signature_m} (n d : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num (.existsE .num
  (graph_m ((n.weakenBound sort_m.num).weakenBound sort_m.num)
    ((d.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here)))

end YesMetaZFC.Logic.Arithmetic.Division
