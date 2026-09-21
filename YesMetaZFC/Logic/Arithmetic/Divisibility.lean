import YesMetaZFC.Logic.Arithmetic.Order

/-! # 内部整除与截段共同倍数的公式 -/
namespace YesMetaZFC.Logic.Arithmetic.Divisibility
open FirstOrder
set_option autoImplicit false

def dvd_m {Γ Δ : SortContext signature_m} (d n : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (.equal (mul_m (d.weakenBound sort_m.num) (.bvar .here)) (n.weakenBound sort_m.num))

/-- c 为正，且被区间 0<d≤n 中的每个内部数整除。 -/
def common_m {Γ Δ : SortContext signature_m} (n c : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .conj (lt_m zero_m c)
  (.forallE .num (.imp (lt_m zero_m (.bvar .here))
    (.imp (le_m (.bvar .here) (n.weakenBound sort_m.num))
      (dvd_m (.bvar .here) (c.weakenBound sort_m.num)))))

/-- 共同倍数还可超过任意给定的内部下界。 -/
def bounded_m {Γ Δ : SortContext signature_m} (n b : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (.conj (lt_m (b.weakenBound sort_m.num) (.bvar .here))
    (common_m (n.weakenBound sort_m.num) (.bvar .here)))

end YesMetaZFC.Logic.Arithmetic.Divisibility
