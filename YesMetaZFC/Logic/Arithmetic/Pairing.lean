import YesMetaZFC.Logic.Arithmetic.Order

/-! # 平方分层配对的图公式

约定与原配对编码一致：m<n 时为 n*n+m，否则为 m*m+m+n。
两个互斥分支都在原语言中定义，不增加配对函数符号。
-/
namespace YesMetaZFC.Logic.Arithmetic.Pairing
open FirstOrder
set_option autoImplicit false

def graph_m {Γ Δ : SortContext signature_m} (m n p : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .disj (.conj (lt_m m n) (.equal (add_m (mul_m n n) m) p))
    (.conj (.neg (lt_m m n)) (.equal (add_m (add_m (mul_m m m) m) n) p))

def domain_m {Γ Δ : SortContext signature_m} (m n : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (graph_m (m.weakenBound sort_m.num) (n.weakenBound sort_m.num) (.bvar .here))

def range_m {Γ Δ : SortContext signature_m} (p : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num (.existsE .num
  (graph_m (.bvar (.there .here)) (.bvar .here) ((p.weakenBound sort_m.num).weakenBound sort_m.num)))

def left_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (graph_m (t.weakenBound sort_m.num) (.bvar .here) (s.weakenBound sort_m.num))

def right_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (graph_m (.bvar .here) (t.weakenBound sort_m.num) (s.weakenBound sort_m.num))

end YesMetaZFC.Logic.Arithmetic.Pairing
