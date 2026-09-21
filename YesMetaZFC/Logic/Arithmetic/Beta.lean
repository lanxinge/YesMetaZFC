import YesMetaZFC.Logic.Arithmetic.Division

/-! # β 编码的模数项与规范读取图

此处只定义读取关系；有限函数的编码存在性是另外的证明义务。
-/
namespace YesMetaZFC.Logic.Arithmetic.Beta
open FirstOrder
set_option autoImplicit false

def modulus_m {Γ Δ : SortContext signature_m} (c i : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := succ_m (mul_m (succ_m i) c)

def graph_m {Γ Δ : SortContext signature_m} (b c i a : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (Division.graph_m (b.weakenBound sort_m.num) ((modulus_m c i).weakenBound sort_m.num)
    (.bvar .here) (a.weakenBound sort_m.num))

def domain_m {Γ Δ : SortContext signature_m} (b c i : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num
  (graph_m (b.weakenBound sort_m.num) (c.weakenBound sort_m.num)
    (i.weakenBound sort_m.num) (.bvar .here))

end YesMetaZFC.Logic.Arithmetic.Beta
