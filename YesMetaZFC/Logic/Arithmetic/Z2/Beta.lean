import YesMetaZFC.Logic.Arithmetic.BetaPrefix
import YesMetaZFC.Logic.Arithmetic.Z2.Order

/-! # 混合参数上下文中的 β 模板

只有数目运算的装配因签名而异；前缀的参数插入和量词骨架复用通用模板。
-/
namespace YesMetaZFC.Logic.Arithmetic.Z2.Beta
open FirstOrder
set_option autoImplicit false
variable {Γ Δ : SortContext signature_m}

def modulus_m (c i : Term signature_m Γ Δ .num) : Term signature_m Γ Δ .num :=
  succ_m (mul_m (succ_m i) c)

def divisor_m (c i M : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.equal (mul_m ((modulus_m c i).weakenBound sort_m.num) (.bvar .here))
    (M.weakenBound sort_m.num))

def inverse_m (c i M : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num
    (.equal (mul_m ((M.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)))
      (add_m (succ_m zero_m) (mul_m (.bvar .here)
        (((modulus_m c i).weakenBound sort_m.num).weakenBound sort_m.num)))))

def remainder_m (b c i a : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.equal (add_m (mul_m (.bvar .here) ((modulus_m c i).weakenBound sort_m.num))
    (a.weakenBound sort_m.num)) (b.weakenBound sort_m.num))

def graph_m (b c i a : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (.equal (add_m (mul_m (.bvar .here) ((modulus_m c i).weakenBound sort_m.num))
      (a.weakenBound sort_m.num)) (b.weakenBound sort_m.num))
    (lt_m (a.weakenBound sort_m.num) ((modulus_m c i).weakenBound sort_m.num)))

def invariant_m (φ : OpenFormula signature_m (.num :: .num :: Δ)) :
    OpenFormula signature_m (.num :: .num :: .num :: Δ) :=
  .imp (le_m (.fvar .here) (.fvar (.there .here)))
    (Arithmetic.Beta.prefix_m φ lt_m le_m divisor_m inverse_m remainder_m)

end YesMetaZFC.Logic.Arithmetic.Z2.Beta
