import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-! # Robinson 公理的共享模板

模板只需要一个数排序及四种项构造；不要求语言仅有数排序。
Q 与 Z₂ 从这里实例化同一组公理。此接口只构造公式，不断言任意
传入的项构造都满足替换自然性或算术公理。
-/
namespace YesMetaZFC.Logic.Arithmetic.Robinson
open FirstOrder
set_option autoImplicit false
universe u v w

inductive base_m where
  | nonzero | injective | predecessor | add_zero | add_succ | mul_zero | mul_succ
  deriving DecidableEq

def parameters_m {σ : Signature.{u, v, w}} (n : σ.SortSymbol) : base_m → SortContext σ
  | .nonzero | .predecessor | .add_zero | .mul_zero => [n]
  | .injective | .add_succ | .mul_succ => [n, n]

/-- 参数槽依次为 x、y；数域运算均显式提供。 -/
def template_m {σ : Signature.{u, v, w}} (n : σ.SortSymbol)
    (z : ∀ {Γ Δ}, Term σ Γ Δ n)
    (s : ∀ {Γ Δ}, Term σ Γ Δ n → Term σ Γ Δ n)
    (a m : ∀ {Γ Δ}, Term σ Γ Δ n → Term σ Γ Δ n → Term σ Γ Δ n)
    (k : base_m) : Formula σ [] (parameters_m n k) :=
  match k with
  | .nonzero => .neg (.equal (s (.fvar .here)) z)
  | .injective => .imp (.equal (s (.fvar .here)) (s (.fvar (.there .here))))
      (.equal (.fvar .here) (.fvar (.there .here)))
  | .predecessor => .disj (.equal (.fvar .here) z)
      (.existsE n (.equal (.fvar .here) (s (.bvar .here))))
  | .add_zero => .equal (a (.fvar .here) z) (.fvar .here)
  | .add_succ => .equal (a (.fvar .here) (s (.fvar (.there .here))))
      (s (a (.fvar .here) (.fvar (.there .here))))
  | .mul_zero => .equal (m (.fvar .here) z) z
  | .mul_succ => .equal (m (.fvar .here) (s (.fvar (.there .here))))
      (a (m (.fvar .here) (.fvar (.there .here))) (.fvar .here))

end YesMetaZFC.Logic.Arithmetic.Robinson
