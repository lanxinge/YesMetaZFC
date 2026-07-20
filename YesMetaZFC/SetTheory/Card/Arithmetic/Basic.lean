import YesMetaZFC.SetTheory.Card.Arithmetic.Syntax
import YesMetaZFC.SetTheory.Card.Basic

/-!
# 基数算术的基础语义

本层把基数和、积、幂公式解释为普通 Lean 关系。运算结果仍由显式 `IsCardinalOf`
见证给出，后续代数层证明代表元选择无关和文献中的结构性等式。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `sum` 是 `left + right`。 -/
def IsCardinalAddition {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sum left right : ℳ.Domain) : Prop :=
  ∃ leftSet rightSet union,
    ℳ.IsCardinalOf 𝕀 left leftSet ∧
      ℳ.IsCardinalOf 𝕀 right rightSet ∧
        ℳ.IsDisjoint leftSet rightSet ∧
          ℳ.IsUnionOfTwo union leftSet rightSet ∧
            ℳ.IsCardinalOf 𝕀 sum union

/-- `product` 是 `left · right`。 -/
def IsCardinalMultiplication {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (product left right : ℳ.Domain) : Prop :=
  ∃ leftSet rightSet cartesian,
    ℳ.IsCardinalOf 𝕀 left leftSet ∧
      ℳ.IsCardinalOf 𝕀 right rightSet ∧
        ℳ.IsCartesianProduct 𝕀 cartesian leftSet rightSet ∧
          ℳ.IsCardinalOf 𝕀 product cartesian

/-- `power` 是 `base ^ exponent`。 -/
def IsCardinalExponentiation {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (power base exponent : ℳ.Domain) : Prop :=
  ∃ baseSet exponentSet space,
    ℳ.IsCardinalOf 𝕀 base baseSet ∧
      ℳ.IsCardinalOf 𝕀 exponent exponentSet ∧
        ℳ.IsFunctionSpace 𝕀 space exponentSet baseSet ∧
          ℳ.IsCardinalOf 𝕀 power space

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- 基数加法公式与纸面代表元定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCardinalAddition_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sum left right : Term depth) :
    satisfies env (isCardinalAddition 𝒞 sum left right) ↔
      ℳ.IsCardinalAddition 𝕀
        (sum.eval env) (left.eval env) (right.eval env) := by
  simp only [isCardinalAddition, Structure.IsCardinalAddition,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isCardinalOf_iff 𝕀 hExt,
    satisfies_isDisjoint_iff, satisfies_isUnionOfTwo_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_weaken]

/-- 基数乘法公式与纸面笛卡尔积定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCardinalMultiplication_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (product left right : Term depth) :
    satisfies env
        (isCardinalMultiplication 𝒞 product left right) ↔
      ℳ.IsCardinalMultiplication 𝕀
        (product.eval env) (left.eval env) (right.eval env) := by
  simp only [isCardinalMultiplication,
    Structure.IsCardinalMultiplication,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isCardinalOf_iff 𝕀 hExt,
    satisfies_isCartesianProduct_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_weaken]

/-- 基数指数公式与纸面函数集定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCardinalExponentiation_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (power base exponent : Term depth) :
    satisfies env
        (isCardinalExponentiation 𝒞 power base exponent) ↔
      ℳ.IsCardinalExponentiation 𝕀
        (power.eval env) (base.eval env) (exponent.eval env) := by
  simp only [isCardinalExponentiation,
    Structure.IsCardinalExponentiation,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isCardinalOf_iff 𝕀 hExt,
    satisfies_isFunctionSpace_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_weaken]

end Formula
end Project
end Definitional

end SetTheory
end YesMetaZFC
