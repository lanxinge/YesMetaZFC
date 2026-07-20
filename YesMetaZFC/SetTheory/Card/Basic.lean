import YesMetaZFC.SetTheory.Card.Syntax
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.FunctionSemantics
import YesMetaZFC.SetTheory.Ord.Basic

/-!
# 基数论的基础语义

本文件把基数论基础公式整理为普通 Lean 谓词。集合之间的大小关系始终由模型内部的
集合编码函数见证，不使用宿主层函数代替对象语言函数。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `left` 与 `right` 等势。 -/
def Equinumerous {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left right : ℳ.Domain) : Prop :=
  ∃ function,
    ℳ.IsSetBijectionFromTo 𝕀 function left right

/-- `left` 的基数不大于 `right` 的基数。 -/
def CardinalLessOrEqual {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left right : ℳ.Domain) : Prop :=
  ∃ function,
    ℳ.IsSetInjectionFromTo 𝕀 function left right

/-- `left` 的基数严格小于 `right` 的基数。 -/
def CardinalLess {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left right : ℳ.Domain) : Prop :=
  ℳ.CardinalLessOrEqual 𝕀 left right ∧
    ¬ ℳ.Equinumerous 𝕀 left right

/-- `κ` 是初始序数，即不与任何更小序数等势。 -/
def IsCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (κ : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal κ ∧
    ∀ α, ℳ.mem α κ →
      ¬ ℳ.Equinumerous 𝕀 α κ

/-- `κ` 是集合 `set` 的基数。 -/
def IsCardinalOf {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (κ set : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 κ ∧
    ℳ.Equinumerous 𝕀 κ set

namespace Equinumerous

/-- 任意集合与自身等势。 -/
theorem refl {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ) (set : ℳ.Domain) :
    ℳ.Equinumerous 𝕀 set set :=
  ZF.exists_identityBijection hZF 𝕀 set

/-- 等势关系具有对称性。 -/
theorem symm {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left right : ℳ.Domain}
    (hEquinumerous : ℳ.Equinumerous 𝕀 left right) :
    ℳ.Equinumerous 𝕀 right left := by
  rcases hEquinumerous with ⟨function, hFunction⟩
  exact ZF.exists_inverseBijection hZF 𝕀 hFunction

/-- 等势关系具有传递性。 -/
theorem trans {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left middle right : ℳ.Domain}
    (hLeft : ℳ.Equinumerous 𝕀 left middle)
    (hRight : ℳ.Equinumerous 𝕀 middle right) :
    ℳ.Equinumerous 𝕀 left right := by
  rcases hLeft with ⟨first, hFirst⟩
  rcases hRight with ⟨second, hSecond⟩
  exact ZF.exists_compositionBijection hZF 𝕀 hFirst hSecond

end Equinumerous

namespace IsCardinal

/-- 两个等势的初始序数相等。 -/
theorem eq_of_equinumerous {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {κ μ : ℳ.Domain}
    (hκ : ℳ.IsCardinal 𝕀 κ)
    (hμ : ℳ.IsCardinal 𝕀 μ)
    (hEquinumerous : ℳ.Equinumerous 𝕀 κ μ) :
    κ = μ := by
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hκ.1 hμ.1 (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF) κ μ) with
    hSame | hκμ | hμκ
  · exact hZF.1.eq_of_same_members κ μ hSame
  · exact False.elim <| hμ.2 κ hκμ hEquinumerous
  · exact False.elim <| hκ.2 μ hμκ <|
      hEquinumerous.symm hZF 𝕀

end IsCardinal

namespace IsCardinalOf

/-- 同一集合的两个基数见证相等。 -/
theorem eq {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {κ μ set : ℳ.Domain}
    (hκ : ℳ.IsCardinalOf 𝕀 κ set)
    (hμ : ℳ.IsCardinalOf 𝕀 μ set) :
    κ = μ := by
  apply hκ.1.eq_of_equinumerous hZF 𝕀 hμ.1
  exact hκ.2.trans hZF 𝕀 <| hμ.2.symm hZF 𝕀

/-- 等势集合具有相同的基数。 -/
theorem of_equinumerous {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {κ left right : ℳ.Domain}
    (hκ : ℳ.IsCardinalOf 𝕀 κ left)
    (hEquinumerous : ℳ.Equinumerous 𝕀 left right) :
    ℳ.IsCardinalOf 𝕀 κ right :=
  ⟨hκ.1, hκ.2.trans hZF 𝕀 hEquinumerous⟩

end IsCardinalOf

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- 单射公式与纸面单射语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isInjective_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function : Term depth) :
    satisfies env (isInjective 𝒞 function) ↔
      ℳ.IsSetInjective 𝕀 (function.eval env) := by
  simp only [isInjective, Structure.IsSetInjective,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_conj_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_weaken]
  constructor
  · intro h first second output hFirst hSecond
    exact h first second output ⟨hFirst, hSecond⟩
  · intro h first second output hPairs
    exact h first second output hPairs.1 hPairs.2

/-- 从源到目标的单射公式与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isInjectionFromTo_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function source target : Term depth) :
    satisfies env
        (isInjectionFromTo 𝒞 function source target) ↔
      ℳ.IsSetInjectionFromTo 𝕀
        (function.eval env) (source.eval env) (target.eval env) := by
  simp only [isInjectionFromTo, Structure.IsSetInjectionFromTo,
    satisfies_conj_iff,
    satisfies_isFunctionFromTo_iff 𝕀 hExt,
    satisfies_isInjective_iff 𝕀 hExt]

/-- 从源到目标的双射公式与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isBijectionFromTo_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function source target : Term depth) :
    satisfies env
        (isBijectionFromTo 𝒞 function source target) ↔
      ℳ.IsSetBijectionFromTo 𝕀
        (function.eval env) (source.eval env) (target.eval env) := by
  simp only [isBijectionFromTo, Structure.IsSetBijectionFromTo,
    satisfies_conj_iff,
    satisfies_isInjectionFromTo_iff 𝕀 hExt,
    satisfies_isSurjectiveOnto_iff 𝕀]

/-- 等势公式与纸面等势语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_equinumerous_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (left right : Term depth) :
    satisfies env (equinumerous 𝒞 left right) ↔
      ℳ.Equinumerous 𝕀 (left.eval env) (right.eval env) := by
  simp only [equinumerous, Structure.Equinumerous,
    satisfies_exists_iff, satisfies_isBijectionFromTo_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 基数小于等于公式与纸面单射定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_cardinalLessOrEqual_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (left right : Term depth) :
    satisfies env (cardinalLessOrEqual 𝒞 left right) ↔
      ℳ.CardinalLessOrEqual 𝕀
        (left.eval env) (right.eval env) := by
  simp only [cardinalLessOrEqual, Structure.CardinalLessOrEqual,
    satisfies_exists_iff, satisfies_isInjectionFromTo_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 基数严格小于公式与纸面定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_cardinalLess_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (left right : Term depth) :
    satisfies env (cardinalLess 𝒞 left right) ↔
      ℳ.CardinalLess 𝕀 (left.eval env) (right.eval env) := by
  simp only [cardinalLess, Structure.CardinalLess,
    satisfies_conj_iff, satisfies_neg_iff,
    satisfies_cardinalLessOrEqual_iff 𝕀 hExt,
    satisfies_equinumerous_iff 𝕀 hExt]

/-- 基数公式与初始序数的纸面定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (κ : Term depth) :
    satisfies env (isCardinal 𝒞 κ) ↔
      ℳ.IsCardinal 𝕀 (κ.eval env) := by
  simp only [isCardinal, Structure.IsCardinal,
    satisfies_conj_iff, satisfies_forallMem_iff, satisfies_neg_iff,
    satisfies_isOrdinal_iff, satisfies_equinumerous_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- “`κ` 是 `set` 的基数”公式与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCardinalOf_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (κ set : Term depth) :
    satisfies env (isCardinalOf 𝒞 κ set) ↔
      ℳ.IsCardinalOf 𝕀 (κ.eval env) (set.eval env) := by
  simp only [isCardinalOf, Structure.IsCardinalOf,
    satisfies_conj_iff,
    satisfies_isCardinal_iff 𝕀 hExt,
    satisfies_equinumerous_iff 𝕀 hExt]

end Formula
end Project
end Definitional

end SetTheory
end YesMetaZFC
