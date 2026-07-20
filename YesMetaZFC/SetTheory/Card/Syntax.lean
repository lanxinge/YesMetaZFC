import YesMetaZFC.SetTheory.FunctionSemantics

/-!
# 基数论基础公式

本文件定义集合编码单射、双射、等势、基数比较，以及初始序数意义下的基数。所有定义
仍然只生成纯隶属公式，并显式携带有序对编码约定。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
namespace Formula

/-- `function` 是从 `source` 到 `target` 的单射。 -/
def isInjectionFromTo (𝒞 : OrderedPairConvention)
    {depth : Nat} (function source target : Term depth) :
    Formula 1 depth :=
  .conj (isFunctionFromTo 𝒞 function source target)
    (isInjective 𝒞 function)

/-- `function` 是从 `source` 到 `target` 的双射。 -/
def isBijectionFromTo (𝒞 : OrderedPairConvention)
    {depth : Nat} (function source target : Term depth) :
    Formula 1 depth :=
  .conj (isInjectionFromTo 𝒞 function source target)
    (isSurjectiveOnto 𝒞 function source target)

/-- `left` 与 `right` 等势。 -/
def equinumerous (𝒞 : OrderedPairConvention)
    {depth : Nat} (left right : Term depth) : Formula 1 depth :=
  .existsE <|
    isBijectionFromTo 𝒞 Term.newest left.weaken right.weaken

/-- `left` 的基数不大于 `right` 的基数。 -/
def cardinalLessOrEqual (𝒞 : OrderedPairConvention)
    {depth : Nat} (left right : Term depth) : Formula 1 depth :=
  .existsE <|
    isInjectionFromTo 𝒞 Term.newest left.weaken right.weaken

/-- `left` 的基数严格小于 `right` 的基数。 -/
def cardinalLess (𝒞 : OrderedPairConvention)
    {depth : Nat} (left right : Term depth) : Formula 1 depth :=
  .conj (cardinalLessOrEqual 𝒞 left right) <|
    .neg (equinumerous 𝒞 left right)

/-- `κ` 是初始序数，即不与任何更小序数等势。 -/
def isCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (κ : Term depth) : Formula 1 depth :=
  .conj (isOrdinal κ) <|
    Formula.forallMem κ <|
      .neg (equinumerous 𝒞 Term.newest κ.weaken)

/-- `κ` 是集合 `set` 的基数。 -/
def isCardinalOf (𝒞 : OrderedPairConvention)
    {depth : Nat} (κ set : Term depth) : Formula 1 depth :=
  .conj (isCardinal 𝒞 κ)
    (equinumerous 𝒞 κ set)

end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
