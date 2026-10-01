import YesMetaZFC.SetTheory.Card.Cofinality.Syntax
import YesMetaZFC.SetTheory.Definitional.Project.Definitions
/-!
# 基数基础性质公式
本层定义不可数、极限、正则、奇异与强极限基数。这些都是普通基数论性质，不依赖
不可达等大基数概念。
-/
namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
namespace Formula
/-- `κ` 是严格大于给定 `ω` 的基数。 -/
def isUncountableCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω κ : Term depth) : Formula 1 depth :=
  .conj (isCardinal 𝒞 κ) (.mem ω κ)
/-- `κ` 是极限基数：每个较小序数上方仍有严格较小的基数。 -/
def isLimitCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (κ : Term depth) : Formula 1 depth :=
  .conj (isCardinal 𝒞 κ) <|
    Formula.forallMem κ <| Formula.existsMem κ.weaken <|
      .conj (isCardinal 𝒞 Term.newest) (.mem (.bound 1) Term.newest)
/-- `κ` 是正则基数，即 `cf(κ) = κ`。 -/
def isRegularCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (κ : Term depth) : Formula 1 depth :=
  isCofinality 𝒞 κ κ
derive_free_closed isRegularCardinal
/-- `κ` 是奇异基数，即其共尾度严格小于自身。 -/
def isSingularCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (κ : Term depth) : Formula 1 depth :=
  .conj (isCardinal 𝒞 κ) <|
    Formula.existsMem κ <|
      isCofinality 𝒞 Term.newest κ.weaken
/-- `κ` 是强极限基数：每个 `α < κ` 的幂集基数仍严格小于 `κ`。 -/
def isStrongLimitCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (κ : Term depth) : Formula 1 depth :=
  .conj (isCardinal 𝒞 κ) <|
    Formula.forallMem κ <| .forallE <|
      .imp (isPowerSet Term.newest (.bound 1)) (cardinalLess 𝒞 Term.newest κ.weaken.weaken)
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
