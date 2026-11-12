import YesMetaZFC.SetTheory.Card.Properties.Syntax
/-!
# 不可达基数定义公式
本层只建立弱不可达与强不可达基数的对象语言定义。它们消费基数层中的不可数、
正则、极限与强极限性质，不重复定义普通基数论概念。
-/
namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
namespace Formula
/-- `κ` 是弱不可达基数：不可数、正则且是极限基数。 -/
def isWeaklyInaccessibleCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω κ : Term depth) : Formula 1 depth :=
  .conj (isUncountableCardinal 𝒞 ω κ) <|
    .conj (isRegularCardinal 𝒞 κ) (isLimitCardinal 𝒞 κ)
/-- `κ` 是强不可达基数：不可数、正则且是强极限基数。 -/
def isStronglyInaccessibleCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω κ : Term depth) : Formula 1 depth :=
  .conj (isUncountableCardinal 𝒞 ω κ) <|
    .conj (isRegularCardinal 𝒞 κ) (isStrongLimitCardinal 𝒞 κ)
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
