import YesMetaZFC.SetTheory.Card.Syntax
import YesMetaZFC.SetTheory.SetConstruction

/-!
# 基数算术公式

基数加法、乘法和指数继续采用关系式接口。每个定义显式量化集合代表元与相应集合构造，
不在基数存在性证明完成前引入宿主层总函数。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
namespace Formula

/-- `sum` 是 `left + right`：某两个不交代表元之并的基数。 -/
def isCardinalAddition (𝒞 : OrderedPairConvention)
    {depth : Nat} (sum left right : Term depth) : Formula 1 depth :=
  .existsE <| .existsE <| .existsE <|
    .conj
      (isCardinalOf 𝒞 left.weaken.weaken.weaken (.bound 2)) <|
    .conj
      (isCardinalOf 𝒞 right.weaken.weaken.weaken (.bound 1)) <|
    .conj (isDisjoint (.bound 2) (.bound 1)) <|
    .conj (isUnionOfTwo (.bound 0) (.bound 2) (.bound 1))
      (isCardinalOf 𝒞 sum.weaken.weaken.weaken (.bound 0))

/-- `product` 是 `left · right`：两个代表元笛卡尔积的基数。 -/
def isCardinalMultiplication (𝒞 : OrderedPairConvention)
    {depth : Nat} (product left right : Term depth) : Formula 1 depth :=
  .existsE <| .existsE <| .existsE <|
    .conj
      (isCardinalOf 𝒞 left.weaken.weaken.weaken (.bound 2)) <|
    .conj
      (isCardinalOf 𝒞 right.weaken.weaken.weaken (.bound 1)) <|
    .conj
      (isCartesianProduct 𝒞 (.bound 0) (.bound 2) (.bound 1))
      (isCardinalOf 𝒞 product.weaken.weaken.weaken (.bound 0))

/-- `power` 是 `base ^ exponent`：从指数代表元到基数代表元的函数集基数。 -/
def isCardinalExponentiation (𝒞 : OrderedPairConvention)
    {depth : Nat} (power base exponent : Term depth) : Formula 1 depth :=
  .existsE <| .existsE <| .existsE <|
    .conj
      (isCardinalOf 𝒞 base.weaken.weaken.weaken (.bound 2)) <|
    .conj
      (isCardinalOf 𝒞 exponent.weaken.weaken.weaken (.bound 1)) <|
    .conj
      (isFunctionSpace 𝒞 (.bound 0) (.bound 1) (.bound 2))
      (isCardinalOf 𝒞 power.weaken.weaken.weaken (.bound 0))

end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
