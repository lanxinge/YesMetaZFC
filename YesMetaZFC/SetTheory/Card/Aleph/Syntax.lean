import YesMetaZFC.SetTheory.Card.Syntax
import YesMetaZFC.SetTheory.Ord.Arithmetic.Syntax
/-!
# Aleph 数公式
本层定义无限基数、可数性、基数后继及 Aleph 超限递归的对象语言公式。Aleph 关系仍
保持关系式接口；存在唯一性留给后续定理层证明。
-/
namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
namespace Formula
/-- `κ` 是相对于 `ω` 的无限基数。 -/
def isInfiniteCardinal (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω κ : Term depth) : Formula 1 depth :=
  .conj (isCardinal 𝒞 κ) (cardinalLessOrEqual 𝒞 ω κ)
derive_free_closed isInfiniteCardinal
/-- `set` 与 `ω` 等势，即 `set` 是可数无限集。 -/
def isCountablyInfinite (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω set : Term depth) : Formula 1 depth :=
  equinumerous 𝒞 set ω
/-- `set` 的基数不超过 `ω`。 -/
def isAtMostCountable (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω set : Term depth) : Formula 1 depth :=
  cardinalLessOrEqual 𝒞 set ω
/--
`successor` 是严格大于 `predecessor` 的最小基数。
最小性使用初始序数的隶属次序表达。
-/
def isCardinalSuccessor (𝒞 : OrderedPairConvention)
    {depth : Nat} (successor predecessor : Term depth) :
    Formula 1 depth :=
  .conj (isCardinal 𝒞 successor) <| .conj (.mem predecessor successor) <|
    .forallE <| .imp (.conj (isCardinal 𝒞 Term.newest) (.mem predecessor.weaken Term.newest)) <|
      .disj (extensionalEq successor.weaken Term.newest) (.mem successor.weaken Term.newest)
derive_free_closed isCardinalSuccessor
end Formula
namespace BinarySchema
/--
Aleph 递归算子。
参数布局为：index `1` 是此前序列，index `0` 是本步输出，index `2` 是 `ω`。
零步取 `ω`，序数后继步取基数后继，非序数后继输入统一取空集，极限步取值域之并。
-/
def alephOperator (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body :=
    .disj (.conj (Formula.isZeroLengthSequence 𝒞 (.bound 1)) (Formula.extensionalEq (.bound 0) (.bound 2))) <|
      .disj (.existsE <| .conj (Formula.isSuccessorLengthSequenceWithLast 𝒞 (.bound 2) Term.newest) <|
          .disj (.conj (Formula.isOrdinal Term.newest) (Formula.isCardinalSuccessor 𝒞 (.bound 1) Term.newest)) (.conj (.neg <| Formula.isOrdinal Term.newest)
              (Formula.isEmpty (.bound 1)))) (Formula.isLimitLengthSequenceWithUnion 𝒞 (.bound 1) (.bound 0))
/-- 由超限递归得到的 Aleph 类关系。 -/
def aleph (𝒞 : OrderedPairConvention) : BinarySchema 1 :=
  transfiniteRecursion 𝒞 (alephOperator 𝒞)
end BinarySchema
namespace Formula
/-- `aleph` 是以 `ω` 为首项的 Aleph 枚举在 `index` 处的值。 -/
def isAlephNumber (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω index aleph : Term depth) : Formula 1 depth :=
  related (BinarySchema.aleph 𝒞) (.singleton ω) index aleph
derive_free_closed isAlephNumber
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
