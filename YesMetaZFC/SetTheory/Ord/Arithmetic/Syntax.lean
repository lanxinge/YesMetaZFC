import YesMetaZFC.SetTheory.Definitional.Project.Ord.Syntax
import YesMetaZFC.SetTheory.SetConstruction

/-!
# 序数算术公式

本层形式化定义对象语言定义。序数加法、乘法和幂仍以
三元关系表示；在存在唯一性定理建立之前，不提前把它们包装成宿主层总函数。

线性序和、积显式保留载体与集合编码关系。积采用文献中的右字典序：先比较第二坐标，
第二坐标相等时再比较第一坐标。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

namespace Formula

/-- `sequence` 的定义域是空序数。 -/
def isZeroLengthSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj
      (isSequenceOfLength 𝒞 sequence.weaken Term.newest)
      (isEmpty Term.newest)

/--
`sequence` 的定义域是某个序数的后继，且 `last` 是其最后一个值。
-/
def isSuccessorLengthSequenceWithLast
    (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence last : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj (isOrdinal Term.newest) <| .existsE <|
      .conj (isSuccessor Term.newest (.bound 1)) <|
        .conj
          (isSequenceOfLength 𝒞 sequence.weaken.weaken
            Term.newest)
          (orderedPairMem 𝒞 (.bound 1) last.weaken.weaken
            sequence.weaken.weaken)

/--
`sequence` 的定义域是极限序数，且 `limit` 是其值域的并。
-/
def isLimitLengthSequenceWithUnion
    (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence limit : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj (isLimitOrdinal Term.newest) <|
      .conj
        (isSequenceOfLength 𝒞 sequence.weaken Term.newest) <|
        .existsE <|
          .conj
            (isRange 𝒞 Term.newest sequence.weaken.weaken)
            (isUnion limit.weaken.weaken Term.newest)

/-- `one` 是空序数的后继。 -/
def isOrdinalOne {depth : Nat} (one : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj (isEmpty Term.newest)
      (isSuccessor one.weaken Term.newest)

end Formula

namespace BinarySchema

/--
固定左参数 `alpha` 的序数加法递归算子。

参数布局为：index `1` 是此前序列，index `0` 是本步输出，index `2` 是 `alpha`。
-/
def ordinalAdditionOperator
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body :=
    .disj
      (.conj
        (Formula.isZeroLengthSequence 𝒞 (.bound 1))
        (Formula.extensionalEq (.bound 0) (.bound 2))) <|
      .disj
        (.existsE <|
          .conj
            (Formula.isSuccessorLengthSequenceWithLast 𝒞
              (.bound 2) Term.newest)
            (Formula.isSuccessor (.bound 1) Term.newest))
        (Formula.isLimitLengthSequenceWithUnion 𝒞
          (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isZeroLengthSequence,
      Formula.isSuccessorLengthSequenceWithLast,
      Formula.isLimitLengthSequenceWithUnion,
      Formula.isSequenceOfLength, Formula.isOrdinal,
      Formula.isTransitive, Formula.isWellOrderOn,
      Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual,
      Formula.isFunction, Formula.isRelation, Formula.isDomain,
      Formula.isRange, Formula.isEmpty, Formula.isSuccessor,
      Formula.isLimitOrdinal, Formula.isUnion,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest,
      Term.weaken]

/-- 由超限递归得到的序数加法类关系。 -/
def ordinalAddition (𝒞 : OrderedPairConvention) :
    BinarySchema 1 :=
  transfiniteRecursion 𝒞 (ordinalAdditionOperator 𝒞)

end BinarySchema

namespace Formula

/-- `sum` 是 `left + right` 的递归值。 -/
def isOrdinalAddition (𝒞 : OrderedPairConvention)
    {depth : Nat} (sum left right : Term depth) : Formula 1 depth :=
  related (BinarySchema.ordinalAddition 𝒞)
    (.singleton left) right sum

end Formula

namespace BinarySchema

/--
固定左参数 `alpha` 的序数乘法递归算子。

后继步使用已经定义的序数加法关系 `(alpha * beta) + alpha`。
为满足超限递归内核对任意序列的全定义要求，非序数左参数统一映到空集；
当 `alpha` 是序数时，第二分支精确恢复文献定义。
-/
def ordinalMultiplicationOperator
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body :=
    .disj
      (.conj (.neg <| Formula.isOrdinal (.bound 2))
        (Formula.isEmpty (.bound 0))) <|
      .conj (Formula.isOrdinal (.bound 2)) <|
        .disj
          (.conj
            (Formula.isZeroLengthSequence 𝒞 (.bound 1))
            (Formula.isEmpty (.bound 0))) <|
          .disj
            (.existsE <|
              .conj
                (Formula.isSuccessorLengthSequenceWithLast 𝒞
                  (.bound 2) Term.newest)
                (Formula.isOrdinalAddition 𝒞
                  (.bound 1) Term.newest (.bound 3)))
            (Formula.isLimitLengthSequenceWithUnion 𝒞
              (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isZeroLengthSequence,
      Formula.isSuccessorLengthSequenceWithLast,
      Formula.isLimitLengthSequenceWithUnion,
      Formula.isOrdinalAddition, Formula.isSequenceOfLength,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.isFunction,
      Formula.isRelation, Formula.isDomain, Formula.isRange,
      Formula.isEmpty, Formula.isSuccessor,
      Formula.isLimitOrdinal, Formula.isUnion,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest,
      TermVector.singleton, Term.weaken]
    exact Formula.related_freeClosed_of_closed
      (relation := ordinalAddition 𝒞)
      (parameters := TermVector.ofFn fun _ => Term.newest)
      (left := .bound 3) (right := .bound 1)
      (by intro entry; simp) (by simp) (by simp)

/-- 由超限递归得到的序数乘法类关系。 -/
def ordinalMultiplication (𝒞 : OrderedPairConvention) :
    BinarySchema 1 :=
  transfiniteRecursion 𝒞
    (ordinalMultiplicationOperator 𝒞)

end BinarySchema

namespace Formula

/-- `product` 是 `left * right` 的递归值。 -/
def isOrdinalMultiplication (𝒞 : OrderedPairConvention)
    {depth : Nat} (product left right : Term depth) : Formula 1 depth :=
  related (BinarySchema.ordinalMultiplication 𝒞)
    (.singleton left) right product

end Formula

namespace BinarySchema

/--
固定底数 `alpha` 的序数幂递归算子。

后继步使用已经定义的序数乘法关系 `(alpha ^ beta) * alpha`。
-/
def ordinalExponentiationOperator
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body :=
    .disj
      (.conj
        (Formula.isZeroLengthSequence 𝒞 (.bound 1))
        (Formula.isOrdinalOne (.bound 0))) <|
      .disj
        (.existsE <|
          .conj
            (Formula.isSuccessorLengthSequenceWithLast 𝒞
              (.bound 2) Term.newest)
            (Formula.isOrdinalMultiplication 𝒞
              (.bound 1) Term.newest (.bound 3)))
        (Formula.isLimitLengthSequenceWithUnion 𝒞
          (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isZeroLengthSequence,
      Formula.isSuccessorLengthSequenceWithLast,
      Formula.isLimitLengthSequenceWithUnion,
      Formula.isOrdinalOne, Formula.isOrdinalMultiplication,
      Formula.isSequenceOfLength, Formula.isOrdinal,
      Formula.isTransitive, Formula.isWellOrderOn,
      Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual,
      Formula.isFunction, Formula.isRelation, Formula.isDomain,
      Formula.isRange, Formula.isEmpty, Formula.isSuccessor,
      Formula.isLimitOrdinal, Formula.isUnion,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest,
      TermVector.singleton, Term.weaken]
    exact Formula.related_freeClosed_of_closed
      (relation := ordinalMultiplication 𝒞)
      (parameters := TermVector.ofFn fun _ => Term.newest)
      (left := .bound 3) (right := .bound 1)
      (by intro entry; simp) (by simp) (by simp)

/-- 由超限递归得到的序数幂类关系。 -/
def ordinalExponentiation (𝒞 : OrderedPairConvention) :
    BinarySchema 1 :=
  transfiniteRecursion 𝒞
    (ordinalExponentiationOperator 𝒞)

end BinarySchema

namespace Formula

/-- `power` 是 `base ^ exponent` 的递归值。 -/
def isOrdinalExponentiation (𝒞 : OrderedPairConvention)
    {depth : Nat} (power base exponent : Term depth) : Formula 1 depth :=
  related (BinarySchema.ordinalExponentiation 𝒞)
    (.singleton base) exponent power

/-- `dividend = divisor * quotient + remainder`，且余项严格小于除数。 -/
def isOrdinalDivision (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (dividend divisor quotient remainder : Term depth) :
    Formula 1 depth :=
  .conj (isOrdinal quotient) <| .conj (.mem remainder divisor) <|
    .existsE <| .conj
      (isOrdinalMultiplication 𝒞
        Term.newest divisor.weaken quotient.weaken)
      (isOrdinalAddition 𝒞
        dividend.weaken Term.newest remainder.weaken)

/-- `relation` 是 `carrier` 上的集合编码严格线序。 -/
def isSetCodedLinearOrder (𝒞 : OrderedPairConvention)
    {depth : Nat} (relation carrier : Term depth) : Formula 1 depth :=
  .conj (isRelation 𝒞 relation)
    (isLinearOrderRelation 𝒞 relation carrier)

/-- `sumRelation` 精确实现不相交线性序的序和关系。 -/
def isLinearOrderSumRelation (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (sumRelation leftCarrier leftRelation rightCarrier rightRelation :
      Term depth) : Formula 1 depth :=
  .forallE <| .forallE <|
    .iff
      (orderedPairMem 𝒞 (.bound 1) Term.newest
        sumRelation.weaken.weaken) <|
      .disj
        (.conj (.mem (.bound 1) leftCarrier.weaken.weaken) <|
          .conj (.mem Term.newest leftCarrier.weaken.weaken) <|
            orderedPairMem 𝒞 (.bound 1) Term.newest
              leftRelation.weaken.weaken) <|
        .disj
          (.conj (.mem (.bound 1) rightCarrier.weaken.weaken) <|
            .conj (.mem Term.newest rightCarrier.weaken.weaken) <|
              orderedPairMem 𝒞 (.bound 1) Term.newest
                rightRelation.weaken.weaken)
          (.conj (.mem (.bound 1) leftCarrier.weaken.weaken)
            (.mem Term.newest rightCarrier.weaken.weaken))

/-- `sumCarrier, sumRelation` 是两个不相交线性序的序和。 -/
def isLinearOrderSum (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (sumCarrier sumRelation leftCarrier leftRelation
      rightCarrier rightRelation : Term depth) : Formula 1 depth :=
  .conj
    (isSetCodedLinearOrder 𝒞 leftRelation leftCarrier) <|
  .conj
    (isSetCodedLinearOrder 𝒞 rightRelation rightCarrier) <|
  .conj (isDisjoint leftCarrier rightCarrier) <|
  .conj (isUnionOfTwo sumCarrier leftCarrier rightCarrier) <|
  .conj (isRelation 𝒞 sumRelation)
    (isLinearOrderSumRelation 𝒞 sumRelation
      leftCarrier leftRelation rightCarrier rightRelation)

/--
`productRelation` 精确实现第二坐标优先的右字典序关系。
-/
def isRightLexicographicProductRelation
    (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (productRelation leftCarrier leftRelation
      rightCarrier rightRelation : Term depth) : Formula 1 depth :=
  .forallE <| .forallE <|
    .iff
      (orderedPairMem 𝒞 (.bound 1) Term.newest
        productRelation.weaken.weaken) <|
      Formula.existsMem leftCarrier.weaken.weaken <|
        Formula.existsMem rightCarrier.weaken.weaken.weaken <|
          Formula.existsMem leftCarrier.weaken.weaken.weaken.weaken <|
            Formula.existsMem
              rightCarrier.weaken.weaken.weaken.weaken.weaken <|
              .conj
                (𝒞.code (.bound 5) (.bound 3) (.bound 2)) <|
              .conj
                (𝒞.code (.bound 4) (.bound 1) (.bound 0)) <|
                .disj
                  (orderedPairMem 𝒞 (.bound 2) (.bound 0)
                    rightRelation.weaken.weaken.weaken.weaken.weaken.weaken)
                  (.conj
                    (extensionalEq (.bound 2) (.bound 0))
                    (orderedPairMem 𝒞 (.bound 3) (.bound 1)
                      leftRelation.weaken.weaken.weaken.weaken.weaken.weaken))

/-- `productCarrier, productRelation` 是两个线性序的右字典序积。 -/
def isLinearOrderProduct (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (productCarrier productRelation leftCarrier leftRelation
      rightCarrier rightRelation : Term depth) : Formula 1 depth :=
  .conj
    (isSetCodedLinearOrder 𝒞 leftRelation leftCarrier) <|
  .conj
    (isSetCodedLinearOrder 𝒞 rightRelation rightCarrier) <|
  .conj
    (isCartesianProduct 𝒞 productCarrier
      leftCarrier rightCarrier) <|
  .conj (isRelation 𝒞 productRelation)
    (isRightLexicographicProductRelation 𝒞 productRelation
      leftCarrier leftRelation rightCarrier rightRelation)

end Formula

end Project
end Definitional
end SetTheory
end YesMetaZFC
