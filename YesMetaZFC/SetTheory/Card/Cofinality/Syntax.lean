import YesMetaZFC.SetTheory.Card.Syntax
import YesMetaZFC.SetTheory.Definitional.Project.Ord.Syntax
/-!
# 共尾度公式
本层定义共尾序列、共尾子集及共尾度的对象语言公式。序列仍由模型内部的集合编码
函数给出，共尾度用所有候选序列长度中的最小序数刻画。
-/
namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
namespace Formula
/-- `sequence` 是长度为 `length`、在极限序数 `α` 中共尾的严格递增序列。 -/
def isCofinalOrdinalSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length α : Term depth) : Formula 1 depth :=
  .conj (isLimitOrdinal α) <|
    .conj (isIncreasingOrdinalSequence 𝒞 sequence length) <|
      .conj (isOrdinalSequenceLimit 𝒞 α sequence length) <|
        Formula.forallMem length <| .forallE <|
          .imp (orderedPairMem 𝒞 (.bound 1) Term.newest
              sequence.weaken.weaken) (.mem Term.newest α.weaken.weaken)
/-- `sequence` 是长度为 `length`、在极限序数 `α` 中共尾的非递减序列。 -/
def isCofinalNondecreasingOrdinalSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length α : Term depth) :
    Formula 1 depth :=
  .conj (isLimitOrdinal α) <|
    .conj (isNondecreasingOrdinalSequence 𝒞 sequence length) <|
      .conj (isOrdinalSequenceLimit 𝒞 α sequence length) <|
        Formula.forallMem length <| .forallE <|
          .imp (orderedPairMem 𝒞 (.bound 1) Term.newest
              sequence.weaken.weaken) (.mem Term.newest α.weaken.weaken)
/-- 存在一个长度为 `length`、在 `α` 中共尾的严格递增序列。 -/
def hasCofinalOrdinalSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (length α : Term depth) : Formula 1 depth :=
  .existsE <|
    isCofinalOrdinalSequence 𝒞
      Term.newest length.weaken α.weaken
/-- 存在一个长度为 `length`、在 `α` 中共尾的非递减序列。 -/
def hasCofinalNondecreasingOrdinalSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (length α : Term depth) : Formula 1 depth :=
  .existsE <|
    isCofinalNondecreasingOrdinalSequence 𝒞
      Term.newest length.weaken α.weaken
/-- `set` 是极限序数 `α` 的共尾子集。 -/
def isCofinalSubset {depth : Nat} (set α : Term depth) : Formula 1 depth :=
  .conj (isLimitOrdinal α) <|
    .conj (subset set α) (isUnion α set)
/-- `bound` 是序数集合 `set` 的非严格上界。 -/
def isOrdinalUpperBound {depth : Nat} (set bound : Term depth) : Formula 1 depth :=
  Formula.forallMem set <|
    .disj (extensionalEq Term.newest bound.weaken) (.mem Term.newest bound.weaken)
derive_free_closed isOrdinalUpperBound
/-- `set` 是序数 `α` 的有界子集：存在 `α` 中的一个序数上界。 -/
def isBoundedSubsetOfOrdinal {depth : Nat} (set α : Term depth) : Formula 1 depth :=
  .conj (isOrdinal α) <|
    .conj (subset set α) <|
      Formula.existsMem α <|
        isOrdinalUpperBound set.weaken Term.newest
/-- `κ` 是 `α` 的共尾度，即具有共尾序列的最小序数长度。 -/
def isCofinality (𝒞 : OrderedPairConvention)
    {depth : Nat} (κ α : Term depth) : Formula 1 depth :=
  .conj (isCardinal 𝒞 κ) <|
    .conj (hasCofinalOrdinalSequence 𝒞 κ α) <|
      .forallE <| .imp (hasCofinalOrdinalSequence 𝒞 Term.newest α.weaken) (.disj (extensionalEq κ.weaken Term.newest) (.mem κ.weaken Term.newest))
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
