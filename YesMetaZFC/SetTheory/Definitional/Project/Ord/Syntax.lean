import YesMetaZFC.SetTheory.Definitional.Project.Order

/-!
# 序数、超限序列与递归公式

序数采用标准纯集合定义：传递集合且由原始隶属关系良序。这里没有把 `∈` 重新编码成
有序对集合，因此序数定义不依赖任何有序对约定。

超限序列使用集合编码函数，递归算子与序数类函数使用 `BinarySchema`。所有定义仍然
只生成纯隶属公式；本层不主张递归解存在，也不把宿主层函数当作集合论函数。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
namespace Formula

/-- `set` 是传递集合。 -/
def isTransitive {depth : Nat} (set : Term depth) : Formula 1 depth :=
  Formula.forallMem set <| Formula.forallMem Term.newest <|
    .mem Term.newest set.weaken.weaken

/-- `α` 是由隶属关系良序的传递集合。 -/
def isOrdinal {depth : Nat} (α : Term depth) : Formula 1 depth :=
  .conj (isTransitive α) <|
    isWellOrderOn RelationSchema.membership TermVector.empty α

/-- `α` 是某个序数的后继。 -/
def isSuccessorOrdinal {depth : Nat}
    (α : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj (isOrdinal Term.newest) <|
      isSuccessor α.weaken Term.newest

/-- `α` 是非零且没有最大元的极限序数。 -/
def isLimitOrdinal {depth : Nat}
    (α : Term depth) : Formula 1 depth :=
  .conj (isOrdinal α) <|
    .conj (Formula.existsMem α .truth) <|
      Formula.forallMem α <| Formula.existsMem α.weaken <|
        .mem (.bound 1) Term.newest

/-- `sequence` 是长度为序数 `length` 的超限序列。 -/
def isSequenceOfLength (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length : Term depth) : Formula 1 depth :=
  .conj (isOrdinal length) <|
    .conj (isFunction 𝒞 sequence)
      (isDomain 𝒞 length sequence)

/-- `sequence` 是长度为 `length`、取值于 `target` 的超限序列。 -/
def isSequenceIn (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length target : Term depth) : Formula 1 depth :=
  .conj (isOrdinal length)
    (isFunctionFromTo 𝒞 sequence length target)

/-- `sequence` 是取值于 `target`、长度严格小于 `bound` 的超限序列。 -/
def isSequenceInBelow (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence bound target : Term depth) : Formula 1 depth :=
  .conj (isOrdinal bound) <|
    Formula.existsMem bound <|
      isSequenceIn 𝒞 sequence.weaken Term.newest target.weaken

/-- `sequence` 的定义域是某个序数。 -/
def isTransfiniteSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence : Term depth) : Formula 1 depth :=
  .existsE <|
    isSequenceOfLength 𝒞 sequence.weaken Term.newest

/--
`extension` 是把 `value` 接在长度为 `length` 的 `sequence` 末尾所得的序列。

定义要求原序列正是新序列在 `length` 上的限制，且新增长度位置的值为 `value`。
-/
def isSequenceExtension (𝒞 : OrderedPairConvention)
    {depth : Nat} (extension sequence length value : Term depth) :
    Formula 1 depth :=
  .conj (isSequenceOfLength 𝒞 sequence length) <|
    .existsE <|
      .conj (isSuccessor Term.newest length.weaken) <|
        .conj
          (isSequenceOfLength 𝒞 extension.weaken Term.newest) <|
          .conj
            (isRestriction 𝒞 sequence.weaken
              extension.weaken length.weaken)
            (orderedPairMem 𝒞 length.weaken value.weaken
              extension.weaken)

/-- `sequence` 是长度为 `length` 的序数值序列。 -/
def isOrdinalValuedSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length : Term depth) : Formula 1 depth :=
  .conj (isSequenceOfLength 𝒞 sequence length) <|
    Formula.forallMem length <| .forallE <|
      .imp
        (orderedPairMem 𝒞 (.bound 1) Term.newest
          sequence.weaken.weaken)
        (isOrdinal Term.newest)

/-- `sequence` 是长度为 `length` 的不下降序数序列。 -/
def isNondecreasingOrdinalSequence
    (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length : Term depth) : Formula 1 depth :=
  .conj (isOrdinalValuedSequence 𝒞 sequence length) <|
    Formula.forallMem length <| Formula.forallMem length.weaken <|
      .imp (.mem (.bound 1) Term.newest) <|
        .forallE <| .forallE <|
          .imp
            (.conj
              (orderedPairMem 𝒞 (.bound 3) (.bound 1)
                sequence.weaken.weaken.weaken.weaken)
              (orderedPairMem 𝒞 (.bound 2) (.bound 0)
                sequence.weaken.weaken.weaken.weaken))
            (lessOrEqual RelationSchema.membership TermVector.empty
              (.bound 1) Term.newest)

/-- `sequence` 是长度为 `length` 的严格递增序数序列。 -/
def isIncreasingOrdinalSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length : Term depth) : Formula 1 depth :=
  .conj (isOrdinalValuedSequence 𝒞 sequence length) <|
    Formula.forallMem length <| Formula.forallMem length.weaken <|
      .imp (.mem (.bound 1) Term.newest) <|
        .forallE <| .forallE <|
          .imp
            (.conj
              (orderedPairMem 𝒞 (.bound 3) (.bound 1)
                sequence.weaken.weaken.weaken.weaken)
              (orderedPairMem 𝒞 (.bound 2) (.bound 0)
                sequence.weaken.weaken.weaken.weaken))
            (.mem (.bound 1) (.bound 0))

/--
`limit` 是序数值序列 `sequence` 在长度 `length` 处的极限。

这里直接采用纸面定义 `limit = ⋃ ran(sequence)`；`range` 作为关系值域显式量化。
-/
def isOrdinalSequenceLimit (𝒞 : OrderedPairConvention)
    {depth : Nat} (limit sequence length : Term depth) : Formula 1 depth :=
  .conj (isOrdinal limit) <|
    .conj (isOrdinalValuedSequence 𝒞 sequence length) <|
      .existsE <|
        .conj
          (isRange 𝒞 Term.newest sequence.weaken)
          (isUnion limit.weaken Term.newest)

/-- `limit` 是不下降序数序列 `sequence` 在 `length` 处的极限。 -/
def isLimitOfNondecreasingOrdinalSequence
    (𝒞 : OrderedPairConvention)
    {depth : Nat} (limit sequence length : Term depth) : Formula 1 depth :=
  .conj
    (isNondecreasingOrdinalSequence 𝒞 sequence length)
    (isOrdinalSequenceLimit 𝒞 limit sequence length)

/-- `sequence` 在定义域内的每个非零极限位置都等于此前值域的并。 -/
def isContinuousOrdinalSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length : Term depth) : Formula 1 depth :=
  .conj (isOrdinalValuedSequence 𝒞 sequence length) <|
    Formula.forallMem length <| .forallE <|
      .imp
        (.conj (isLimitOrdinal (.bound 1))
          (orderedPairMem 𝒞 (.bound 1) (.bound 0)
            sequence.weaken.weaken)) <|
        .existsE <| .existsE <|
          .conj
            (isRestriction 𝒞 (.bound 1)
              sequence.weaken.weaken.weaken.weaken (.bound 3)) <|
            .conj
              (isRange 𝒞 (.bound 0) (.bound 1))
              (isUnion (.bound 2) (.bound 0))

/-- `sequence` 是严格递增且连续的序数序列。 -/
def isNormalOrdinalSequence (𝒞 : OrderedPairConvention)
    {depth : Nat} (sequence length : Term depth) : Formula 1 depth :=
  .conj
    (isIncreasingOrdinalSequence 𝒞 sequence length)
    (isContinuousOrdinalSequence 𝒞 sequence length)

/--
`sequence` 在 `length` 上服从递归算子 `operator`。

`operator` 的左参数是限制序列，右参数是本步输出；所有 schema 参数由
`parameters` 显式提供。
-/
def obeysRecursion {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (sequence length : Term depth) : Formula 1 depth :=
  Formula.forallMem length <| .forallE <|
    .imp
      (orderedPairMem 𝒞 (.bound 1) (.bound 0)
        sequence.weaken.weaken) <|
      .existsE <|
        .conj
          (isRestriction 𝒞 Term.newest
            sequence.weaken.weaken.weaken (.bound 2))
          (related operator parameters.weaken.weaken.weaken
            Term.newest (.bound 1))

/-- `sequence` 是长度为 `length`、服从 `operator` 的递归序列。 -/
def isRecursiveSequence {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (sequence length : Term depth) : Formula 1 depth :=
  .conj (isSequenceOfLength 𝒞 sequence length)
    (obeysRecursion 𝒞 operator parameters sequence length)

/-- `sequence` 是取值于 `target`、服从 `operator` 的递归序列。 -/
def isRecursiveSequenceIn {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (sequence length target : Term depth) : Formula 1 depth :=
  .conj (isSequenceIn 𝒞 sequence length target)
    (obeysRecursion 𝒞 operator parameters sequence length)

/--
`value` 是由取值于 `target` 的递归序列在 `α` 处产生的递归值，并且仍属于
`target`。
-/
def isRecursionValueIn {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (α value target : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj
      (isRecursiveSequenceIn 𝒞 operator parameters.weaken
        Term.newest α.weaken target.weaken) <|
    .conj
      (related operator parameters.weaken Term.newest value.weaken)
      (.mem value.weaken target.weaken)

/--
`value` 是超限递归在 `α` 处由 `operator` 给出的值。

这正是 Jech 证明中的式 (2.6)：存在一个 `α`-递归序列，且最后再应用一次
`operator` 得到 `value`。递归序列及结果的唯一性由后续归纳定理证明，不写入定义。
-/
def isRecursionValue {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (α value : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj
      (isRecursiveSequence 𝒞 operator parameters.weaken
        Term.newest α.weaken)
      (related operator parameters.weaken Term.newest value.weaken)

/-- `function` 是序数类上的单值且全定义类函数，输出不预设为序数。 -/
def isClassFunctionOnOrdinals {parameterCount depth : Nat}
    (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) : Formula 1 depth :=
  .forallE <|
    .imp (isOrdinal Term.newest) <|
      .existsE <|
        .conj
          (related function parameters.weaken.weaken
            (.bound 1) Term.newest) <|
          .forallE <|
            .imp
              (related function parameters.weaken.weaken.weaken
                (.bound 2) Term.newest)
              (extensionalEq (.bound 1) Term.newest)

/-- `function` 是序数类上的单值、全定义且序数值的类函数。 -/
def isOrdinalClassFunction {parameterCount depth : Nat}
    (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) : Formula 1 depth :=
  .conj (isClassFunctionOnOrdinals function parameters) <|
    .forallE <| .forallE <|
      .imp
        (.conj (isOrdinal (.bound 1))
          (related function parameters.weaken.weaken
            (.bound 1) Term.newest))
        (isOrdinal Term.newest)

/-- `operator` 是所有集合编码超限序列上的单值且全定义类函数。 -/
def isClassFunctionOnTransfiniteSequences {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) : Formula 1 depth :=
  .forallE <|
    .imp (isTransfiniteSequence 𝒞 Term.newest) <|
      .existsE <|
        .conj
          (related operator parameters.weaken.weaken
            (.bound 1) Term.newest) <|
          .forallE <|
            .imp
              (related operator parameters.weaken.weaken.weaken
                (.bound 2) Term.newest)
              (extensionalEq (.bound 1) Term.newest)

/-- `operator` 是所有长度小于 `bound`、取值于 `target` 的序列上的类函数。 -/
def isClassFunctionOnSequencesInBelow {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (bound target : Term depth) : Formula 1 depth :=
  .forallE <|
    .imp
      (isSequenceInBelow 𝒞 Term.newest
        bound.weaken target.weaken) <|
      .existsE <|
        .conj
          (related operator parameters.weaken.weaken
            (.bound 1) Term.newest) <|
          .forallE <|
            .imp
              (related operator parameters.weaken.weaken.weaken
                (.bound 2) Term.newest)
              (extensionalEq (.bound 1) Term.newest)

/-- `operator` 把长度小于 `bound` 的 `target` 值序列仍映到 `target`。 -/
def mapsSequencesInBelowInto {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (bound target : Term depth) : Formula 1 depth :=
  .forallE <| .forallE <|
    .imp
      (.conj
        (isSequenceInBelow 𝒞 (.bound 1)
          bound.weaken.weaken target.weaken.weaken)
        (related operator parameters.weaken.weaken
          (.bound 1) Term.newest))
      (.mem Term.newest target.weaken.weaken)

/-- 类关系 `function` 在序数上严格递增。 -/
def isIncreasingOnOrdinals {parameterCount depth : Nat}
    (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) : Formula 1 depth :=
  .forallE <| .forallE <|
    .imp
      (.conj (isOrdinal (.bound 1)) <|
        .conj (isOrdinal Term.newest)
          (.mem (.bound 1) Term.newest)) <|
      .forallE <| .forallE <|
        .imp
          (.conj
            (related function parameters.weaken.weaken.weaken.weaken
              (.bound 3) (.bound 1))
            (related function parameters.weaken.weaken.weaken.weaken
              (.bound 2) Term.newest))
          (.mem (.bound 1) Term.newest)

/--
类关系 `function` 在非零极限序数处连续。

对极限输入 `α`，输出是所有较小输入之函数值构成集合的并。
-/
def isContinuousOnOrdinals {parameterCount depth : Nat}
    (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) : Formula 1 depth :=
  .forallE <| .forallE <|
    .imp
      (.conj (isLimitOrdinal (.bound 1))
        (related function parameters.weaken.weaken
          (.bound 1) Term.newest)) <|
      .existsE <|
        .conj
          (.forallE <|
            .iff (.mem Term.newest (.bound 1)) <|
              Formula.existsMem (.bound 3) <|
                related function
                  parameters.weaken.weaken.weaken.weaken.weaken
                  Term.newest (.bound 1))
          (isUnion (.bound 1) Term.newest)

/-- `function` 是序数类上的正规函数：序数值、严格递增且在极限处连续。 -/
def isNormalOrdinalFunction {parameterCount depth : Nat}
    (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) : Formula 1 depth :=
  .conj (isOrdinalClassFunction function parameters) <|
    .conj
      (isIncreasingOnOrdinals function parameters)
      (isContinuousOnOrdinals function parameters)

/-- 传递性是 `Δ₀` 性质。 -/
theorem isTransitive_delta0 {depth : Nat} (set : Term depth) :
    (isTransitive set).IsDelta0 := by
  exact Formula.IsDelta0.forallMem set
    (Formula.IsDelta0.forallMem Term.newest (Formula.IsDelta0.mem _ _))

end Formula

namespace BinarySchema

/-- “在给定序数长度上存在一个取值于固定目标集的递归序列”的归纳模式。 -/
def recursiveSequenceInExistence
    (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (operator : BinarySchema parameterCount) :
    UnarySchema (parameterCount + 1) where
  body :=
    .existsE <|
      Formula.isRecursiveSequenceIn 𝒞 operator
        (TermVector.boundParameters parameterCount 3)
        Term.newest (.bound 1) (.bound 2)
  freeClosed := by
    simp [Formula.isRecursiveSequenceIn, Formula.isSequenceIn,
      Formula.obeysRecursion,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.isFunctionFromTo,
      Formula.isFunction, Formula.isRelation, Formula.isDomain,
      Formula.isRestriction, Formula.orderedPairMem,
      Formula.forallMem, Formula.existsMem, Formula.subset,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]

/--
“给定序数长度上的任意两个固定目标集值递归序列相等”的归纳模式。
-/
def recursiveSequenceInUniqueness
    (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (operator : BinarySchema parameterCount) :
    UnarySchema (parameterCount + 1) where
  body :=
    .forallE <| .forallE <|
      .imp
        (Formula.isRecursiveSequenceIn 𝒞 operator
          (TermVector.boundParameters parameterCount 4)
          (.bound 1) (.bound 2) (.bound 3)) <|
      .imp
        (Formula.isRecursiveSequenceIn 𝒞 operator
          (TermVector.boundParameters parameterCount 4)
          Term.newest (.bound 2) (.bound 3))
        (Formula.extensionalEq (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.isRecursiveSequenceIn, Formula.isSequenceIn,
      Formula.obeysRecursion,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.isFunctionFromTo,
      Formula.isFunction, Formula.isRelation, Formula.isDomain,
      Formula.isRestriction, Formula.orderedPairMem,
      Formula.forallMem, Formula.existsMem, Formula.subset,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]

/-- 把序数映到编码其固定目标集内递归值的有序对。 -/
def recursionGraphPairIn (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (operator : BinarySchema parameterCount) :
    BinarySchema (parameterCount + 1) where
  body :=
    .existsE <|
      .conj
        (Formula.isRecursionValueIn 𝒞 operator
          (TermVector.boundParameters parameterCount 4)
          (.bound 2) Term.newest (.bound 3))
        (𝒞.code (.bound 1) (.bound 2) Term.newest)
  freeClosed := by
    simp [Formula.isRecursionValueIn,
      Formula.isRecursiveSequenceIn, Formula.isSequenceIn,
      Formula.obeysRecursion,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.isFunctionFromTo,
      Formula.isFunction, Formula.isRelation, Formula.isDomain,
      Formula.isRestriction, Formula.orderedPairMem,
      Formula.forallMem, Formula.existsMem, Formula.subset,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]

/-- “在给定序数长度上存在递归序列”的一元归纳模式。 -/
def recursiveSequenceExistence (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (operator : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body :=
    .existsE <|
      Formula.isRecursiveSequence 𝒞 operator
        (TermVector.boundParameters parameterCount 2)
        Term.newest (.bound 1)
  freeClosed := by
    simp [Formula.isRecursiveSequence, Formula.isSequenceOfLength,
      Formula.obeysRecursion, Formula.isOrdinal,
      Formula.isTransitive, Formula.isWellOrderOn,
      Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual, Formula.isFunction,
      Formula.isRelation, Formula.isDomain, Formula.isRestriction,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed,
      Term.newest]

/-- “给定序数长度上的任意两个递归序列相等”的一元归纳模式。 -/
def recursiveSequenceUniqueness (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (operator : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body :=
    .forallE <| .forallE <|
      .imp
        (Formula.isRecursiveSequence 𝒞 operator
          (TermVector.boundParameters parameterCount 3)
          (.bound 1) (.bound 2)) <|
      .imp
        (Formula.isRecursiveSequence 𝒞 operator
          (TermVector.boundParameters parameterCount 3)
          Term.newest (.bound 2))
        (Formula.extensionalEq (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.isRecursiveSequence, Formula.isSequenceOfLength,
      Formula.obeysRecursion, Formula.isOrdinal,
      Formula.isTransitive, Formula.isWellOrderOn,
      Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual, Formula.isFunction,
      Formula.isRelation, Formula.isDomain, Formula.isRestriction,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed,
      Term.newest]

/--
把序数 `α` 映到编码 `(α, value)` 的有序对，其中 `value` 是递归值。

该模式用于函数式替换直接构造超限递归图。
-/
def recursionGraphPair (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (operator : BinarySchema parameterCount) :
    BinarySchema parameterCount where
  body :=
    .existsE <|
      .conj
        (Formula.isRecursionValue 𝒞 operator
          (TermVector.boundParameters parameterCount 3)
          (.bound 2) Term.newest)
        (𝒞.code (.bound 1) (.bound 2) Term.newest)
  freeClosed := by
    simp [Formula.isRecursionValue, Formula.isRecursiveSequence,
      Formula.isSequenceOfLength, Formula.obeysRecursion,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.isFunction,
      Formula.isRelation, Formula.isDomain, Formula.isRestriction,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed,
      Term.newest]

/--
由递归算子 `operator` 定义的超限递归类图。

主变量仍遵守 `BinarySchema` 约定：index `1` 是序数输入，index `0` 是输出。
-/
def transfiniteRecursion (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (operator : BinarySchema parameterCount) :
    BinarySchema parameterCount where
  body :=
    Formula.isRecursionValue 𝒞 operator
      (TermVector.boundParameters parameterCount 2)
      (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.isRecursionValue, Formula.isRecursiveSequence,
      Formula.isSequenceOfLength, Formula.obeysRecursion,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.isFunction, Formula.isRelation,
      Formula.isDomain, Formula.isRestriction,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed,
      Term.newest]

end BinarySchema
end Project
end Definitional
end SetTheory
end YesMetaZFC
