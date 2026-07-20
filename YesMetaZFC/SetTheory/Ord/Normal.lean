import YesMetaZFC.SetTheory.Ord.Recursion

/-!
# 序数序列极限与正规函数

本文件形式化定义 2.17：不下降序数序列的极限，以及严格递增且在极限处连续的正规
序列和正规类函数。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `sequence` 是长度为 `length` 的序数值序列。 -/
def IsOrdinalValuedSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence length : ℳ.Domain) : Prop :=
  ℳ.IsSequenceOfLength 𝕀 sequence length ∧
    ∀ index, ℳ.mem index length →
      ∀ value, ℳ.PairMember 𝕀 index value sequence →
        ℳ.IsOrdinal value

/-- `sequence` 是不下降序数序列。 -/
def IsNondecreasingOrdinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence length : ℳ.Domain) : Prop :=
  ℳ.IsOrdinalValuedSequence 𝕀 sequence length ∧
    ∀ left, ℳ.mem left length →
      ∀ right, ℳ.mem right length → ℳ.mem left right →
        ∀ leftValue rightValue,
          ℳ.PairMember 𝕀 left leftValue sequence →
          ℳ.PairMember 𝕀 right rightValue sequence →
            leftValue = rightValue ∨ ℳ.mem leftValue rightValue

/-- `sequence` 是严格递增序数序列。 -/
def IsIncreasingOrdinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence length : ℳ.Domain) : Prop :=
  ℳ.IsOrdinalValuedSequence 𝕀 sequence length ∧
    ∀ left, ℳ.mem left length →
      ∀ right, ℳ.mem right length → ℳ.mem left right →
        ∀ leftValue rightValue,
          ℳ.PairMember 𝕀 left leftValue sequence →
          ℳ.PairMember 𝕀 right rightValue sequence →
            ℳ.mem leftValue rightValue

/-- `limit` 是序数值序列全部值的上确界。 -/
def IsOrdinalSequenceLimit {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (limit sequence length : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal limit ∧
    ℳ.IsOrdinalValuedSequence 𝕀 sequence length ∧
      ∃ range,
        ℳ.IsRangeOf 𝕀 range sequence ∧
          ℳ.IsUnionOf limit range

/-- `limit` 是不下降序数序列的极限。 -/
def IsLimitOfNondecreasingOrdinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (limit sequence length : ℳ.Domain) : Prop :=
  ℳ.IsNondecreasingOrdinalSequence 𝕀 sequence length ∧
    ℳ.IsOrdinalSequenceLimit 𝕀 limit sequence length

/-- 序列在定义域内的每个非零极限位置都等于此前值域的并。 -/
def IsContinuousOrdinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence length : ℳ.Domain) : Prop :=
  ℳ.IsOrdinalValuedSequence 𝕀 sequence length ∧
    ∀ index, ℳ.mem index length →
      ∀ value,
        ℳ.IsLimitOrdinal index ∧
          ℳ.PairMember 𝕀 index value sequence →
        ∃ restriction range,
          ℳ.IsRestrictionOf 𝕀 restriction sequence index ∧
            ℳ.IsRangeOf 𝕀 range restriction ∧
              ℳ.IsUnionOf value range

/-- `sequence` 是严格递增且连续的序数序列。 -/
def IsNormalOrdinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence length : ℳ.Domain) : Prop :=
  ℳ.IsIncreasingOrdinalSequence 𝕀 sequence length ∧
    ℳ.IsContinuousOrdinalSequence 𝕀 sequence length

/-- `function` 是序数类上的全定义、单值且序数值类函数。 -/
def IsOrdinalClassFunction (ℳ : Structure.{u})
    (function : ℳ.Domain → ℳ.Domain → Prop) : Prop :=
  ℳ.IsClassFunctionOnOrdinals function ∧
    ∀ α value,
      ℳ.IsOrdinal α → function α value →
        ℳ.IsOrdinal value

/-- `function` 在序数类上严格递增。 -/
def IsIncreasingOnOrdinals (ℳ : Structure.{u})
    (function : ℳ.Domain → ℳ.Domain → Prop) : Prop :=
  ∀ left right,
    ℳ.IsOrdinal left → ℳ.IsOrdinal right → ℳ.mem left right →
      ∀ leftValue rightValue,
        function left leftValue → function right rightValue →
          ℳ.mem leftValue rightValue

/-- `function` 在每个非零极限序数处等于此前值集合的并。 -/
def IsContinuousOnOrdinals (ℳ : Structure.{u})
    (function : ℳ.Domain → ℳ.Domain → Prop) : Prop :=
  ∀ α value,
    ℳ.IsLimitOrdinal α ∧ function α value →
      ∃ range,
        (∀ member, ℳ.mem member range ↔
          ∃ input, ℳ.mem input α ∧ function input member) ∧
        ℳ.IsUnionOf value range

/-- `function` 是序数类上的正规函数。 -/
def IsNormalOrdinalFunction (ℳ : Structure.{u})
    (function : ℳ.Domain → ℳ.Domain → Prop) : Prop :=
  ℳ.IsOrdinalClassFunction function ∧
    ℳ.IsIncreasingOnOrdinals function ∧
      ℳ.IsContinuousOnOrdinals function

namespace IsNormalOrdinalFunction

/-- 正规函数把非零极限序数映到非零极限序数。 -/
theorem limit_value {ℳ : Structure.{u}}
    {function : ℳ.Domain → ℳ.Domain → Prop}
    (hNormal : ℳ.IsNormalOrdinalFunction function)
    {α value : ℳ.Domain}
    (hLimit : ℳ.IsLimitOrdinal α)
    (hValue : function α value) :
    ℳ.IsLimitOrdinal value := by
  have hValueOrdinal : ℳ.IsOrdinal value :=
    hNormal.1.2 α value hLimit.1 hValue
  rcases hNormal.2.2 α value ⟨hLimit, hValue⟩ with
    ⟨range, hRange, hUnion⟩
  refine ⟨hValueOrdinal, ?_, ?_⟩
  · rcases hLimit.2.1 with ⟨input, hInput⟩
    rcases hLimit.2.2 input hInput with
      ⟨larger, hLarger, hInputLarger⟩
    rcases hNormal.1.1 input (hLimit.1.mem hInput) with
      ⟨inputValue, hInputValue, _⟩
    rcases hNormal.1.1 larger (hLimit.1.mem hLarger) with
      ⟨largerValue, hLargerValue, _⟩
    have hInputValueLarger : ℳ.mem inputValue largerValue :=
      hNormal.2.1 input larger
        (hLimit.1.mem hInput) (hLimit.1.mem hLarger)
        hInputLarger inputValue largerValue
        hInputValue hLargerValue
    exact ⟨inputValue, (hUnion inputValue).mpr
      ⟨largerValue,
        (hRange largerValue).mpr
          ⟨larger, hLarger, hLargerValue⟩,
        hInputValueLarger⟩⟩
  · intro predecessor hPredecessor
    rcases (hUnion predecessor).mp hPredecessor with
      ⟨container, hContainerRange, hPredecessorContainer⟩
    rcases (hRange container).mp hContainerRange with
      ⟨input, hInput, hContainerValue⟩
    rcases hLimit.2.2 input hInput with
      ⟨larger, hLarger, hInputLarger⟩
    rcases hNormal.1.1 larger (hLimit.1.mem hLarger) with
      ⟨largerValue, hLargerValue, _⟩
    have hContainerLarger : ℳ.mem container largerValue :=
      hNormal.2.1 input larger
        (hLimit.1.mem hInput) (hLimit.1.mem hLarger)
        hInputLarger container largerValue
        hContainerValue hLargerValue
    exact ⟨container,
      (hUnion container).mpr
        ⟨largerValue,
          (hRange largerValue).mpr
            ⟨larger, hLarger, hLargerValue⟩,
          hContainerLarger⟩,
      hPredecessorContainer⟩

/--
两个正规函数在极限处复合时，按原极限指标收集复合值所得的并，
等于外层函数在内层极限值处的值。
-/
theorem compose_limit_union_eq {ℳ : Structure.{u}}
    (hExt : Extensional ℳ)
    {outer inner : ℳ.Domain → ℳ.Domain → Prop}
    (hOuter : ℳ.IsNormalOrdinalFunction outer)
    (hInner : ℳ.IsNormalOrdinalFunction inner)
    {limit innerLimit outerLimit range composed : ℳ.Domain}
    (hLimit : ℳ.IsLimitOrdinal limit)
    (hInnerLimit : inner limit innerLimit)
    (hOuterLimit : outer innerLimit outerLimit)
    (hRange : ∀ member, ℳ.mem member range ↔
      ∃ index, ℳ.mem index limit ∧
        ∃ innerValue,
          inner index innerValue ∧
            outer innerValue member)
    (hUnion : ℳ.IsUnionOf composed range) :
    composed = outerLimit := by
  have hInnerLimitOrdinal : ℳ.IsLimitOrdinal innerLimit :=
    hInner.limit_value hLimit hInnerLimit
  rcases hInner.2.2 limit innerLimit
      ⟨hLimit, hInnerLimit⟩ with
    ⟨innerRange, hInnerRange, hInnerUnion⟩
  rcases hOuter.2.2 innerLimit outerLimit
      ⟨hInnerLimitOrdinal, hOuterLimit⟩ with
    ⟨outerRange, hOuterRange, hOuterUnion⟩
  apply hExt.eq_of_same_members
  intro value
  constructor
  · intro hValue
    rcases (hUnion value).mp hValue with
      ⟨composedValue, hComposedRange, hValueComposed⟩
    rcases (hRange composedValue).mp hComposedRange with
      ⟨index, hIndex, innerValue, hInnerValue,
        hOuterValue⟩
    rcases hLimit.2.2 index hIndex with
      ⟨larger, hLarger, hIndexLarger⟩
    rcases hInner.1.1 larger (hLimit.1.mem hLarger) with
      ⟨largerValue, hLargerValue, _⟩
    have hInnerValueLarger : ℳ.mem innerValue largerValue :=
      hInner.2.1 index larger
        (hLimit.1.mem hIndex) (hLimit.1.mem hLarger)
        hIndexLarger innerValue largerValue
        hInnerValue hLargerValue
    have hInnerValueLimit : ℳ.mem innerValue innerLimit :=
      (hInnerUnion innerValue).mpr
        ⟨largerValue,
          (hInnerRange largerValue).mpr
            ⟨larger, hLarger, hLargerValue⟩,
          hInnerValueLarger⟩
    exact (hOuterUnion value).mpr
      ⟨composedValue,
        (hOuterRange composedValue).mpr
          ⟨innerValue, hInnerValueLimit, hOuterValue⟩,
        hValueComposed⟩
  · intro hValue
    rcases (hOuterUnion value).mp hValue with
      ⟨outerValue, hOuterRangeValue, hValueOuter⟩
    rcases (hOuterRange outerValue).mp hOuterRangeValue with
      ⟨innerInput, hInnerInputLimit, hOuterValue⟩
    rcases (hInnerUnion innerInput).mp hInnerInputLimit with
      ⟨innerValue, hInnerRangeValue, hInnerInputValue⟩
    rcases (hInnerRange innerValue).mp hInnerRangeValue with
      ⟨index, hIndex, hInnerValue⟩
    rcases hOuter.1.1 innerValue
        (hInner.1.2 index innerValue
          (hLimit.1.mem hIndex) hInnerValue) with
      ⟨composedValue, hComposedValue, _⟩
    have hOuterValueComposed : ℳ.mem outerValue composedValue :=
      hOuter.2.1 innerInput innerValue
        (hInnerLimitOrdinal.1.mem hInnerInputLimit)
        (hInner.1.2 index innerValue
          (hLimit.1.mem hIndex) hInnerValue)
        hInnerInputValue outerValue composedValue
        hOuterValue hComposedValue
    have hComposedOrdinal : ℳ.IsOrdinal composedValue :=
      hOuter.1.2 innerValue composedValue
        (hInner.1.2 index innerValue
          (hLimit.1.mem hIndex) hInnerValue)
        hComposedValue
    exact (hUnion value).mpr
      ⟨composedValue,
        (hRange composedValue).mpr
          ⟨index, hIndex, innerValue,
            hInnerValue, hComposedValue⟩,
        hComposedOrdinal.transitive outerValue
          hOuterValueComposed value hValueOuter⟩

/--
两对正规函数在极限以下逐点复合值相同，则第一对复合极限值的每个成员
也属于第二对复合极限值。
-/
theorem compose_limit_member_of_pointwise_eq
    {ℳ : Structure.{u}}
    {firstOuter firstInner secondOuter secondInner :
      ℳ.Domain → ℳ.Domain → Prop}
    (hFirstOuter : ℳ.IsNormalOrdinalFunction firstOuter)
    (hFirstInner : ℳ.IsNormalOrdinalFunction firstInner)
    (hSecondOuter : ℳ.IsNormalOrdinalFunction secondOuter)
    (hSecondInner : ℳ.IsNormalOrdinalFunction secondInner)
    {limit firstInnerLimit firstLimit
      secondInnerLimit secondLimit : ℳ.Domain}
    (hLimit : ℳ.IsLimitOrdinal limit)
    (hFirstInnerLimit : firstInner limit firstInnerLimit)
    (hFirstLimit : firstOuter firstInnerLimit firstLimit)
    (hSecondInnerLimit : secondInner limit secondInnerLimit)
    (hSecondLimit : secondOuter secondInnerLimit secondLimit)
    (hPointwise : ∀ index, ℳ.mem index limit →
      ∀ firstInnerValue firstValue
        secondInnerValue secondValue,
        firstInner index firstInnerValue →
        firstOuter firstInnerValue firstValue →
        secondInner index secondInnerValue →
        secondOuter secondInnerValue secondValue →
          firstValue = secondValue)
    {value : ℳ.Domain} (hValue : ℳ.mem value firstLimit) :
    ℳ.mem value secondLimit := by
  have hFirstInnerLimitOrdinal : ℳ.IsLimitOrdinal firstInnerLimit :=
    hFirstInner.limit_value hLimit hFirstInnerLimit
  have hSecondInnerLimitOrdinal : ℳ.IsLimitOrdinal secondInnerLimit :=
    hSecondInner.limit_value hLimit hSecondInnerLimit
  rcases hFirstInner.2.2 limit firstInnerLimit
      ⟨hLimit, hFirstInnerLimit⟩ with
    ⟨firstInnerRange, hFirstInnerRange, hFirstInnerUnion⟩
  rcases hFirstOuter.2.2 firstInnerLimit firstLimit
      ⟨hFirstInnerLimitOrdinal, hFirstLimit⟩ with
    ⟨firstOuterRange, hFirstOuterRange, hFirstOuterUnion⟩
  rcases (hFirstOuterUnion value).mp hValue with
    ⟨firstOuterValue, hFirstOuterValueRange,
      hValueFirstOuter⟩
  rcases (hFirstOuterRange firstOuterValue).mp
      hFirstOuterValueRange with
    ⟨firstInnerInput, hFirstInnerInputLimit,
      hFirstOuterValue⟩
  rcases (hFirstInnerUnion firstInnerInput).mp
      hFirstInnerInputLimit with
    ⟨firstInnerValue, hFirstInnerValueRange,
      hFirstInnerInputValue⟩
  rcases (hFirstInnerRange firstInnerValue).mp
      hFirstInnerValueRange with
    ⟨index, hIndex, hFirstInnerValue⟩
  have hFirstInnerValueOrdinal : ℳ.IsOrdinal firstInnerValue :=
    hFirstInner.1.2 index firstInnerValue
      (hLimit.1.mem hIndex) hFirstInnerValue
  rcases hFirstOuter.1.1 firstInnerValue
      hFirstInnerValueOrdinal with
    ⟨firstValue, hFirstValue, _⟩
  have hFirstOuterValueFirst : ℳ.mem firstOuterValue firstValue :=
    hFirstOuter.2.1 firstInnerInput firstInnerValue
      (hFirstInnerLimitOrdinal.1.mem hFirstInnerInputLimit)
      hFirstInnerValueOrdinal hFirstInnerInputValue
      firstOuterValue firstValue hFirstOuterValue hFirstValue
  rcases hSecondInner.1.1 index (hLimit.1.mem hIndex) with
    ⟨secondInnerValue, hSecondInnerValue, _⟩
  have hSecondInnerValueOrdinal : ℳ.IsOrdinal secondInnerValue :=
    hSecondInner.1.2 index secondInnerValue
      (hLimit.1.mem hIndex) hSecondInnerValue
  rcases hSecondOuter.1.1 secondInnerValue
      hSecondInnerValueOrdinal with
    ⟨secondValue, hSecondValue, _⟩
  have hValueEq : firstValue = secondValue :=
    hPointwise index hIndex
      firstInnerValue firstValue
      secondInnerValue secondValue
      hFirstInnerValue hFirstValue
      hSecondInnerValue hSecondValue
  have hSecondInnerValueLimit :
      ℳ.mem secondInnerValue secondInnerLimit :=
    hSecondInner.2.1 index limit
      (hLimit.1.mem hIndex) hLimit.1 hIndex
      secondInnerValue secondInnerLimit
      hSecondInnerValue hSecondInnerLimit
  have hSecondValueLimit : ℳ.mem secondValue secondLimit :=
    hSecondOuter.2.1 secondInnerValue secondInnerLimit
      hSecondInnerValueOrdinal hSecondInnerLimitOrdinal.1
      hSecondInnerValueLimit secondValue secondLimit
      hSecondValue hSecondLimit
  have hFirstValueOrdinal : ℳ.IsOrdinal firstValue :=
    hFirstOuter.1.2 firstInnerValue firstValue
      hFirstInnerValueOrdinal hFirstValue
  have hValueFirst : ℳ.mem value firstValue :=
    hFirstValueOrdinal.transitive firstOuterValue
      hFirstOuterValueFirst value hValueFirstOuter
  have hSecondLimitOrdinal : ℳ.IsOrdinal secondLimit :=
    hSecondOuter.1.2 secondInnerLimit secondLimit
      hSecondInnerLimitOrdinal.1 hSecondLimit
  exact hSecondLimitOrdinal.transitive secondValue
    hSecondValueLimit value (hValueEq ▸ hValueFirst)

/-- 两对正规函数在极限以下逐点复合值相同，则它们的复合极限值相等。 -/
theorem compose_limit_eq_of_pointwise_eq
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {firstOuter firstInner secondOuter secondInner :
      ℳ.Domain → ℳ.Domain → Prop}
    (hFirstOuter : ℳ.IsNormalOrdinalFunction firstOuter)
    (hFirstInner : ℳ.IsNormalOrdinalFunction firstInner)
    (hSecondOuter : ℳ.IsNormalOrdinalFunction secondOuter)
    (hSecondInner : ℳ.IsNormalOrdinalFunction secondInner)
    {limit firstInnerLimit firstLimit
      secondInnerLimit secondLimit : ℳ.Domain}
    (hLimit : ℳ.IsLimitOrdinal limit)
    (hFirstInnerLimit : firstInner limit firstInnerLimit)
    (hFirstLimit : firstOuter firstInnerLimit firstLimit)
    (hSecondInnerLimit : secondInner limit secondInnerLimit)
    (hSecondLimit : secondOuter secondInnerLimit secondLimit)
    (hPointwise : ∀ index, ℳ.mem index limit →
      ∀ firstInnerValue firstValue
        secondInnerValue secondValue,
        firstInner index firstInnerValue →
        firstOuter firstInnerValue firstValue →
        secondInner index secondInnerValue →
        secondOuter secondInnerValue secondValue →
          firstValue = secondValue) :
    firstLimit = secondLimit := by
  apply hExt.eq_of_same_members
  intro value
  constructor
  · exact hFirstOuter.compose_limit_member_of_pointwise_eq
      hFirstInner hSecondOuter hSecondInner
      hLimit hFirstInnerLimit hFirstLimit
      hSecondInnerLimit hSecondLimit hPointwise
  · apply hSecondOuter.compose_limit_member_of_pointwise_eq
      hSecondInner hFirstOuter hFirstInner
      hLimit hSecondInnerLimit hSecondLimit
      hFirstInnerLimit hFirstLimit
    intro index hIndex secondInnerValue secondValue
      firstInnerValue firstValue
      hSecondInnerValue hSecondValue
      hFirstInnerValue hFirstValue
    exact (hPointwise index hIndex
      firstInnerValue firstValue
      secondInnerValue secondValue
      hFirstInnerValue hFirstValue
      hSecondInnerValue hSecondValue).symm

end IsNormalOrdinalFunction

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- 序数值序列公式与纸面语义一致。 -/
theorem satisfies_isOrdinalValuedSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence length : Term depth) :
    satisfies env
        (isOrdinalValuedSequence 𝒞 sequence length) ↔
      ℳ.IsOrdinalValuedSequence 𝕀
        (sequence.eval env) (length.eval env) := by
  simp only [isOrdinalValuedSequence,
    Structure.IsOrdinalValuedSequence, satisfies_conj_iff,
    satisfies_isSequenceOfLength_iff 𝕀 hExt,
    satisfies_forallMem_iff, satisfies_forall_iff,
    satisfies_imp_iff, satisfies_orderedPairMem_iff 𝕀,
    satisfies_isOrdinal_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 不下降序数序列公式与纸面语义一致。 -/
theorem satisfies_isNondecreasingOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence length : Term depth) :
    satisfies env
        (isNondecreasingOrdinalSequence 𝒞 sequence length) ↔
      ℳ.IsNondecreasingOrdinalSequence 𝕀
        (sequence.eval env) (length.eval env) := by
  simp only [isNondecreasingOrdinalSequence,
    Structure.IsNondecreasingOrdinalSequence,
    satisfies_conj_iff,
    satisfies_isOrdinalValuedSequence_iff 𝕀 hExt,
    satisfies_forallMem_iff, satisfies_imp_iff,
    satisfies_forall_iff, satisfies_mem_iff,
    satisfies_orderedPairMem_iff 𝕀,
    lessOrEqual, related_membership,
    satisfies_disj_iff, satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    and_imp]

/-- 严格递增序数序列公式与纸面语义一致。 -/
theorem satisfies_isIncreasingOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence length : Term depth) :
    satisfies env
        (isIncreasingOrdinalSequence 𝒞 sequence length) ↔
      ℳ.IsIncreasingOrdinalSequence 𝕀
        (sequence.eval env) (length.eval env) := by
  simp only [isIncreasingOrdinalSequence,
    Structure.IsIncreasingOrdinalSequence,
    satisfies_conj_iff,
    satisfies_isOrdinalValuedSequence_iff 𝕀 hExt,
    satisfies_forallMem_iff, satisfies_imp_iff,
    satisfies_forall_iff, satisfies_mem_iff,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    and_imp]

/-- 序数序列极限公式与“值域之并”语义一致。 -/
theorem satisfies_isOrdinalSequenceLimit_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (limit sequence length : Term depth) :
    satisfies env
        (isOrdinalSequenceLimit 𝒞 limit sequence length) ↔
      ℳ.IsOrdinalSequenceLimit 𝕀
        (limit.eval env) (sequence.eval env) (length.eval env) := by
  simp only [isOrdinalSequenceLimit,
    Structure.IsOrdinalSequenceLimit, satisfies_conj_iff,
    satisfies_exists_iff,
    satisfies_isOrdinal_iff,
    satisfies_isOrdinalValuedSequence_iff 𝕀 hExt,
    satisfies_isRange_iff 𝕀,
    satisfies_isUnion_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 不下降序数序列极限公式与纸面定义一致。 -/
theorem satisfies_isLimitOfNondecreasingOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (limit sequence length : Term depth) :
    satisfies env
        (isLimitOfNondecreasingOrdinalSequence 𝒞
          limit sequence length) ↔
      ℳ.IsLimitOfNondecreasingOrdinalSequence 𝕀
        (limit.eval env) (sequence.eval env) (length.eval env) := by
  simp only [isLimitOfNondecreasingOrdinalSequence,
    Structure.IsLimitOfNondecreasingOrdinalSequence,
    satisfies_conj_iff,
    satisfies_isNondecreasingOrdinalSequence_iff
      𝕀 hExt,
    satisfies_isOrdinalSequenceLimit_iff 𝕀 hExt]

/-- 连续序数序列公式与纸面语义一致。 -/
theorem satisfies_isContinuousOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence length : Term depth) :
    satisfies env
        (isContinuousOrdinalSequence 𝒞 sequence length) ↔
      ℳ.IsContinuousOrdinalSequence 𝕀
        (sequence.eval env) (length.eval env) := by
  simp only [isContinuousOrdinalSequence,
    Structure.IsContinuousOrdinalSequence,
    satisfies_conj_iff,
    satisfies_isOrdinalValuedSequence_iff 𝕀 hExt,
    satisfies_forallMem_iff, satisfies_forall_iff,
    satisfies_imp_iff, satisfies_exists_iff,
    satisfies_isLimitOrdinal_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_isRestriction_iff 𝕀,
    satisfies_isRange_iff 𝕀,
    satisfies_isUnion_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_weaken]

/-- 正规序列公式与纸面语义一致。 -/
theorem satisfies_isNormalOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence length : Term depth) :
    satisfies env
        (isNormalOrdinalSequence 𝒞 sequence length) ↔
      ℳ.IsNormalOrdinalSequence 𝕀
        (sequence.eval env) (length.eval env) := by
  simp only [isNormalOrdinalSequence,
    Structure.IsNormalOrdinalSequence, satisfies_conj_iff,
    satisfies_isIncreasingOrdinalSequence_iff 𝕀 hExt,
    satisfies_isContinuousOrdinalSequence_iff 𝕀 hExt]

/-- 序数类函数公式与纸面语义一致。 -/
theorem satisfies_isClassFunctionOnOrdinals_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) :
    satisfies env
        (isClassFunctionOnOrdinals function parameters) ↔
      ℳ.IsClassFunctionOnOrdinals
        (function.denote (parameters.evalEnv env)) := by
  simp only [isClassFunctionOnOrdinals,
    Structure.IsClassFunctionOnOrdinals,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isOrdinal_iff, satisfies_related_iff,
    satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push,
    Definitional.Term.eval_newest,
    TermVector.evalEnv_weaken]
  constructor
  · intro h α hα
    rcases h α hα with
      ⟨value, hValue, hUnique⟩
    exact
      ⟨value, hValue, fun other hOther =>
        (hUnique other hOther).symm⟩
  · intro h α hα
    rcases h α hα with
      ⟨value, hValue, hUnique⟩
    exact
      ⟨value, hValue, fun other hOther =>
        (hUnique other hOther).symm⟩

/-- 序数值类函数公式与纸面语义一致。 -/
theorem satisfies_isOrdinalClassFunction_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) :
    satisfies env
        (isOrdinalClassFunction function parameters) ↔
      ℳ.IsOrdinalClassFunction
        (function.denote (parameters.evalEnv env)) := by
  simp only [isOrdinalClassFunction,
    Structure.IsOrdinalClassFunction, satisfies_conj_iff,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_isClassFunctionOnOrdinals_iff hExt,
    satisfies_isOrdinal_iff, satisfies_related_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest,
    TermVector.evalEnv_weaken, and_imp]

/-- 序数类上的严格递增公式与纸面语义一致。 -/
theorem satisfies_isIncreasingOnOrdinals_iff
    {ℳ : Structure.{u}}
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) :
    satisfies env
        (isIncreasingOnOrdinals function parameters) ↔
      ℳ.IsIncreasingOnOrdinals
        (function.denote (parameters.evalEnv env)) := by
  simp only [isIncreasingOnOrdinals,
    Structure.IsIncreasingOnOrdinals,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_conj_iff, satisfies_isOrdinal_iff,
    satisfies_related_iff, satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest,
    TermVector.evalEnv_weaken, and_imp]

/-- 序数类上的连续公式与纸面语义一致。 -/
theorem satisfies_isContinuousOnOrdinals_iff
    {ℳ : Structure.{u}}
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) :
    satisfies env
        (isContinuousOnOrdinals function parameters) ↔
      ℳ.IsContinuousOnOrdinals
        (function.denote (parameters.evalEnv env)) := by
  simp only [isContinuousOnOrdinals,
    Structure.IsContinuousOnOrdinals,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_conj_iff, satisfies_exists_iff,
    satisfies_iff_iff, satisfies_mem_iff,
    satisfies_existsMem_iff,
    satisfies_isLimitOrdinal_iff, satisfies_related_iff,
    satisfies_isUnion_iff]
  simp only [Definitional.Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    TermVector.evalEnv_weaken]

/-- 正规序数类函数公式与纸面语义一致。 -/
theorem satisfies_isNormalOrdinalFunction_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth) :
    satisfies env
        (isNormalOrdinalFunction function parameters) ↔
      ℳ.IsNormalOrdinalFunction
        (function.denote (parameters.evalEnv env)) := by
  simp only [isNormalOrdinalFunction,
    Structure.IsNormalOrdinalFunction, satisfies_conj_iff,
    satisfies_isOrdinalClassFunction_iff hExt,
    satisfies_isIncreasingOnOrdinals_iff,
    satisfies_isContinuousOnOrdinals_iff]

end Formula
end Project
end Definitional

end SetTheory
end YesMetaZFC
