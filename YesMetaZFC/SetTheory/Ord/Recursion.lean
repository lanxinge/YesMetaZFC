import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.Ord.Induction
import YesMetaZFC.SetTheory.Replacement
import YesMetaZFC.SetTheory.SetConstruction

/-!
# 超限递归

本文件先把集合编码递归序列整理成纸面语义，再沿序数归纳证明递归序列的唯一性与
存在性。数学构造、见证、归纳阶段及简单结构组装均保持显式。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `sequence` 是定义域恰为序数 `length` 的集合编码函数。 -/
def IsSequenceOfLength {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence length : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal length ∧
    ℳ.IsSetFunction 𝕀 sequence ∧
      ℳ.IsDomainOf 𝕀 length sequence

/-- `sequence` 是长度为 `length`、取值于 `target` 的集合编码函数。 -/
def IsSequenceIn {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence length target : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal length ∧
    ℳ.IsSetFunctionFromTo 𝕀 sequence length target

/-- `sequence` 取值于 `target`，且长度严格小于序数 `bound`。 -/
def IsSequenceInBelow {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence bound target : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal bound ∧
    ∃ length, ℳ.mem length bound ∧
      ℳ.IsSequenceIn 𝕀 sequence length target

/-- `sequence` 是某个序数长度的集合编码函数。 -/
def IsTransfiniteSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence : ℳ.Domain) : Prop :=
  ∃ length, ℳ.IsSequenceOfLength 𝕀 sequence length

/-- `sequence` 在每个位置都由其此前限制经 `operator` 给出。 -/
def ObeysRecursion {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop)
    (sequence length : ℳ.Domain) : Prop :=
  ∀ index, ℳ.mem index length →
    ∀ value, ℳ.PairMember 𝕀 index value sequence →
      ∃ restriction,
        ℳ.IsRestrictionOf 𝕀 restriction sequence index ∧
          operator restriction value

/-- `sequence` 是长度为 `length`、服从 `operator` 的递归序列。 -/
def IsRecursiveSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop)
    (sequence length : ℳ.Domain) : Prop :=
  ℳ.IsSequenceOfLength 𝕀 sequence length ∧
    ℳ.ObeysRecursion 𝕀 operator sequence length

/-- `sequence` 是长度为 `length`、取值于 `target` 的递归序列。 -/
def IsRecursiveSequenceIn {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop)
    (sequence length target : ℳ.Domain) : Prop :=
  ℳ.IsSequenceIn 𝕀 sequence length target ∧
    ℳ.ObeysRecursion 𝕀 operator sequence length

/-- `value` 是由 `target` 值递归序列产生且仍属于 `target` 的递归值。 -/
def IsRecursionValueIn {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop)
    (α value target : ℳ.Domain) : Prop :=
  ∃ sequence,
    ℳ.IsRecursiveSequenceIn 𝕀
        operator sequence α target ∧
      operator sequence value ∧
        ℳ.mem value target

/-- `value` 是在 `α` 处由超限递归算子给出的值。 -/
def IsRecursionValue {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop)
    (α value : ℳ.Domain) : Prop :=
  ∃ sequence,
    ℳ.IsRecursiveSequence 𝕀 operator sequence α ∧
      operator sequence value

/-- `operator` 在所有超限序列上全定义且单值。 -/
def IsClassFunctionOnTransfiniteSequences {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop) : Prop :=
  ∀ sequence, ℳ.IsTransfiniteSequence 𝕀 sequence →
    ∃ value, operator sequence value ∧
      ∀ other, operator sequence other → other = value

/-- `operator` 在所有长度小于 `bound` 的 `target` 值序列上全定义且单值。 -/
def IsClassFunctionOnSequencesInBelow {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop)
    (bound target : ℳ.Domain) : Prop :=
  ∀ sequence,
    ℳ.IsSequenceInBelow 𝕀 sequence bound target →
      ∃ value, operator sequence value ∧
        ∀ other, operator sequence other → other = value

/-- `operator` 把长度小于 `bound` 的 `target` 值序列仍映入 `target`。 -/
def MapsSequencesInBelowInto {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (operator : ℳ.Domain → ℳ.Domain → Prop)
    (bound target : ℳ.Domain) : Prop :=
  ∀ sequence value,
    ℳ.IsSequenceInBelow 𝕀 sequence bound target →
      operator sequence value →
        ℳ.mem value target

/-- `function` 在所有序数上全定义且单值。 -/
def IsClassFunctionOnOrdinals (ℳ : Structure.{u})
    (function : ℳ.Domain → ℳ.Domain → Prop) : Prop :=
  ∀ α, ℳ.IsOrdinal α →
    ∃ value, function α value ∧
      ∀ other, function α other → other = value

namespace IsSequenceOfLength

/-- 空对象同时作为空函数图与空定义域时给出零长度序列。 -/
theorem empty {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {empty : ℳ.Domain} (hEmpty : ∀ value, ¬ ℳ.mem value empty) :
    ℳ.IsSequenceOfLength 𝕀 empty empty := by
  refine ⟨Structure.IsOrdinal.of_no_members hEmpty, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro pair hPair
      exact False.elim (hEmpty pair hPair)
    · intro input first _ hFirst
      rcases hFirst with ⟨pair, _, hPair⟩
      exact False.elim (hEmpty pair hPair)
  · intro input
    constructor
    · intro hInput
      exact False.elim (hEmpty input hInput)
    · rintro ⟨output, pair, _, hPair⟩
      exact False.elim (hEmpty pair hPair)

/--
向长度为 `length` 的序列末尾追加一个值。

结果序列的定义域是 `length` 的给定后继；其坐标恰为旧坐标，或新末坐标
`(length, value)`。
-/
theorem exists_append {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sequence length successor value : ℳ.Domain}
    (hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length)
    (hSuccessorOrdinal : ℳ.IsOrdinal successor)
    (hSuccessor : ℳ.SuccessorOf successor length) :
    ∃ appended,
      ℳ.IsSequenceOfLength 𝕀 appended successor ∧
        ∀ input output,
          ℳ.PairMember 𝕀 input output appended ↔
            ℳ.PairMember 𝕀 input output sequence ∨
              (input = length ∧ output = value) := by
  rcases 𝕀.total length value with
    ⟨lastPair, hLastPair⟩
  rcases KP.exists_insert hKP sequence lastPair with
    ⟨appended, hAppended⟩
  have hPairMember (input output : ℳ.Domain) :
      ℳ.PairMember 𝕀 input output appended ↔
        ℳ.PairMember 𝕀 input output sequence ∨
          (input = length ∧ output = value) := by
    constructor
    · rintro ⟨pair, hPairCode, hPairAppended⟩
      rcases (hAppended pair).mp hPairAppended with
        hPairSequence | hPairEq
      · exact Or.inl ⟨pair, hPairCode, hPairSequence⟩
      · subst pair
        exact Or.inr (𝕀.injective hPairCode hLastPair)
    · rintro (hPairSequence | ⟨rfl, rfl⟩)
      · rcases hPairSequence with
          ⟨pair, hPairCode, hPairSequence⟩
        exact
          ⟨pair, hPairCode,
            (hAppended pair).mpr (Or.inl hPairSequence)⟩
      · exact
          ⟨lastPair, hLastPair,
            (hAppended lastPair).mpr (Or.inr rfl)⟩
  have hRelation : ℳ.IsSetRelation 𝕀 appended := by
    intro pair hPairAppended
    rcases (hAppended pair).mp hPairAppended with
      hPairSequence | hPairEq
    · exact hSequence.2.1.1 pair hPairSequence
    · subst pair
      exact ⟨length, value, hLastPair⟩
  have hFunction : ℳ.IsSetFunction 𝕀 appended := by
    refine ⟨hRelation, ?_⟩
    intro input first second hFirst hSecond
    rcases (hPairMember input first).mp hFirst with
      hFirstOld | ⟨hInputLength, hFirstValue⟩ <;>
      rcases (hPairMember input second).mp hSecond with
        hSecondOld | ⟨hInputLength', hSecondValue⟩
    · exact hSequence.2.1.2 input first second hFirstOld hSecondOld
    · subst input
      have hSelf : ℳ.mem length length :=
        (hSequence.2.2 length).mpr ⟨first, hFirstOld⟩
      exact False.elim <|
        hSequence.1.wellOrder.linear.irrefl length hSelf hSelf
    · subst input
      have hSelf : ℳ.mem length length :=
        (hSequence.2.2 length).mpr ⟨second, hSecondOld⟩
      exact False.elim <|
        hSequence.1.wellOrder.linear.irrefl length hSelf hSelf
    · exact hFirstValue.trans hSecondValue.symm
  have hDomain : ℳ.IsDomainOf 𝕀 successor appended := by
    intro input
    constructor
    · intro hInput
      rcases (hSuccessor input).mp hInput with
        hInputLength | hInputSame
      · rcases (hSequence.2.2 input).mp hInputLength with
          ⟨output, hOutput⟩
        exact ⟨output, (hPairMember input output).mpr (Or.inl hOutput)⟩
      · have hInputEq :=
          hKP.1.eq_of_same_members input length hInputSame
        subst input
        exact
          ⟨value,
            (hPairMember length value).mpr
              (Or.inr ⟨rfl, rfl⟩)⟩
    · rintro ⟨output, hOutput⟩
      rcases (hPairMember input output).mp hOutput with
        hOutputOld | ⟨hInputLength, _⟩
      · exact (hSuccessor input).mpr <| Or.inl <|
          (hSequence.2.2 input).mpr ⟨output, hOutputOld⟩
      · subst input
        exact (hSuccessor length).mpr <|
          Or.inr (fun _ => Iff.rfl)
  exact
    ⟨appended, ⟨hSuccessorOrdinal, hFunction, hDomain⟩,
      hPairMember⟩

/-- 序列限制到任意较小索引后，定义域恰为该索引。 -/
theorem restriction {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length index restricted : ℳ.Domain}
    (hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length)
    (hIndex : ℳ.mem index length)
    (hRestriction :
      ℳ.IsRestrictionOf 𝕀 restricted sequence index) :
    ℳ.IsSequenceOfLength 𝕀 restricted index := by
  prove_auto

/--
两个后继长度序列若前缀限制相等且最后一项相同，则整个函数图相等。
-/
theorem eq_of_restriction_eq_of_last
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {first second firstLength secondLength previous
      firstRestriction secondRestriction lastValue : ℳ.Domain}
    (hFirst :
      ℳ.IsSequenceOfLength 𝕀 first firstLength)
    (hSecond :
      ℳ.IsSequenceOfLength 𝕀 second secondLength)
    (hFirstLength : ℳ.SuccessorOf firstLength previous)
    (hSecondLength : ℳ.SuccessorOf secondLength previous)
    (hFirstRestriction :
      ℳ.IsRestrictionOf 𝕀
        firstRestriction first previous)
    (hSecondRestriction :
      ℳ.IsRestrictionOf 𝕀
        secondRestriction second previous)
    (hRestrictionEq : firstRestriction = secondRestriction)
    (hFirstLast :
      ℳ.PairMember 𝕀 previous lastValue first)
    (hSecondLast :
      ℳ.PairMember 𝕀 previous lastValue second) :
    first = second := by
  have hLengthEq : firstLength = secondLength := by
    apply hExt.eq_of_same_members
    intro member
    rw [hFirstLength member, hSecondLength member]
  subst secondLength
  apply hFirst.2.1.1.eq_of_pairMember_iff hExt hSecond.2.1.1
  intro input output
  have transfer
      {left right leftRestriction rightRestriction : ℳ.Domain}
      (hLeft :
        ℳ.IsSequenceOfLength 𝕀 left firstLength)
      (hRight :
        ℳ.IsSequenceOfLength 𝕀 right firstLength)
      (hLeftRestriction :
        ℳ.IsRestrictionOf 𝕀
          leftRestriction left previous)
      (hRightRestriction :
        ℳ.IsRestrictionOf 𝕀
          rightRestriction right previous)
      (hRestrictionEq : leftRestriction = rightRestriction)
      (hLeftLast :
        ℳ.PairMember 𝕀 previous lastValue left)
      (hRightLast :
        ℳ.PairMember 𝕀 previous lastValue right)
      (hValue :
        ℳ.PairMember 𝕀 input output left) :
      ℳ.PairMember 𝕀 input output right := by
    have hInputLength :
        ℳ.mem input firstLength :=
      (hLeft.2.2 input).mpr ⟨output, hValue⟩
    rcases (hFirstLength input).mp hInputLength with
      hInputPrevious | hInputSame
    · have hRestricted :
          ℳ.PairMember 𝕀
            input output leftRestriction :=
        (hLeftRestriction.2 input output).mpr
          ⟨hInputPrevious, hValue⟩
      subst rightRestriction
      exact
        ((hRightRestriction.2 input output).mp hRestricted).2
    · have hInputEq :=
        hExt.eq_of_same_members input previous hInputSame
      subst input
      have hOutputEq :=
        hLeft.2.1.2 previous output lastValue
          hValue hLeftLast
      subst output
      exact hRightLast
  constructor
  · exact transfer hFirst hSecond
      hFirstRestriction hSecondRestriction hRestrictionEq
      hFirstLast hSecondLast
  · exact transfer hSecond hFirst
      hSecondRestriction hFirstRestriction hRestrictionEq.symm
      hSecondLast hFirstLast

end IsSequenceOfLength

namespace IsRecursiveSequence

/-- 递归序列限制到任意较小序数后仍是递归序列。 -/
theorem restriction {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    {sequence length index restricted : ℳ.Domain}
    (hSequence :
      ℳ.IsRecursiveSequence 𝕀 operator sequence length)
    (hIndex : ℳ.mem index length)
    (hRestriction :
      ℳ.IsRestrictionOf 𝕀 restricted sequence index) :
    ℳ.IsRecursiveSequence 𝕀 operator restricted index := by
  have hIndexOrdinal : ℳ.IsOrdinal index :=
    Structure.IsOrdinal.mem hSequence.1.1 hIndex
  have hRestrictedFunction : ℳ.IsSetFunction 𝕀 restricted :=
    hRestriction.isSetFunction hSequence.1.2.1
  have hRestrictedDomain : ℳ.IsDomainOf 𝕀 index restricted :=
    hRestriction.isDomainOf hSequence.1.2.2
      (hSequence.1.1.transitive index hIndex)
  have hRestrictedRecursion :
      ℳ.ObeysRecursion 𝕀 operator restricted index := by
    intro predecessor hPredecessor value hValue
    have hPredecessorLength :
        ℳ.mem predecessor length :=
      hSequence.1.1.transitive index hIndex predecessor hPredecessor
    have hValueSequence :
        ℳ.PairMember 𝕀 predecessor value sequence :=
      ((hRestriction.2 predecessor value).mp hValue).2
    rcases hSequence.2 predecessor hPredecessorLength value
        hValueSequence with
      ⟨prior, hPrior, hOperator⟩
    have hPredecessorSubset :
        ∀ member, ℳ.mem member predecessor → ℳ.mem member index :=
      hIndexOrdinal.transitive predecessor hPredecessor
    exact ⟨prior, hRestriction.trans hPrior hPredecessorSubset,
      hOperator⟩
  exact
    ⟨⟨hIndexOrdinal, hRestrictedFunction, hRestrictedDomain⟩,
      hRestrictedRecursion⟩

/-- 递归序列在某位置的函数值正是该位置的超限递归值。 -/
theorem recursionValue_of_pairMember {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    {sequence length index value : ℳ.Domain}
    (hSequence :
      ℳ.IsRecursiveSequence 𝕀 operator sequence length)
    (hIndex : ℳ.mem index length)
    (hValue :
      ℳ.PairMember 𝕀 index value sequence) :
    ℳ.IsRecursionValue 𝕀 operator index value := by
  rcases hSequence.2 index hIndex value hValue with
    ⟨restricted, hRestriction, hOperator⟩
  exact
    ⟨restricted, hSequence.restriction hIndex hRestriction,
      hOperator⟩

/--
若当前长度以下的递归序列都唯一，则当前长度的递归序列也唯一。

证明逐点比较两个函数图；每个位置的两个前段限制由归纳假设相等，再由递归算子的
单值性得到该位置的值相等。
-/
theorem eq_of_predecessor_uniqueness {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    (hExt : Extensional ℳ)
    (hOperator :
      ℳ.IsClassFunctionOnTransfiniteSequences 𝕀 operator)
    {α left right : ℳ.Domain}
    (hLeft :
      ℳ.IsRecursiveSequence 𝕀 operator left α)
    (hRight :
      ℳ.IsRecursiveSequence 𝕀 operator right α)
    (hPrevious : ∀ index, ℳ.mem index α →
      ∀ first second,
        ℳ.IsRecursiveSequence 𝕀 operator first index →
        ℳ.IsRecursiveSequence 𝕀 operator second index →
        first = second) :
    left = right := by
  apply hLeft.1.2.1.1.eq_of_pairMember_iff hExt hRight.1.2.1.1
  intro index value
  have transfer {first second : ℳ.Domain}
      (hFirst :
        ℳ.IsRecursiveSequence 𝕀 operator first α)
      (hSecond :
        ℳ.IsRecursiveSequence 𝕀 operator second α)
      (hValueFirst :
        ℳ.PairMember 𝕀 index value first) :
      ℳ.PairMember 𝕀 index value second := by
    have hIndex : ℳ.mem index α :=
      (hFirst.1.2.2 index).mpr ⟨value, hValueFirst⟩
    rcases (hSecond.1.2.2 index).mp hIndex with
      ⟨secondValue, hValueSecond⟩
    rcases hFirst.2 index hIndex value hValueFirst with
      ⟨firstRestriction, hFirstRestriction, hFirstOperator⟩
    rcases hSecond.2 index hIndex secondValue hValueSecond with
      ⟨secondRestriction, hSecondRestriction, hSecondOperator⟩
    have hFirstRecursive :=
      hFirst.restriction hIndex hFirstRestriction
    have hSecondRecursive :=
      hSecond.restriction hIndex hSecondRestriction
    have hRestrictionEq :=
      hPrevious index hIndex firstRestriction secondRestriction
        hFirstRecursive hSecondRecursive
    subst secondRestriction
    rcases hOperator firstRestriction
        ⟨index, hFirstRecursive.1⟩ with
      ⟨selected, _, hUnique⟩
    have hValueEq : value = secondValue := by
      rw [hUnique value hFirstOperator,
        hUnique secondValue hSecondOperator]
    simpa [hValueEq] using hValueSecond
  exact ⟨transfer hLeft hRight, transfer hRight hLeft⟩

end IsRecursiveSequence

namespace IsRecursiveSequenceIn

/-- 忘掉目标集约束后，仍得到普通递归序列。 -/
theorem toRecursiveSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    {sequence length target : ℳ.Domain}
    (hSequence :
      ℳ.IsRecursiveSequenceIn 𝕀
        operator sequence length target) :
    ℳ.IsRecursiveSequence 𝕀 operator sequence length := by
  prove_auto

/-- 固定目标集值递归序列限制到较小序数后仍取值于同一目标集。 -/
theorem restriction {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    {sequence length target index restricted : ℳ.Domain}
    (hSequence :
      ℳ.IsRecursiveSequenceIn 𝕀
        operator sequence length target)
    (hIndex : ℳ.mem index length)
    (hRestriction :
      ℳ.IsRestrictionOf 𝕀 restricted sequence index) :
    ℳ.IsRecursiveSequenceIn 𝕀
      operator restricted index target := by
  have hRecursive :=
    hSequence.toRecursiveSequence.restriction hIndex hRestriction
  have hInputLength :
      ∀ input, ℳ.mem input index → ℳ.mem input length :=
    hSequence.1.1.transitive index hIndex
  have hIntoTarget :
      ∀ input, ℳ.mem input index →
        ∃ output, ℳ.mem output target ∧
          ℳ.PairMember 𝕀 input output restricted := by
    intro input hInput
    rcases hSequence.1.2.2.2 input (hInputLength input hInput) with
      ⟨output, hOutputTarget, hOutputSequence⟩
    exact
      ⟨output, hOutputTarget,
        (hRestriction.2 input output).mpr
          ⟨hInput, hOutputSequence⟩⟩
  exact
    ⟨⟨hRecursive.1.1,
        ⟨hRecursive.1.2.1, hRecursive.1.2.2, hIntoTarget⟩⟩,
      hRecursive.2⟩

/-- 固定目标集值递归序列在某位置的值是同一目标集内的递归值。 -/
theorem recursionValue_of_pairMember {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    {sequence length target index value : ℳ.Domain}
    (hSequence :
      ℳ.IsRecursiveSequenceIn 𝕀
        operator sequence length target)
    (hIndex : ℳ.mem index length)
    (hValue :
      ℳ.PairMember 𝕀 index value sequence) :
    ℳ.IsRecursionValueIn 𝕀
      operator index value target := by
  rcases hSequence.2 index hIndex value hValue with
    ⟨restricted, hRestriction, hOperator⟩
  rcases hSequence.1.2.2.2 index hIndex with
    ⟨selected, hSelectedTarget, hSelected⟩
  have hValueEq :=
    hSequence.1.2.1.2 index value selected hValue hSelected
  subst selected
  exact
    ⟨restricted,
      hSequence.restriction hIndex hRestriction,
      hOperator, hSelectedTarget⟩

/--
在固定上界与目标集内，若所有真前段递归序列唯一，则当前长度的递归序列也唯一。
-/
theorem eq_of_predecessor_uniqueness {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    (hExt : Extensional ℳ)
    {bound target current left right : ℳ.Domain}
    (hBound : ℳ.IsOrdinal bound)
    (hCurrentWithin : current = bound ∨ ℳ.mem current bound)
    (hOperator :
      ℳ.IsClassFunctionOnSequencesInBelow 𝕀
        operator bound target)
    (hLeft :
      ℳ.IsRecursiveSequenceIn 𝕀
        operator left current target)
    (hRight :
      ℳ.IsRecursiveSequenceIn 𝕀
        operator right current target)
    (hPrevious : ∀ index, ℳ.mem index current →
      ∀ first second,
        ℳ.IsRecursiveSequenceIn 𝕀
            operator first index target →
          ℳ.IsRecursiveSequenceIn 𝕀
            operator second index target →
          first = second) :
    left = right := by
  apply hLeft.1.2.1.1.eq_of_pairMember_iff hExt hRight.1.2.1.1
  intro index value
  have hIndexBound (hIndex : ℳ.mem index current) :
      ℳ.mem index bound := by
    rcases hCurrentWithin with hEq | hCurrent
    · simpa [hEq] using hIndex
    · exact hBound.transitive current hCurrent index hIndex
  have transfer {first second : ℳ.Domain}
      (hFirst :
        ℳ.IsRecursiveSequenceIn 𝕀
          operator first current target)
      (hSecond :
        ℳ.IsRecursiveSequenceIn 𝕀
          operator second current target)
      (hValueFirst :
        ℳ.PairMember 𝕀 index value first) :
      ℳ.PairMember 𝕀 index value second := by
    have hIndex : ℳ.mem index current :=
      (hFirst.1.2.2.1 index).mpr ⟨value, hValueFirst⟩
    rcases (hSecond.1.2.2.1 index).mp hIndex with
      ⟨secondValue, hValueSecond⟩
    rcases hFirst.2 index hIndex value hValueFirst with
      ⟨firstRestriction, hFirstRestriction, hFirstOperator⟩
    rcases hSecond.2 index hIndex secondValue hValueSecond with
      ⟨secondRestriction, hSecondRestriction, hSecondOperator⟩
    have hFirstRecursive :=
      hFirst.restriction hIndex hFirstRestriction
    have hSecondRecursive :=
      hSecond.restriction hIndex hSecondRestriction
    have hRestrictionEq :=
      hPrevious index hIndex firstRestriction secondRestriction
        hFirstRecursive hSecondRecursive
    subst secondRestriction
    rcases hOperator firstRestriction
        ⟨hBound, index, hIndexBound hIndex, hFirstRecursive.1⟩ with
      ⟨selected, _, hUnique⟩
    have hValueEq : value = secondValue := by
      rw [hUnique value hFirstOperator,
        hUnique secondValue hSecondOperator]
    simpa [hValueEq] using hValueSecond
  exact ⟨transfer hLeft hRight, transfer hRight hLeft⟩

end IsRecursiveSequenceIn
end Structure

namespace Definitional
namespace Project
namespace Formula

/-- 长度固定的序列公式与纸面语义一致。 -/
theorem satisfies_isSequenceOfLength_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence length : Term depth) :
    satisfies env (isSequenceOfLength 𝒞 sequence length) ↔
      ℳ.IsSequenceOfLength 𝕀
        (sequence.eval env) (length.eval env) := by
  simp only [isSequenceOfLength, Structure.IsSequenceOfLength,
    satisfies_conj_iff, satisfies_isOrdinal_iff,
    satisfies_isFunction_iff 𝕀 hExt,
    satisfies_isDomain_iff 𝕀]

/-- 固定目标集值序列公式与纸面语义一致。 -/
theorem satisfies_isSequenceIn_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence length target : Term depth) :
    satisfies env
        (isSequenceIn 𝒞 sequence length target) ↔
      ℳ.IsSequenceIn 𝕀
        (sequence.eval env) (length.eval env) (target.eval env) := by
  simp only [isSequenceIn, Structure.IsSequenceIn,
    satisfies_conj_iff, satisfies_isOrdinal_iff,
    satisfies_isFunctionFromTo_iff 𝕀 hExt]

/-- 有界固定目标集值序列公式与纸面语义一致。 -/
theorem satisfies_isSequenceInBelow_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence bound target : Term depth) :
    satisfies env
        (isSequenceInBelow 𝒞 sequence bound target) ↔
      ℳ.IsSequenceInBelow 𝕀
        (sequence.eval env) (bound.eval env) (target.eval env) := by
  simp only [isSequenceInBelow, Structure.IsSequenceInBelow,
    satisfies_conj_iff, satisfies_isOrdinal_iff]
  constructor
  · rintro ⟨hBound, hExists⟩
    rw [satisfies_existsMem_iff] at hExists
    rcases hExists with
      ⟨length, hLength, hSequence⟩
    refine ⟨hBound, length, hLength, ?_⟩
    simpa using
      (satisfies_isSequenceIn_iff 𝕀 hExt
        (env.push length) sequence.weaken Term.newest
        target.weaken).mp hSequence
  · rintro ⟨hBound, length, hLength, hSequence⟩
    refine ⟨hBound, ?_⟩
    rw [satisfies_existsMem_iff]
    refine ⟨length, hLength, ?_⟩
    apply
      (satisfies_isSequenceIn_iff 𝕀 hExt
        (env.push length) sequence.weaken Term.newest
        target.weaken).mpr
    simpa using hSequence

/-- 超限序列公式与纸面语义一致。 -/
theorem satisfies_isTransfiniteSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (sequence : Term depth) :
    satisfies env (isTransfiniteSequence 𝒞 sequence) ↔
      ℳ.IsTransfiniteSequence 𝕀 (sequence.eval env) := by
  simp only [isTransfiniteSequence, Structure.IsTransfiniteSequence,
    satisfies_exists_iff, satisfies_isSequenceOfLength_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 递归方程公式与纸面逐位置语义一致。 -/
theorem satisfies_obeysRecursion_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (sequence length : Term depth) :
    satisfies env
        (obeysRecursion 𝒞 operator parameters sequence length) ↔
      ℳ.ObeysRecursion 𝕀
        (operator.denote (parameters.evalEnv env))
        (sequence.eval env) (length.eval env) := by
  unfold obeysRecursion Structure.ObeysRecursion
  rw [satisfies_forallMem_iff]
  simp only [satisfies_forall_iff, satisfies_imp_iff,
    satisfies_exists_iff, satisfies_conj_iff]
  constructor
  · intro h index hIndex value hValue
    have hValueFormula :
        satisfies ((env.push index).push value)
          (orderedPairMem 𝒞 (.bound 1) (.bound 0)
            sequence.weaken.weaken) := by
      rw [satisfies_orderedPairMem_iff 𝕀]
      simpa using hValue
    rcases h index hIndex value hValueFormula with
      ⟨restriction, hRestriction, hOperator⟩
    refine ⟨restriction, ?_, ?_⟩
    · have hRestriction' :=
        (satisfies_isRestriction_iff 𝕀
          (((env.push index).push value).push restriction)
          Term.newest sequence.weaken.weaken.weaken
          (.bound 2)).mp hRestriction
      simpa using hRestriction'
    · have hOperator' :=
        (satisfies_related_iff
          (((env.push index).push value).push restriction)
          operator parameters.weaken.weaken.weaken
          Term.newest (.bound 1)).mp hOperator
      simpa using hOperator'
  · intro h index hIndex value hValue
    have hValue' :=
      (satisfies_orderedPairMem_iff 𝕀
        ((env.push index).push value) (.bound 1) (.bound 0)
        sequence.weaken.weaken).mp hValue
    rcases h index hIndex value (by simpa using hValue') with
      ⟨restriction, hRestriction, hOperator⟩
    refine ⟨restriction, ?_, ?_⟩
    · apply
        (satisfies_isRestriction_iff 𝕀
          (((env.push index).push value).push restriction)
          Term.newest sequence.weaken.weaken.weaken
          (.bound 2)).mpr
      simpa using hRestriction
    · apply
        (satisfies_related_iff
          (((env.push index).push value).push restriction)
          operator parameters.weaken.weaken.weaken
          Term.newest (.bound 1)).mpr
      simpa using hOperator

/-- 递归序列公式与纸面语义一致。 -/
theorem satisfies_isRecursiveSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (sequence length : Term depth) :
    satisfies env
        (isRecursiveSequence 𝒞 operator parameters
          sequence length) ↔
      ℳ.IsRecursiveSequence 𝕀
        (operator.denote (parameters.evalEnv env))
        (sequence.eval env) (length.eval env) := by
  simp only [isRecursiveSequence, Structure.IsRecursiveSequence,
    satisfies_conj_iff, satisfies_isSequenceOfLength_iff 𝕀 hExt,
    satisfies_obeysRecursion_iff 𝕀]

/-- 固定目标集值递归序列公式与纸面语义一致。 -/
theorem satisfies_isRecursiveSequenceIn_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (sequence length target : Term depth) :
    satisfies env
        (isRecursiveSequenceIn 𝒞 operator parameters
          sequence length target) ↔
      ℳ.IsRecursiveSequenceIn 𝕀
        (operator.denote (parameters.evalEnv env))
        (sequence.eval env) (length.eval env) (target.eval env) := by
  simp only [isRecursiveSequenceIn, Structure.IsRecursiveSequenceIn,
    satisfies_conj_iff, satisfies_isSequenceIn_iff 𝕀 hExt,
    satisfies_obeysRecursion_iff 𝕀]

/-- 固定目标集内递归值公式与纸面语义一致。 -/
theorem satisfies_isRecursionValueIn_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (α value target : Term depth) :
    satisfies env
        (isRecursionValueIn 𝒞 operator parameters
          α value target) ↔
      ℳ.IsRecursionValueIn 𝕀
        (operator.denote (parameters.evalEnv env))
        (α.eval env) (value.eval env) (target.eval env) := by
  simp only [isRecursionValueIn, Structure.IsRecursionValueIn,
    satisfies_exists_iff, satisfies_conj_iff, satisfies_mem_iff,
    satisfies_isRecursiveSequenceIn_iff 𝕀 hExt,
    satisfies_related_iff, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken, TermVector.evalEnv_weaken]

/-- 超限递归值公式与纸面语义一致。 -/
theorem satisfies_isRecursionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (α value : Term depth) :
    satisfies env
        (isRecursionValue 𝒞 operator parameters α value) ↔
      ℳ.IsRecursionValue 𝕀
        (operator.denote (parameters.evalEnv env))
        (α.eval env) (value.eval env) := by
  simp only [isRecursionValue, Structure.IsRecursionValue,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isRecursiveSequence_iff 𝕀 hExt,
    satisfies_related_iff, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken, TermVector.evalEnv_weaken]

/-- 固定目标集值递归序列存在性模式的纸面语义。 -/
theorem satisfies_recursiveSequenceInExistence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : BinarySchema parameterCount)
    (target α : ℳ.Domain) :
    satisfies ((env.push target).push α)
        (operator.recursiveSequenceInExistence 𝒞).body ↔
      ∃ sequence,
        ℳ.IsRecursiveSequenceIn 𝕀
          (operator.denote env) sequence α target := by
  simp only [BinarySchema.recursiveSequenceInExistence,
    satisfies_exists_iff,
    satisfies_isRecursiveSequenceIn_iff 𝕀 hExt,
    TermVector.evalEnv_boundParameters_three,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_newest]

/-- 固定目标集值递归序列唯一性模式的纸面语义。 -/
theorem satisfies_recursiveSequenceInUniqueness_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : BinarySchema parameterCount)
    (target α : ℳ.Domain) :
    satisfies ((env.push target).push α)
        (operator.recursiveSequenceInUniqueness 𝒞).body ↔
      ∀ left right,
        ℳ.IsRecursiveSequenceIn 𝕀
            (operator.denote env) left α target →
          ℳ.IsRecursiveSequenceIn 𝕀
            (operator.denote env) right α target →
          left = right := by
  simp only [BinarySchema.recursiveSequenceInUniqueness,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_isRecursiveSequenceIn_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    TermVector.evalEnv_boundParameters_four,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest]

/-- 固定目标集递归图有序对模式的纸面语义。 -/
theorem denote_recursionGraphPairIn_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : BinarySchema parameterCount)
    (target α pair : ℳ.Domain) :
    (operator.recursionGraphPairIn 𝒞).denote
        (env.push target) α pair ↔
      ∃ value,
        ℳ.IsRecursionValueIn 𝕀
            (operator.denote env) α value target ∧
          𝕀.Codes pair α value := by
  simp only [BinarySchema.recursionGraphPairIn,
    BinarySchema.denote, satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isRecursionValueIn_iff 𝕀 hExt,
    𝕀.satisfies_code_iff,
    TermVector.evalEnv_boundParameters_four,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest]

/-- 递归序列存在性模式与纸面存在命题一致。 -/
theorem satisfies_recursiveSequenceExistence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : BinarySchema parameterCount) (α : ℳ.Domain) :
    satisfies (env.push α)
        (operator.recursiveSequenceExistence 𝒞).body ↔
      ∃ sequence,
        ℳ.IsRecursiveSequence 𝕀
          (operator.denote env) sequence α := by
  simp only [BinarySchema.recursiveSequenceExistence,
    satisfies_exists_iff,
    satisfies_isRecursiveSequence_iff 𝕀 hExt,
    TermVector.evalEnv_boundParameters_two,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest]

/-- 递归序列唯一性模式与纸面唯一命题一致。 -/
theorem satisfies_recursiveSequenceUniqueness_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : BinarySchema parameterCount) (α : ℳ.Domain) :
    satisfies (env.push α)
        (operator.recursiveSequenceUniqueness 𝒞).body ↔
      ∀ left right,
        ℳ.IsRecursiveSequence 𝕀
            (operator.denote env) left α →
          ℳ.IsRecursiveSequence 𝕀
            (operator.denote env) right α →
          left = right := by
  simp only [BinarySchema.recursiveSequenceUniqueness,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_isRecursiveSequence_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    TermVector.evalEnv_boundParameters_three,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_newest]

/-- 递归图有序对模式恰好编码“索引及其递归值”。 -/
theorem denote_recursionGraphPair_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : BinarySchema parameterCount)
    (α pair : ℳ.Domain) :
    (operator.recursionGraphPair 𝒞).denote
        env α pair ↔
      ∃ value,
        ℳ.IsRecursionValue 𝕀
            (operator.denote env) α value ∧
          𝕀.Codes pair α value := by
  simp only [BinarySchema.recursionGraphPair,
    BinarySchema.denote, satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isRecursionValue_iff 𝕀 hExt,
    𝕀.satisfies_code_iff,
    TermVector.evalEnv_boundParameters_three,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_newest]

/-- `transfiniteRecursion` 的 schema 解释正是纸面递归值关系。 -/
theorem denote_transfiniteRecursion_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : BinarySchema parameterCount)
    (α value : ℳ.Domain) :
    (operator.transfiniteRecursion 𝒞).denote
        env α value ↔
      ℳ.IsRecursionValue 𝕀
        (operator.denote env) α value := by
  simp only [BinarySchema.transfiniteRecursion,
    BinarySchema.denote,
    satisfies_isRecursionValue_iff 𝕀 hExt,
    TermVector.evalEnv_boundParameters_two,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

/-- 局部序列类函数公式与纸面语义一致。 -/
theorem satisfies_isClassFunctionOnSequencesInBelow_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (bound target : Term depth) :
    satisfies env
        (isClassFunctionOnSequencesInBelow 𝒞 operator
          parameters bound target) ↔
      ℳ.IsClassFunctionOnSequencesInBelow 𝕀
        (operator.denote (parameters.evalEnv env))
        (bound.eval env) (target.eval env) := by
  simp only [isClassFunctionOnSequencesInBelow,
    Structure.IsClassFunctionOnSequencesInBelow,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isSequenceInBelow_iff 𝕀 hExt,
    satisfies_related_iff,
    satisfies_extensionalEq_iff_eq hExt]
  simp only [Term.eval_weaken, Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, TermVector.evalEnv_weaken]
  constructor
  · intro h sequence hSequence
    rcases h sequence hSequence with
      ⟨value, hValue, hUnique⟩
    exact
      ⟨value, hValue, fun other hOther =>
        (hUnique other hOther).symm⟩
  · intro h sequence hSequence
    rcases h sequence hSequence with
      ⟨value, hValue, hUnique⟩
    exact
      ⟨value, hValue, fun other hOther =>
        (hUnique other hOther).symm⟩

/-- 局部递归算子闭包公式与纸面映入关系一致。 -/
theorem satisfies_mapsSequencesInBelowInto_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount depth : Nat}
    (env : Env ℳ depth) (operator : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (bound target : Term depth) :
    satisfies env
        (mapsSequencesInBelowInto 𝒞 operator
          parameters bound target) ↔
      ℳ.MapsSequencesInBelowInto 𝕀
        (operator.denote (parameters.evalEnv env))
        (bound.eval env) (target.eval env) := by
  simp only [mapsSequencesInBelowInto,
    Structure.MapsSequencesInBelowInto,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_conj_iff,
    satisfies_mem_iff,
    satisfies_isSequenceInBelow_iff 𝕀 hExt,
    satisfies_related_iff, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken, Term.eval_bound_zero_push,
    Term.eval_bound_one_push,
    TermVector.evalEnv_weaken, and_imp]

end Formula
end Project
end Definitional

namespace ZF

/--
ZF 中，固定目标集值递归序列在给定上界以内的任意序数长度上唯一。
-/
theorem recursiveSequenceIn_unique {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    {bound target α left right : ℳ.Domain}
    (hBound : ℳ.IsOrdinal bound)
    (hOrdinalWithin : α = bound ∨ ℳ.mem α bound)
    (hOperator :
      ℳ.IsClassFunctionOnSequencesInBelow 𝕀
        (operator.denote env) bound target)
    (hLeft :
      ℳ.IsRecursiveSequenceIn 𝕀
        (operator.denote env) left α target)
    (hRight :
      ℳ.IsRecursiveSequenceIn 𝕀
        (operator.denote env) right α target) :
    left = right := by
  let property : ℳ.Domain → Prop := fun current =>
    ∀ first second,
      ℳ.IsRecursiveSequenceIn 𝕀
          (operator.denote env) first current target →
        ℳ.IsRecursiveSequenceIn 𝕀
          (operator.denote env) second current target →
        first = second
  have hProperty : property α := by
    apply Structure.IsOrdinal.inductionWithin
      hLeft.1.1 property
    · rcases exists_separation hZF
          (operator.recursiveSequenceInUniqueness 𝒞).neg
          (env.push target) α with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun value => ?_⟩
      rw [hCounterexamples value]
      simp [property, Definitional.Project.UnarySchema.neg,
        Definitional.Project.Formula.satisfies_neg_iff,
        Definitional.Project.Formula.satisfies_recursiveSequenceInUniqueness_iff
          𝕀 hZF.1 env operator target value]
    · intro current hCurrent hCurrentWithin hPrevious
      have hCurrentWithinBound :
          current = bound ∨ ℳ.mem current bound := by
        rcases hOrdinalWithin with hOrdinalEq | hOrdinalBound
        · subst α
          exact hCurrentWithin
        · rcases hCurrentWithin with hCurrentEq | hCurrentOrdinal
          · subst current
            exact Or.inr hOrdinalBound
          · exact Or.inr <|
              hBound.transitive α hOrdinalBound
                current hCurrentOrdinal
      change ∀ first second,
        ℳ.IsRecursiveSequenceIn 𝕀
            (operator.denote env) first current target →
          ℳ.IsRecursiveSequenceIn 𝕀
            (operator.denote env) second current target →
          first = second
      intro first second hFirst hSecond
      exact
        Structure.IsRecursiveSequenceIn.eq_of_predecessor_uniqueness
          hZF.1 hBound hCurrentWithinBound hOperator
          hFirst hSecond hPrevious
  exact hProperty left right hLeft hRight

/-- ZF 中，固定目标集内的递归值在每个严格小于上界的序数处唯一。 -/
theorem recursionValueIn_unique {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    {bound target α first second : ℳ.Domain}
    (hBound : ℳ.IsOrdinal bound)
    (hOrdinalBound : ℳ.mem α bound)
    (hOperator :
      ℳ.IsClassFunctionOnSequencesInBelow 𝕀
        (operator.denote env) bound target)
    (hFirst :
      ℳ.IsRecursionValueIn 𝕀
        (operator.denote env) α first target)
    (hSecond :
      ℳ.IsRecursionValueIn 𝕀
        (operator.denote env) α second target) :
    first = second := by
  rcases hFirst with
    ⟨firstSequence, hFirstSequence, hFirstOperator, _⟩
  rcases hSecond with
    ⟨secondSequence, hSecondSequence, hSecondOperator, _⟩
  have hSequenceEq :=
    recursiveSequenceIn_unique hZF 𝕀 env operator
      hBound (Or.inr hOrdinalBound) hOperator
      hFirstSequence hSecondSequence
  subst secondSequence
  rcases hOperator firstSequence
      ⟨hBound, α, hOrdinalBound, hFirstSequence.1⟩ with
    ⟨selected, _, hUnique⟩
  rw [hUnique first hFirstOperator,
    hUnique second hSecondOperator]

/-- ZF 中，函数式递归算子在任意给定序数长度上的递归序列唯一。 -/
theorem recursiveSequence_unique {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    (hOperator :
      ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
        (operator.denote env))
    {α left right : ℳ.Domain}
    (hLeft :
      ℳ.IsRecursiveSequence 𝕀
        (operator.denote env) left α)
    (hRight :
      ℳ.IsRecursiveSequence 𝕀
        (operator.denote env) right α) :
    left = right := by
  let property : ℳ.Domain → Prop := fun current =>
    ∀ first second,
      ℳ.IsRecursiveSequence 𝕀
          (operator.denote env) first current →
        ℳ.IsRecursiveSequence 𝕀
          (operator.denote env) second current →
        first = second
  have hProperty : property α := by
    apply Structure.IsOrdinal.induction hLeft.1.1 property
    · rcases exists_separation hZF
          (operator.recursiveSequenceUniqueness 𝒞).neg
          env α with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun value => ?_⟩
      rw [hCounterexamples value]
      simp [property, Definitional.Project.UnarySchema.neg,
        Definitional.Project.Formula.satisfies_neg_iff,
        Definitional.Project.Formula.satisfies_recursiveSequenceUniqueness_iff
          𝕀 hZF.1 env operator value]
    · intro current _ hPrevious
      change ∀ first second,
        ℳ.IsRecursiveSequence 𝕀
            (operator.denote env) first current →
          ℳ.IsRecursiveSequence 𝕀
            (operator.denote env) second current →
          first = second
      intro first second hFirst hSecond
      exact
        Structure.IsRecursiveSequence.eq_of_predecessor_uniqueness
          hZF.1 hOperator hFirst hSecond hPrevious
  exact hProperty left right hLeft hRight

/-- ZF 中，超限递归关系在每个序数处至多有一个值。 -/
theorem recursionValue_unique {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    (hOperator :
      ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
        (operator.denote env))
    {α first second : ℳ.Domain}
    (hFirst :
      ℳ.IsRecursionValue 𝕀
        (operator.denote env) α first)
    (hSecond :
      ℳ.IsRecursionValue 𝕀
        (operator.denote env) α second) :
    first = second := by
  rcases hFirst with
    ⟨firstSequence, hFirstSequence, hFirstOperator⟩
  rcases hSecond with
    ⟨secondSequence, hSecondSequence, hSecondOperator⟩
  have hSequenceEq :=
    recursiveSequence_unique hZF 𝕀 env operator
      hOperator hFirstSequence hSecondSequence
  subst secondSequence
  rcases hOperator firstSequence
      ⟨α, hFirstSequence.1⟩ with
    ⟨selected, _, hUnique⟩
  rw [hUnique first hFirstOperator,
    hUnique second hSecondOperator]

/--
若当前长度的每个真前段都有固定目标集值递归序列，则可构造当前长度的同类序列。
-/
theorem recursiveSequenceIn_of_predecessors {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    {bound target current : ℳ.Domain}
    (hBound : ℳ.IsOrdinal bound)
    (hCurrent : ℳ.IsOrdinal current)
    (hCurrentWithin : current = bound ∨ ℳ.mem current bound)
    (hOperator :
      ℳ.IsClassFunctionOnSequencesInBelow 𝕀
        (operator.denote env) bound target)
    (hMaps :
      ℳ.MapsSequencesInBelowInto 𝕀
        (operator.denote env) bound target)
    (hPrevious : ∀ index, ℳ.mem index current →
      ∃ sequence,
        ℳ.IsRecursiveSequenceIn 𝕀
          (operator.denote env) sequence index target) :
    ∃ sequence,
      ℳ.IsRecursiveSequenceIn 𝕀
        (operator.denote env) sequence current target := by
  have hIndexBound {index : ℳ.Domain}
      (hIndex : ℳ.mem index current) :
      ℳ.mem index bound := by
    rcases hCurrentWithin with hEq | hCurrentBound
    · simpa [hEq] using hIndex
    · exact
        hBound.transitive current hCurrentBound index hIndex
  have hGraphTotal : ∀ index, ℳ.mem index current →
      ∃ pair,
        (operator.recursionGraphPairIn 𝒞).denote
          (env.push target) index pair := by
    intro index hIndex
    rcases hPrevious index hIndex with
      ⟨prior, hPrior⟩
    have hPriorBelow :
        ℳ.IsSequenceInBelow 𝕀 prior bound target :=
      ⟨hBound, index, hIndexBound hIndex, hPrior.1⟩
    rcases hOperator prior hPriorBelow with
      ⟨value, hValue, _⟩
    have hValueTarget := hMaps prior value hPriorBelow hValue
    rcases 𝕀.total index value with
      ⟨pair, hPair⟩
    refine ⟨pair, ?_⟩
    apply
      (Definitional.Project.Formula.denote_recursionGraphPairIn_iff
        𝕀 hZF.1 env operator
        target index pair).mpr
    exact
      ⟨value, ⟨prior, hPrior, hValue, hValueTarget⟩, hPair⟩
  have hGraphUnique : ∀ index, ℳ.mem index current →
      ∀ first second,
        (operator.recursionGraphPairIn 𝒞).denote
            (env.push target) index first →
          (operator.recursionGraphPairIn 𝒞).denote
            (env.push target) index second →
          first = second := by
    intro index hIndex first second hFirst hSecond
    rcases
        (Definitional.Project.Formula.denote_recursionGraphPairIn_iff
          𝕀 hZF.1 env operator
          target index first).mp hFirst with
      ⟨firstValue, hFirstValue, hFirstCode⟩
    rcases
        (Definitional.Project.Formula.denote_recursionGraphPairIn_iff
          𝕀 hZF.1 env operator
          target index second).mp hSecond with
      ⟨secondValue, hSecondValue, hSecondCode⟩
    have hValueEq :=
      recursionValueIn_unique hZF 𝕀 env operator
        hBound (hIndexBound hIndex) hOperator
        hFirstValue hSecondValue
    subst secondValue
    exact 𝕀.unique hFirstCode hSecondCode
  rcases exists_functionalImageOn hZF
      (operator.recursionGraphPairIn 𝒞)
      (env.push target) current hGraphTotal hGraphUnique with
    ⟨sequence, hSequenceMembers⟩
  have hPairMember (index value : ℳ.Domain) :
      ℳ.PairMember 𝕀 index value sequence ↔
        ℳ.mem index current ∧
          ℳ.IsRecursionValueIn 𝕀
            (operator.denote env) index value target := by
    constructor
    · rintro ⟨pair, hPairCode, hPairMem⟩
      rcases (hSequenceMembers pair).mp hPairMem with
        ⟨source, hSource, hGraph⟩
      rcases
          (Definitional.Project.Formula.denote_recursionGraphPairIn_iff
            𝕀 hZF.1 env operator
            target source pair).mp hGraph with
        ⟨output, hOutput, hGraphCode⟩
      rcases 𝕀.injective hPairCode hGraphCode with
        ⟨hIndexEq, hValueEq⟩
      subst source
      subst output
      exact ⟨hSource, hOutput⟩
    · rintro ⟨hIndex, hValue⟩
      rcases 𝕀.total index value with
        ⟨pair, hPairCode⟩
      refine ⟨pair, hPairCode, (hSequenceMembers pair).mpr ?_⟩
      refine ⟨index, hIndex, ?_⟩
      apply
        (Definitional.Project.Formula.denote_recursionGraphPairIn_iff
          𝕀 hZF.1 env operator
          target index pair).mpr
      exact ⟨value, hValue, hPairCode⟩
  have hRelation :
      ℳ.IsSetRelation 𝕀 sequence := by
    intro pair hPair
    rcases (hSequenceMembers pair).mp hPair with
      ⟨index, _, hGraph⟩
    rcases
        (Definitional.Project.Formula.denote_recursionGraphPairIn_iff
          𝕀 hZF.1 env operator
          target index pair).mp hGraph with
      ⟨value, _, hCode⟩
    exact ⟨index, value, hCode⟩
  have hFunction :
      ℳ.IsSetFunction 𝕀 sequence := by
    refine ⟨hRelation, ?_⟩
    intro index first second hFirst hSecond
    have hIndex := ((hPairMember index first).mp hFirst).1
    exact
      recursionValueIn_unique hZF 𝕀 env operator
        hBound (hIndexBound hIndex) hOperator
        ((hPairMember index first).mp hFirst).2
        ((hPairMember index second).mp hSecond).2
  have hDomain :
      ℳ.IsDomainOf 𝕀 current sequence := by
    intro index
    constructor
    · intro hIndex
      rcases hPrevious index hIndex with
        ⟨prior, hPrior⟩
      have hPriorBelow :
          ℳ.IsSequenceInBelow 𝕀 prior bound target :=
        ⟨hBound, index, hIndexBound hIndex, hPrior.1⟩
      rcases hOperator prior hPriorBelow with
        ⟨value, hValue, _⟩
      have hValueTarget := hMaps prior value hPriorBelow hValue
      exact
        ⟨value, (hPairMember index value).mpr
          ⟨hIndex, prior, hPrior, hValue, hValueTarget⟩⟩
    · rintro ⟨value, hValue⟩
      exact ((hPairMember index value).mp hValue).1
  have hIntoTarget :
      ∀ index, ℳ.mem index current →
        ∃ value, ℳ.mem value target ∧
          ℳ.PairMember 𝕀 index value sequence := by
    intro index hIndex
    rcases (hDomain index).mp hIndex with
      ⟨value, hValue⟩
    rcases ((hPairMember index value).mp hValue).2 with
      ⟨prior, hPrior, hOperatorValue, hValueTarget⟩
    exact ⟨value, hValueTarget, hValue⟩
  have hRecursion :
      ℳ.ObeysRecursion 𝕀
        (operator.denote env) sequence current := by
    intro index hIndex value hValue
    rcases ((hPairMember index value).mp hValue).2 with
      ⟨prior, hPrior, hPriorOperator, _⟩
    refine ⟨prior, ?_, hPriorOperator⟩
    refine ⟨hPrior.1.2.1.1, ?_⟩
    intro input output
    constructor
    · intro hOutputPrior
      have hInput : ℳ.mem input index :=
        (hPrior.1.2.2.1 input).mpr
          ⟨output, hOutputPrior⟩
      have hInputCurrent : ℳ.mem input current :=
        hCurrent.transitive index hIndex input hInput
      have hInputValue :=
        hPrior.recursionValue_of_pairMember hInput hOutputPrior
      exact
        ⟨hInput, (hPairMember input output).mpr
          ⟨hInputCurrent, hInputValue⟩⟩
    · rintro ⟨hInput, hOutputSequence⟩
      rcases (hPrior.1.2.2.1 input).mp hInput with
        ⟨priorOutput, hPriorOutput⟩
      have hPriorValue :=
        hPrior.recursionValue_of_pairMember hInput hPriorOutput
      have hSequenceValue :=
        ((hPairMember input output).mp hOutputSequence).2
      have hInputBound :
          ℳ.mem input bound :=
        hBound.transitive index (hIndexBound hIndex)
          input hInput
      have hValueEq :=
        recursionValueIn_unique hZF 𝕀 env operator
          hBound hInputBound hOperator
          hPriorValue hSequenceValue
      simpa [hValueEq] using hPriorOutput
  exact
    ⟨sequence,
      ⟨⟨hCurrent,
          ⟨hFunction, hDomain, hIntoTarget⟩⟩,
        hRecursion⟩⟩

/--
ZF 中，上界以内的每个序数长度上都存在固定目标集值递归序列。
-/
theorem recursiveSequenceIn_exists {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    {bound target α : ℳ.Domain}
    (hBound : ℳ.IsOrdinal bound)
    (hα : ℳ.IsOrdinal α)
    (hOrdinalWithin : α = bound ∨ ℳ.mem α bound)
    (hOperator :
      ℳ.IsClassFunctionOnSequencesInBelow 𝕀
        (operator.denote env) bound target)
    (hMaps :
      ℳ.MapsSequencesInBelowInto 𝕀
        (operator.denote env) bound target) :
    ∃ sequence,
      ℳ.IsRecursiveSequenceIn 𝕀
        (operator.denote env) sequence α target := by
  let property : ℳ.Domain → Prop := fun current =>
    ∃ sequence,
      ℳ.IsRecursiveSequenceIn 𝕀
        (operator.denote env) sequence current target
  apply Structure.IsOrdinal.inductionWithin hα property
  · rcases exists_separation hZF
        (operator.recursiveSequenceInExistence 𝒞).neg
        (env.push target) α with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun value => ?_⟩
    rw [hCounterexamples value]
    simp [property, Definitional.Project.UnarySchema.neg,
      Definitional.Project.Formula.satisfies_neg_iff,
      Definitional.Project.Formula.satisfies_recursiveSequenceInExistence_iff
        𝕀 hZF.1 env operator target value]
  · intro current hCurrent hCurrentWithin hPrevious
    have hCurrentWithinBound :
        current = bound ∨ ℳ.mem current bound := by
      rcases hOrdinalWithin with hOrdinalEq | hOrdinalBound
      · subst α
        exact hCurrentWithin
      · rcases hCurrentWithin with hCurrentEq | hCurrentOrdinal
        · subst current
          exact Or.inr hOrdinalBound
        · exact Or.inr <|
            hBound.transitive α hOrdinalBound
              current hCurrentOrdinal
    exact
      recursiveSequenceIn_of_predecessors hZF 𝕀
        env operator hBound hCurrent hCurrentWithinBound
        hOperator hMaps hPrevious

/--
推论 2.16：局部函数式且保持 `target` 的算子在长度 `bound` 上产生唯一的
`target` 值递归序列。
-/
theorem recursiveSequenceIn_existsUnique {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    {bound target : ℳ.Domain}
    (hBound : ℳ.IsOrdinal bound)
    (hOperator :
      ℳ.IsClassFunctionOnSequencesInBelow 𝕀
        (operator.denote env) bound target)
    (hMaps :
      ℳ.MapsSequencesInBelowInto 𝕀
        (operator.denote env) bound target) :
    ∃ sequence,
      ℳ.IsRecursiveSequenceIn 𝕀
          (operator.denote env) sequence bound target ∧
        ∀ other,
          ℳ.IsRecursiveSequenceIn 𝕀
              (operator.denote env) other bound target →
            other = sequence := by
  rcases recursiveSequenceIn_exists hZF 𝕀
      env operator hBound hBound (Or.inl rfl)
      hOperator hMaps with
    ⟨sequence, hSequence⟩
  refine ⟨sequence, hSequence, ?_⟩
  intro other hOther
  exact
    recursiveSequenceIn_unique hZF 𝕀 env operator
      hBound (Or.inl rfl) hOperator hOther hSequence

/--
若每个真前段长度上都已有递归序列，则可由函数式替换构造当前长度的递归序列。
-/
theorem recursiveSequence_of_predecessors {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    (hOperator :
      ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
        (operator.denote env))
    {α : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hPrevious : ∀ index, ℳ.mem index α →
      ∃ sequence,
        ℳ.IsRecursiveSequence 𝕀
          (operator.denote env) sequence index) :
    ∃ sequence,
      ℳ.IsRecursiveSequence 𝕀
        (operator.denote env) sequence α := by
  have hGraphTotal : ∀ index, ℳ.mem index α →
      ∃ pair,
        (operator.recursionGraphPair 𝒞).denote
          env index pair := by
    intro index hIndex
    rcases hPrevious index hIndex with
      ⟨prior, hPrior⟩
    rcases hOperator prior ⟨index, hPrior.1⟩ with
      ⟨value, hValue, _⟩
    rcases 𝕀.total index value with
      ⟨pair, hPair⟩
    refine ⟨pair, ?_⟩
    apply
      (Definitional.Project.Formula.denote_recursionGraphPair_iff
        𝕀 hZF.1 env operator index pair).mpr
    exact ⟨value, ⟨prior, hPrior, hValue⟩, hPair⟩
  have hGraphUnique : ∀ index first second,
      (operator.recursionGraphPair 𝒞).denote
          env index first →
        (operator.recursionGraphPair 𝒞).denote
          env index second →
        first = second := by
    intro index first second hFirst hSecond
    rcases
        (Definitional.Project.Formula.denote_recursionGraphPair_iff
          𝕀 hZF.1 env operator index first).mp
          hFirst with
      ⟨firstValue, hFirstValue, hFirstCode⟩
    rcases
        (Definitional.Project.Formula.denote_recursionGraphPair_iff
          𝕀 hZF.1 env operator index second).mp
          hSecond with
      ⟨secondValue, hSecondValue, hSecondCode⟩
    have hValueEq :=
      recursionValue_unique hZF 𝕀 env operator
        hOperator hFirstValue hSecondValue
    subst secondValue
    exact 𝕀.unique hFirstCode hSecondCode
  rcases exists_functionalImage hZF
      (operator.recursionGraphPair 𝒞) env α
      hGraphTotal hGraphUnique with
    ⟨sequence, hSequenceMembers⟩
  have hPairMember (index value : ℳ.Domain) :
      ℳ.PairMember 𝕀 index value sequence ↔
        ℳ.mem index α ∧
          ℳ.IsRecursionValue 𝕀
            (operator.denote env) index value := by
    constructor
    · rintro ⟨pair, hPairCode, hPairMem⟩
      rcases (hSequenceMembers pair).mp hPairMem with
        ⟨source, hSource, hGraph⟩
      rcases
          (Definitional.Project.Formula.denote_recursionGraphPair_iff
            𝕀 hZF.1 env operator source pair).mp
            hGraph with
        ⟨output, hOutput, hGraphCode⟩
      rcases 𝕀.injective hPairCode hGraphCode with
        ⟨hIndexEq, hValueEq⟩
      subst source
      subst output
      exact ⟨hSource, hOutput⟩
    · rintro ⟨hIndex, hValue⟩
      rcases 𝕀.total index value with
        ⟨pair, hPairCode⟩
      refine ⟨pair, hPairCode, (hSequenceMembers pair).mpr ?_⟩
      refine ⟨index, hIndex, ?_⟩
      apply
        (Definitional.Project.Formula.denote_recursionGraphPair_iff
          𝕀 hZF.1 env operator index pair).mpr
      exact ⟨value, hValue, hPairCode⟩
  have hRelation :
      ℳ.IsSetRelation 𝕀 sequence := by
    intro pair hPair
    rcases (hSequenceMembers pair).mp hPair with
      ⟨index, _, hGraph⟩
    rcases
        (Definitional.Project.Formula.denote_recursionGraphPair_iff
          𝕀 hZF.1 env operator index pair).mp
          hGraph with
      ⟨value, _, hCode⟩
    exact ⟨index, value, hCode⟩
  have hFunction :
      ℳ.IsSetFunction 𝕀 sequence := by
    refine ⟨hRelation, ?_⟩
    intro index first second hFirst hSecond
    exact
      recursionValue_unique hZF 𝕀 env operator
        hOperator
        ((hPairMember index first).mp hFirst).2
        ((hPairMember index second).mp hSecond).2
  have hDomain :
      ℳ.IsDomainOf 𝕀 α sequence := by
    intro index
    constructor
    · intro hIndex
      rcases hPrevious index hIndex with
        ⟨prior, hPrior⟩
      rcases hOperator prior ⟨index, hPrior.1⟩ with
        ⟨value, hValue, _⟩
      exact
        ⟨value, (hPairMember index value).mpr
          ⟨hIndex, prior, hPrior, hValue⟩⟩
    · rintro ⟨value, hValue⟩
      exact ((hPairMember index value).mp hValue).1
  have hRecursion :
      ℳ.ObeysRecursion 𝕀
        (operator.denote env) sequence α := by
    intro index hIndex value hValue
    rcases ((hPairMember index value).mp hValue).2 with
      ⟨prior, hPrior, hPriorOperator⟩
    refine ⟨prior, ?_, hPriorOperator⟩
    refine ⟨hPrior.1.2.1.1, ?_⟩
    intro input output
    constructor
    · intro hOutputPrior
      have hInput : ℳ.mem input index :=
        (hPrior.1.2.2 input).mpr ⟨output, hOutputPrior⟩
      have hInputOrdinal : ℳ.mem input α :=
        hα.transitive index hIndex input hInput
      have hInputValue :=
        hPrior.recursionValue_of_pairMember hInput hOutputPrior
      exact
        ⟨hInput, (hPairMember input output).mpr
          ⟨hInputOrdinal, hInputValue⟩⟩
    · rintro ⟨hInput, hOutputSequence⟩
      rcases (hPrior.1.2.2 input).mp hInput with
        ⟨priorOutput, hPriorOutput⟩
      have hPriorValue :=
        hPrior.recursionValue_of_pairMember hInput hPriorOutput
      have hSequenceValue :=
        ((hPairMember input output).mp hOutputSequence).2
      have hValueEq :=
        recursionValue_unique hZF 𝕀 env operator
          hOperator hPriorValue hSequenceValue
      simpa [hValueEq] using hPriorOutput
  exact
    ⟨sequence,
      ⟨⟨hα, hFunction, hDomain⟩, hRecursion⟩⟩

/-- ZF 中，每个序数长度上都存在服从函数式算子的递归序列。 -/
theorem recursiveSequence_exists {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    (hOperator :
      ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
        (operator.denote env))
    {α : ℳ.Domain} (hα : ℳ.IsOrdinal α) :
    ∃ sequence,
      ℳ.IsRecursiveSequence 𝕀
        (operator.denote env) sequence α := by
  let property : ℳ.Domain → Prop := fun current =>
    ∃ sequence,
      ℳ.IsRecursiveSequence 𝕀
        (operator.denote env) sequence current
  apply Structure.IsOrdinal.induction hα property
  · rcases exists_separation hZF
        (operator.recursiveSequenceExistence 𝒞).neg
        env α with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun value => ?_⟩
    rw [hCounterexamples value]
    simp [property, Definitional.Project.UnarySchema.neg,
      Definitional.Project.Formula.satisfies_neg_iff,
      Definitional.Project.Formula.satisfies_recursiveSequenceExistence_iff
        𝕀 hZF.1 env operator value]
  · intro current hCurrent hPrevious
    exact
      recursiveSequence_of_predecessors hZF 𝕀
        env operator hOperator hCurrent hPrevious

/-- ZF 中，超限递归关系在每个序数处都有值。 -/
theorem recursionValue_exists {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    (hOperator :
      ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
        (operator.denote env))
    {α : ℳ.Domain} (hα : ℳ.IsOrdinal α) :
    ∃ value,
      ℳ.IsRecursionValue 𝕀
        (operator.denote env) α value := by
  rcases recursiveSequence_exists hZF 𝕀
      env operator hOperator hα with
    ⟨sequence, hSequence⟩
  rcases hOperator sequence ⟨α, hSequence.1⟩ with
    ⟨value, hValue, _⟩
  exact ⟨value, sequence, hSequence, hValue⟩

/--
超限递归定理：函数式算子诱导出序数类上的唯一全定义类函数。

其图就是 `operator.transfiniteRecursion 𝒞` 所表示的递归值关系。
-/
theorem transfiniteRecursion_isClassFunctionOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (operator : Definitional.Project.BinarySchema parameterCount)
    (hOperator :
      ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
        (operator.denote env)) :
    ℳ.IsClassFunctionOnOrdinals
      ((operator.transfiniteRecursion 𝒞).denote env) := by
  intro α hα
  rcases recursionValue_exists hZF 𝕀 env operator
      hOperator hα with
    ⟨value, hValue⟩
  refine ⟨value, ?_, ?_⟩
  · exact
      (Definitional.Project.Formula.denote_transfiniteRecursion_iff
        𝕀 hZF.1 env operator α value).mpr
        hValue
  · intro other hOther
    apply recursionValue_unique hZF 𝕀 env operator
      hOperator
    · exact
        (Definitional.Project.Formula.denote_transfiniteRecursion_iff
          𝕀 hZF.1 env operator α other).mp
          hOther
    · exact hValue

end ZF

end SetTheory
end YesMetaZFC
