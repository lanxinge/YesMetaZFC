import YesMetaZFC.SetTheory.Ord.Arithmetic.Semantics

/-!
# 序数算术的递归定理

本层先提取序数算术共同使用的零、后继、极限三分支递归算子，并证明该算子在所有
超限序列上全定义且单值。加法、乘法和幂随后只需分别提供后继步的存在唯一性。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/--
给定初值条件与后继运算的零、后继、极限三分支递归步。

极限步固定取此前序列值域的并。
-/
def IsZeroSuccessorLimitStep {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (initialCondition : ℳ.Domain → Prop)
    (successorOperation : ℳ.Domain → ℳ.Domain → Prop)
    (sequence output : ℳ.Domain) : Prop :=
  (ℳ.IsZeroLengthSequence 𝕀 sequence ∧
      initialCondition output) ∨
    (∃ previous,
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous ∧
        successorOperation previous output) ∨
    ℳ.IsLimitLengthSequenceWithUnion 𝕀 sequence output

namespace SuccessorOf

/-- 同一对象的两个后继相等。 -/
theorem eq {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {left right predecessor : ℳ.Domain}
    (hLeft : ℳ.SuccessorOf left predecessor)
    (hRight : ℳ.SuccessorOf right predecessor) :
    left = right := by
  apply hExt.eq_of_same_members
  intro value
  rw [hLeft value, hRight value]

/-- 两个序数若有同一后继，则它们相等。 -/
theorem predecessor_eq {ℳ : Structure.{u}}
    (hExt : Extensional ℳ)
    {successor first second : ℳ.Domain}
    (hFirstOrdinal : ℳ.IsOrdinal first)
    (hFirst : ℳ.SuccessorOf successor first)
    (hSecond : ℳ.SuccessorOf successor second) :
    first = second := by
  have hFirstMem :
      ℳ.mem first successor :=
    (hFirst first).mpr (Or.inr fun _ => Iff.rfl)
  have hSecondMem :
      ℳ.mem second successor :=
    (hSecond second).mpr (Or.inr fun _ => Iff.rfl)
  rcases (hSecond first).mp hFirstMem with hFirstSecond | hSame
  · rcases (hFirst second).mp hSecondMem with hSecondFirst | hSame
    · have hSelf : ℳ.mem first first :=
        hFirstOrdinal.transitive second hSecondFirst first hFirstSecond
      exact False.elim <|
        hFirstOrdinal.wellOrder.linear.irrefl first hSelf hSelf
    · exact
        (hExt.eq_of_same_members second first hSame).symm
  · exact hExt.eq_of_same_members first second hSame

register_prove_auto_sequent_rule predecessor_eq PRIORITY 200

end SuccessorOf

namespace IsOrdinalOne

/-- 任意两个序数一相等。 -/
theorem eq {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinalOne left)
    (hRight : ℳ.IsOrdinalOne right) :
    left = right := by
  rcases hLeft with ⟨leftZero, hLeftZero, hLeft⟩
  rcases hRight with ⟨rightZero, hRightZero, hRight⟩
  have hZeroEq : leftZero = rightZero := by
    apply hExt.eq_of_same_members
    intro value
    exact iff_of_false (hLeftZero value) (hRightZero value)
  subst rightZero
  exact SuccessorOf.eq hExt hLeft hRight

end IsOrdinalOne

namespace IsSequenceOfLength

/-- 同一序列的两个精确定义域相等。 -/
theorem length_eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {sequence left right : ℳ.Domain}
    (hLeft : ℳ.IsSequenceOfLength 𝕀 sequence left)
    (hRight : ℳ.IsSequenceOfLength 𝕀 sequence right) :
    left = right :=
  IsDomainOf.eq hExt hLeft.2.2 hRight.2.2

register_prove_auto_sequent_rule length_eq PRIORITY 200

end IsSequenceOfLength

namespace IsZeroLengthSequence

/-- 零长度序列不可能同时具有后继长度。 -/
theorem not_successorLength {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {sequence previous : ℳ.Domain}
    (hZero : ℳ.IsZeroLengthSequence 𝕀 sequence)
    (hSuccessor :
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀
        sequence previous) :
    False := by
  prove_auto

/-- 零长度序列不可能同时具有非零极限长度。 -/
theorem not_limitLength {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {sequence limit : ℳ.Domain}
    (hZero : ℳ.IsZeroLengthSequence 𝕀 sequence)
    (hLimit :
      ℳ.IsLimitLengthSequenceWithUnion 𝕀 sequence limit) :
    False := by
  prove_auto

end IsZeroLengthSequence

namespace IsSuccessorLengthSequenceWithLast

/-- 同一函数序列的后继长度末值唯一。 -/
theorem last_eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {sequence first second : ℳ.Domain}
    (hFirst :
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀
        sequence first)
    (hSecond :
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀
        sequence second) :
    first = second := by
  prove_auto

/-- 后继长度序列不可能同时具有非零极限长度。 -/
theorem not_limitLength {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {sequence previous limit : ℳ.Domain}
    (hSuccessor :
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀
        sequence previous)
    (hLimit :
      ℳ.IsLimitLengthSequenceWithUnion 𝕀 sequence limit) :
    False := by
  prove_auto

end IsSuccessorLengthSequenceWithLast

namespace IsLimitLengthSequenceWithUnion

/-- 同一极限长度序列的值域之并唯一。 -/
theorem union_eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {sequence left right : ℳ.Domain}
    (hLeft :
      ℳ.IsLimitLengthSequenceWithUnion 𝕀 sequence left)
    (hRight :
      ℳ.IsLimitLengthSequenceWithUnion 𝕀 sequence right) :
    left = right := by
  prove_auto

end IsLimitLengthSequenceWithUnion

namespace IsRecursiveSequence

/--
递归序列的精确值域就是各定义域位置上的递归值集合。

反向使用递归值单值性，把值域中函数实际选取的值与给定递归值对齐。
-/
theorem range_iff_recursionValue {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    {sequence length range : ℳ.Domain}
    (hSequence :
      ℳ.IsRecursiveSequence 𝕀 operator sequence length)
    (hRange : ℳ.IsRangeOf 𝕀 range sequence)
    (hUnique : ∀ index, ℳ.mem index length →
      ∀ first second,
        ℳ.IsRecursionValue 𝕀 operator index first →
        ℳ.IsRecursionValue 𝕀 operator index second →
        first = second) :
    ∀ value,
      ℳ.mem value range ↔
        ∃ index, ℳ.mem index length ∧
          ℳ.IsRecursionValue 𝕀 operator index value := by
  intro value
  rw [hRange value]
  constructor
  · rintro ⟨index, hValue⟩
    have hIndex : ℳ.mem index length :=
      (hSequence.1.2.2 index).mpr ⟨value, hValue⟩
    exact
      ⟨index, hIndex,
        hSequence.recursionValue_of_pairMember hIndex hValue⟩
  · rintro ⟨index, hIndex, hValue⟩
    rcases (hSequence.1.2.2 index).mp hIndex with
      ⟨selected, hSelected⟩
    have hSelectedValue :=
      hSequence.recursionValue_of_pairMember hIndex hSelected
    have hValueEq :=
      hUnique index hIndex value selected hValue hSelectedValue
    subst selected
    exact ⟨index, hSelected⟩

end IsRecursiveSequence

namespace IsRecursionValue

/--
若某递归值的当前步确为值域之并，则该值域可精确刻画为此前各位置的递归值集合。
-/
theorem limit_range {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {operator : ℳ.Domain → ℳ.Domain → Prop}
    {α value : ℳ.Domain}
    (hValue :
      ℳ.IsRecursionValue 𝕀 operator α value)
    (hLimitStep : ∀ {sequence output},
      ℳ.IsRecursiveSequence 𝕀 operator sequence α →
      operator sequence output →
        ℳ.IsLimitLengthSequenceWithUnion 𝕀
          sequence output)
    (hUnique : ∀ index, ℳ.mem index α →
      ∀ first second,
        ℳ.IsRecursionValue 𝕀 operator index first →
        ℳ.IsRecursionValue 𝕀 operator index second →
        first = second) :
    ∃ range,
      (∀ member,
        ℳ.mem member range ↔
          ∃ index, ℳ.mem index α ∧
            ℳ.IsRecursionValue 𝕀 operator index member) ∧
        ℳ.IsUnionOf value range := by
  rcases hValue with
    ⟨sequence, hSequence, hOutput⟩
  rcases hLimitStep hSequence hOutput with
    ⟨_, _, _, range, hRange, hUnion⟩
  exact
    ⟨range,
      hSequence.range_iff_recursionValue hRange hUnique,
      hUnion⟩

end IsRecursionValue

end Structure

namespace KP

/-- KP 模型中任意对象都有后继。 -/
theorem exists_successor {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    (predecessor : ℳ.Domain) :
    ∃ successor, ℳ.SuccessorOf successor predecessor := by
  rcases exists_insert hKP predecessor predecessor with
    ⟨successor, hSuccessor⟩
  refine ⟨successor, fun value => ?_⟩
  rw [hSuccessor value]
  constructor
  · rintro (hMember | rfl)
    · exact Or.inl hMember
    · exact Or.inr fun _ => Iff.rfl
  · rintro (hMember | hSame)
    · exact Or.inl hMember
    · exact Or.inr <|
        hKP.1.eq_of_same_members value predecessor hSame

/-- KP 模型中存在序数一。 -/
theorem exists_ordinalOne {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) :
    ∃ one, ℳ.IsOrdinalOne one := by
  rcases exists_empty hKP with ⟨zero, hZero⟩
  rcases exists_successor hKP zero with
    ⟨one, hOne⟩
  exact ⟨one, zero, hZero, hOne⟩

/--
KP 模型中，序数的后继仍是序数。

自动化候选：本定理本应注册为序数后继闭包规则；当前 `APPLY` 无法把未由结论确定的
隐式 `ℳ.Domain` 对象参数暴露为 checked leaf，故暂不注册。
-/
theorem successor_isOrdinal {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    {predecessor successor : ℳ.Domain}
    (hPredecessor : ℳ.IsOrdinal predecessor)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.IsOrdinal successor := by
  refine ⟨?_, ?_⟩
  · intro middle hMiddle value hValue
    rcases (hSuccessor middle).mp hMiddle with
      hMiddlePredecessor | hSame
    · exact
        (hSuccessor value).mpr <| Or.inl <|
          hPredecessor.transitive middle
            hMiddlePredecessor value hValue
    · have hEq :=
        hKP.1.eq_of_same_members middle predecessor hSame
      subst middle
      exact (hSuccessor value).mpr (Or.inl hValue)
  · refine ⟨?_, ?_⟩
    · refine {
        irrefl := ?_
        trans := ?_
        compare := ?_
      }
      · intro value hValue hSelf
        rcases (hSuccessor value).mp hValue with
          hValuePredecessor | hSame
        · exact
            hPredecessor.wellOrder.linear.irrefl
              value hValuePredecessor hSelf
        · have hEq :=
            hKP.1.eq_of_same_members value predecessor hSame
          subst value
          exact
            hPredecessor.wellOrder.linear.irrefl
              predecessor hSelf hSelf
      · intro left _ middle _ right hRight hLeftMiddle hMiddleRight
        rcases (hSuccessor right).mp hRight with
          hRightPredecessor | hSame
        · have hMiddlePredecessor :=
            hPredecessor.transitive right hRightPredecessor
              middle hMiddleRight
          have hLeftPredecessor :=
            hPredecessor.transitive middle hMiddlePredecessor
              left hLeftMiddle
          exact
            hPredecessor.wellOrder.linear.trans
              left hLeftPredecessor
              middle hMiddlePredecessor
              right hRightPredecessor
              hLeftMiddle hMiddleRight
        · have hEq :=
            hKP.1.eq_of_same_members right predecessor hSame
          subst right
          exact
            hPredecessor.transitive middle hMiddleRight
              left hLeftMiddle
      · intro left hLeft right hRight
        rcases (hSuccessor left).mp hLeft with
          hLeftPredecessor | hLeftSame
        · rcases (hSuccessor right).mp hRight with
            hRightPredecessor | hRightSame
          · exact
              hPredecessor.wellOrder.linear.compare
                left hLeftPredecessor right hRightPredecessor
          · have hEq :=
              hKP.1.eq_of_same_members right predecessor
                hRightSame
            subst right
            exact Or.inr (Or.inl hLeftPredecessor)
        · have hLeftEq :=
            hKP.1.eq_of_same_members left predecessor hLeftSame
          subst left
          rcases (hSuccessor right).mp hRight with
            hRightPredecessor | hRightSame
          · exact Or.inr (Or.inr hRightPredecessor)
          · exact Or.inl fun value => (hRightSame value).symm
    · intro subset hSubset hNonempty
      by_cases hHasPredecessorMember :
          ∃ value, ℳ.mem value subset ∧ ℳ.mem value predecessor
      · rcases exists_intersection hKP subset predecessor with
          ⟨intersection, hIntersection⟩
        have hIntersectionSubset :
            ℳ.MemberSubset intersection predecessor := by
          intro value hValue
          exact (hIntersection value).mp hValue |>.2
        have hIntersectionNonempty :
            ∃ value, ℳ.mem value intersection := by
          rcases hHasPredecessorMember with
            ⟨value, hValueSubset, hValuePredecessor⟩
          exact
            ⟨value, (hIntersection value).mpr
              ⟨hValueSubset, hValuePredecessor⟩⟩
        rcases hPredecessor.wellOrder.least intersection
            hIntersectionSubset hIntersectionNonempty with
          ⟨candidate, hCandidate, hLeast⟩
        have hCandidateData :=
          (hIntersection candidate).mp hCandidate
        refine ⟨candidate, hCandidateData.1, ?_⟩
        intro value hValueSubset
        rcases (hSuccessor value).mp
            (hSubset value hValueSubset) with
          hValuePredecessor | hSame
        · exact hLeast value <|
            (hIntersection value).mpr
              ⟨hValueSubset, hValuePredecessor⟩
        · exact Or.inr <|
            (hSame candidate).mpr hCandidateData.2
      · rcases hNonempty with ⟨candidate, hCandidate⟩
        have hCandidateSame :
            ℳ.SameMembers candidate predecessor := by
          rcases (hSuccessor candidate).mp
              (hSubset candidate hCandidate) with
            hCandidatePredecessor | hSame
          · exact False.elim <|
              hHasPredecessorMember
                ⟨candidate, hCandidate, hCandidatePredecessor⟩
          · exact hSame
        refine ⟨candidate, hCandidate, ?_⟩
        intro value hValue
        have hValueSame :
            ℳ.SameMembers value predecessor := by
          rcases (hSuccessor value).mp
              (hSubset value hValue) with
            hValuePredecessor | hSame
          · exact False.elim <|
              hHasPredecessorMember
                ⟨value, hValue, hValuePredecessor⟩
          · exact hSame
        exact Or.inl fun member =>
          (hCandidateSame member).trans (hValueSame member).symm

/-- KP 模型中的序数一确实是序数。 -/
theorem ordinalOne_isOrdinal {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) {one : ℳ.Domain}
    (hOne : ℳ.IsOrdinalOne one) :
    ℳ.IsOrdinal one := by
  rcases hOne with ⟨zero, hZero, hSuccessor⟩
  exact successor_isOrdinal hKP
    (Structure.IsOrdinal.of_no_members hZero) hSuccessor

end KP

namespace ZF

/-- ZF 中，集合编码函数具有精确值域。 -/
theorem exists_range_of_setFunction {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function domain : ℳ.Domain}
    (hFunction : ℳ.IsSetFunction 𝕀 function)
    (hDomain : ℳ.IsDomainOf 𝕀 domain function) :
    ∃ range, ℳ.IsRangeOf 𝕀 range function := by
  let env : Env ℳ 1 := {
    bound := fun _ => function
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hTotal : ∀ input, ℳ.mem input domain →
      ∃ output,
        (Definitional.Project.RelationSchema.setCoded 𝒞).denote
          env input output := by
    intro input hInput
    rcases (hDomain input).mp hInput with
      ⟨output, hOutput⟩
    refine ⟨output, ?_⟩
    apply
      (Definitional.Project.BinarySchema.denote_setCoded_iff
        𝕀 env input output).mpr
    simpa [env] using hOutput
  have hUnique : ∀ input, ℳ.mem input domain →
      ∀ first second,
        (Definitional.Project.RelationSchema.setCoded 𝒞).denote
            env input first →
          (Definitional.Project.RelationSchema.setCoded 𝒞).denote
            env input second →
          first = second := by
    intro input _ first second hFirst hSecond
    apply hFunction.2 input first second
    · have :=
        (Definitional.Project.BinarySchema.denote_setCoded_iff
          𝕀 env input first).mp hFirst
      simpa [env] using this
    · have :=
        (Definitional.Project.BinarySchema.denote_setCoded_iff
          𝕀 env input second).mp hSecond
      simpa [env] using this
  rcases exists_functionalImageOn hZF
      (Definitional.Project.RelationSchema.setCoded 𝒞) env domain
      hTotal hUnique with
    ⟨range, hRange⟩
  refine ⟨range, fun output => ?_⟩
  rw [hRange output]
  constructor
  · rintro ⟨input, _, hOutput⟩
    refine ⟨input, ?_⟩
    have :=
      (Definitional.Project.BinarySchema.denote_setCoded_iff
        𝕀 env input output).mp hOutput
    simpa [env] using this
  · rintro ⟨input, hOutput⟩
    have hInput : ℳ.mem input domain :=
      (hDomain input).mpr ⟨output, hOutput⟩
    refine ⟨input, hInput, ?_⟩
    apply
      (Definitional.Project.BinarySchema.denote_setCoded_iff
        𝕀 env input output).mpr
    simpa [env] using hOutput

/-- ZF 中，极限长度函数序列具有值域之并。 -/
theorem exists_limitLengthSequenceWithUnion {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sequence length : ℳ.Domain}
    (hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length)
    (hLimit : ℳ.IsLimitOrdinal length) :
    ∃ union,
      ℳ.IsLimitLengthSequenceWithUnion 𝕀
        sequence union := by
  rcases exists_range_of_setFunction hZF 𝕀
      hSequence.2.1 hSequence.2.2 with
    ⟨range, hRange⟩
  rcases KP.exists_union (ZF.modelsKP hZF) range with
    ⟨union, hUnion⟩
  exact
    ⟨union, length, hLimit, hSequence, range, hRange, hUnion⟩

/--
零、后继、极限三分支算子在所有超限序列上全定义且单值。

证明只要求后继运算本身全定义且单值；零步由固定初值给出，极限步由函数值域的并给出。
-/
theorem zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (initialCondition : ℳ.Domain → Prop)
    (successorOperation : ℳ.Domain → ℳ.Domain → Prop)
    (hInitialCondition :
      ∃ output, initialCondition output ∧
        ∀ other, initialCondition other → other = output)
    (hSuccessorOperation : ∀ previous,
      ∃ output, successorOperation previous output ∧
        ∀ other, successorOperation previous other →
          other = output) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      (ℳ.IsZeroSuccessorLimitStep 𝕀 initialCondition
        successorOperation) := by
  rcases hInitialCondition with
    ⟨initial, hInitial, hInitialUnique⟩
  intro sequence hSequence
  rcases hSequence with ⟨length, hSequence⟩
  rcases Structure.IsOrdinal.classify hZF.1 hSequence.1 with
    hZero | hSuccessor | hLimit
  · have hZeroLength :
        ℳ.IsZeroLengthSequence 𝕀 sequence :=
      ⟨length, hSequence, hZero⟩
    refine ⟨initial, Or.inl ⟨hZeroLength, hInitial⟩, ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther | hOther
    · exact hInitialUnique other hOther.2
    · rcases hOther with ⟨previous, hPrevious, _⟩
      exact False.elim <|
        hZeroLength.not_successorLength hZF.1 hPrevious
    · exact False.elim <|
        hZeroLength.not_limitLength hZF.1 hOther
  · rcases hSuccessor with
      ⟨predecessor, hPredecessorOrdinal, hLength⟩
    have hPredecessorMem : ℳ.mem predecessor length :=
      (hLength predecessor).mpr (Or.inr fun _ => Iff.rfl)
    rcases (hSequence.2.2 predecessor).mp hPredecessorMem with
      ⟨previous, hPreviousValue⟩
    have hSuccessorLength :
        ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous :=
      ⟨predecessor, hPredecessorOrdinal, length, hLength,
        hSequence, hPreviousValue⟩
    rcases hSuccessorOperation previous with
      ⟨output, hOutput, hOutputUnique⟩
    refine
      ⟨output, Or.inr (Or.inl
        ⟨previous, hSuccessorLength, hOutput⟩), ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther | hOther
    · exact False.elim <|
        hOther.1.not_successorLength hZF.1 hSuccessorLength
    · rcases hOther with
        ⟨otherPrevious, hOtherLength, hOtherOutput⟩
      have hPreviousEq :=
        hOtherLength.last_eq hZF.1 hSuccessorLength
      subst otherPrevious
      exact hOutputUnique other hOtherOutput
    · exact False.elim <|
        hSuccessorLength.not_limitLength hZF.1 hOther
  · rcases exists_range_of_setFunction hZF 𝕀
        hSequence.2.1 hSequence.2.2 with
      ⟨range, hRange⟩
    rcases KP.exists_union (ZF.modelsKP hZF) range with
      ⟨union, hUnion⟩
    have hLimitLength :
        ℳ.IsLimitLengthSequenceWithUnion 𝕀
          sequence union :=
      ⟨length, hLimit, hSequence, range, hRange, hUnion⟩
    refine ⟨union, Or.inr (Or.inr hLimitLength), ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther | hOther
    · exact False.elim <|
        hOther.1.not_limitLength hZF.1 hLimitLength
    · rcases hOther with ⟨previous, hPrevious, _⟩
      exact False.elim <|
        hPrevious.not_limitLength hZF.1 hLimitLength
    · exact hOther.union_eq hZF.1 hLimitLength

/-- 固定左参数的序数加法递归步在所有超限序列上全定义且单值。 -/
theorem ordinalAdditionStep_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left : ℳ.Domain) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      (ℳ.IsOrdinalAdditionStep 𝕀 left) := by
  have hStep :=
    zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀
      (fun output => output = left)
      (fun previous output => ℳ.SuccessorOf output previous)
      ⟨left, rfl, fun other hOther => hOther⟩
      fun previous => by
        rcases KP.exists_successor (ZF.modelsKP hZF) previous with
          ⟨output, hOutput⟩
        exact
          ⟨output, hOutput, fun other hOther =>
            Structure.SuccessorOf.eq hZF.1 hOther hOutput⟩
  simpa [Structure.IsZeroSuccessorLimitStep,
    Structure.IsOrdinalAdditionStep] using hStep

/--
加法递归算子的 schema 解释在所有超限序列上全定义且单值。
-/
theorem ordinalAdditionOperator_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      ((Definitional.Project.BinarySchema.ordinalAdditionOperator 𝒞).denote env) := by
  have hStep :=
    ordinalAdditionStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀 (env.bound 0)
  intro sequence hSequence
  rcases hStep sequence hSequence with
    ⟨output, hOutput, hUnique⟩
  refine ⟨output, ?_, ?_⟩
  · exact
      (Definitional.Project.BinarySchema.denote_ordinalAdditionOperator_iff
        𝕀 hZF.1 env sequence output).mpr hOutput
  · intro other hOther
    apply hUnique other
    exact
      (Definitional.Project.BinarySchema.denote_ordinalAdditionOperator_iff
        𝕀 hZF.1 env sequence other).mp hOther

/--
固定左参数后，序数加法关系在所有序数右参数上全定义且单值。
-/
theorem ordinalAddition_isClassFunctionOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left : ℳ.Domain) :
    ℳ.IsClassFunctionOnOrdinals
      (fun right sum =>
        ℳ.IsOrdinalAddition 𝕀 sum left right) := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hClass :
      ℳ.IsClassFunctionOnOrdinals
        ((Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env) := by
    simpa [Definitional.Project.BinarySchema.ordinalAddition] using
      transfiniteRecursion_isClassFunctionOnOrdinals
        hZF 𝕀 env
        (Definitional.Project.BinarySchema.ordinalAdditionOperator 𝒞)
        (ordinalAdditionOperator_isClassFunctionOnTransfiniteSequences
          hZF 𝕀 env)
  intro right hRight
  rcases hClass right hRight with
    ⟨sum, hSum, hUnique⟩
  refine ⟨sum, ?_, ?_⟩
  · have hSemantic :=
      (Definitional.Project.BinarySchema.denote_ordinalAddition_iff
        𝕀 hZF.1 env right sum).mp hSum
    simpa [env] using hSemantic
  · intro other hOther
    apply hUnique other
    apply
      (Definitional.Project.BinarySchema.denote_ordinalAddition_iff
        𝕀 hZF.1 env right other).mpr
    simpa [env] using hOther

/-- 序数加法对任意左参数与序数右参数存在唯一。 -/
theorem ordinalAddition_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left : ℳ.Domain) {right : ℳ.Domain}
    (hRight : ℳ.IsOrdinal right) :
    ∃ sum,
      ℳ.IsOrdinalAddition 𝕀 sum left right ∧
        ∀ other,
          ℳ.IsOrdinalAddition 𝕀 other left right →
            other = sum :=
  ordinalAddition_isClassFunctionOnOrdinals
    hZF 𝕀 left right hRight

/--
固定左参数的乘法递归步在所有超限序列上全定义且单值。

序数左参数走文献中的零、后继、极限递归；非序数左参数走定义层的空集全定义化分支。
-/
theorem ordinalMultiplicationStep_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left : ℳ.Domain) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      (ℳ.IsOrdinalMultiplicationStep 𝕀 left) := by
  rcases KP.exists_empty (ZF.modelsKP hZF) with
    ⟨zero, hZero⟩
  by_cases hLeft : ℳ.IsOrdinal left
  · have hStep :=
      zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
        hZF 𝕀
        (fun output => ∀ value, ¬ ℳ.mem value output)
        (fun previous output =>
          ℳ.IsOrdinalAddition 𝕀 output previous left)
        ⟨zero, hZero, fun other hOther => by
          apply hZF.1.eq_of_same_members
          intro value
          exact iff_of_false (hOther value) (hZero value)⟩
        fun previous =>
          ordinalAddition_existsUnique
            hZF 𝕀 previous hLeft
    intro sequence hSequence
    rcases hStep sequence hSequence with
      ⟨output, hOutput, hUnique⟩
    refine ⟨output, Or.inr ⟨hLeft, hOutput⟩, ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther
    · exact False.elim <| hOther.1 hLeft
    · exact hUnique other hOther.2
  · intro sequence _
    refine ⟨zero, Or.inl ⟨hLeft, hZero⟩, ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther
    · apply hZF.1.eq_of_same_members
      intro value
      exact iff_of_false (hOther.2 value) (hZero value)
    · exact False.elim <| hLeft hOther.1

/--
乘法递归算子的 schema 解释在所有超限序列上全定义且单值。
-/
theorem ordinalMultiplicationOperator_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      ((Definitional.Project.BinarySchema.ordinalMultiplicationOperator 𝒞).denote
        env) := by
  have hStep :=
    ordinalMultiplicationStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀 (env.bound 0)
  intro sequence hSequence
  rcases hStep sequence hSequence with
    ⟨output, hOutput, hUnique⟩
  refine ⟨output, ?_, ?_⟩
  · exact
      (Definitional.Project.BinarySchema.denote_ordinalMultiplicationOperator_iff
        𝕀 hZF.1 env sequence output).mpr hOutput
  · intro other hOther
    apply hUnique other
    exact
      (Definitional.Project.BinarySchema.denote_ordinalMultiplicationOperator_iff
        𝕀 hZF.1 env sequence other).mp hOther

/--
固定左参数后，全定义化的序数乘法关系在所有序数右参数上全定义且单值。

后续序数算术定理仍会显式假设左参数为序数；域外分支只服务递归内核的全定义合同。
-/
theorem ordinalMultiplication_isClassFunctionOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left : ℳ.Domain) :
    ℳ.IsClassFunctionOnOrdinals
      (fun right product =>
        ℳ.IsOrdinalMultiplication 𝕀 product left right) := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hClass :
      ℳ.IsClassFunctionOnOrdinals
        ((Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env) := by
    simpa [Definitional.Project.BinarySchema.ordinalMultiplication] using
      transfiniteRecursion_isClassFunctionOnOrdinals
        hZF 𝕀 env
        (Definitional.Project.BinarySchema.ordinalMultiplicationOperator 𝒞)
        (ordinalMultiplicationOperator_isClassFunctionOnTransfiniteSequences
          hZF 𝕀 env)
  intro right hRight
  rcases hClass right hRight with
    ⟨product, hProduct, hUnique⟩
  refine ⟨product, ?_, ?_⟩
  · have hSemantic :=
      (Definitional.Project.BinarySchema.denote_ordinalMultiplication_iff
        𝕀 hZF.1 env right product).mp hProduct
    simpa [env] using hSemantic
  · intro other hOther
    apply hUnique other
    apply
      (Definitional.Project.BinarySchema.denote_ordinalMultiplication_iff
        𝕀 hZF.1 env right other).mpr
    simpa [env] using hOther

/-- 全定义化的序数乘法对任意左参数与序数右参数存在唯一。 -/
theorem ordinalMultiplication_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left : ℳ.Domain) {right : ℳ.Domain}
    (hRight : ℳ.IsOrdinal right) :
    ∃ product,
      ℳ.IsOrdinalMultiplication 𝕀 product left right ∧
        ∀ other,
          ℳ.IsOrdinalMultiplication 𝕀 other left right →
            other = product :=
  ordinalMultiplication_isClassFunctionOnOrdinals
    hZF 𝕀 left right hRight

/--
固定序数底数的幂递归步在所有超限序列上全定义且单值。

底数的序数性保证后继步中的 `previous * base` 处于乘法关系的序数右参数域。
-/
theorem ordinalExponentiationStep_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base : ℳ.Domain} (hBase : ℳ.IsOrdinal base) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      (ℳ.IsOrdinalExponentiationStep 𝕀 base) := by
  rcases KP.exists_ordinalOne (ZF.modelsKP hZF) with
    ⟨one, hOne⟩
  have hStep :=
    zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀 ℳ.IsOrdinalOne
      (fun previous output =>
        ℳ.IsOrdinalMultiplication 𝕀 output previous base)
      ⟨one, hOne, fun other hOther =>
        Structure.IsOrdinalOne.eq hZF.1 hOther hOne⟩
      fun previous =>
        ordinalMultiplication_existsUnique
          hZF 𝕀 previous hBase
  simpa [Structure.IsZeroSuccessorLimitStep,
    Structure.IsOrdinalExponentiationStep] using hStep

/--
幂递归算子的 schema 解释在所有超限序列上全定义且单值。
-/
theorem ordinalExponentiationOperator_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1)
    (hBase : ℳ.IsOrdinal (env.bound 0)) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      ((Definitional.Project.BinarySchema.ordinalExponentiationOperator 𝒞).denote
        env) := by
  have hStep :=
    ordinalExponentiationStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀 hBase
  intro sequence hSequence
  rcases hStep sequence hSequence with
    ⟨output, hOutput, hUnique⟩
  refine ⟨output, ?_, ?_⟩
  · exact
      (Definitional.Project.BinarySchema.denote_ordinalExponentiationOperator_iff
        𝕀 hZF.1 env sequence output).mpr hOutput
  · intro other hOther
    apply hUnique other
    exact
      (Definitional.Project.BinarySchema.denote_ordinalExponentiationOperator_iff
        𝕀 hZF.1 env sequence other).mp hOther

/--
固定序数底数后，序数幂关系在所有序数指数上全定义且单值。
-/
theorem ordinalExponentiation_isClassFunctionOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base : ℳ.Domain} (hBase : ℳ.IsOrdinal base) :
    ℳ.IsClassFunctionOnOrdinals
      (fun exponent power =>
        ℳ.IsOrdinalExponentiation 𝕀 power base exponent) := by
  let env : Env ℳ 1 := {
    bound := fun _ => base
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hEnvBase : ℳ.IsOrdinal (env.bound 0) := by
    simpa [env] using hBase
  have hClass :
      ℳ.IsClassFunctionOnOrdinals
        ((Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env) := by
    simpa [Definitional.Project.BinarySchema.ordinalExponentiation] using
      transfiniteRecursion_isClassFunctionOnOrdinals
        hZF 𝕀 env
        (Definitional.Project.BinarySchema.ordinalExponentiationOperator 𝒞)
        (ordinalExponentiationOperator_isClassFunctionOnTransfiniteSequences
          hZF 𝕀 env hEnvBase)
  intro exponent hExponent
  rcases hClass exponent hExponent with
    ⟨power, hPower, hUnique⟩
  refine ⟨power, ?_, ?_⟩
  · have hSemantic :=
      (Definitional.Project.BinarySchema.denote_ordinalExponentiation_iff
        𝕀 hZF.1 env exponent power).mp hPower
    simpa [env] using hSemantic
  · intro other hOther
    apply hUnique other
    apply
      (Definitional.Project.BinarySchema.denote_ordinalExponentiation_iff
        𝕀 hZF.1 env exponent other).mpr
    simpa [env] using hOther

/-- 序数幂对序数底数与序数指数存在唯一。 -/
theorem ordinalExponentiation_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base exponent : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base)
    (hExponent : ℳ.IsOrdinal exponent) :
    ∃ power,
      ℳ.IsOrdinalExponentiation 𝕀 power base exponent ∧
        ∀ other,
          ℳ.IsOrdinalExponentiation 𝕀 other base exponent →
            other = power :=
  ordinalExponentiation_isClassFunctionOnOrdinals
    hZF 𝕀 hBase exponent hExponent

/-- 加法的零步方程：`left + 0 = left`。 -/
theorem ordinalAddition_zero_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left zero : ℳ.Domain}
    (hZero : ∀ value, ¬ ℳ.mem value zero) :
    ℳ.IsOrdinalAddition 𝕀 sum left zero ↔
      sum = left := by
  have value_eq {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalAddition 𝕀 value left zero) :
      value = left := by
    rcases hValue with
      ⟨sequence, hSequence, hOutput⟩
    have hZeroLength :
        ℳ.IsZeroLengthSequence 𝕀 sequence :=
      ⟨zero, hSequence.1, hZero⟩
    rcases
        ordinalAdditionStep_isClassFunctionOnTransfiniteSequences
          hZF 𝕀 left sequence
          ⟨zero, hSequence.1⟩ with
      ⟨selected, _, hUnique⟩
    have hLeftOutput :
        ℳ.IsOrdinalAdditionStep 𝕀 left sequence left :=
      Or.inl ⟨hZeroLength, rfl⟩
    exact
      (hUnique value hOutput).trans
        (hUnique left hLeftOutput).symm
  constructor
  · exact value_eq
  · intro hEq
    subst sum
    rcases ordinalAddition_existsUnique hZF 𝕀 left
        (Structure.IsOrdinal.of_no_members hZero) with
      ⟨value, hValue, _⟩
    have hValueEq := value_eq hValue
    simpa [hValueEq] using hValue

/-- 乘法的零步方程：序数左参数乘零得到空集。 -/
theorem ordinalMultiplication_zero_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left zero : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hZero : ∀ value, ¬ ℳ.mem value zero) :
    ℳ.IsOrdinalMultiplication 𝕀 product left zero ↔
      ∀ value, ¬ ℳ.mem value product := by
  have value_empty {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalMultiplication 𝕀 value left zero) :
      ∀ member, ¬ ℳ.mem member value := by
    rcases hValue with
      ⟨sequence, hSequence, hOutput⟩
    have hZeroLength :
        ℳ.IsZeroLengthSequence 𝕀 sequence :=
      ⟨zero, hSequence.1, hZero⟩
    rcases hOutput with hOutside | hOutput
    · exact False.elim <| hOutside.1 hLeft
    · rcases hOutput.2 with
        hOutput | hOutput | hOutput
      · exact hOutput.2
      · rcases hOutput with ⟨_, hSuccessorLength, _⟩
        exact False.elim <|
          hZeroLength.not_successorLength
            hZF.1 hSuccessorLength
      · exact False.elim <|
          hZeroLength.not_limitLength hZF.1 hOutput
  constructor
  · exact value_empty
  · intro hProduct
    rcases ordinalMultiplication_existsUnique hZF 𝕀
        left (Structure.IsOrdinal.of_no_members hZero) with
      ⟨selected, hSelected, _⟩
    have hSelectedEmpty := value_empty hSelected
    have hSelectedEq : selected = product := by
      apply hZF.1.eq_of_same_members
      intro value
      exact iff_of_false
        (hSelectedEmpty value) (hProduct value)
    simpa [hSelectedEq] using hSelected

/-- 幂的零步方程：序数底数的零次幂是序数一。 -/
theorem ordinalExponentiation_zero_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power base zero : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base)
    (hZero : ∀ value, ¬ ℳ.mem value zero) :
    ℳ.IsOrdinalExponentiation 𝕀 power base zero ↔
      ℳ.IsOrdinalOne power := by
  have value_one {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalExponentiation 𝕀 value base zero) :
      ℳ.IsOrdinalOne value := by
    rcases hValue with
      ⟨sequence, hSequence, hOutput⟩
    have hZeroLength :
        ℳ.IsZeroLengthSequence 𝕀 sequence :=
      ⟨zero, hSequence.1, hZero⟩
    rcases hOutput with hOutput | hOutput | hOutput
    · exact hOutput.2
    · rcases hOutput with ⟨_, hSuccessorLength, _⟩
      exact False.elim <|
        hZeroLength.not_successorLength
          hZF.1 hSuccessorLength
    · exact False.elim <|
        hZeroLength.not_limitLength hZF.1 hOutput
  constructor
  · exact value_one
  · intro hPower
    rcases ordinalExponentiation_existsUnique hZF 𝕀
        hBase (Structure.IsOrdinal.of_no_members hZero) with
      ⟨selected, hSelected, _⟩
    have hSelectedOne := value_one hSelected
    have hSelectedEq :=
      Structure.IsOrdinalOne.eq hZF.1 hSelectedOne hPower
    simpa [hSelectedEq] using hSelected

/--
加法的后继步方程：
`left + successor` 恰为 `left + predecessor` 的后继。
-/
theorem ordinalAddition_successor_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left predecessor successor : ℳ.Domain}
    (hPredecessor : ℳ.IsOrdinal predecessor)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.IsOrdinalAddition 𝕀 sum left successor ↔
      ∃ previous,
        ℳ.IsOrdinalAddition 𝕀
            previous left predecessor ∧
          ℳ.SuccessorOf sum previous := by
  have characterize {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalAddition 𝕀 value left successor) :
      ∃ previous,
        ℳ.IsOrdinalAddition 𝕀
            previous left predecessor ∧
          ℳ.SuccessorOf value previous := by
    rcases hValue with
      ⟨sequence, hSequence, hOutput⟩
    have hPredecessorMem : ℳ.mem predecessor successor :=
      (hSuccessor predecessor).mpr
        (Or.inr fun _ => Iff.rfl)
    rcases (hSequence.1.2.2 predecessor).mp
        hPredecessorMem with
      ⟨previous, hPrevious⟩
    have hSuccessorLength :
        ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous :=
      ⟨predecessor, hPredecessor, successor, hSuccessor,
        hSequence.1, hPrevious⟩
    have hPreviousValue :
        ℳ.IsOrdinalAddition 𝕀
          previous left predecessor :=
      hSequence.recursionValue_of_pairMember
        hPredecessorMem hPrevious
    rcases hOutput with hOutput | hOutput | hOutput
    · exact False.elim <|
        hOutput.1.not_successorLength
          hZF.1 hSuccessorLength
    · rcases hOutput with
        ⟨otherPrevious, hOtherLength, hOtherOutput⟩
      have hPreviousEq :=
        hOtherLength.last_eq hZF.1 hSuccessorLength
      subst otherPrevious
      exact ⟨previous, hPreviousValue, hOtherOutput⟩
    · exact False.elim <|
        hSuccessorLength.not_limitLength hZF.1 hOutput
  constructor
  · exact characterize
  · rintro ⟨previous, hPrevious, hSum⟩
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        hPredecessor hSuccessor
    rcases ordinalAddition_existsUnique hZF 𝕀 left
        hSuccessorOrdinal with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedPrevious, hSelectedPrevious, hSelectedSum⟩
    rcases ordinalAddition_existsUnique hZF 𝕀 left
        hPredecessor with
      ⟨_, _, hPreviousUnique⟩
    have hPreviousEq : selectedPrevious = previous :=
      (hPreviousUnique selectedPrevious hSelectedPrevious).trans
        (hPreviousUnique previous hPrevious).symm
    subst selectedPrevious
    have hSelectedEq :=
      Structure.SuccessorOf.eq hZF.1 hSelectedSum hSum
    simpa [hSelectedEq] using hSelected

/--
乘法的后继步方程：
`left * successor = (left * predecessor) + left`。
-/
theorem ordinalMultiplication_successor_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left predecessor successor : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hPredecessor : ℳ.IsOrdinal predecessor)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.IsOrdinalMultiplication 𝕀
        product left successor ↔
      ∃ previous,
        ℳ.IsOrdinalMultiplication 𝕀
            previous left predecessor ∧
          ℳ.IsOrdinalAddition 𝕀 product previous left := by
  have characterize {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalMultiplication 𝕀
          value left successor) :
      ∃ previous,
        ℳ.IsOrdinalMultiplication 𝕀
            previous left predecessor ∧
          ℳ.IsOrdinalAddition 𝕀 value previous left := by
    rcases hValue with
      ⟨sequence, hSequence, hOutput⟩
    have hPredecessorMem : ℳ.mem predecessor successor :=
      (hSuccessor predecessor).mpr
        (Or.inr fun _ => Iff.rfl)
    rcases (hSequence.1.2.2 predecessor).mp
        hPredecessorMem with
      ⟨previous, hPrevious⟩
    have hSuccessorLength :
        ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous :=
      ⟨predecessor, hPredecessor, successor, hSuccessor,
        hSequence.1, hPrevious⟩
    have hPreviousValue :
        ℳ.IsOrdinalMultiplication 𝕀
          previous left predecessor :=
      hSequence.recursionValue_of_pairMember
        hPredecessorMem hPrevious
    rcases hOutput with hOutside | hOutput
    · exact False.elim <| hOutside.1 hLeft
    · rcases hOutput.2 with hOutput | hOutput | hOutput
      · exact False.elim <|
          hOutput.1.not_successorLength
            hZF.1 hSuccessorLength
      · rcases hOutput with
          ⟨otherPrevious, hOtherLength, hOtherOutput⟩
        have hPreviousEq :=
          hOtherLength.last_eq hZF.1 hSuccessorLength
        subst otherPrevious
        exact ⟨previous, hPreviousValue, hOtherOutput⟩
      · exact False.elim <|
          hSuccessorLength.not_limitLength hZF.1 hOutput
  constructor
  · exact characterize
  · rintro ⟨previous, hPrevious, hProduct⟩
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        hPredecessor hSuccessor
    rcases ordinalMultiplication_existsUnique hZF 𝕀
        left hSuccessorOrdinal with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedPrevious, hSelectedPrevious, hSelectedProduct⟩
    rcases ordinalMultiplication_existsUnique hZF 𝕀
        left hPredecessor with
      ⟨_, _, hPreviousUnique⟩
    have hPreviousEq : selectedPrevious = previous :=
      (hPreviousUnique selectedPrevious hSelectedPrevious).trans
        (hPreviousUnique previous hPrevious).symm
    subst selectedPrevious
    rcases ordinalAddition_existsUnique hZF 𝕀
        previous hLeft with
      ⟨_, _, hProductUnique⟩
    have hSelectedEq : selected = product :=
      (hProductUnique selected hSelectedProduct).trans
        (hProductUnique product hProduct).symm
    simpa [hSelectedEq] using hSelected

/--
幂的后继步方程：
`base ^ successor = (base ^ predecessor) * base`。
-/
theorem ordinalExponentiation_successor_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power base predecessor successor : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base)
    (hPredecessor : ℳ.IsOrdinal predecessor)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.IsOrdinalExponentiation 𝕀
        power base successor ↔
      ∃ previous,
        ℳ.IsOrdinalExponentiation 𝕀
            previous base predecessor ∧
          ℳ.IsOrdinalMultiplication 𝕀 power previous base := by
  have characterize {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalExponentiation 𝕀
          value base successor) :
      ∃ previous,
        ℳ.IsOrdinalExponentiation 𝕀
            previous base predecessor ∧
          ℳ.IsOrdinalMultiplication 𝕀 value previous base := by
    rcases hValue with
      ⟨sequence, hSequence, hOutput⟩
    have hPredecessorMem : ℳ.mem predecessor successor :=
      (hSuccessor predecessor).mpr
        (Or.inr fun _ => Iff.rfl)
    rcases (hSequence.1.2.2 predecessor).mp
        hPredecessorMem with
      ⟨previous, hPrevious⟩
    have hSuccessorLength :
        ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous :=
      ⟨predecessor, hPredecessor, successor, hSuccessor,
        hSequence.1, hPrevious⟩
    have hPreviousValue :
        ℳ.IsOrdinalExponentiation 𝕀
          previous base predecessor :=
      hSequence.recursionValue_of_pairMember
        hPredecessorMem hPrevious
    rcases hOutput with hOutput | hOutput | hOutput
    · exact False.elim <|
        hOutput.1.not_successorLength
          hZF.1 hSuccessorLength
    · rcases hOutput with
        ⟨otherPrevious, hOtherLength, hOtherOutput⟩
      have hPreviousEq :=
        hOtherLength.last_eq hZF.1 hSuccessorLength
      subst otherPrevious
      exact ⟨previous, hPreviousValue, hOtherOutput⟩
    · exact False.elim <|
        hSuccessorLength.not_limitLength hZF.1 hOutput
  constructor
  · exact characterize
  · rintro ⟨previous, hPrevious, hPower⟩
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        hPredecessor hSuccessor
    rcases ordinalExponentiation_existsUnique hZF 𝕀
        hBase hSuccessorOrdinal with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedPrevious, hSelectedPrevious, hSelectedPower⟩
    rcases ordinalExponentiation_existsUnique hZF 𝕀
        hBase hPredecessor with
      ⟨_, _, hPreviousUnique⟩
    have hPreviousEq : selectedPrevious = previous :=
      (hPreviousUnique selectedPrevious hSelectedPrevious).trans
        (hPreviousUnique previous hPrevious).symm
    subst selectedPrevious
    rcases ordinalMultiplication_existsUnique hZF 𝕀
        previous hBase with
      ⟨_, _, hPowerUnique⟩
    have hSelectedEq : selected = power :=
      (hPowerUnique selected hSelectedPower).trans
        (hPowerUnique power hPower).symm
    simpa [hSelectedEq] using hSelected

/--
加法的极限步方程：极限处的值是所有此前加法值组成之集合的并。
-/
theorem ordinalAddition_limit_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left limit : ℳ.Domain}
    (hLimit : ℳ.IsLimitOrdinal limit) :
    ℳ.IsOrdinalAddition 𝕀 sum left limit ↔
      ∃ range,
        (∀ value,
          ℳ.mem value range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalAddition 𝕀 value left index) ∧
          ℳ.IsUnionOf sum range := by
  have characterize {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalAddition 𝕀 value left limit) :
      ∃ range,
        (∀ member,
          ℳ.mem member range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalAddition 𝕀 member left index) ∧
          ℳ.IsUnionOf value range := by
    apply Structure.IsRecursionValue.limit_range hValue
    · intro sequence output hSequence hOutput
      rcases exists_limitLengthSequenceWithUnion
          hZF 𝕀 hSequence.1 hLimit with
        ⟨_, hCanonical⟩
      rcases hOutput with hOutput | hOutput | hOutput
      · exact False.elim <|
          hOutput.1.not_limitLength hZF.1 hCanonical
      · rcases hOutput with ⟨_, hSuccessorLength, _⟩
        exact False.elim <|
          hSuccessorLength.not_limitLength
            hZF.1 hCanonical
      · exact hOutput
    · intro index hIndex first second hFirst hSecond
      change
        ℳ.IsOrdinalAddition 𝕀 first left index
          at hFirst
      change
        ℳ.IsOrdinalAddition 𝕀 second left index
          at hSecond
      rcases ordinalAddition_existsUnique hZF 𝕀 left
          (Structure.IsOrdinal.mem hLimit.1 hIndex) with
        ⟨_, _, hUnique⟩
      exact
        (hUnique first hFirst).trans
          (hUnique second hSecond).symm
  constructor
  · exact characterize
  · rintro ⟨range, hRange, hUnion⟩
    rcases ordinalAddition_existsUnique hZF 𝕀 left
        hLimit.1 with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedRange, hSelectedRange, hSelectedUnion⟩
    have hRangeEq : range = selectedRange := by
      apply hZF.1.eq_of_same_members
      intro value
      rw [hRange value, hSelectedRange value]
    subst selectedRange
    have hValueEq :=
      Structure.IsUnionOf.eq hZF.1 hUnion hSelectedUnion
    simpa [hValueEq] using hSelected

/--
乘法的极限步方程：极限处的值是所有此前乘法值组成之集合的并。
-/
theorem ordinalMultiplication_limit_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left limit : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hLimit : ℳ.IsLimitOrdinal limit) :
    ℳ.IsOrdinalMultiplication 𝕀 product left limit ↔
      ∃ range,
        (∀ value,
          ℳ.mem value range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalMultiplication 𝕀
                value left index) ∧
          ℳ.IsUnionOf product range := by
  have characterize {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalMultiplication 𝕀 value left limit) :
      ∃ range,
        (∀ member,
          ℳ.mem member range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalMultiplication 𝕀
                member left index) ∧
          ℳ.IsUnionOf value range := by
    apply Structure.IsRecursionValue.limit_range hValue
    · intro sequence output hSequence hOutput
      rcases exists_limitLengthSequenceWithUnion
          hZF 𝕀 hSequence.1 hLimit with
        ⟨_, hCanonical⟩
      rcases hOutput with hOutside | hOutput
      · exact False.elim <| hOutside.1 hLeft
      · rcases hOutput.2 with hOutput | hOutput | hOutput
        · exact False.elim <|
            hOutput.1.not_limitLength hZF.1 hCanonical
        · rcases hOutput with ⟨_, hSuccessorLength, _⟩
          exact False.elim <|
            hSuccessorLength.not_limitLength
              hZF.1 hCanonical
        · exact hOutput
    · intro index hIndex first second hFirst hSecond
      change
        ℳ.IsOrdinalMultiplication 𝕀 first left index
          at hFirst
      change
        ℳ.IsOrdinalMultiplication 𝕀 second left index
          at hSecond
      rcases ordinalMultiplication_existsUnique hZF
          𝕀 left
          (Structure.IsOrdinal.mem hLimit.1 hIndex) with
        ⟨_, _, hUnique⟩
      exact
        (hUnique first hFirst).trans
          (hUnique second hSecond).symm
  constructor
  · exact characterize
  · rintro ⟨range, hRange, hUnion⟩
    rcases ordinalMultiplication_existsUnique hZF
        𝕀 left hLimit.1 with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedRange, hSelectedRange, hSelectedUnion⟩
    have hRangeEq : range = selectedRange := by
      apply hZF.1.eq_of_same_members
      intro value
      rw [hRange value, hSelectedRange value]
    subst selectedRange
    have hValueEq :=
      Structure.IsUnionOf.eq hZF.1 hUnion hSelectedUnion
    simpa [hValueEq] using hSelected

/--
幂的极限步方程：极限处的值是所有此前幂值组成之集合的并。
-/
theorem ordinalExponentiation_limit_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power base limit : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base)
    (hLimit : ℳ.IsLimitOrdinal limit) :
    ℳ.IsOrdinalExponentiation 𝕀 power base limit ↔
      ∃ range,
        (∀ value,
          ℳ.mem value range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalExponentiation 𝕀
                value base index) ∧
          ℳ.IsUnionOf power range := by
  have characterize {value : ℳ.Domain}
      (hValue :
        ℳ.IsOrdinalExponentiation 𝕀 value base limit) :
      ∃ range,
        (∀ member,
          ℳ.mem member range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalExponentiation 𝕀
                member base index) ∧
          ℳ.IsUnionOf value range := by
    apply Structure.IsRecursionValue.limit_range hValue
    · intro sequence output hSequence hOutput
      rcases exists_limitLengthSequenceWithUnion
          hZF 𝕀 hSequence.1 hLimit with
        ⟨_, hCanonical⟩
      rcases hOutput with hOutput | hOutput | hOutput
      · exact False.elim <|
          hOutput.1.not_limitLength hZF.1 hCanonical
      · rcases hOutput with ⟨_, hSuccessorLength, _⟩
        exact False.elim <|
          hSuccessorLength.not_limitLength
            hZF.1 hCanonical
      · exact hOutput
    · intro index hIndex first second hFirst hSecond
      change
        ℳ.IsOrdinalExponentiation 𝕀 first base index
          at hFirst
      change
        ℳ.IsOrdinalExponentiation 𝕀 second base index
          at hSecond
      rcases ordinalExponentiation_existsUnique hZF
          𝕀 hBase
          (Structure.IsOrdinal.mem hLimit.1 hIndex) with
        ⟨_, _, hUnique⟩
      exact
        (hUnique first hFirst).trans
          (hUnique second hSecond).symm
  constructor
  · exact characterize
  · rintro ⟨range, hRange, hUnion⟩
    rcases ordinalExponentiation_existsUnique hZF
        𝕀 hBase hLimit.1 with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedRange, hSelectedRange, hSelectedUnion⟩
    have hRangeEq : range = selectedRange := by
      apply hZF.1.eq_of_same_members
      intro value
      rw [hRange value, hSelectedRange value]
    subst selectedRange
    have hValueEq :=
      Structure.IsUnionOf.eq hZF.1 hUnion hSelectedUnion
    simpa [hValueEq] using hSelected

end ZF

end SetTheory
end YesMetaZFC
