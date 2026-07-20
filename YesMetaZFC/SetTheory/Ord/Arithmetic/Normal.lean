import YesMetaZFC.SetTheory.Ord.Arithmetic.Identity

/-!
# 序数加法与乘法的正规性

本文件证明固定左参数后的序数加法是正规函数，并证明固定非零序数左参数后的序数
乘法是正规函数。乘法必须显式排除零左因子，因为常值零函数不严格递增。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace ZF

/-- 固定序数左参数的序数加法在右参数上严格递增。 -/
theorem ordinalAddition_isIncreasingOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeft : ℳ.IsOrdinal left) :
    ℳ.IsIncreasingOnOrdinals
      (fun right sum =>
        ℳ.IsOrdinalAddition 𝕀 sum left right) := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env =
        fun right sum =>
          ℳ.IsOrdinalAddition 𝕀 sum left right := by
    funext right sum
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalAddition_iff
        𝕀 hZF.1 env right sum
  have hIncreasing :
      ℳ.IsIncreasingOnOrdinals
        ((Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env) := by
    apply increasingOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞)
    intro α hα hPrevious predecessor
      hPredecessorOrdinal predecessorValue αValue
      hPredecessorValue hαValue
    rw [hRelation] at hPrevious hPredecessorValue hαValue
    rcases hα.classify hZF.1 with
      hEmpty | hSuccessor | hLimit
    · exact False.elim
        (hEmpty predecessor hPredecessorOrdinal)
    · rcases hSuccessor with
        ⟨immediate, hImmediateOrdinal, hSuccessor⟩
      rcases (ordinalAddition_successor_iff
          hZF 𝕀 hImmediateOrdinal hSuccessor).mp
          hαValue with
        ⟨immediateValue, hImmediateValue, hValueSuccessor⟩
      have hImmediateMem : ℳ.mem immediate α :=
        (hSuccessor immediate).mpr
          (Or.inr fun _ => Iff.rfl)
      have hImmediateValueMem : ℳ.mem immediateValue αValue :=
        (hValueSuccessor immediateValue).mpr
          (Or.inr fun _ => Iff.rfl)
      rcases (hSuccessor predecessor).mp hPredecessorOrdinal with
        hEarlier | hSame
      · have hEarlierValue : ℳ.mem predecessorValue immediateValue :=
          hPrevious immediate hImmediateMem
            predecessor hEarlier predecessorValue immediateValue
            hPredecessorValue hImmediateValue
        exact
          (ordinalAddition_isOrdinal hZF 𝕀
            hLeft hα hαValue).transitive
            immediateValue hImmediateValueMem
            predecessorValue hEarlierValue
      · have hEq :=
          hZF.1.eq_of_same_members predecessor immediate hSame
        subst predecessor
        rcases ordinalAddition_existsUnique hZF 𝕀
            left hImmediateOrdinal with
          ⟨_, _, hUnique⟩
        have hValueEq : predecessorValue = immediateValue :=
          (hUnique predecessorValue hPredecessorValue).trans
            (hUnique immediateValue hImmediateValue).symm
        simpa [hValueEq] using hImmediateValueMem
    · rcases (ordinalAddition_limit_iff
          hZF 𝕀 hLimit).mp hαValue with
        ⟨range, hRange, hUnion⟩
      rcases hLimit.2.2 predecessor hPredecessorOrdinal with
        ⟨larger, hLarger, hPredecessorLarger⟩
      rcases ordinalAddition_existsUnique hZF 𝕀
          left (hLimit.1.mem hLarger) with
        ⟨largerValue, hLargerValue, _⟩
      have hPredecessorValueLarger :
          ℳ.mem predecessorValue largerValue :=
        hPrevious larger hLarger
          predecessor hPredecessorLarger
          predecessorValue largerValue
          hPredecessorValue hLargerValue
      exact (hUnion predecessorValue).mpr
        ⟨largerValue,
          (hRange largerValue).mpr
            ⟨larger, hLarger, hLargerValue⟩,
          hPredecessorValueLarger⟩
  rw [hRelation] at hIncreasing
  exact hIncreasing

/-- 固定序数左参数的序数加法在非零极限右参数处连续。 -/
theorem ordinalAddition_isContinuousOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} :
    ℳ.IsContinuousOnOrdinals
      (fun right sum =>
        ℳ.IsOrdinalAddition 𝕀 sum left right) := by
  intro α value hData
  exact
    (ordinalAddition_limit_iff
      hZF 𝕀 hData.1).mp hData.2

/-- 固定序数左参数的序数加法是正规序数函数。 -/
theorem ordinalAddition_isNormalOrdinalFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeft : ℳ.IsOrdinal left) :
    ℳ.IsNormalOrdinalFunction
      (fun right sum =>
        ℳ.IsOrdinalAddition 𝕀 sum left right) :=
  ⟨ordinalAddition_isOrdinalClassFunction
      hZF 𝕀 hLeft,
    ordinalAddition_isIncreasingOnOrdinals
      hZF 𝕀 hLeft,
    ordinalAddition_isContinuousOnOrdinals
      hZF 𝕀⟩

/-- 固定非零序数左参数的序数乘法在右参数上严格递增。 -/
theorem ordinalMultiplication_isIncreasingOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeft : ℳ.IsOrdinal left)
    (hLeftNonempty : ∃ value, ℳ.mem value left) :
    ℳ.IsIncreasingOnOrdinals
      (fun right product =>
        ℳ.IsOrdinalMultiplication 𝕀 product left right) := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env =
        fun right product =>
          ℳ.IsOrdinalMultiplication 𝕀 product left right := by
    funext right product
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalMultiplication_iff
        𝕀 hZF.1 env right product
  have hIncreasing :
      ℳ.IsIncreasingOnOrdinals
        ((Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env) := by
    apply increasingOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞)
    intro α hα hPrevious predecessor
      hPredecessorOrdinal predecessorValue αValue
      hPredecessorValue hαValue
    rw [hRelation] at hPrevious hPredecessorValue hαValue
    rcases hα.classify hZF.1 with
      hEmpty | hSuccessor | hLimit
    · exact False.elim
        (hEmpty predecessor hPredecessorOrdinal)
    · rcases hSuccessor with
        ⟨immediate, hImmediateOrdinal, hSuccessor⟩
      rcases (ordinalMultiplication_successor_iff
          hZF 𝕀 hLeft hImmediateOrdinal hSuccessor).mp
          hαValue with
        ⟨immediateValue, hImmediateValue, hValueAddition⟩
      have hImmediateMem : ℳ.mem immediate α :=
        (hSuccessor immediate).mpr
          (Or.inr fun _ => Iff.rfl)
      have hImmediateValueOrdinal : ℳ.IsOrdinal immediateValue :=
        ordinalMultiplication_isOrdinal hZF 𝕀
          hLeft hImmediateOrdinal hImmediateValue
      rcases KP.exists_empty (ZF.modelsKP hZF) with
        ⟨zero, hZero⟩
      have hZeroOrdinal : ℳ.IsOrdinal zero :=
        Structure.IsOrdinal.of_no_members hZero
      have hZeroLeft : ℳ.mem zero left :=
        hLeft.empty_mem_of_nonempty
          (ZF.modelsKP hZF) hLeftNonempty hZero
      have hImmediatePlusZero :
          ℳ.IsOrdinalAddition 𝕀
            immediateValue immediateValue zero :=
        (ordinalAddition_zero_iff
          hZF 𝕀 hZero).mpr rfl
      have hImmediateValueMem : ℳ.mem immediateValue αValue :=
        ordinalAddition_isIncreasingOnOrdinals
          hZF 𝕀 hImmediateValueOrdinal
          zero left hZeroOrdinal hLeft hZeroLeft
          immediateValue αValue
          hImmediatePlusZero hValueAddition
      rcases (hSuccessor predecessor).mp hPredecessorOrdinal with
        hEarlier | hSame
      · have hEarlierValue : ℳ.mem predecessorValue immediateValue :=
          hPrevious immediate hImmediateMem
            predecessor hEarlier predecessorValue immediateValue
            hPredecessorValue hImmediateValue
        exact
          (ordinalMultiplication_isOrdinal hZF 𝕀
            hLeft hα hαValue).transitive
            immediateValue hImmediateValueMem
            predecessorValue hEarlierValue
      · have hEq :=
          hZF.1.eq_of_same_members predecessor immediate hSame
        subst predecessor
        rcases ordinalMultiplication_existsUnique hZF 𝕀
            left hImmediateOrdinal with
          ⟨_, _, hUnique⟩
        have hValueEq : predecessorValue = immediateValue :=
          (hUnique predecessorValue hPredecessorValue).trans
            (hUnique immediateValue hImmediateValue).symm
        simpa [hValueEq] using hImmediateValueMem
    · rcases (ordinalMultiplication_limit_iff
          hZF 𝕀 hLeft hLimit).mp hαValue with
        ⟨range, hRange, hUnion⟩
      rcases hLimit.2.2 predecessor hPredecessorOrdinal with
        ⟨larger, hLarger, hPredecessorLarger⟩
      rcases ordinalMultiplication_existsUnique hZF 𝕀
          left (hLimit.1.mem hLarger) with
        ⟨largerValue, hLargerValue, _⟩
      have hPredecessorValueLarger :
          ℳ.mem predecessorValue largerValue :=
        hPrevious larger hLarger
          predecessor hPredecessorLarger
          predecessorValue largerValue
          hPredecessorValue hLargerValue
      exact (hUnion predecessorValue).mpr
        ⟨largerValue,
          (hRange largerValue).mpr
            ⟨larger, hLarger, hLargerValue⟩,
          hPredecessorValueLarger⟩
  rw [hRelation] at hIncreasing
  exact hIncreasing

/-- 固定序数左参数的序数乘法在非零极限右参数处连续。 -/
theorem ordinalMultiplication_isContinuousOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeft : ℳ.IsOrdinal left) :
    ℳ.IsContinuousOnOrdinals
      (fun right product =>
        ℳ.IsOrdinalMultiplication 𝕀 product left right) := by
  intro α value hData
  exact
    (ordinalMultiplication_limit_iff
      hZF 𝕀 hLeft hData.1).mp hData.2

/-- 固定非零序数左参数的序数乘法是正规序数函数。 -/
theorem ordinalMultiplication_isNormalOrdinalFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeft : ℳ.IsOrdinal left)
    (hLeftNonempty : ∃ value, ℳ.mem value left) :
    ℳ.IsNormalOrdinalFunction
      (fun right product =>
        ℳ.IsOrdinalMultiplication 𝕀 product left right) :=
  ⟨ordinalMultiplication_isOrdinalClassFunction
      hZF 𝕀 hLeft,
    ordinalMultiplication_isIncreasingOnOrdinals
      hZF 𝕀 hLeft hLeftNonempty,
    ordinalMultiplication_isContinuousOnOrdinals
      hZF 𝕀 hLeft⟩

/-- 固定非零序数底数的幂在所有序数指数处非空。 -/
theorem ordinalExponentiation_isNonemptyOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base : ℳ.Domain} (hBase : ℳ.IsOrdinal base)
    (hBaseNonempty : ∃ value, ℳ.mem value base) :
    ∀ exponent, ℳ.IsOrdinal exponent →
      ∀ power,
        ℳ.IsOrdinalExponentiation 𝕀 power base exponent →
          ∃ member, ℳ.mem member power := by
  let env : Env ℳ 1 := {
    bound := fun _ => base
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env =
        fun exponent power =>
          ℳ.IsOrdinalExponentiation 𝕀
            power base exponent := by
    funext exponent power
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalExponentiation_iff
        𝕀 hZF.1 env exponent power
  have hNonempty :=
    nonemptyValuesOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞)
      (fun exponent hExponent hPrevious power hPower => by
        rw [hRelation] at hPrevious hPower
        rcases hExponent.classify hZF.1 with
          hZero | hSuccessor | hLimit
        · have hPowerOne :=
            (ordinalExponentiation_zero_iff
              hZF 𝕀 hBase hZero).mp hPower
          rcases hPowerOne with
            ⟨zero, hEmpty, hPowerSuccessor⟩
          exact ⟨zero, (hPowerSuccessor zero).mpr
            (Or.inr fun _ => Iff.rfl)⟩
        · rcases hSuccessor with
            ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
          rcases (ordinalExponentiation_successor_iff
              hZF 𝕀 hBase
              hPredecessorOrdinal hSuccessor).mp hPower with
            ⟨previous, hPreviousPower, hProduct⟩
          have hPredecessorMem : ℳ.mem predecessor exponent :=
            (hSuccessor predecessor).mpr
              (Or.inr fun _ => Iff.rfl)
          have hPreviousNonempty :=
            hPrevious predecessor hPredecessorMem
              previous hPreviousPower
          rcases KP.exists_empty (ZF.modelsKP hZF) with
            ⟨zero, hZero⟩
          have hZeroBase : ℳ.mem zero base :=
            hBase.empty_mem_of_nonempty
              (ZF.modelsKP hZF) hBaseNonempty hZero
          have hPreviousOrdinal :=
            ordinalExponentiation_isOrdinal hZF
              𝕀 hBase hPredecessorOrdinal
              hPreviousPower
          rcases ordinalMultiplication_existsUnique hZF
              𝕀 previous
              (Structure.IsOrdinal.of_no_members hZero) with
            ⟨previousTimesZero, hPreviousTimesZero, _⟩
          have hPreviousTimesZeroEmpty :=
            (ordinalMultiplication_zero_iff
              hZF 𝕀 hPreviousOrdinal hZero).mp
              hPreviousTimesZero
          have hPreviousTimesZeroMem :
              ℳ.mem previousTimesZero power :=
            ordinalMultiplication_isIncreasingOnOrdinals
              hZF 𝕀 hPreviousOrdinal
              hPreviousNonempty
              zero base
              (Structure.IsOrdinal.of_no_members hZero) hBase
              hZeroBase previousTimesZero power
              hPreviousTimesZero hProduct
          exact ⟨previousTimesZero, hPreviousTimesZeroMem⟩
        · rcases (ordinalExponentiation_limit_iff
              hZF 𝕀 hBase hLimit).mp hPower with
            ⟨range, hRange, hUnion⟩
          rcases hLimit.2.1 with ⟨index, hIndex⟩
          rcases ordinalExponentiation_existsUnique hZF
              𝕀 hBase
              (hLimit.1.mem hIndex) with
            ⟨indexValue, hIndexValue, _⟩
          rcases hPrevious index hIndex
              indexValue hIndexValue with
            ⟨member, hMember⟩
          exact ⟨member, (hUnion member).mpr
            ⟨indexValue,
              (hRange indexValue).mpr
                ⟨index, hIndex, hIndexValue⟩,
              hMember⟩⟩)
  rw [hRelation] at hNonempty
  exact hNonempty

/-- 固定大于一的序数底数后，序数幂在指数上严格递增。 -/
theorem ordinalExponentiation_isIncreasingOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base one : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base) (hOne : ℳ.IsOrdinalOne one)
    (hOneBase : ℳ.mem one base) :
    ℳ.IsIncreasingOnOrdinals
      (fun exponent power =>
        ℳ.IsOrdinalExponentiation 𝕀
          power base exponent) := by
  have hBaseNonempty : ∃ value, ℳ.mem value base :=
    ⟨one, hOneBase⟩
  let env : Env ℳ 1 := {
    bound := fun _ => base
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env =
        fun exponent power =>
          ℳ.IsOrdinalExponentiation 𝕀
            power base exponent := by
    funext exponent power
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalExponentiation_iff
        𝕀 hZF.1 env exponent power
  have hIncreasing :
      ℳ.IsIncreasingOnOrdinals
        ((Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env) := by
    apply increasingOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞)
    intro exponent hExponent hPrevious predecessor
      hPredecessorOrdinal predecessorValue exponentValue
      hPredecessorValue hExponentValue
    rw [hRelation] at hPrevious hPredecessorValue hExponentValue
    rcases hExponent.classify hZF.1 with
      hZero | hSuccessor | hLimit
    · exact False.elim (hZero predecessor hPredecessorOrdinal)
    · rcases hSuccessor with
        ⟨immediate, hImmediateOrdinal, hSuccessor⟩
      rcases (ordinalExponentiation_successor_iff
          hZF 𝕀 hBase
          hImmediateOrdinal hSuccessor).mp hExponentValue with
        ⟨immediateValue, hImmediateValue, hProduct⟩
      have hImmediateMem : ℳ.mem immediate exponent :=
        (hSuccessor immediate).mpr
          (Or.inr fun _ => Iff.rfl)
      have hImmediateValueOrdinal :=
        ordinalExponentiation_isOrdinal hZF
          𝕀 hBase hImmediateOrdinal
          hImmediateValue
      have hImmediateValueNonempty :=
        ordinalExponentiation_isNonemptyOnOrdinals
          hZF 𝕀 hBase hBaseNonempty
          immediate hImmediateOrdinal
          immediateValue hImmediateValue
      rcases ordinalMultiplication_existsUnique hZF
          𝕀 immediateValue
          (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hOne) with
        ⟨immediateTimesOne, hImmediateTimesOne, _⟩
      have hImmediateTimesOneEq :=
        ordinalMultiplication_one_right
          hZF 𝕀 hImmediateValueOrdinal
          hOne hImmediateTimesOne
      have hImmediateValueMem : ℳ.mem immediateValue exponentValue := by
        have hComparison :=
          ordinalMultiplication_isIncreasingOnOrdinals
            hZF 𝕀 hImmediateValueOrdinal
            hImmediateValueNonempty
            one base
            (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hOne)
            hBase hOneBase
            immediateTimesOne exponentValue
            hImmediateTimesOne hProduct
        simpa [hImmediateTimesOneEq] using hComparison
      rcases (hSuccessor predecessor).mp hPredecessorOrdinal with
        hEarlier | hSame
      · have hEarlierValue : ℳ.mem predecessorValue immediateValue :=
          hPrevious immediate hImmediateMem
            predecessor hEarlier predecessorValue immediateValue
            hPredecessorValue hImmediateValue
        exact
          (ordinalExponentiation_isOrdinal hZF
            𝕀 hBase hExponent hExponentValue).transitive
            immediateValue hImmediateValueMem
            predecessorValue hEarlierValue
      · have hEq :=
          hZF.1.eq_of_same_members predecessor immediate hSame
        subst predecessor
        rcases ordinalExponentiation_existsUnique hZF
            𝕀 hBase hImmediateOrdinal with
          ⟨_, _, hUnique⟩
        have hValueEq : predecessorValue = immediateValue :=
          (hUnique predecessorValue hPredecessorValue).trans
            (hUnique immediateValue hImmediateValue).symm
        simpa [hValueEq] using hImmediateValueMem
    · rcases (ordinalExponentiation_limit_iff
          hZF 𝕀 hBase hLimit).mp hExponentValue with
        ⟨range, hRange, hUnion⟩
      rcases hLimit.2.2 predecessor hPredecessorOrdinal with
        ⟨larger, hLarger, hPredecessorLarger⟩
      rcases ordinalExponentiation_existsUnique hZF
          𝕀 hBase (hLimit.1.mem hLarger) with
        ⟨largerValue, hLargerValue, _⟩
      have hPredecessorValueLarger :
          ℳ.mem predecessorValue largerValue :=
        hPrevious larger hLarger
          predecessor hPredecessorLarger
          predecessorValue largerValue
          hPredecessorValue hLargerValue
      exact (hUnion predecessorValue).mpr
        ⟨largerValue,
          (hRange largerValue).mpr
            ⟨larger, hLarger, hLargerValue⟩,
          hPredecessorValueLarger⟩
  rw [hRelation] at hIncreasing
  exact hIncreasing

/-- 固定大于一的序数底数后，序数幂是正规序数函数。 -/
theorem ordinalExponentiation_isNormalOrdinalFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base one : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base) (hOne : ℳ.IsOrdinalOne one)
    (hOneBase : ℳ.mem one base) :
    ℳ.IsNormalOrdinalFunction
      (fun exponent power =>
        ℳ.IsOrdinalExponentiation 𝕀
          power base exponent) :=
  ⟨ordinalExponentiation_isOrdinalClassFunction
      hZF 𝕀 hBase,
    ordinalExponentiation_isIncreasingOnOrdinals
      hZF 𝕀 hBase hOne hOneBase,
    fun _ _ hData =>
      (ordinalExponentiation_limit_iff
        hZF 𝕀 hBase hData.1).mp hData.2⟩

/-- 序数加法值不小于右参数。 -/
theorem ordinalAddition_right_eq_or_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hRight : ℳ.IsOrdinal right)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum left right) :
    right = sum ∨ ℳ.mem right sum := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env =
        fun input output =>
          ℳ.IsOrdinalAddition 𝕀 output left input := by
    funext input output
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalAddition_iff
        𝕀 hZF.1 env input output
  have hNormal :
      ℳ.IsNormalOrdinalFunction
        ((Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env) := by
    rw [hRelation]
    exact ordinalAddition_isNormalOrdinalFunction
      hZF 𝕀 hLeft
  have hDominates :=
    normalValuesDominateInputs hZF env
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞) hNormal
      right hRight sum
  rw [hRelation] at hDominates
  exact hDominates hSum

/-- 非零左因子的序数乘法值不小于右参数。 -/
theorem ordinalMultiplication_right_eq_or_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hLeftNonempty : ∃ value, ℳ.mem value left)
    (hRight : ℳ.IsOrdinal right)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left right) :
    right = product ∨ ℳ.mem right product := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env =
        fun input output =>
          ℳ.IsOrdinalMultiplication 𝕀 output left input := by
    funext input output
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalMultiplication_iff
        𝕀 hZF.1 env input output
  have hNormal :
      ℳ.IsNormalOrdinalFunction
        ((Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env) := by
    rw [hRelation]
    exact ordinalMultiplication_isNormalOrdinalFunction
      hZF 𝕀 hLeft hLeftNonempty
  have hDominates :=
    normalValuesDominateInputs hZF env
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞) hNormal
      right hRight product
  rw [hRelation] at hDominates
  exact hDominates hProduct

/-- 底数大于一时，序数幂值不小于指数。 -/
theorem ordinalExponentiation_exponent_eq_or_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power base exponent one : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base) (hOne : ℳ.IsOrdinalOne one)
    (hOneBase : ℳ.mem one base)
    (hExponent : ℳ.IsOrdinal exponent)
    (hPower :
      ℳ.IsOrdinalExponentiation 𝕀 power base exponent) :
    exponent = power ∨ ℳ.mem exponent power := by
  let env : Env ℳ 1 := {
    bound := fun _ => base
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env =
        fun input output =>
          ℳ.IsOrdinalExponentiation 𝕀
            output base input := by
    funext input output
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalExponentiation_iff
        𝕀 hZF.1 env input output
  have hNormal :
      ℳ.IsNormalOrdinalFunction
        ((Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env) := by
    rw [hRelation]
    exact ordinalExponentiation_isNormalOrdinalFunction
      hZF 𝕀 hBase hOne hOneBase
  have hDominates :=
    normalValuesDominateInputs hZF env
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞) hNormal
      exponent hExponent power
  rw [hRelation] at hDominates
  exact hDominates hPower

end ZF

end SetTheory
end YesMetaZFC
