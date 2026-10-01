import YesMetaZFC.SetTheory.Card.Cofinality.Basic
import YesMetaZFC.SetTheory.Card.CantorBernstein
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion
/-!
# 共尾序列的复合
本层证明严格或非递减共尾序列可由模型内部函数复合，并由此得到共尾度的幂等性。
复合函数、值域和所有序列值都保留为模型内部集合编码。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure.IsCardinal
/-- 两个基数之间存在模型内部单射时，源基数不大于目标基数。 -/
theorem eq_or_mem_of_cardinalLessOrEqual
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {κ μ : ℳ.Domain} (hκ : ℳ.IsCardinal 𝕀 κ) (hμ : ℳ.IsCardinal 𝕀 μ) (hLessOrEqual : ℳ.CardinalLessOrEqual 𝕀 κ μ) :
    κ = μ ∨ ℳ.mem κ μ := by
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hκ.1 hμ.1 (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ) with
    hSame | hκμ | hμκ
  · exact Or.inl <| hZF.1.eq_of_same_members κ μ hSame
  · exact Or.inr hκμ
  · rcases hLessOrEqual with ⟨forward, hForward⟩
    rcases ZF.exists_inclusionInjection hZF 𝕀 (hκ.1.transitive μ hμκ) with
      ⟨reverse, hReverse⟩
    have hEquinumerous :=
      ZF.equinumerous_of_injections hZF 𝕀 hForward hReverse
    exact False.elim <|
      hκ.2 μ hμκ <| hEquinumerous.symm hZF 𝕀
end Structure.IsCardinal
namespace Structure.IsCofinalOrdinalSequence
/-- 共尾序列给出从其长度到目标序数的模型内部函数。 -/
theorem isSetFunctionFromTo
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) :
    ℳ.IsSetFunctionFromTo 𝕀 sequence length α := by
  have hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length :=
    hCofinal.isIncreasing.1.1
  refine ⟨hSequence.2.1, hSequence.2.2, ?_⟩
  intro index hIndex
  rcases (hSequence.2.2 index).mp hIndex with
    ⟨value, hValue⟩
  exact ⟨value, hCofinal.value_mem hIndex hValue, hValue⟩
/-- 严格递增共尾序列的函数图在其定义域上单射。 -/
theorem isSetInjectionFromTo
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) :
    ℳ.IsSetInjectionFromTo 𝕀 sequence length α := by
  have hFunction := hCofinal.isSetFunctionFromTo
  refine ⟨hFunction, ?_⟩
  intro first second output hFirst hSecond
  have hFirstLength :=
    hFunction.input_mem_of_pairMember hFirst
  have hSecondLength :=
    hFunction.input_mem_of_pairMember hSecond
  have hLengthOrdinal :=
    hCofinal.isIncreasing.1.1.1
  rcases hLengthOrdinal.wellOrder.linear.compare
      first hFirstLength second hSecondLength with
    hSame | hFirstSecond | hSecondFirst
  · exact hZF.1.eq_of_same_members first second hSame
  · have hSelf :=
      hCofinal.isIncreasing.2
        first hFirstLength second hSecondLength hFirstSecond
        output output hFirst hSecond
    have hOutputOrdinal :=
      hCofinal.isIncreasing.1.2
        first hFirstLength output hFirst
    exact False.elim <|
      hOutputOrdinal.wellOrder.linear.irrefl
        output hSelf hSelf
  · have hSelf :=
      hCofinal.isIncreasing.2
        second hSecondLength first hFirstLength hSecondFirst
        output output hSecond hFirst
    have hOutputOrdinal :=
      hCofinal.isIncreasing.1.2
        first hFirstLength output hFirst
    exact False.elim <|
      hOutputOrdinal.wellOrder.linear.irrefl
        output hSelf hSelf
/--
若 `inner` 在 `length` 中共尾，而 `outer` 在 `α` 中共尾，则函数复合
`outer ∘ inner` 仍在 `α` 中共尾。
-/
theorem exists_composition
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {outer inner outerLength innerLength α : ℳ.Domain} (hOuter :
      ℳ.IsCofinalOrdinalSequence 𝕀
        outer outerLength α) (hInner :
      ℳ.IsCofinalOrdinalSequence 𝕀
        inner innerLength outerLength) :
    ∃ composition,
      ℳ.IsCofinalOrdinalSequence 𝕀
        composition innerLength α := by
  have hOuterFunction := hOuter.isSetFunctionFromTo
  have hInnerFunction := hInner.isSetFunctionFromTo
  rcases ZF.exists_compositionFunction hZF 𝕀
      hInnerFunction hOuterFunction with
    ⟨composition, hCompositionFunction, hCompositionPairs⟩
  have hInnerLengthOrdinal :=
    hInner.isIncreasing.1.1.1
  have hCompositionSequence :
      ℳ.IsSequenceOfLength 𝕀 composition innerLength :=
    ⟨hInnerLengthOrdinal,
      hCompositionFunction.1,
      hCompositionFunction.2.1⟩
  have hCompositionOrdinalValued :
      ℳ.IsOrdinalValuedSequence 𝕀
        composition innerLength := by
    refine ⟨hCompositionSequence, ?_⟩
    intro index _ value hValue
    exact hOuter.isLimitOrdinal.1.mem <|
      hCompositionFunction.output_mem_of_pairMember hValue
  have hCompositionIncreasing :
      ℳ.IsIncreasingOrdinalSequence 𝕀
        composition innerLength := by
    refine ⟨hCompositionOrdinalValued, ?_⟩
    intro left hLeft right hRight hLeftRight
      leftValue rightValue hLeftValue hRightValue
    rcases (hCompositionPairs left leftValue).mp
        hLeftValue with
      ⟨_, leftMiddle, hLeftMiddle, hLeftOuter⟩
    rcases (hCompositionPairs right rightValue).mp
        hRightValue with
      ⟨_, rightMiddle, hRightMiddle, hRightOuter⟩
    have hLeftMiddleLength :=
      hInner.value_mem hLeft hLeftMiddle
    have hRightMiddleLength :=
      hInner.value_mem hRight hRightMiddle
    have hMiddleOrder :=
      hInner.isIncreasing.2
        left hLeft right hRight hLeftRight
        leftMiddle rightMiddle hLeftMiddle hRightMiddle
    exact hOuter.isIncreasing.2
      leftMiddle hLeftMiddleLength
      rightMiddle hRightMiddleLength hMiddleOrder
      leftValue rightValue hLeftOuter hRightOuter
  rcases ZF.exists_range_of_setFunction hZF 𝕀
      hCompositionFunction.1
      hCompositionFunction.2.1 with
    ⟨compositionRange, hCompositionRange⟩
  rcases hOuter.isLimit.2.2 with
    ⟨outerRange, hOuterRange, hOuterUnion⟩
  rcases hInner.isLimit.2.2 with
    ⟨innerRange, hInnerRange, hInnerUnion⟩
  have hCompositionUnion :
      ℳ.IsUnionOf α compositionRange := by
    intro value
    constructor
    · intro hValue
      rcases (hOuterUnion value).mp hValue with
        ⟨outerValue, hOuterValueRange, hValueOuter⟩
      rcases (hOuterRange outerValue).mp
          hOuterValueRange with
        ⟨outerIndex, hOuterIndexValue⟩
      have hOuterIndexLength :=
        hOuterFunction.input_mem_of_pairMember
          hOuterIndexValue
      rcases (hInnerUnion outerIndex).mp
          hOuterIndexLength with
        ⟨innerValue, hInnerValueRange, hOuterIndexInner⟩
      rcases (hInnerRange innerValue).mp
          hInnerValueRange with
        ⟨innerIndex, hInnerIndexValue⟩
      have hInnerIndexLength :=
        hInnerFunction.input_mem_of_pairMember
          hInnerIndexValue
      have hInnerValueLength :=
        hInner.value_mem hInnerIndexLength hInnerIndexValue
      rcases hOuterFunction.2.2 innerValue
          hInnerValueLength with
        ⟨composedValue, hComposedValueα, hInnerOuter⟩
      have hCompositionValue :
          ℳ.PairMember 𝕀
            innerIndex composedValue composition := (hCompositionPairs innerIndex composedValue).mpr
          ⟨hInnerIndexLength, innerValue,
            hInnerIndexValue, hInnerOuter⟩
      have hOuterValueComposed :
          ℳ.mem outerValue composedValue :=
        hOuter.isIncreasing.2
          outerIndex hOuterIndexLength
          innerValue hInnerValueLength hOuterIndexInner
          outerValue composedValue
          hOuterIndexValue hInnerOuter
      have hComposedValueOrdinal :=
        hOuter.isLimitOrdinal.1.mem hComposedValueα
      exact
        ⟨composedValue, (hCompositionRange composedValue).mpr
            ⟨innerIndex, hCompositionValue⟩,
          hComposedValueOrdinal.transitive
            outerValue hOuterValueComposed
            value hValueOuter⟩
    · rintro ⟨composedValue, hComposedRange, hValueComposed⟩
      rcases (hCompositionRange composedValue).mp
          hComposedRange with
        ⟨index, hCompositionValue⟩
      have hComposedValueα :=
        hCompositionFunction.output_mem_of_pairMember
          hCompositionValue
      exact hOuter.isLimitOrdinal.1.transitive
        composedValue hComposedValueα
        value hValueComposed
  have hCompositionLimit :
      ℳ.IsOrdinalSequenceLimit 𝕀
        α composition innerLength :=
    ⟨hOuter.isLimitOrdinal.1,
      hCompositionOrdinalValued,
      compositionRange,
      hCompositionRange,
      hCompositionUnion⟩
  refine ⟨composition, hOuter.isLimitOrdinal,
    hCompositionIncreasing, hCompositionLimit, ?_⟩
  intro index _ value hValue
  exact hCompositionFunction.output_mem_of_pairMember hValue
end Structure.IsCofinalOrdinalSequence
namespace Structure.IsCofinalNondecreasingOrdinalSequence
/--
若 `inner` 在 `outerLength` 中严格共尾，而 `outer` 在 `α` 中非递减共尾，
则函数复合 `outer ∘ inner` 仍在 `α` 中非递减共尾。
-/
theorem exists_composition
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {outer inner outerLength innerLength α : ℳ.Domain} (hOuter :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        outer outerLength α) (hInner :
      ℳ.IsCofinalOrdinalSequence 𝕀
        inner innerLength outerLength) :
    ∃ composition,
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        composition innerLength α := by
  have hOuterFunction := hOuter.isSetFunctionFromTo
  have hInnerFunction := hInner.isSetFunctionFromTo
  rcases ZF.exists_compositionFunction hZF 𝕀
      hInnerFunction hOuterFunction with
    ⟨composition, hCompositionFunction, hCompositionPairs⟩
  have hInnerLengthOrdinal :=
    hInner.isIncreasing.1.1.1
  have hCompositionSequence :
      ℳ.IsSequenceOfLength 𝕀 composition innerLength :=
    ⟨hInnerLengthOrdinal,
      hCompositionFunction.1,
      hCompositionFunction.2.1⟩
  have hCompositionOrdinalValued :
      ℳ.IsOrdinalValuedSequence 𝕀
        composition innerLength := by
    refine ⟨hCompositionSequence, ?_⟩
    intro index _ value hValue
    exact hOuter.isLimitOrdinal.1.mem <|
      hCompositionFunction.output_mem_of_pairMember hValue
  have hCompositionNondecreasing :
      ℳ.IsNondecreasingOrdinalSequence 𝕀
        composition innerLength := by
    refine ⟨hCompositionOrdinalValued, ?_⟩
    intro left hLeft right hRight hLeftRight
      leftValue rightValue hLeftValue hRightValue
    rcases (hCompositionPairs left leftValue).mp hLeftValue with
      ⟨_, leftMiddle, hLeftMiddle, hLeftOuter⟩
    rcases (hCompositionPairs right rightValue).mp hRightValue with
      ⟨_, rightMiddle, hRightMiddle, hRightOuter⟩
    have hLeftMiddleLength :=
      hInner.value_mem hLeft hLeftMiddle
    have hRightMiddleLength :=
      hInner.value_mem hRight hRightMiddle
    have hMiddleOrder :=
      hInner.isIncreasing.2
        left hLeft right hRight hLeftRight
        leftMiddle rightMiddle hLeftMiddle hRightMiddle
    exact hOuter.isNondecreasing.2
      leftMiddle hLeftMiddleLength
      rightMiddle hRightMiddleLength hMiddleOrder
      leftValue rightValue hLeftOuter hRightOuter
  rcases ZF.exists_range_of_setFunction hZF 𝕀
      hCompositionFunction.1
      hCompositionFunction.2.1 with
    ⟨compositionRange, hCompositionRange⟩
  rcases hOuter.isLimit.2.2 with
    ⟨outerRange, hOuterRange, hOuterUnion⟩
  rcases hInner.isLimit.2.2 with
    ⟨innerRange, hInnerRange, hInnerUnion⟩
  have hCompositionUnion :
      ℳ.IsUnionOf α compositionRange := by
    intro value
    constructor
    · intro hValue
      rcases (hOuterUnion value).mp hValue with
        ⟨outerValue, hOuterValueRange, hValueOuter⟩
      rcases (hOuterRange outerValue).mp hOuterValueRange with
        ⟨outerIndex, hOuterIndexValue⟩
      have hOuterIndexLength :=
        hOuterFunction.input_mem_of_pairMember hOuterIndexValue
      rcases (hInnerUnion outerIndex).mp hOuterIndexLength with
        ⟨innerValue, hInnerValueRange, hOuterIndexInner⟩
      rcases (hInnerRange innerValue).mp hInnerValueRange with
        ⟨innerIndex, hInnerIndexValue⟩
      have hInnerIndexLength :=
        hInnerFunction.input_mem_of_pairMember hInnerIndexValue
      have hInnerValueLength :=
        hInner.value_mem hInnerIndexLength hInnerIndexValue
      rcases hOuterFunction.2.2 innerValue hInnerValueLength with
        ⟨composedValue, hComposedValueα, hInnerOuter⟩
      have hCompositionValue :
          ℳ.PairMember 𝕀
            innerIndex composedValue composition := (hCompositionPairs innerIndex composedValue).mpr
          ⟨hInnerIndexLength, innerValue,
            hInnerIndexValue, hInnerOuter⟩
      have hOuterValueComposed :=
        hOuter.isNondecreasing.2
          outerIndex hOuterIndexLength
          innerValue hInnerValueLength hOuterIndexInner
          outerValue composedValue
          hOuterIndexValue hInnerOuter
      have hValueComposed : ℳ.mem value composedValue := by
        rcases hOuterValueComposed with hSame | hMember
        · simpa [hSame] using hValueOuter
        · exact (hOuter.isLimitOrdinal.1.mem hComposedValueα).transitive
              outerValue hMember value hValueOuter
      exact ⟨composedValue, (hCompositionRange composedValue).mpr
          ⟨innerIndex, hCompositionValue⟩,
        hValueComposed⟩
    · rintro ⟨composedValue, hComposedRange, hValueComposed⟩
      rcases (hCompositionRange composedValue).mp hComposedRange with
        ⟨index, hCompositionValue⟩
      have hComposedValueα :=
        hCompositionFunction.output_mem_of_pairMember hCompositionValue
      exact hOuter.isLimitOrdinal.1.transitive
        composedValue hComposedValueα value hValueComposed
  have hCompositionLimit :
      ℳ.IsOrdinalSequenceLimit 𝕀
        α composition innerLength :=
    ⟨hOuter.isLimitOrdinal.1,
      hCompositionOrdinalValued,
      compositionRange,
      hCompositionRange,
      hCompositionUnion⟩
  refine ⟨composition, hOuter.isLimitOrdinal,
    hCompositionNondecreasing, hCompositionLimit, ?_⟩
  intro index _ value hValue
  exact hCompositionFunction.output_mem_of_pairMember hValue
end Structure.IsCofinalNondecreasingOrdinalSequence
namespace Structure.IsCofinality
/-- 引理 3.6：若 `κ = cf(α)` 且 `μ = cf(κ)`，则 `μ = κ`。 -/
theorem idempotent
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {α κ μ : ℳ.Domain} (hκ : ℳ.IsCofinality 𝕀 κ α) (hμ : ℳ.IsCofinality 𝕀 μ κ) :
    μ = κ := by
  rcases hκ.hasCofinalSequence with
    ⟨outer, hOuter⟩
  rcases hμ.hasCofinalSequence with
    ⟨inner, hInner⟩
  rcases hOuter.exists_composition hZF 𝕀 hInner with
    ⟨composition, hComposition⟩
  have hκLeμ :=
    hκ.minimal ⟨composition, hComposition⟩
  have hμLeκ :=
    hμ.isCardinal.eq_or_mem_of_cardinalLessOrEqual
      hZF 𝕀 hκ.isCardinal
      ⟨inner, hInner.isSetInjectionFromTo hZF 𝕀⟩
  rcases hμLeκ with hEq | hμκ
  · exact hEq
  rcases hκLeμ with hEq | hκμ
  · exact hEq.symm
  have hSelf : ℳ.mem κ κ :=
    hκ.isCardinal.1.transitive μ hμκ κ hκμ
  exact False.elim <|
    hκ.isCardinal.1.wellOrder.linear.irrefl
      κ hSelf hSelf
end Structure.IsCofinality
end SetTheory
end YesMetaZFC
