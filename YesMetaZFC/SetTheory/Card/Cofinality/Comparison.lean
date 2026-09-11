import YesMetaZFC.SetTheory.Card.Cofinality.OrderType
/-!
# 共尾度比较
本层用序数良序给模型内部满射选择最小原像，并构造非递减共尾序列的首次越过函数。
这些选择函数把共尾子集的序型比较提升为基数比较，最终给出引理 3.7(ii)。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Definitional
namespace Project
namespace UnarySchema
/-- 从序数源集中筛出固定函数值的全部原像。 -/
def functionPreimageMember (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := Formula.orderedPairMem 𝒞
    Term.newest (.bound 1) (.bound 2)
/-- 从序列长度中筛出其值严格超过固定序数的全部索引。 -/
def sequenceIndexAboveMember (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := .existsE <| .conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 0) (.bound 3)) (.mem (.bound 2) (.bound 0))
end UnarySchema
namespace BinarySchema
/-- 以序数良序选择固定函数值的最小原像。 -/
def leastPreimageValue (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .conj (.mem (.bound 0) (.bound 2)) <| .conj (Formula.orderedPairMem 𝒞 (.bound 0) (.bound 1) (.bound 3)) <|
    Formula.forallMem (.bound 0) <| .neg <|
      Formula.orderedPairMem 𝒞
        Term.newest (.bound 2) (.bound 4)
/-- 选择共尾序列中首个严格超过输入序数的索引。 -/
def firstIndexAboveValue (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .conj (.mem (.bound 0) (.bound 2)) <| .conj (.existsE <| .conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 0) (.bound 4))
      (.mem (.bound 2) (.bound 0))) <|
    Formula.forallMem (.bound 0) <| .neg <| .existsE <| .conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 0) (.bound 5)) (.mem (.bound 3) (.bound 0))
end BinarySchema
namespace Formula
/-- 函数原像成员模式的纸面语义。 -/
theorem satisfies_functionPreimageMember_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 2) (index : ℳ.Domain) :
    satisfies (env.push index) (UnarySchema.functionPreimageMember 𝒞).body ↔
      ℳ.PairMember 𝕀 index (env.bound 0) (env.bound 1) := by
  simp only [UnarySchema.functionPreimageMember,
    satisfies_orderedPairMem_iff 𝕀]
  rfl
/-- 序列越过索引模式的纸面语义。 -/
theorem satisfies_sequenceIndexAboveMember_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 2) (index : ℳ.Domain) :
    satisfies (env.push index) (UnarySchema.sequenceIndexAboveMember 𝒞).body ↔
      ∃ value,
        ℳ.PairMember 𝕀 index value (env.bound 1) ∧
          ℳ.mem (env.bound 0) value := by
  simp only [UnarySchema.sequenceIndexAboveMember,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_orderedPairMem_iff 𝕀, satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push]
  rfl
/-- 最小原像值模式的纸面语义。 -/
theorem denote_leastPreimageValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.leastPreimageValue 𝒞).denote
        env input output ↔
      ℳ.mem output (env.bound 0) ∧
        ℳ.PairMember 𝕀 output input (env.bound 1) ∧
          ∀ earlier, ℳ.mem earlier output →
            ¬ ℳ.PairMember 𝕀 earlier input (env.bound 1) := by
  simp only [BinarySchema.leastPreimageValue,
    BinarySchema.denote, satisfies_conj_iff,
    satisfies_mem_iff, satisfies_orderedPairMem_iff 𝕀,
    satisfies_forallMem_iff, satisfies_neg_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push]
  rfl
/-- 首次越过值模式的纸面语义。 -/
theorem denote_firstIndexAboveValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.firstIndexAboveValue 𝒞).denote
        env input output ↔
      ℳ.mem output (env.bound 0) ∧ (∃ value,
          ℳ.PairMember 𝕀 output value (env.bound 1) ∧
            ℳ.mem input value) ∧
          ∀ earlier, ℳ.mem earlier output →
            ¬ ∃ value,
              ℳ.PairMember 𝕀 earlier value (env.bound 1) ∧
                ℳ.mem input value := by
  simp only [BinarySchema.firstIndexAboveValue,
    BinarySchema.denote, satisfies_conj_iff,
    satisfies_exists_iff, satisfies_mem_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_forallMem_iff, satisfies_neg_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl
end Formula
end Project
end Definitional
open Definitional.Project
namespace ZF
/--
若模型内部函数从序数 `source` 满射到 `target`，逐点选择最小原像可得到
从 `target` 到 `source` 的模型内部单射。
-/
theorem exists_rightInverseInjection_of_surjection_from_ordinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {function source target : ℳ.Domain} (hSourceOrdinal : ℳ.IsOrdinal source) (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function source target) (hSurjective :
      ℳ.IsSetSurjectiveOnto 𝕀 function source target) :
    ∃ inverse,
      ℳ.IsSetInjectionFromTo 𝕀 inverse target source := by
  let env : Env ℳ 2 := {
    bound := Fin.cases source <| Fin.cases function Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setInjectionFromTo_of_denote
      hZF 𝕀 (BinarySchema.leastPreimageValue 𝒞) env
  · intro input hInput
    rcases hSurjective input hInput with
      ⟨witness, hWitnessSource, hWitnessPair⟩
    let preimageEnv : Env ℳ 2 := {
      bound := Fin.cases input <| Fin.cases function Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases separation_exists_d hZF (UnarySchema.functionPreimageMember 𝒞)
        preimageEnv source with
      ⟨preimage, hPreimage⟩
    have hPreimageSemantic (index : ℳ.Domain) :
        ℳ.mem index preimage ↔
          ℳ.mem index source ∧
            ℳ.PairMember 𝕀 index input function := by
      rw [hPreimage index,
        Formula.satisfies_functionPreimageMember_iff 𝕀]
      rfl
    have hPreimageSubset :
        ℳ.MemberSubset preimage source := by
      intro index hIndex
      exact ((hPreimageSemantic index).mp hIndex).1
    have hPreimageNonempty :
        ∃ index, ℳ.mem index preimage :=
      ⟨witness, (hPreimageSemantic witness).mpr
        ⟨hWitnessSource, hWitnessPair⟩⟩
    rcases hSourceOrdinal.wellOrder.least
        preimage hPreimageSubset hPreimageNonempty with
      ⟨least, hLeastPreimage, hLeast⟩
    have hLeastData := (hPreimageSemantic least).mp hLeastPreimage
    refine ⟨least, (Formula.denote_leastPreimageValue_iff
        𝕀 env input least).mpr ?_⟩
    refine ⟨hLeastData.1, hLeastData.2, ?_⟩
    intro earlier hEarlierLeast hEarlierPair
    have hEarlierSource :=
      hSourceOrdinal.transitive
        least hLeastData.1 earlier hEarlierLeast
    have hEarlierPreimage :
        ℳ.mem earlier preimage := (hPreimageSemantic earlier).mpr
        ⟨hEarlierSource, hEarlierPair⟩
    rcases hLeast earlier hEarlierPreimage with
      hSame | hLeastEarlier
    · have hEq :=
        hZF.1.eq_of_same_members least earlier hSame
      subst earlier
      exact hSourceOrdinal.wellOrder.linear.irrefl
        least hLeastData.1 hEarlierLeast
    · have hLeastOrdinal :=
        hSourceOrdinal.mem hLeastData.1
      have hSelf :=
        hLeastOrdinal.transitive
          earlier hEarlierLeast least hLeastEarlier
      exact hLeastOrdinal.wellOrder.linear.irrefl
        least hSelf hSelf
  · intro input _ first second hFirst hSecond
    rw [Formula.denote_leastPreimageValue_iff 𝕀]
      at hFirst hSecond
    rcases hSourceOrdinal.wellOrder.linear.compare
        first hFirst.1 second hSecond.1 with
      hSame | hFirstSecond | hSecondFirst
    · exact hZF.1.eq_of_same_members first second hSame
    · exact False.elim <|
        hSecond.2.2 first hFirstSecond hFirst.2.1
    · exact False.elim <|
        hFirst.2.2 second hSecondFirst hSecond.2.1
  · intro input output _ hValue
    rw [Formula.denote_leastPreimageValue_iff 𝕀] at hValue
    exact hValue.1
  · intro first second output _ _ hFirst hSecond
    rw [Formula.denote_leastPreimageValue_iff 𝕀]
      at hFirst hSecond
    exact hFunction.1.2 output first second
      hFirst.2.1 hSecond.2.1
end ZF
namespace Structure.IsCofinalNondecreasingOrdinalSequence
/--
非递减共尾序列为目标序数中的每个输入选择首个严格超过它的序列索引。
-/
theorem exists_firstIndexAboveFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) :
    ∃ firstIndex,
      ℳ.IsSetFunctionFromTo 𝕀 firstIndex α length ∧
        ∀ input output,
          ℳ.PairMember 𝕀 input output firstIndex ↔
            ℳ.mem input α ∧
              ℳ.mem output length ∧ (∃ value,
                  ℳ.PairMember 𝕀 output value sequence ∧
                    ℳ.mem input value) ∧
                  ∀ earlier, ℳ.mem earlier output →
                    ¬ ∃ value,
                      ℳ.PairMember 𝕀 earlier value sequence ∧
                        ℳ.mem input value := by
  have hSequenceFunction := hCofinal.isSetFunctionFromTo
  rcases hCofinal.isLimit.2.2 with
    ⟨range, hRange, hUnion⟩
  let env : Env ℳ 2 := {
    bound := Fin.cases length <| Fin.cases sequence Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases ZF.exists_setFunctionFromTo_of_denote
      hZF 𝕀 (BinarySchema.firstIndexAboveValue 𝒞) env (by
        intro input hInput
        rcases (hUnion input).mp hInput with
          ⟨value, hValueRange, hInputValue⟩
        rcases (hRange value).mp hValueRange with
          ⟨witness, hWitnessValue⟩
        have hWitnessLength :=
          hSequenceFunction.input_mem_of_pairMember hWitnessValue
        let candidateEnv : Env ℳ 2 := {
          bound := Fin.cases input <| Fin.cases sequence Fin.elim0
          free := fun _ => Classical.choice ℳ.nonempty
        }
        rcases ZF.separation_exists_d hZF (UnarySchema.sequenceIndexAboveMember 𝒞)
            candidateEnv length with
          ⟨candidates, hCandidates⟩
        have hCandidatesSemantic (index : ℳ.Domain) :
            ℳ.mem index candidates ↔
              ℳ.mem index length ∧
                ∃ selectedValue,
                  ℳ.PairMember 𝕀 index selectedValue sequence ∧
                    ℳ.mem input selectedValue := by
          rw [hCandidates index,
            Formula.satisfies_sequenceIndexAboveMember_iff 𝕀]
          rfl
        have hCandidatesSubset :
            ℳ.MemberSubset candidates length := by
          intro index hIndex
          exact ((hCandidatesSemantic index).mp hIndex).1
        have hCandidatesNonempty :
            ∃ index, ℳ.mem index candidates :=
          ⟨witness, (hCandidatesSemantic witness).mpr
            ⟨hWitnessLength, value,
              hWitnessValue, hInputValue⟩⟩
        have hLengthOrdinal :=
          hCofinal.isNondecreasing.1.1.1
        rcases hLengthOrdinal.wellOrder.least
            candidates hCandidatesSubset hCandidatesNonempty with
          ⟨least, hLeastCandidate, hLeast⟩
        have hLeastData := (hCandidatesSemantic least).mp hLeastCandidate
        refine ⟨least, (Formula.denote_firstIndexAboveValue_iff
            𝕀 env input least).mpr ?_⟩
        refine ⟨hLeastData.1, hLeastData.2, ?_⟩
        intro earlier hEarlierLeast hEarlierValue
        have hEarlierLength :=
          hLengthOrdinal.transitive
            least hLeastData.1 earlier hEarlierLeast
        have hEarlierCandidate :
            ℳ.mem earlier candidates := (hCandidatesSemantic earlier).mpr
            ⟨hEarlierLength, hEarlierValue⟩
        rcases hLeast earlier hEarlierCandidate with
          hSame | hLeastEarlier
        · have hEq :=
            hZF.1.eq_of_same_members least earlier hSame
          subst earlier
          exact hLengthOrdinal.wellOrder.linear.irrefl
            least hLeastData.1 hEarlierLeast
        · have hLeastOrdinal :=
            hLengthOrdinal.mem hLeastData.1
          have hSelf :=
            hLeastOrdinal.transitive
              earlier hEarlierLeast least hLeastEarlier
          exact hLeastOrdinal.wellOrder.linear.irrefl
            least hSelf hSelf) (by
        intro input _ first second hFirst hSecond
        rw [Formula.denote_firstIndexAboveValue_iff 𝕀]
          at hFirst hSecond
        have hLengthOrdinal :=
          hCofinal.isNondecreasing.1.1.1
        rcases hLengthOrdinal.wellOrder.linear.compare
            first hFirst.1 second hSecond.1 with
          hSame | hFirstSecond | hSecondFirst
        · exact hZF.1.eq_of_same_members first second hSame
        · exact False.elim <|
            hSecond.2.2 first hFirstSecond hFirst.2.1
        · exact False.elim <|
            hFirst.2.2 second hSecondFirst hSecond.2.1) (by
        intro input output _ hValue
        rw [Formula.denote_firstIndexAboveValue_iff 𝕀] at hValue
        exact hValue.1) with
    ⟨firstIndex, hFirstIndex, hFirstIndexPairs⟩
  refine ⟨firstIndex, hFirstIndex, ?_⟩
  intro input output
  rw [hFirstIndexPairs input output,
    Formula.denote_firstIndexAboveValue_iff 𝕀]
  rfl
end Structure.IsCofinalNondecreasingOrdinalSequence
namespace Structure.IsCofinality
/--
若以基数 `source` 为定义域的模型内部函数具有在 `α` 中共尾的精确值域，
则 `cf(α) ≤ source`。
-/
theorem eq_or_mem_of_cofinalFunctionRange
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {κ α function source range : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 κ α) (hSourceCardinal : ℳ.IsCardinal 𝕀 source) (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function source α) (hRange : ℳ.IsRangeOf 𝕀 range function) (hCofinalRange : ℳ.IsCofinalSubset range α) :
    κ = source ∨ ℳ.mem κ source := by
  have hFunctionToRange :
      ℳ.IsSetFunctionFromTo 𝕀 function source range := by
    refine ⟨hFunction.1, hFunction.2.1, ?_⟩
    intro input hInput
    rcases hFunction.2.2 input hInput with
      ⟨output, _, hPair⟩
    exact ⟨output, (hRange output).mpr ⟨input, hPair⟩,
      hPair⟩
  have hSurjective :
      ℳ.IsSetSurjectiveOnto 𝕀 function source range := by
    intro output hOutput
    rcases (hRange output).mp hOutput with
      ⟨input, hPair⟩
    exact ⟨input,
      hFunction.input_mem_of_pairMember hPair,
      hPair⟩
  rcases ZF.exists_rightInverseInjection_of_surjection_from_ordinal
      hZF 𝕀 hSourceCardinal.1 hFunctionToRange hSurjective with
    ⟨rangeToSource, hRangeToSource⟩
  rcases ZF.exists_membershipWellOrderType_of_subsetOrdinal
      hZF 𝕀 hCofinalRange.1.1 hCofinalRange.2.1 with
    ⟨relation, orderType, hRelation, hOrder, hOrderType⟩
  have hOrderTypeOrdinal :=
    hOrderType.isOrdinal hZF 𝕀 hOrder
  have hCofinalityOrderType :=
    hCofinalRange.cofinality_le_orderType
      hZF 𝕀 hRelation hOrder hOrderType hCofinality
  rcases (hOrderType.equinumerous hZF 𝕀 hOrder).symm
      hZF 𝕀 with
    ⟨orderTypeToRange, hOrderTypeToRange⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hOrderTypeToRange.1 hRangeToSource with
    ⟨orderTypeToSource, hOrderTypeToSource⟩
  rcases hCofinalityOrderType with hSame | hκOrderType
  · subst orderType
    exact hCofinality.isCardinal.eq_or_mem_of_cardinalLessOrEqual
      hZF 𝕀 hSourceCardinal
      ⟨orderTypeToSource, hOrderTypeToSource⟩
  · rcases ZF.exists_inclusionInjection hZF 𝕀 (hOrderTypeOrdinal.transitive κ hκOrderType) with
      ⟨κToOrderType, hκToOrderType⟩
    rcases ZF.exists_compositionInjection hZF 𝕀
        hκToOrderType hOrderTypeToSource with
      ⟨κToSource, hκToSource⟩
    exact hCofinality.isCardinal.eq_or_mem_of_cardinalLessOrEqual
      hZF 𝕀 hSourceCardinal
      ⟨κToSource, hκToSource⟩
end Structure.IsCofinality
namespace Structure.IsCofinalNondecreasingOrdinalSequence
/-- 引理 3.7(ii)：非递减共尾 `length`-序列保持共尾度。 -/
theorem cofinality_eq_lengthCofinality
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {sequence length α κ μ : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) (hLengthCofinality : ℳ.IsCofinality 𝕀 κ length) (hTargetCofinality : ℳ.IsCofinality 𝕀 μ α) :
    κ = μ := by
  -- 复合 `cf(length) → length → α`，其值域共尾，得到 `cf(α) ≤ cf(length)`。
  rcases hLengthCofinality.hasCofinalSequence with
    ⟨lengthSequence, hLengthSequence⟩
  rcases hCofinal.exists_composition hZF 𝕀 hLengthSequence with
    ⟨targetComposition, hTargetComposition⟩
  have hTargetCompositionFunction :=
    hTargetComposition.isSetFunctionFromTo
  rcases ZF.exists_range_of_setFunction hZF 𝕀
      hTargetCompositionFunction.1
      hTargetCompositionFunction.2.1 with
    ⟨targetRange, hTargetRange⟩
  have hTargetRangeCofinal :=
    hTargetComposition.range_isCofinalSubset hZF.1 hTargetRange
  have hTargetLeLength :=
    hTargetCofinality.eq_or_mem_of_cofinalFunctionRange
      hZF 𝕀 hLengthCofinality.isCardinal
      hTargetCompositionFunction hTargetRange hTargetRangeCofinal
  -- 对 `α` 的共尾序列逐点取首次越过索引，所得值域在 `length` 中共尾。
  rcases hTargetCofinality.hasCofinalSequence with
    ⟨targetSequence, hTargetSequence⟩
  rcases hCofinal.exists_firstIndexAboveFunction hZF 𝕀 with
    ⟨firstIndex, hFirstIndexFunction, hFirstIndexPairs⟩
  rcases ZF.exists_compositionFunction hZF 𝕀
      hTargetSequence.isSetFunctionFromTo
      hFirstIndexFunction with
    ⟨indexSequence, hIndexSequenceFunction, hIndexSequencePairs⟩
  rcases ZF.exists_range_of_setFunction hZF 𝕀
      hIndexSequenceFunction.1
      hIndexSequenceFunction.2.1 with
    ⟨indexRange, hIndexRange⟩
  have hLengthOrdinal :=
    hLengthSequence.isLimitOrdinal.1
  have hSequenceFunction :=
    hCofinal.isSetFunctionFromTo
  have hIndexRangeCofinal :
      ℳ.IsCofinalSubset indexRange length := by
    refine ⟨hLengthSequence.isLimitOrdinal, ?_, ?_⟩
    · intro index hIndex
      rcases (hIndexRange index).mp hIndex with
        ⟨input, hPair⟩
      exact hIndexSequenceFunction.output_mem_of_pairMember hPair
    · intro index
      constructor
      · intro hIndexLength
        rcases hSequenceFunction.2.2 index hIndexLength with
          ⟨indexValue, hIndexValueα, hIndexValuePair⟩
        rcases hTargetSequence.isLimit.2.2 with
          ⟨targetSequenceRange, hTargetSequenceRange,
            hTargetSequenceUnion⟩
        rcases (hTargetSequenceUnion indexValue).mp hIndexValueα with
          ⟨targetValue, hTargetValueRange, hIndexValueTarget⟩
        rcases (hTargetSequenceRange targetValue).mp
            hTargetValueRange with
          ⟨targetIndex, hTargetIndexValue⟩
        have hTargetIndexκ :=
          hTargetSequence.isSetFunctionFromTo.input_mem_of_pairMember
            hTargetIndexValue
        have hTargetValueα :=
          hTargetSequence.value_mem hTargetIndexκ hTargetIndexValue
        rcases hFirstIndexFunction.2.2 targetValue hTargetValueα with
          ⟨selectedIndex, hSelectedIndexLength,
            hTargetValueSelectedIndex⟩
        rcases (hFirstIndexPairs targetValue selectedIndex).mp
            hTargetValueSelectedIndex with
          ⟨_, _, hSelectedValue, _⟩
        rcases hSelectedValue with
          ⟨selectedValue, hSelectedIndexValue,
            hTargetValueSelected⟩
        have hIndexValueOrdinal :=
          hCofinal.isNondecreasing.1.2
            index hIndexLength indexValue hIndexValuePair
        have hSelectedValueOrdinal :=
          hCofinal.isNondecreasing.1.2
            selectedIndex hSelectedIndexLength
            selectedValue hSelectedIndexValue
        have hIndexValueSelected :
            ℳ.mem indexValue selectedValue :=
          hSelectedValueOrdinal.transitive
            targetValue hTargetValueSelected
            indexValue hIndexValueTarget
        have hIndexSelected :
            ℳ.mem index selectedIndex := by
          rcases hLengthOrdinal.wellOrder.linear.compare
              index hIndexLength
              selectedIndex hSelectedIndexLength with
            hSame | hIndexSelected | hSelectedIndex
          · have hIndexEq :=
              hZF.1.eq_of_same_members
                index selectedIndex hSame
            subst selectedIndex
            have hValueEq :=
              hSequenceFunction.1.2
                index indexValue selectedValue
                hIndexValuePair hSelectedIndexValue
            subst selectedValue
            exact False.elim <|
              hIndexValueOrdinal.wellOrder.linear.irrefl
                indexValue hIndexValueSelected hIndexValueSelected
          · exact hIndexSelected
          · rcases hCofinal.isNondecreasing.2
                selectedIndex hSelectedIndexLength
                index hIndexLength hSelectedIndex
                selectedValue indexValue
                hSelectedIndexValue hIndexValuePair with
              hSameValue | hSelectedValueIndex
            · subst selectedValue
              exact False.elim <|
                hIndexValueOrdinal.wellOrder.linear.irrefl
                  indexValue hIndexValueSelected hIndexValueSelected
            · have hSelf :=
                hIndexValueOrdinal.transitive
                  selectedValue hSelectedValueIndex
                  indexValue hIndexValueSelected
              exact False.elim <|
                hIndexValueOrdinal.wellOrder.linear.irrefl
                  indexValue hSelf hSelf
        have hIndexSequencePair :
            ℳ.PairMember 𝕀
              targetIndex selectedIndex indexSequence := (hIndexSequencePairs targetIndex selectedIndex).mpr
            ⟨hTargetIndexκ, targetValue,
              hTargetIndexValue, hTargetValueSelectedIndex⟩
        exact ⟨selectedIndex, (hIndexRange selectedIndex).mpr
            ⟨targetIndex, hIndexSequencePair⟩,
          hIndexSelected⟩
      · rintro ⟨selectedIndex, hSelectedRange, hIndexSelected⟩
        rcases (hIndexRange selectedIndex).mp hSelectedRange with
          ⟨targetIndex, hTargetIndexSelected⟩
        have hSelectedIndexLength :=
          hIndexSequenceFunction.output_mem_of_pairMember
            hTargetIndexSelected
        exact hLengthOrdinal.transitive
          selectedIndex hSelectedIndexLength
          index hIndexSelected
  have hLengthLeTarget :=
    hLengthCofinality.eq_or_mem_of_cofinalFunctionRange
      hZF 𝕀 hTargetCofinality.isCardinal
      hIndexSequenceFunction hIndexRange hIndexRangeCofinal
  -- 两个初始序数双向不大于；若均严格小于，就产生循环隶属。
  rcases hLengthLeTarget with hSame | hκμ
  · exact hSame
  rcases hTargetLeLength with hSame | hμκ
  · exact hSame.symm
  have hκOrdinal :=
    hLengthCofinality.isCardinal.1
  have hSelf :=
    hκOrdinal.transitive μ hμκ κ hκμ
  exact False.elim <|
    hκOrdinal.wellOrder.linear.irrefl κ hSelf hSelf
end Structure.IsCofinalNondecreasingOrdinalSequence
end SetTheory
end YesMetaZFC
