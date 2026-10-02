import YesMetaZFC.SetTheory.Card.Cofinality.Basic
/-!
# 共尾序列长度
本层证明严格递增共尾序列的长度必为非零极限序数，并构造任意极限序数上的恒等共尾
序列。这两个结论只依赖共尾序列本身，供正则性与有界性共同复用。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure.IsCofinalOrdinalSequence
/-- 极限序数中的严格递增共尾序列，其长度必为非零极限序数。 -/
theorem length_isLimitOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) :
    ℳ.IsLimitOrdinal length := by
  have hLengthOrdinal :
      ℳ.IsOrdinal length :=
    hCofinal.isIncreasing.1.1.1
  rcases Structure.IsOrdinal.classify hZF.1 hLengthOrdinal with
    hEmpty | hSuccessor | hLimit
  · rcases hCofinal.isLimitOrdinal.2.1 with
      ⟨value, hValue⟩
    rcases hCofinal.isLimit.2.2 with
      ⟨range, hRange, hUnion⟩
    rcases (hUnion value).mp hValue with
      ⟨rangeValue, hRangeValue, _⟩
    rcases (hRange rangeValue).mp hRangeValue with
      ⟨index, hIndexValue⟩
    have hIndex :
        ℳ.mem index length := (hCofinal.isIncreasing.1.1.2.2 index).mpr
        ⟨rangeValue, hIndexValue⟩
    exact False.elim <| hEmpty index hIndex
  · rcases hSuccessor with
      ⟨predecessor, _, hLengthSuccessor⟩
    have hPredecessor :
        ℳ.mem predecessor length :=
      hLengthSuccessor.predecessor_mem
    rcases (hCofinal.isIncreasing.1.1.2.2 predecessor).mp
          hPredecessor with
      ⟨last, hLastValue⟩
    have hLast :
        ℳ.mem last α :=
      hCofinal.value_mem hPredecessor hLastValue
    rcases hCofinal.isLimitOrdinal.2.2 last hLast with
      ⟨larger, hLarger, hLastLarger⟩
    rcases hCofinal.isLimit.2.2 with
      ⟨range, hRange, hUnion⟩
    rcases (hUnion larger).mp hLarger with
      ⟨rangeValue, hRangeValue, hLargerRangeValue⟩
    rcases (hRange rangeValue).mp hRangeValue with
      ⟨index, hIndexValue⟩
    have hIndex :
        ℳ.mem index length := (hCofinal.isIncreasing.1.1.2.2 index).mpr
        ⟨rangeValue, hIndexValue⟩
    have hRangeValue :
        ℳ.mem rangeValue α :=
      hCofinal.value_mem hIndex hIndexValue
    rcases (hLengthSuccessor index).mp hIndex with
      hIndexPredecessor | hIndexEqPredecessor
    · have hRangeValueLast :
          ℳ.mem rangeValue last :=
        hCofinal.isIncreasing.2
          index hIndex predecessor hPredecessor
          hIndexPredecessor rangeValue last
          hIndexValue hLastValue
      have hRangeValueLarger :
          ℳ.mem rangeValue larger :=
        hCofinal.isLimitOrdinal.1.wellOrder.linear.trans
          rangeValue hRangeValue last hLast larger hLarger
          hRangeValueLast hLastLarger
      have hSelf :
          ℳ.mem rangeValue rangeValue :=
        hCofinal.isLimitOrdinal.1.wellOrder.linear.trans
          rangeValue hRangeValue larger hLarger
          rangeValue hRangeValue
          hRangeValueLarger hLargerRangeValue
      exact False.elim <|
        hCofinal.isLimitOrdinal.1.wellOrder.linear.irrefl
          rangeValue hRangeValue hSelf
    · have hIndexEq :
          index = predecessor :=
        hZF.1.eq_of_same_members
          index predecessor hIndexEqPredecessor
      subst index
      have hRangeValueEq :
          rangeValue = last :=
        hCofinal.isIncreasing.1.1.2.1.2
          predecessor rangeValue last hIndexValue hLastValue
      subst rangeValue
      have hSelf :
          ℳ.mem last last :=
        hCofinal.isLimitOrdinal.1.wellOrder.linear.trans
          last hLast larger hLarger last hLast
          hLastLarger hLargerRangeValue
      exact False.elim <|
        hCofinal.isLimitOrdinal.1.wellOrder.linear.irrefl
          last hLast hSelf
  · exact hLimit
end Structure.IsCofinalOrdinalSequence
namespace Structure.IsLimitOrdinal
/-- 极限序数上的恒等函数图给出以该序数自身为长度的严格递增共尾序列。 -/
theorem hasCofinalOrdinalSequence_self
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {α : ℳ.Domain} (hα : ℳ.IsLimitOrdinal α) :
    ℳ.HasCofinalOrdinalSequence 𝕀 α α := by
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases ZF.exists_setFunctionFromTo_of_denote
      hZF 𝕀 Definitional.Project.BinarySchema.identityValue env (by
        intro input hInput
        exact ⟨input, (Definitional.Project.Formula.denote_identityValue_iff
            hZF.1 env input input).mpr rfl⟩) (by
        intro input _ first second hFirst hSecond
        rw [Definitional.Project.Formula.denote_identityValue_iff hZF.1]
          at hFirst hSecond
        exact hFirst.symm.trans hSecond) (by
        intro input output hInput hValue
        rw [Definitional.Project.Formula.denote_identityValue_iff hZF.1]
          at hValue
        simpa [hValue] using hInput) with
    ⟨identity, hIdentityFunction, hIdentityValue⟩
  have hSequence :
      ℳ.IsSequenceOfLength 𝕀 identity α :=
    ⟨hα.1, hIdentityFunction.1, hIdentityFunction.2.1⟩
  have hOrdinalValued :
      ℳ.IsOrdinalValuedSequence 𝕀 identity α := by
    refine ⟨hSequence, ?_⟩
    intro index hIndex value hValue
    have hValueData := (hIdentityValue index value).mp hValue
    have hEq := (Definitional.Project.Formula.denote_identityValue_iff
        hZF.1 env index value).mp hValueData.2
    subst value
    exact hα.1.mem hIndex
  have hIncreasing :
      ℳ.IsIncreasingOrdinalSequence 𝕀 identity α := by
    refine ⟨hOrdinalValued, ?_⟩
    intro left hLeft right _ hLeftRight
      leftValue rightValue hLeftValue hRightValue
    have hLeftEq := (Definitional.Project.Formula.denote_identityValue_iff
        hZF.1 env left leftValue).mp ((hIdentityValue left leftValue).mp hLeftValue).2
    have hRightEq := (Definitional.Project.Formula.denote_identityValue_iff
        hZF.1 env right rightValue).mp ((hIdentityValue right rightValue).mp hRightValue).2
    simpa [← hLeftEq, ← hRightEq] using hLeftRight
  have hRange :
      ℳ.IsRangeOf 𝕀 α identity := by
    intro output
    constructor
    · intro hOutput
      exact ⟨output, (hIdentityValue output output).mpr
          ⟨hOutput, (Definitional.Project.Formula.denote_identityValue_iff
              hZF.1 env output output).mpr rfl⟩⟩
    · rintro ⟨input, hValue⟩
      have hValueData := (hIdentityValue input output).mp hValue
      have hEq := (Definitional.Project.Formula.denote_identityValue_iff
          hZF.1 env input output).mp hValueData.2
      simpa [hEq] using hValueData.1
  have hUnion :
      ℳ.IsUnionOf α α := by
    intro value
    constructor
    · intro hValue
      rcases hα.2.2 value hValue with
        ⟨larger, hLarger, hValueLarger⟩
      exact ⟨larger, hLarger, hValueLarger⟩
    · rintro ⟨member, hMember, hValueMember⟩
      exact hα.1.transitive member hMember value hValueMember
  refine ⟨identity, hα, hIncreasing, ?_, ?_⟩
  · exact ⟨hα.1, hOrdinalValued, α, hRange, hUnion⟩
  · intro index hIndex value hValue
    have hValueData := (hIdentityValue index value).mp hValue
    have hEq := (Definitional.Project.Formula.denote_identityValue_iff
        hZF.1 env index value).mp hValueData.2
    simpa [hEq] using hValueData.1
end Structure.IsLimitOrdinal
end SetTheory
end YesMetaZFC
