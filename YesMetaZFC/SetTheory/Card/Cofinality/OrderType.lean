import YesMetaZFC.SetTheory.Card.Cofinality.Composition
import YesMetaZFC.SetTheory.Ord.OrderType
/-!
# 共尾子集的序型
本层把序数子集上的成员关系集合化为模型内部良序，并证明共尾子集的成员关系序型
给出一条严格递增共尾枚举。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace ZF
/-- 序数子集上的成员关系可集合化为良序，并具有规范序型。 -/
theorem exists_membershipWellOrderType_of_subsetOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {carrier α : ℳ.Domain} (hα : ℳ.IsOrdinal α) (hCarrierSubset : ℳ.MemberSubset carrier α) :
    ∃ relation orderType, (∀ left right,
        ℳ.PairMember 𝕀 left right relation ↔
          ℳ.mem left carrier ∧
            ℳ.mem right carrier ∧
              ℳ.mem left right) ∧
        ℳ.IsSetCodedWellOrder 𝕀 relation carrier ∧
          ℳ.IsWellOrderType 𝕀
            relation carrier orderType := by
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_setRelationOn_of_denote hZF 𝕀
      Definitional.Project.RelationSchema.membership
      env carrier with
    ⟨relation, hRelationOn, hRelationPairs⟩
  have hRelation (left right : ℳ.Domain) :
      ℳ.PairMember 𝕀 left right relation ↔
        ℳ.mem left carrier ∧
          ℳ.mem right carrier ∧
            ℳ.mem left right := by
    simpa [Definitional.Project.RelationSchema.membership,
      Definitional.Project.BinarySchema.denote,
      Definitional.Project.Formula.satisfies_mem_iff]
      using! hRelationPairs left right
  have hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier := by
    refine ⟨⟨hRelationOn.1, ?_⟩, ?_⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro value hValue hSelf
        exact hα.wellOrder.linear.irrefl
          value (hCarrierSubset value hValue) ((hRelation value value).mp hSelf).2.2
      · intro left hLeft middle hMiddle right hRight
          hLeftMiddle hMiddleRight
        exact (hRelation left right).mpr
          ⟨hLeft, hRight,
            hα.wellOrder.linear.trans
              left (hCarrierSubset left hLeft)
              middle (hCarrierSubset middle hMiddle)
              right (hCarrierSubset right hRight) ((hRelation left middle).mp hLeftMiddle).2.2 ((hRelation middle right).mp hMiddleRight).2.2⟩
      · intro left hLeft right hRight
        rcases hα.wellOrder.linear.compare
            left (hCarrierSubset left hLeft)
            right (hCarrierSubset right hRight) with
          hSame | hLeftRight | hRightLeft
        · exact Or.inl hSame
        · exact Or.inr <| Or.inl <| (hRelation left right).mpr
              ⟨hLeft, hRight, hLeftRight⟩
        · exact Or.inr <| Or.inr <| (hRelation right left).mpr
              ⟨hRight, hLeft, hRightLeft⟩
    · intro subset hSubset hNonempty
      rcases hα.wellOrder.least subset (fun value hValue =>
            hCarrierSubset value (hSubset value hValue))
          hNonempty with
        ⟨least, hLeastSubset, hLeast⟩
      refine ⟨least, hLeastSubset, ?_⟩
      intro value hValue
      rcases hLeast value hValue with hSame | hLeastValue
      · exact Or.inl hSame
      · exact Or.inr <| (hRelation least value).mpr
          ⟨hSubset least hLeastSubset,
            hSubset value hValue, hLeastValue⟩
  rcases wellOrderType_existsUnique hZF 𝕀 hOrder with
    ⟨orderType, hOrderType, _⟩
  exact ⟨relation, orderType, hRelation, hOrder, hOrderType⟩
end ZF
namespace Structure.IsCofinalSubset
/--
共尾子集的成员关系规范序型给出其严格递增枚举，因此也是目标序数的共尾序列长度。
-/
theorem orderType_hasCofinalSequence
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {set α relation orderType : ℳ.Domain} (hCofinal : ℳ.IsCofinalSubset set α) (hRelation : ∀ left right,
      ℳ.PairMember 𝕀 left right relation ↔
        ℳ.mem left set ∧
          ℳ.mem right set ∧
            ℳ.mem left right) (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation set) (hOrderType :
      ℳ.IsWellOrderType 𝕀 relation set orderType) :
    ℳ.HasCofinalOrdinalSequence 𝕀 orderType α := by
  have hOrderTypeOrdinal :=
    hOrderType.isOrdinal hZF 𝕀 hOrder
  rcases hOrderType with
    ⟨collapse, hCollapse, hCollapseRange⟩
  have hCollapseFunction :
      ℳ.IsSetFunctionFromTo 𝕀
        collapse set orderType := by
    refine ⟨hCollapse.1, hCollapse.2.1, ?_⟩
    intro input hInput
    rcases (hCollapse.2.1 input).mp hInput with
      ⟨output, hOutput⟩
    exact ⟨output, (hCollapseRange output).mpr
        ⟨input, hOutput⟩,
      hOutput⟩
  have hCollapseSurjective :
      ℳ.IsSetSurjectiveOnto 𝕀
        collapse set orderType := by
    intro output hOutput
    rcases (hCollapseRange output).mp hOutput with
      ⟨input, hInputOutput⟩
    exact ⟨input,
      hCollapseFunction.input_mem_of_pairMember
        hInputOutput,
      hInputOutput⟩
  have hCollapseBijection :
      ℳ.IsSetBijectionFromTo 𝕀
        collapse set orderType :=
    ⟨⟨hCollapseFunction,
      hCollapse.isSetInjective hZF 𝕀 hOrder⟩,
      hCollapseSurjective⟩
  rcases ZF.exists_inverseBijectionWithPairs hZF 𝕀
      hCollapseBijection with
    ⟨sequence, hSequenceBijection, hSequencePairs⟩
  have hSequenceFunction :=
    hSequenceBijection.1.1
  have hSequenceOfLength :
      ℳ.IsSequenceOfLength 𝕀 sequence orderType :=
    ⟨hOrderTypeOrdinal,
      hSequenceFunction.1,
      hSequenceFunction.2.1⟩
  have hSequenceOrdinalValued :
      ℳ.IsOrdinalValuedSequence 𝕀
        sequence orderType := by
    refine ⟨hSequenceOfLength, ?_⟩
    intro index _ value hValue
    exact hCofinal.1.1.mem <|
      hCofinal.2.1 value <|
        hSequenceFunction.output_mem_of_pairMember hValue
  have hSequenceIncreasing :
      ℳ.IsIncreasingOrdinalSequence 𝕀
        sequence orderType := by
    refine ⟨hSequenceOrdinalValued, ?_⟩
    intro left hLeft right hRight hLeftRight
      leftValue rightValue hLeftValue hRightValue
    have hLeftCollapse := (hSequencePairs left leftValue).mp hLeftValue
    have hRightCollapse := (hSequencePairs right rightValue).mp hRightValue
    have hRelationValue :
        ℳ.PairMember 𝕀 leftValue rightValue relation := (hCollapse.relation_iff_mem hZF 𝕀 hOrder
        hLeftCollapse hRightCollapse).mpr hLeftRight
    exact (hRelation leftValue rightValue).mp
      hRelationValue |>.2.2
  have hSequenceRange :
      ℳ.IsRangeOf 𝕀 set sequence := by
    intro value
    constructor
    · intro hValue
      rcases hSequenceBijection.2 value hValue with
        ⟨index, _, hIndexValue⟩
      exact ⟨index, hIndexValue⟩
    · rintro ⟨index, hIndexValue⟩
      exact hSequenceFunction.output_mem_of_pairMember
        hIndexValue
  have hSequenceLimit :
      ℳ.IsOrdinalSequenceLimit 𝕀
        α sequence orderType :=
    ⟨hCofinal.1.1,
      hSequenceOrdinalValued,
      set, hSequenceRange, hCofinal.2.2⟩
  refine ⟨sequence, hCofinal.1,
    hSequenceIncreasing, hSequenceLimit, ?_⟩
  intro index _ value hValue
  exact hCofinal.2.1 value <|
    hSequenceFunction.output_mem_of_pairMember hValue
/-- 引理 3.7(i)：共尾子集的成员关系序型至少为目标序数的共尾度。 -/
theorem cofinality_le_orderType
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {set α relation orderType κ : ℳ.Domain} (hCofinal : ℳ.IsCofinalSubset set α) (hRelation : ∀ left right,
      ℳ.PairMember 𝕀 left right relation ↔
        ℳ.mem left set ∧
          ℳ.mem right set ∧
            ℳ.mem left right) (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation set) (hOrderType :
      ℳ.IsWellOrderType 𝕀 relation set orderType) (hCofinality : ℳ.IsCofinality 𝕀 κ α) :
    κ = orderType ∨ ℳ.mem κ orderType :=
  hCofinality.minimal <|
    hCofinal.orderType_hasCofinalSequence
      hZF 𝕀 hRelation hOrder hOrderType
end Structure.IsCofinalSubset
end SetTheory
end YesMetaZFC
