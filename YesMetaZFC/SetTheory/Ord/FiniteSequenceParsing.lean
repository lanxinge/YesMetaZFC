import YesMetaZFC.SetTheory.Ord.Natural
/-!
# 模型内部有限序列的完整解析
有限序列不在元层强行转换成 `List`：模型中的 `ω` 可以包含外部看来的非标准元素。
本模块因此以定义域、函数图和点值关系为解析数据，给出长度唯一性、逐点值唯一性，
以及非空序列唯一的“前缀 + 末项”分解。这正是对象语言字符串解析所需的模型内接口。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/-- 定义域属于模型 `ω` 的序列。 -/
def IsFiniteSequenceOfLength
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω sequence length : ℳ.Domain) : Prop :=
  ℳ.mem length ω ∧ ℳ.IsSequenceOfLength 𝕀 sequence length
/-- 存在某个模型内部有限长度的序列。 -/
def IsFiniteSequence
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω sequence : ℳ.Domain) : Prop :=
  ∃ length, ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length
/-- 非空有限序列的末项解析证书。 -/
structure IsFiniteSequenceLastDecomposition
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω sequence length predecessor prefix_graph last : ℳ.Domain) : Prop where
  source : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length
  predecessor_mem_omega : ℳ.mem predecessor ω
  length_successor : ℳ.SuccessorOf length predecessor
  prefix_sequence :
    ℳ.IsFiniteSequenceOfLength 𝕀 ω prefix_graph predecessor
  prefix_restriction :
    ℳ.IsRestrictionOf 𝕀 prefix_graph sequence predecessor
  last_value : ℳ.PairMember 𝕀 predecessor last sequence
namespace IsFiniteSequenceOfLength
/-- 同一序列的有限长度唯一。 -/
theorem length_unique
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω sequence left right : ℳ.Domain} (hLeft : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence left) (hRight : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence right) :
    left = right :=
  IsSequenceOfLength.length_eq hExt hLeft.2 hRight.2
/-- 有限序列的长度存在且唯一。 -/
theorem existsUnique_length
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω sequence : ℳ.Domain} (hSequence : ℳ.IsFiniteSequence 𝕀 ω sequence) :
    ∃ length,
      ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length ∧
        ∀ other,
          ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence other →
            other = length := by
  rcases hSequence with ⟨length, hLength⟩
  refine ⟨length, hLength, ?_⟩
  intro other hOther
  exact (hLength.length_unique hExt hOther).symm
/-- 在序列定义域中的每个位置都有唯一值。 -/
theorem value_existsUnique
    {ℳ : Structure.{u}} {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω sequence length index : ℳ.Domain} (hSequence : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length) (hIndex : ℳ.mem index length) :
    ∃ value,
      ℳ.PairMember 𝕀 index value sequence ∧
        ∀ other,
          ℳ.PairMember 𝕀 index other sequence →
            other = value := by
  rcases (hSequence.2.2.2 index).mp hIndex with ⟨value, hValue⟩
  refine ⟨value, hValue, ?_⟩
  intro other hOther
  exact (hSequence.2.2.1.2 index value other hValue hOther).symm
/-- 两个有限序列若逐点相同，则其函数图相同。 -/
theorem eq_of_pairMember_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω first second firstLength secondLength : ℳ.Domain} (hFirst : ℳ.IsFiniteSequenceOfLength 𝕀 ω first firstLength)
    (hSecond : ℳ.IsFiniteSequenceOfLength 𝕀 ω second secondLength) (hPairs : ∀ index value,
      ℳ.PairMember 𝕀 index value first ↔
        ℳ.PairMember 𝕀 index value second) :
    first = second := by
  apply hFirst.2.2.1.1.eq_of_pairMember_iff hExt hSecond.2.2.1.1
  exact hPairs
/-- 两个零长度有限序列的函数图都为空，因而唯一。 -/
theorem empty_sequence_unique
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω first second firstLength secondLength : ℳ.Domain} (hFirst : ℳ.IsFiniteSequenceOfLength 𝕀 ω first firstLength)
    (hSecond : ℳ.IsFiniteSequenceOfLength 𝕀 ω second secondLength) (hFirstEmpty : ∀ index, ¬ ℳ.mem index firstLength)
    (hSecondEmpty : ∀ index, ¬ ℳ.mem index secondLength) :
    first = second := by
  apply hFirst.eq_of_pairMember_iff hExt hSecond
  intro index value
  constructor
  · intro hValue
    have hIndex := (hFirst.2.2.2 index).mpr ⟨value, hValue⟩
    exact False.elim (hFirstEmpty index hIndex)
  · intro hValue
    have hIndex := (hSecond.2.2.2 index).mpr ⟨value, hValue⟩
    exact False.elim (hSecondEmpty index hIndex)
end IsFiniteSequenceOfLength
namespace IsFiniteSequenceLastDecomposition
/-- 从一个非空有限序列中解析出前缀和末项。 -/
theorem exists_of_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω sequence length : ℳ.Domain} (hω : ℳ.IsOmega ω) (hSource : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length) (hNonempty : ∃ index, ℳ.mem index length) :
    ∃ predecessor prefix_graph last,
      ℳ.IsFiniteSequenceLastDecomposition
        𝕀 ω sequence length predecessor prefix_graph last := by
  rcases hω.exists_predecessor_of_mem_of_nonempty
      hZF hSource.1 hNonempty with
    ⟨predecessor, hPredecessorOmega, hSuccessor⟩
  have hPredecessorLength : ℳ.mem predecessor length := (hSuccessor predecessor).mpr (Or.inr fun _ => Iff.rfl)
  rcases ZF.exists_restriction hZF 𝕀 sequence predecessor with
    ⟨prefix_graph, hRestriction⟩
  have hPrefixSequence :
      ℳ.IsFiniteSequenceOfLength 𝕀 ω prefix_graph predecessor :=
    ⟨hPredecessorOmega,
      IsSequenceOfLength.restriction
        hSource.2 hPredecessorLength hRestriction⟩
  rcases (hSource.2.2.2 predecessor).mp hPredecessorLength with
    ⟨last, hLast⟩
  exact ⟨predecessor, prefix_graph, last,
    ⟨hSource, hPredecessorOmega, hSuccessor,
      hPrefixSequence, hRestriction, hLast⟩⟩
/-- 同一个序列的末项解析组件逐一唯一。 -/
theorem components_unique
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω sequence length firstPredecessor secondPredecessor
      firstPrefixSequence secondPrefixSequence firstLast secondLast : ℳ.Domain} (hFirst :
      ℳ.IsFiniteSequenceLastDecomposition
        𝕀 ω sequence length firstPredecessor firstPrefixSequence firstLast) (hSecond :
      ℳ.IsFiniteSequenceLastDecomposition
        𝕀 ω sequence length secondPredecessor secondPrefixSequence secondLast) :
    firstPredecessor = secondPredecessor ∧
      firstPrefixSequence = secondPrefixSequence ∧
        firstLast = secondLast := by
  have hFirstPredecessorLength : ℳ.mem firstPredecessor length := (hFirst.length_successor firstPredecessor).mpr (Or.inr fun _ => Iff.rfl)
  have hFirstPredecessorOrdinal : ℳ.IsOrdinal firstPredecessor :=
    hFirst.source.2.1.mem hFirstPredecessorLength
  have hPredecessorEq : firstPredecessor = secondPredecessor :=
    SuccessorOf.predecessor_eq hExt hFirstPredecessorOrdinal
      hFirst.length_successor hSecond.length_successor
  have hPrefixEq : firstPrefixSequence = secondPrefixSequence := by
    subst secondPredecessor
    exact IsRestrictionOf.eq hExt
      hFirst.prefix_restriction hSecond.prefix_restriction
  have hLastEq : firstLast = secondLast := by
    subst secondPredecessor
    exact hFirst.source.2.2.1.2 firstPredecessor
      firstLast secondLast hFirst.last_value hSecond.last_value
  exact ⟨hPredecessorEq, hPrefixEq, hLastEq⟩
/-- 非空有限序列的前缀、末项和前驱长度存在且唯一。 -/
theorem exists_unique_of_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω sequence length : ℳ.Domain} (hω : ℳ.IsOmega ω) (hSource : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length) (hNonempty : ∃ index, ℳ.mem index length) :
    ∃ predecessor prefix_graph last,
      ℳ.IsFiniteSequenceLastDecomposition
          𝕀 ω sequence length predecessor prefix_graph last ∧
        ∀ otherPredecessor otherPrefixGraph otherLast,
          ℳ.IsFiniteSequenceLastDecomposition
              𝕀 ω sequence length
                otherPredecessor otherPrefixGraph otherLast →
            otherPredecessor = predecessor ∧
              otherPrefixGraph = prefix_graph ∧
                otherLast = last := by
  rcases exists_of_nonempty hZF 𝕀 hω hSource hNonempty with
    ⟨predecessor, prefix_graph, last, hDecomposition⟩
  refine ⟨predecessor, prefix_graph, last, hDecomposition, ?_⟩
  intro otherPredecessor otherPrefixGraph otherLast hOther
  have hComponents := components_unique hZF.1
    hDecomposition hOther
  exact ⟨hComponents.1.symm, hComponents.2.1.symm,
    hComponents.2.2.symm⟩
/-- 每个有限序列都完整解析为空分支或唯一的前缀/末项分支。 -/
theorem empty_or_decomposition_exists_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω sequence length : ℳ.Domain} (hω : ℳ.IsOmega ω) (hSource : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length) : (∀ index, ¬ ℳ.mem index length) ∨
      ∃ predecessor prefix_graph last,
        ℳ.IsFiniteSequenceLastDecomposition
            𝕀 ω sequence length predecessor prefix_graph last ∧
          ∀ otherPredecessor otherPrefixGraph otherLast,
            ℳ.IsFiniteSequenceLastDecomposition
                𝕀 ω sequence length
                  otherPredecessor otherPrefixGraph otherLast →
              otherPredecessor = predecessor ∧
                otherPrefixGraph = prefix_graph ∧
                  otherLast = last := by
  by_cases hNonempty : ∃ index, ℳ.mem index length
  · exact Or.inr (exists_unique_of_nonempty
      hZF 𝕀 hω hSource hNonempty)
  · exact Or.inl (by
      intro index hIndex
      exact hNonempty ⟨index, hIndex⟩)
/-- 相同解析组件重建出唯一的原序列。 -/
theorem sequence_unique_of_components
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω first second length predecessor prefix_sequence last : ℳ.Domain} (hFirst :
      ℳ.IsFiniteSequenceLastDecomposition
        𝕀 ω first length predecessor prefix_sequence last) (hSecond :
      ℳ.IsFiniteSequenceLastDecomposition
        𝕀 ω second length predecessor prefix_sequence last) :
    first = second :=
  IsSequenceOfLength.eq_of_restriction_eq_of_last hExt
    hFirst.source.2 hSecond.source.2
    hFirst.length_successor hSecond.length_successor
    hFirst.prefix_restriction hSecond.prefix_restriction
    rfl hFirst.last_value hSecond.last_value
end IsFiniteSequenceLastDecomposition
end Structure
end SetTheory
end YesMetaZFC
