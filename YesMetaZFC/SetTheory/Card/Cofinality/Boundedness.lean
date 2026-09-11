import YesMetaZFC.SetTheory.Card.Cofinality.Comparison
import YesMetaZFC.SetTheory.Card.Cofinality.LimitLength
import YesMetaZFC.SetTheory.Card.OrdinalCardinality
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Separation
/-!
# 共尾度与有界子集
本层形式化引理 3.9 的有界性核心。集合在序数中有界，指存在目标序数内部的一个上界，
使集合中每个序数都不超过该上界。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Definitional
namespace Project
namespace UnarySchema
/-- 从目标序数中筛出给定集合的全部非严格上界。 -/
private def ordinalUpperBoundCandidate : UnarySchema 1 where
  body := Formula.isOrdinalUpperBound (.bound 1) Term.newest
end UnarySchema
namespace BinarySchema
/-- 为模型内部集合族的每个成员选择目标序数中的最小上界。 -/
private def leastFamilyBoundValue (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .conj (.mem (.bound 0) (.bound 2)) <| .conj (.existsE <| .conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 0) (.bound 4))
      (Formula.isOrdinalUpperBound (.bound 0) (.bound 1))) <|
    Formula.forallMem (.bound 0) <| .neg <| .existsE <| .conj (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 0) (.bound 5)) (Formula.isOrdinalUpperBound
        (.bound 0) (.bound 1))
end BinarySchema
namespace Formula
/-- 序数上界公式与“每个成员不超过给定界”一致。 -/
theorem satisfies_isOrdinalUpperBound_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (set bound : Term depth) :
    satisfies env (isOrdinalUpperBound set bound) ↔
      ∀ value, ℳ.mem value (set.eval env) →
        value = bound.eval env ∨
          ℳ.mem value (bound.eval env) := by
  simp only [isOrdinalUpperBound,
    satisfies_forallMem_iff, satisfies_disj_iff,
    satisfies_extensionalEq_iff_eq hExt, satisfies_mem_iff,
    Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]
/-- 上界候选分离模式的纸面语义。 -/
private theorem satisfies_ordinalUpperBoundCandidate_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ) (env : Env ℳ 1) (candidate : ℳ.Domain) :
    satisfies (env.push candidate)
        UnarySchema.ordinalUpperBoundCandidate.body ↔
      ∀ value, ℳ.mem value (env.bound 0) →
        value = candidate ∨ ℳ.mem value candidate := by
  simp only [UnarySchema.ordinalUpperBoundCandidate,
    satisfies_isOrdinalUpperBound_iff hExt,
    Term.eval_bound_one_push,
    Definitional.Term.eval_newest]
  rfl
/-- 最小族成员上界选择模式的纸面语义。 -/
private theorem denote_leastFamilyBoundValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ) (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.leastFamilyBoundValue 𝒞).denote
        env input output ↔
      ℳ.mem output (env.bound 0) ∧ (∃ set,
          ℳ.PairMember 𝕀 input set (env.bound 1) ∧
            ∀ value, ℳ.mem value set →
              value = output ∨ ℳ.mem value output) ∧
          ∀ earlier, ℳ.mem earlier output →
            ¬ ∃ set,
              ℳ.PairMember 𝕀 input set (env.bound 1) ∧
                ∀ value, ℳ.mem value set →
                  value = earlier ∨ ℳ.mem value earlier := by
  simp only [BinarySchema.leastFamilyBoundValue,
    BinarySchema.denote, satisfies_conj_iff,
    satisfies_mem_iff, satisfies_exists_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_isOrdinalUpperBound_iff hExt,
    satisfies_forallMem_iff, satisfies_neg_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl
end Formula
end Project
end Definitional
open Definitional.Project
namespace Structure
/-- `set` 是序数 `α` 的有界子集。 -/
def IsBoundedSubsetOfOrdinal (ℳ : Structure.{u}) (set α : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal α ∧
    ℳ.MemberSubset set α ∧
      ∃ bound, ℳ.mem bound α ∧
        ∀ value, ℳ.mem value set →
          value = bound ∨ ℳ.mem value bound
namespace IsBoundedSubsetOfOrdinal
/-- 有界子集的目标是序数。 -/
theorem isOrdinal {ℳ : Structure.{u}}
    {set α : ℳ.Domain} (hBounded : ℳ.IsBoundedSubsetOfOrdinal set α) :
    ℳ.IsOrdinal α :=
  hBounded.1
/-- 有界子集确实包含于目标序数。 -/
theorem subset {ℳ : Structure.{u}}
    {set α : ℳ.Domain} (hBounded : ℳ.IsBoundedSubsetOfOrdinal set α) :
    ℳ.MemberSubset set α :=
  hBounded.2.1
/-- 读出有界子集的一个序数上界。 -/
theorem exists_bound {ℳ : Structure.{u}}
    {set α : ℳ.Domain} (hBounded : ℳ.IsBoundedSubsetOfOrdinal set α) :
    ∃ bound, ℳ.mem bound α ∧
      ∀ value, ℳ.mem value set →
        value = bound ∨ ℳ.mem value bound :=
  hBounded.2.2
/-- 非零极限序数不可能作为自身的有界子集。 -/
theorem not_self {ℳ : Structure.{u}}
    {α : ℳ.Domain} (hα : ℳ.IsLimitOrdinal α) :
    ¬ ℳ.IsBoundedSubsetOfOrdinal α α := by
  intro hBounded
  rcases hBounded.exists_bound with
    ⟨bound, hBound, hUpper⟩
  rcases hα.2.2 bound hBound with
    ⟨larger, hLarger, hBoundLarger⟩
  rcases hUpper larger hLarger with
    hEq | hLargerBound
  · subst larger
    exact hα.1.wellOrder.linear.irrefl
      bound hBound hBoundLarger
  · have hSelf : ℳ.mem bound bound := (hα.1.mem hBound).transitive
        larger hLargerBound bound hBoundLarger
    exact hα.1.wellOrder.linear.irrefl
      bound hBound hSelf
end IsBoundedSubsetOfOrdinal
/--
为模型内部集合族逐点选择目标序数中的最小上界。
选择由序数良序和分离完成，因此输出仍是模型内部函数图，不使用宿主层选择函数。
-/
private theorem exists_leastFamilyBoundFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {family length κ : ℳ.Domain}
    (hκ : ℳ.IsOrdinal κ)
    (hFamily :
      ℳ.IsSequenceOfLength 𝕀 family length)
    (hEachBounded :
      ∀ index, ℳ.mem index length →
        ∀ set, ℳ.PairMember 𝕀 index set family →
          ℳ.IsBoundedSubsetOfOrdinal set κ) :
    ∃ bounds,
      ℳ.IsSetFunctionFromTo 𝕀 bounds length κ ∧
        ∀ index bound,
          ℳ.PairMember 𝕀 index bound bounds ↔
            ℳ.mem index length ∧
              (Definitional.Project.BinarySchema.leastFamilyBoundValue
                𝒞).denote
                ({ bound := Fin.cases κ <| Fin.cases family Fin.elim0
                   free := fun _ => Classical.choice ℳ.nonempty } :
                  Env ℳ 2)
                index bound := by
  let env : Env ℳ 2 := {
    bound := Fin.cases κ <| Fin.cases family Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply ZF.exists_setFunctionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.leastFamilyBoundValue 𝒞)
      env
  · intro input hInput
    rcases (hFamily.2.2 input).mp hInput with
      ⟨set, hInputSet⟩
    have hSetBounded :=
      hEachBounded input hInput set hInputSet
    let candidateEnv : Env ℳ 1 := {
      bound := fun _ => set
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases ZF.separation_exists_d hZF
        Definitional.Project.UnarySchema.ordinalUpperBoundCandidate
        candidateEnv κ with
      ⟨candidates, hCandidatesRaw⟩
    have hCandidates (candidate : ℳ.Domain) :
        ℳ.mem candidate candidates ↔
          ℳ.mem candidate κ ∧
            ∀ value, ℳ.mem value set →
              value = candidate ∨ ℳ.mem value candidate := by
      rw [hCandidatesRaw candidate,
        Definitional.Project.Formula.satisfies_ordinalUpperBoundCandidate_iff
          hZF.1 candidateEnv candidate]
    have hCandidatesSubset :
        ℳ.MemberSubset candidates κ := by
      intro candidate hCandidate
      exact (hCandidates candidate).mp hCandidate |>.1
    rcases hSetBounded.exists_bound with
      ⟨someBound, hSomeBound, hSomeUpper⟩
    have hCandidatesNonempty :
        ∃ candidate, ℳ.mem candidate candidates :=
      ⟨someBound, (hCandidates someBound).mpr
          ⟨hSomeBound, hSomeUpper⟩⟩
    rcases hκ.wellOrder.least candidates
        hCandidatesSubset hCandidatesNonempty with
      ⟨least, hLeastCandidate, hLeast⟩
    have hLeastData := (hCandidates least).mp hLeastCandidate
    refine ⟨least, (Definitional.Project.Formula.denote_leastFamilyBoundValue_iff
          𝕀 hZF.1 env input least).mpr
        ⟨hLeastData.1, ⟨set, hInputSet, hLeastData.2⟩, ?_⟩⟩
    intro earlier hEarlier hEarlierBound
    rcases hEarlierBound with
      ⟨otherSet, hInputOtherSet, hEarlierUpper⟩
    have hSetEq :=
      hFamily.2.1.2 input otherSet set
        hInputOtherSet hInputSet
    subst otherSet
    have hEarlierκ :
        ℳ.mem earlier κ :=
      hκ.transitive least hLeastData.1 earlier hEarlier
    have hEarlierCandidate :
        ℳ.mem earlier candidates := (hCandidates earlier).mpr
        ⟨hEarlierκ, hEarlierUpper⟩
    rcases hLeast earlier hEarlierCandidate with
      hSame | hLeastEarlier
    · have hEq :=
        hZF.1.eq_of_same_members least earlier hSame
      have hSelf : ℳ.mem least least := by
        simpa [hEq] using hEarlier
      exact hκ.wellOrder.linear.irrefl
        least hLeastData.1 hSelf
    · have hSelf : ℳ.mem least least :=
        hκ.wellOrder.linear.trans
          least hLeastData.1 earlier hEarlierκ
          least hLeastData.1 hLeastEarlier hEarlier
      exact hκ.wellOrder.linear.irrefl
        least hLeastData.1 hSelf
  · intro input _ first second hFirst hSecond
    have hFirstData := (Definitional.Project.Formula.denote_leastFamilyBoundValue_iff
          𝕀 hZF.1 env input first).mp hFirst
    have hSecondData := (Definitional.Project.Formula.denote_leastFamilyBoundValue_iff
          𝕀 hZF.1 env input second).mp hSecond
    rcases Structure.IsOrdinal.trichotomy hZF.1 (hκ.mem hFirstData.1) (hκ.mem hSecondData.1) (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF)
          first second) with
      hSame | hFirstSecond | hSecondFirst
    · exact hZF.1.eq_of_same_members first second hSame
    · exact False.elim <|
        hSecondData.2.2 first hFirstSecond hFirstData.2.1
    · exact False.elim <|
        hFirstData.2.2 second hSecondFirst hSecondData.2.1
  · intro input output _ hValue
    exact ((Definitional.Project.Formula.denote_leastFamilyBoundValue_iff
          𝕀 hZF.1 env input output).mp hValue).1
/-- 极限序数的任意子集或者有界，或者是共尾子集。 -/
theorem bounded_or_cofinalSubset
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {set α : ℳ.Domain} (hα : ℳ.IsLimitOrdinal α) (hSubset : ℳ.MemberSubset set α) :
    ℳ.IsBoundedSubsetOfOrdinal set α ∨
      ℳ.IsCofinalSubset set α := by
  classical
  by_cases hBounded :
      ℳ.IsBoundedSubsetOfOrdinal set α
  · exact Or.inl hBounded
  · apply Or.inr
    refine ⟨hα, hSubset, ?_⟩
    intro value
    constructor
    · intro hValue
      apply Classical.byContradiction
      intro hNoLarger
      apply hBounded
      refine ⟨hα.1, hSubset, value, hValue, ?_⟩
      intro member hMember
      have hMemberα : ℳ.mem member α :=
        hSubset member hMember
      rcases Structure.IsOrdinal.trichotomy hZF.1 (hα.1.mem hMemberα) (hα.1.mem hValue) (KP.difference_exists_d (ZF.modelsKP hZF))
          (KP.intersection_exists_d (ZF.modelsKP hZF)
            member value) with
        hSame | hMemberValue | hValueMember
      · exact Or.inl <|
          hZF.1.eq_of_same_members member value hSame
      · exact Or.inr hMemberValue
      · exact False.elim <| hNoLarger
          ⟨member, hMember, hValueMember⟩
    · rintro ⟨member, hMember, hValueMember⟩
      exact hα.1.transitive member (hSubset member hMember) value hValueMember
namespace IsCofinality
/--
引理 3.9(i)：基数严格小于 `cf(κ)` 的 `κ` 子集必有界。
这里不需要额外使用 `κ` 的基数性，因此结论对任意具有共尾度见证的极限序数成立。
-/
theorem bounded_of_cardinality_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {κ cf set μ : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 cf κ) (hSubset : ℳ.MemberSubset set κ) (hCardinality : ℳ.IsCardinalOf 𝕀 μ set)
    (hμcf : ℳ.mem μ cf) :
    ℳ.IsBoundedSubsetOfOrdinal set κ := by
  classical
  apply Classical.byContradiction
  intro hNotBounded
  have hκLimit :
      ℳ.IsLimitOrdinal κ := by
    rcases hCofinality.hasCofinalSequence with
      ⟨sequence, hSequence⟩
    exact hSequence.isLimitOrdinal
  have hCofinalSet :
      ℳ.IsCofinalSubset set κ := by
    rcases bounded_or_cofinalSubset hZF hκLimit hSubset with
      hBounded | hCofinal
    · exact False.elim <| hNotBounded hBounded
    · exact hCofinal
  rcases hCardinality.2 with
    ⟨function, hBijection⟩
  have hFunctionToκ :
      ℳ.IsSetFunctionFromTo 𝕀 function μ κ := by
    refine ⟨hBijection.1.1.1,
      hBijection.1.1.2.1, ?_⟩
    intro input hInput
    rcases hBijection.1.1.2.2 input hInput with
      ⟨output, hOutput, hPair⟩
    exact ⟨output, hSubset output hOutput, hPair⟩
  have hRange :
      ℳ.IsRangeOf 𝕀 set function := by
    intro output
    constructor
    · intro hOutput
      rcases hBijection.2 output hOutput with
        ⟨input, _, hPair⟩
      exact ⟨input, hPair⟩
    · rintro ⟨input, hPair⟩
      exact hBijection.1.1.output_mem_of_pairMember hPair
  have hcfLeμ :=
    hCofinality.eq_or_mem_of_cofinalFunctionRange
      hZF 𝕀 hCardinality.1 hFunctionToκ hRange hCofinalSet
  rcases hcfLeμ with hEq | hcfμ
  · subst μ
    exact hCofinality.isCardinal.1.wellOrder.linear.irrefl
      cf hμcf hμcf
  · have hSelf : ℳ.mem cf cf :=
      hCofinality.isCardinal.1.transitive
        μ hμcf cf hcfμ
    exact hCofinality.isCardinal.1.wellOrder.linear.irrefl
      cf hSelf hSelf
/-- 引理 3.9(ii)：定义域严格小于 `cf(κ)` 的函数，其值域在 `κ` 中有界。 -/
theorem range_bounded_of_domain_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {κ cf function length range : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 cf κ) (hLengthCf : ℳ.mem length cf) (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function length κ) (hRange : ℳ.IsRangeOf 𝕀 range function) :
    ℳ.IsBoundedSubsetOfOrdinal range κ := by
  classical
  have hLengthOrdinal :
      ℳ.IsOrdinal length :=
    hCofinality.isCardinal.1.mem hLengthCf
  rcases ZF.ordinalCardinal_existsUnique
      hZF 𝕀 hLengthOrdinal with
    ⟨ν, hν, _⟩
  rcases hν.2 with
    ⟨cardinalToLength, hCardinalToLength⟩
  have hLengthSubsetcf :
      ℳ.MemberSubset length cf :=
    hCofinality.isCardinal.1.transitive length hLengthCf
  rcases ZF.exists_inclusionInjection
      hZF 𝕀 hLengthSubsetcf with
    ⟨lengthToCf, hLengthToCf⟩
  rcases ZF.exists_compositionInjection
      hZF 𝕀 hCardinalToLength.1 hLengthToCf with
    ⟨cardinalToCf, hCardinalToCf⟩
  have hνcf :
      ℳ.mem ν cf := by
    rcases hν.1.eq_or_mem_of_cardinalLessOrEqual
        hZF 𝕀 hCofinality.isCardinal
        ⟨cardinalToCf, hCardinalToCf⟩ with
      hEq | hνcf
    · subst ν
      exact False.elim <|
        hCofinality.isCardinal.2 length hLengthCf <|
          hν.2.symm hZF 𝕀
    · exact hνcf
  have hRangeSubset :
      ℳ.MemberSubset range κ := by
    intro output hOutput
    rcases (hRange output).mp hOutput with
      ⟨input, hPair⟩
    exact hFunction.output_mem_of_pairMember hPair
  apply Classical.byContradiction
  intro hNotBounded
  have hκLimit :
      ℳ.IsLimitOrdinal κ := by
    rcases hCofinality.hasCofinalSequence with
      ⟨sequence, hSequence⟩
    exact hSequence.isLimitOrdinal
  have hCofinalRange :
      ℳ.IsCofinalSubset range κ := by
    rcases bounded_or_cofinalSubset
        hZF hκLimit hRangeSubset with
      hBounded | hCofinal
    · exact False.elim <| hNotBounded hBounded
    · exact hCofinal
  rcases ZF.exists_compositionFunction
      hZF 𝕀 hCardinalToLength.1.1 hFunction with
    ⟨composition, hComposition, hCompositionValue⟩
  have hCompositionRange :
      ℳ.IsRangeOf 𝕀 range composition := by
    intro output
    constructor
    · intro hOutput
      rcases (hRange output).mp hOutput with
        ⟨middle, hMiddleOutput⟩
      have hMiddleLength :
          ℳ.mem middle length :=
        hFunction.input_mem_of_pairMember hMiddleOutput
      rcases hCardinalToLength.2 middle hMiddleLength with
        ⟨input, hInput, hInputMiddle⟩
      exact ⟨input, (hCompositionValue input output).mpr
          ⟨hInput, middle, hInputMiddle, hMiddleOutput⟩⟩
    · rintro ⟨input, hInputOutput⟩
      rcases (hCompositionValue input output).mp
          hInputOutput with
        ⟨_, middle, _, hMiddleOutput⟩
      exact (hRange output).mpr
        ⟨middle, hMiddleOutput⟩
  have hcfLeν :=
    hCofinality.eq_or_mem_of_cofinalFunctionRange
      hZF 𝕀 hν.1 hComposition
      hCompositionRange hCofinalRange
  rcases hcfLeν with hEq | hcfν
  · subst ν
    exact hCofinality.isCardinal.1.wellOrder.linear.irrefl
      cf hνcf hνcf
  · have hSelf : ℳ.mem cf cf :=
      hCofinality.isCardinal.1.transitive
        ν hνcf cf hcfν
    exact hCofinality.isCardinal.1.wellOrder.linear.irrefl
      cf hSelf hSelf
/--
少于 `cf(κ)` 个有界子集的并仍有界。
集合族、逐点最小上界函数、两个值域及最终并集都由模型内部集合编码。
-/
theorem familyUnion_bounded_of_length_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {κ cf family length familyRange union : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 cf κ) (hLengthCf : ℳ.mem length cf) (hFamily :
      ℳ.IsSequenceOfLength 𝕀 family length) (hFamilyRange :
      ℳ.IsRangeOf 𝕀 familyRange family) (hUnion :
      ℳ.IsUnionOf union familyRange) (hEachBounded :
      ∀ index, ℳ.mem index length →
        ∀ set, ℳ.PairMember 𝕀 index set family →
          ℳ.IsBoundedSubsetOfOrdinal set κ) :
    ℳ.IsBoundedSubsetOfOrdinal union κ := by
  have hκLimit :
      ℳ.IsLimitOrdinal κ := by
    rcases hCofinality.hasCofinalSequence with
      ⟨sequence, hSequence⟩
    exact hSequence.isLimitOrdinal
  rcases exists_leastFamilyBoundFunction
      hZF 𝕀 hκLimit.1 hFamily hEachBounded with
    ⟨bounds, hBounds, hBoundsValue⟩
  rcases ZF.exists_range_of_setFunction
      hZF 𝕀 hBounds.1 hBounds.2.1 with
    ⟨boundRange, hBoundRange⟩
  have hBoundRangeBounded :=
    range_bounded_of_domain_mem
      hZF 𝕀 hCofinality hLengthCf hBounds hBoundRange
  rcases hBoundRangeBounded.exists_bound with
    ⟨commonBound, hCommonBound, hCommonUpper⟩
  have hUnionSubset :
      ℳ.MemberSubset union κ := by
    intro value hValue
    rcases (hUnion value).mp hValue with
      ⟨set, hSetRange, hValueSet⟩
    rcases (hFamilyRange set).mp hSetRange with
      ⟨index, hIndexSet⟩
    have hIndex :
        ℳ.mem index length := (hFamily.2.2 index).mpr ⟨set, hIndexSet⟩
    exact (hEachBounded index hIndex set hIndexSet).subset
        value hValueSet
  refine ⟨hκLimit.1, hUnionSubset,
    commonBound, hCommonBound, ?_⟩
  intro value hValue
  rcases (hUnion value).mp hValue with
    ⟨set, hSetRange, hValueSet⟩
  rcases (hFamilyRange set).mp hSetRange with
    ⟨index, hIndexSet⟩
  have hIndex :
      ℳ.mem index length := (hFamily.2.2 index).mpr ⟨set, hIndexSet⟩
  rcases hBounds.2.2 index hIndex with
    ⟨selectedBound, hSelectedBound, hIndexBound⟩
  have hSelectedDenote := ((hBoundsValue index selectedBound).mp hIndexBound).2
  let boundEnv : Env ℳ 2 := {
    bound := Fin.cases κ <| Fin.cases family Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hSelectedData := (Definitional.Project.Formula.denote_leastFamilyBoundValue_iff
      𝕀 hZF.1 boundEnv index selectedBound).mp <| by
        simpa [boundEnv] using hSelectedDenote
  rcases hSelectedData.2.1 with
    ⟨selectedSet, hIndexSelectedSet, hSelectedUpper⟩
  have hSetEq :=
    hFamily.2.1.2 index selectedSet set
      hIndexSelectedSet hIndexSet
  subst selectedSet
  have hValueSelected :=
    hSelectedUpper value hValueSet
  have hSelectedRange :
      ℳ.mem selectedBound boundRange := (hBoundRange selectedBound).mpr
      ⟨index, hIndexBound⟩
  have hSelectedCommon :=
    hCommonUpper selectedBound hSelectedRange
  rcases hValueSelected with
    hValueEq | hValueSelected
  · simpa [hValueEq] using hSelectedCommon
  · rcases hSelectedCommon with
      hSelectedEq | hSelectedCommon
    · exact Or.inr <| by
        simpa [hSelectedEq] using hValueSelected
    · exact Or.inr <| (hκLimit.1.mem hCommonBound).transitive
          selectedBound hSelectedCommon
          value hValueSelected
/-- 引理 3.9(iii)：模型内部有限序列族的有界子集之并仍有界。 -/
theorem finiteFamilyUnion_bounded
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω κ cf family length familyRange union : ℳ.Domain} (hω : ℳ.IsOmega ω) (hCofinality : ℳ.IsCofinality 𝕀 cf κ) (hLengthFinite : ℳ.mem length ω) (hFamily :
      ℳ.IsSequenceOfLength 𝕀 family length) (hFamilyRange :
      ℳ.IsRangeOf 𝕀 familyRange family) (hUnion :
      ℳ.IsUnionOf union familyRange) (hEachBounded :
      ∀ index, ℳ.mem index length →
        ∀ set, ℳ.PairMember 𝕀 index set family →
          ℳ.IsBoundedSubsetOfOrdinal set κ) :
    ℳ.IsBoundedSubsetOfOrdinal union κ := by
  rcases hCofinality.hasCofinalSequence with
    ⟨sequence, hSequence⟩
  have hCfLimit :
      ℳ.IsLimitOrdinal cf :=
    hSequence.length_isLimitOrdinal hZF
  have hLengthCf :
      ℳ.mem length cf :=
    hω.subset_limitOrdinal hZF hCfLimit
      length hLengthFinite
  exact familyUnion_bounded_of_length_mem
    hZF 𝕀 hCofinality hLengthCf hFamily
    hFamilyRange hUnion hEachBounded
end IsCofinality
namespace IsBoundedSubsetOfOrdinal
/-- 两个有界子集的并仍有界；这是引理 3.9(iii) 的二元归纳步。 -/
theorem unionOfTwo
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {union left right α : ℳ.Domain} (hUnion : ℳ.IsUnionOfTwo union left right) (hLeft : ℳ.IsBoundedSubsetOfOrdinal left α)
    (hRight : ℳ.IsBoundedSubsetOfOrdinal right α) :
    ℳ.IsBoundedSubsetOfOrdinal union α := by
  rcases hLeft.exists_bound with
    ⟨leftBound, hLeftBound, hLeftUpper⟩
  rcases hRight.exists_bound with
    ⟨rightBound, hRightBound, hRightUpper⟩
  have hUnionSubset :
      ℳ.MemberSubset union α := by
    intro value hValue
    rcases (hUnion value).mp hValue with
      hValueLeft | hValueRight
    · exact hLeft.subset value hValueLeft
    · exact hRight.subset value hValueRight
  rcases Structure.IsOrdinal.trichotomy hZF.1 (hLeft.isOrdinal.mem hLeftBound) (hRight.isOrdinal.mem hRightBound) (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF)
        leftBound rightBound) with
    hSame | hLeftRight | hRightLeft
  · have hEq :=
      hZF.1.eq_of_same_members
        leftBound rightBound hSame
    subst rightBound
    refine ⟨hLeft.isOrdinal, hUnionSubset,
      leftBound, hLeftBound, ?_⟩
    intro value hValue
    rcases (hUnion value).mp hValue with
      hValueLeft | hValueRight
    · exact hLeftUpper value hValueLeft
    · exact hRightUpper value hValueRight
  · refine ⟨hLeft.isOrdinal, hUnionSubset,
      rightBound, hRightBound, ?_⟩
    intro value hValue
    rcases (hUnion value).mp hValue with
      hValueLeft | hValueRight
    · rcases hLeftUpper value hValueLeft with
        hEq | hValueLeftBound
      · exact Or.inr <| by simpa [hEq] using hLeftRight
      · exact Or.inr <| (hRight.isOrdinal.mem hRightBound).transitive
            leftBound hLeftRight value hValueLeftBound
    · exact hRightUpper value hValueRight
  · refine ⟨hLeft.isOrdinal, hUnionSubset,
      leftBound, hLeftBound, ?_⟩
    intro value hValue
    rcases (hUnion value).mp hValue with
      hValueLeft | hValueRight
    · exact hLeftUpper value hValueLeft
    · rcases hRightUpper value hValueRight with
        hEq | hValueRightBound
      · exact Or.inr <| by simpa [hEq] using hRightLeft
      · exact Or.inr <| (hLeft.isOrdinal.mem hLeftBound).transitive
            rightBound hRightLeft value hValueRightBound
end IsBoundedSubsetOfOrdinal
end Structure
namespace Definitional
namespace Project
namespace Formula
/-- 序数内有界子集公式与显式序数上界语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isBoundedSubsetOfOrdinal_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (set α : Term depth) :
    satisfies env (isBoundedSubsetOfOrdinal set α) ↔
      ℳ.IsBoundedSubsetOfOrdinal (set.eval env) (α.eval env) := by
  simp only [isBoundedSubsetOfOrdinal,
    Structure.IsBoundedSubsetOfOrdinal,
    Structure.MemberSubset,
    satisfies_conj_iff, satisfies_isOrdinal_iff,
    satisfies_subset_iff, satisfies_existsMem_iff,
    satisfies_isOrdinalUpperBound_iff hExt,
    Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
