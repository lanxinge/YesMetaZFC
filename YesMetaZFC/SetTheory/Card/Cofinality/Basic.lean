import YesMetaZFC.SetTheory.Card.Cofinality.Syntax
import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.Ord.Normal
import YesMetaZFC.SetTheory.SetConstruction
/-!
# 共尾度的基础语义
本层把共尾度公式解释为模型内部的集合论关系，并给出最小见证唯一性和值域共尾性。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/-- `sequence` 是长度为 `length`、在极限序数 `α` 中共尾的严格递增序列。 -/
def IsCofinalOrdinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (sequence length α : ℳ.Domain) : Prop :=
  ℳ.IsLimitOrdinal α ∧
    ℳ.IsIncreasingOrdinalSequence 𝕀 sequence length ∧
      ℳ.IsOrdinalSequenceLimit 𝕀 α sequence length ∧
        ∀ index, ℳ.mem index length →
          ∀ value, ℳ.PairMember 𝕀 index value sequence →
            ℳ.mem value α
/-- `sequence` 是长度为 `length`、在极限序数 `α` 中共尾的非递减序列。 -/
def IsCofinalNondecreasingOrdinalSequence
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (sequence length α : ℳ.Domain) : Prop :=
  ℳ.IsLimitOrdinal α ∧
    ℳ.IsNondecreasingOrdinalSequence 𝕀 sequence length ∧
      ℳ.IsOrdinalSequenceLimit 𝕀 α sequence length ∧
        ∀ index, ℳ.mem index length →
          ∀ value, ℳ.PairMember 𝕀 index value sequence →
            ℳ.mem value α
/-- 存在一个长度为 `length`、在 `α` 中共尾的严格递增序列。 -/
def HasCofinalOrdinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (length α : ℳ.Domain) : Prop :=
  ∃ sequence,
    ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α
/-- 存在一个长度为 `length`、在 `α` 中共尾的非递减序列。 -/
def HasCofinalNondecreasingOrdinalSequence
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (length α : ℳ.Domain) : Prop :=
  ∃ sequence,
    ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
      sequence length α
/-- `set` 是极限序数 `α` 的共尾子集。 -/
def IsCofinalSubset (ℳ : Structure.{u}) (set α : ℳ.Domain) : Prop :=
  ℳ.IsLimitOrdinal α ∧
    ℳ.MemberSubset set α ∧
      ℳ.IsUnionOf α set
/-- `κ` 是 `α` 的共尾度，即具有共尾序列的最小序数长度。 -/
def IsCofinality {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (κ α : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 κ ∧
    ℳ.HasCofinalOrdinalSequence 𝕀 κ α ∧
      ∀ length,
        ℳ.HasCofinalOrdinalSequence 𝕀 length α →
          κ = length ∨ ℳ.mem κ length
namespace IsCofinalOrdinalSequence
/-- 共尾序列的目标是极限序数。 -/
theorem isLimitOrdinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) :
    ℳ.IsLimitOrdinal α :=
  hCofinal.1
/-- 共尾序列严格递增。 -/
theorem isIncreasing {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) :
    ℳ.IsIncreasingOrdinalSequence 𝕀 sequence length :=
  hCofinal.2.1
/-- 共尾序列的上确界是目标序数。 -/
theorem isLimit {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) :
    ℳ.IsOrdinalSequenceLimit 𝕀 α sequence length :=
  hCofinal.2.2.1
/-- 共尾序列的每个值都严格小于目标序数。 -/
theorem value_mem {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α index value : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) (hIndex : ℳ.mem index length) (hValue : ℳ.PairMember 𝕀 index value sequence) :
    ℳ.mem value α :=
  hCofinal.2.2.2 index hIndex value hValue
/-- 共尾序列的任意精确值域都是目标序数的共尾子集。 -/
theorem range_isCofinalSubset {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α range : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀 sequence length α) (hRange : ℳ.IsRangeOf 𝕀 range sequence) :
    ℳ.IsCofinalSubset range α := by
  rcases hCofinal.isLimit.2.2 with
    ⟨canonicalRange, hCanonicalRange, hUnion⟩
  have hRangeEq : range = canonicalRange := by
    exact hExt.eq_of_same_members range canonicalRange
      (fun x => (hRange x).trans (hCanonicalRange x).symm)
  subst canonicalRange
  refine ⟨hCofinal.isLimitOrdinal, ?_, hUnion⟩
  intro value hValue
  rcases (hRange value).mp hValue with ⟨index, hPair⟩
  have hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length :=
    hCofinal.isIncreasing.1.1
  have hIndex : ℳ.mem index length := (hSequence.2.2 index).mpr
      ⟨value, hPair⟩
  exact hCofinal.value_mem hIndex hPair
end IsCofinalOrdinalSequence
namespace IsCofinalNondecreasingOrdinalSequence
/-- 非递减共尾序列的目标是极限序数。 -/
theorem isLimitOrdinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) :
    ℳ.IsLimitOrdinal α :=
  hCofinal.1
/-- 共尾序列按索引非递减。 -/
theorem isNondecreasing {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) :
    ℳ.IsNondecreasingOrdinalSequence 𝕀 sequence length :=
  hCofinal.2.1
/-- 非递减共尾序列的上确界是目标序数。 -/
theorem isLimit {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) :
    ℳ.IsOrdinalSequenceLimit 𝕀 α sequence length :=
  hCofinal.2.2.1
/-- 非递减共尾序列的每个值都严格小于目标序数。 -/
theorem value_mem {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α index value : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) (hIndex : ℳ.mem index length) (hValue : ℳ.PairMember 𝕀 index value sequence) :
    ℳ.mem value α :=
  hCofinal.2.2.2 index hIndex value hValue
/-- 非递减共尾序列给出从其长度到目标序数的模型内部函数。 -/
theorem isSetFunctionFromTo
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) :
    ℳ.IsSetFunctionFromTo 𝕀 sequence length α := by
  have hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length :=
    hCofinal.isNondecreasing.1.1
  refine ⟨hSequence.2.1, hSequence.2.2, ?_⟩
  intro index hIndex
  rcases (hSequence.2.2 index).mp hIndex with
    ⟨value, hValue⟩
  exact ⟨value, hCofinal.value_mem hIndex hValue, hValue⟩
/-- 非递减共尾序列的任意精确值域都是目标序数的共尾子集。 -/
theorem range_isCofinalSubset
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence length α range : ℳ.Domain} (hCofinal :
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀
        sequence length α) (hRange : ℳ.IsRangeOf 𝕀 range sequence) :
    ℳ.IsCofinalSubset range α := by
  rcases hCofinal.isLimit.2.2 with
    ⟨canonicalRange, hCanonicalRange, hUnion⟩
  have hRangeEq : range = canonicalRange := by
    exact hExt.eq_of_same_members range canonicalRange
      (fun x => (hRange x).trans (hCanonicalRange x).symm)
  subst canonicalRange
  refine ⟨hCofinal.isLimitOrdinal, ?_, hUnion⟩
  intro value hValue
  rcases (hRange value).mp hValue with ⟨index, hPair⟩
  exact hCofinal.isSetFunctionFromTo.output_mem_of_pairMember hPair
end IsCofinalNondecreasingOrdinalSequence
namespace IsCofinality
/-- 共尾度见证本身是基数。 -/
theorem isCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {κ α : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 κ α) :
    ℳ.IsCardinal 𝕀 κ :=
  hCofinality.1
/-- 共尾度长度确实具有一条共尾序列。 -/
theorem hasCofinalSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {κ α : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 κ α) :
    ℳ.HasCofinalOrdinalSequence 𝕀 κ α :=
  hCofinality.2.1
/-- 共尾度不大于任何其他共尾序列长度。 -/
theorem minimal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {κ α length : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 κ α) (hLength : ℳ.HasCofinalOrdinalSequence 𝕀 length α) :
    κ = length ∨ ℳ.mem κ length :=
  hCofinality.2.2 length hLength
/-- 同一序数的两个共尾度见证相等。 -/
theorem eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {κ μ α : ℳ.Domain} (hκ : ℳ.IsCofinality 𝕀 κ α) (hμ : ℳ.IsCofinality 𝕀 μ α) :
    κ = μ := by
  rcases hκ.minimal hμ.hasCofinalSequence with hEq | hκμ
  · exact hEq
  rcases hμ.minimal hκ.hasCofinalSequence with hEq | hμκ
  · exact hEq.symm
  have hSelf : ℳ.mem κ κ :=
    hκ.isCardinal.1.transitive μ hμκ κ hκμ
  exact False.elim <|
    hκ.isCardinal.1.wellOrder.linear.irrefl κ hSelf hSelf
end IsCofinality
end Structure
namespace Definitional
namespace Project
namespace Formula
/-- 共尾序列公式与模型内部的序数序列语义一致。 -/

theorem satisfies_isCofinalOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (sequence length α : Term depth) :
    satisfies env (isCofinalOrdinalSequence 𝒞 sequence length α) ↔
      ℳ.IsCofinalOrdinalSequence 𝕀 (sequence.eval env) (length.eval env) (α.eval env) := by
  simp only [isCofinalOrdinalSequence,
    Structure.IsCofinalOrdinalSequence,
    satisfies_conj_iff,
    satisfies_isLimitOrdinal_iff,
    satisfies_isIncreasingOrdinalSequence_iff 𝕀 hExt,
    satisfies_isOrdinalSequenceLimit_iff 𝕀 hExt,
    satisfies_forallMem_iff, satisfies_forall_iff,
    satisfies_imp_iff, satisfies_orderedPairMem_iff 𝕀,
    satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
/-- 非递减共尾序列公式与模型内部序列语义一致。 -/

theorem satisfies_isCofinalNondecreasingOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (sequence length α : Term depth) :
    satisfies env (isCofinalNondecreasingOrdinalSequence
          𝒞 sequence length α) ↔
      ℳ.IsCofinalNondecreasingOrdinalSequence 𝕀 (sequence.eval env) (length.eval env) (α.eval env) := by
  simp only [isCofinalNondecreasingOrdinalSequence,
    Structure.IsCofinalNondecreasingOrdinalSequence,
    satisfies_conj_iff,
    satisfies_isLimitOrdinal_iff,
    satisfies_isNondecreasingOrdinalSequence_iff 𝕀 hExt,
    satisfies_isOrdinalSequenceLimit_iff 𝕀 hExt,
    satisfies_forallMem_iff, satisfies_forall_iff,
    satisfies_imp_iff, satisfies_orderedPairMem_iff 𝕀,
    satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
/-- 共尾序列存在公式与模型内部存在量词语义一致。 -/

theorem satisfies_hasCofinalOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (length α : Term depth) :
    satisfies env (hasCofinalOrdinalSequence 𝒞 length α) ↔
      ℳ.HasCofinalOrdinalSequence 𝕀 (length.eval env) (α.eval env) := by
  simp only [hasCofinalOrdinalSequence,
    Structure.HasCofinalOrdinalSequence,
    satisfies_exists_iff,
    satisfies_isCofinalOrdinalSequence_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
/-- 非递减共尾序列存在公式与模型内部存在量词语义一致。 -/

theorem satisfies_hasCofinalNondecreasingOrdinalSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (length α : Term depth) :
    satisfies env (hasCofinalNondecreasingOrdinalSequence 𝒞 length α) ↔
      ℳ.HasCofinalNondecreasingOrdinalSequence 𝕀 (length.eval env) (α.eval env) := by
  simp only [hasCofinalNondecreasingOrdinalSequence,
    Structure.HasCofinalNondecreasingOrdinalSequence,
    satisfies_exists_iff,
    satisfies_isCofinalNondecreasingOrdinalSequence_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
/-- 共尾子集公式与“子集且并为目标”的纸面语义一致。 -/

theorem satisfies_isCofinalSubset_iff
    {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (set α : Term depth) :
    satisfies env (isCofinalSubset set α) ↔
      ℳ.IsCofinalSubset (set.eval env) (α.eval env) := by
  simp only [isCofinalSubset, Structure.IsCofinalSubset,
    satisfies_conj_iff, satisfies_isLimitOrdinal_iff,
    satisfies_subset_iff, satisfies_isUnion_iff,
    Structure.MemberSubset]
/-- 共尾度公式与最小共尾序列长度的模型内部语义一致。 -/

theorem satisfies_isCofinality_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (κ α : Term depth) :
    satisfies env (isCofinality 𝒞 κ α) ↔
      ℳ.IsCofinality 𝕀 (κ.eval env) (α.eval env) := by
  simp only [isCofinality, Structure.IsCofinality,
    satisfies_conj_iff, satisfies_forall_iff,
    satisfies_imp_iff, satisfies_disj_iff,
    satisfies_isCardinal_iff 𝕀 hExt,
    satisfies_hasCofinalOrdinalSequence_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
