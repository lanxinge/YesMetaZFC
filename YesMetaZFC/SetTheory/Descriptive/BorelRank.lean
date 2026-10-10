import YesMetaZFC.SetTheory.Descriptive.Borel.RankRelative

/-! # Borel 秩公共入口

Brank / Bcr 是码树上的 sup(子秩+1) 函数及其根值，叶秩从零计。
Bsig / Bpi 是标准超限层级，Bsr 是集合所属 Σ⁰α ∪ Π⁰α 的最小正阶数。
bsr_exists_l 给出有码集合的唯一可数标准秩；bsr_compl_l、bsr_trace_l
分别给出补集保秩与子空间限制不增秩。所有定义都有原公式及语义对应。

ZF 中的存在性结论针对仓库的内部有码集合，未把无统一码族的集合并
强行认作有码并；标准层级的定义本身量化实际内部集合族。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 自动构造两种空间及其两种秩接口，没有外加的序数标号或选择函数。 -/
theorem dst_borel_rank_l (hZF : M.Models ZF) : ∃ ω D B C A S,
    Baire_d I ω B ∧ M.IsOrdinalTwo D ∧ M.IsFunctionSpace I C ω D ∧
    Fseq_space_d I ω ω A ∧ Fseq_space_d I ω D S ∧
    (∀ Q c, Bcode_d I ω A Q c → ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bcr_d I ω A Q c α) ∧
    (∀ K, Borel_d I ω A A B K → ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsr_d I ω A B K α) ∧
    (∀ K, Borel_d I ω A S C K → ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsr_d I ω S C K α) := by
  obtain ⟨ω, D, B, C, A, S, hB, hD, hC, hA, ha, hS, _⟩ := ds_spaces_l I hZF
  refine ⟨ω, D, B, C, A, S, hB, hD, hC, hA, hS, fun Q c hc => bcr_exists_l I hZF hB.1 ha hc, ?_, ?_⟩
  · intro K hK
    obtain ⟨α, ho, hc, hr, _⟩ := bsr_exists_l I hZF hB.1 hB.2 hA ha hK
    exact ⟨α, ho, hc, hr⟩
  · intro K hK
    obtain ⟨α, ho, hc, hr, _⟩ := bsr_exists_l I hZF hB.1 hC hS ha hK
    exact ⟨α, ho, hc, hr⟩

end YesMetaZFC.SetTheory.Descriptive
