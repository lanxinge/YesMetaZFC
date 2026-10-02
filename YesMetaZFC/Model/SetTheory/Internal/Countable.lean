import YesMetaZFC.Model.SetTheory.Internal.CanonicalCode

/-! # 全部内部公式码的规范可数性见证

原可数性入口直接使用固定编码的图，含模型内部的非标准有限公式；所有调用者
共享同一规范编号，不再另行选择字母表与有限序列的计数函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 全部原公式码与规范自然数码之间的图，作为到 ω 的实际单射返回。 -/
theorem scode_numbering_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) :
    ∃ C N, Scode_d I ω C ∧ M.IsSetInjectionFromTo I N C ω := by
  obtain ⟨C, D, E, _, hC, hd, he, _⟩ := sc_num_tables_l I hZF hω
  refine ⟨C, E, hC, ⟨he.1.1.1, he.1.1.2.1, fun a ha => ?_⟩, he.1.2⟩
  obtain ⟨z, hz, haz⟩ := he.1.1.2.2 a ha
  exact ⟨z, hd z hz, haz⟩

theorem scode_countable_l (hZF : M.Models ZF) {ω C} (hω : M.IsOmega ω) (hC : Scode_d I ω C) :
    M.CardinalLessOrEqual I C ω := by
  obtain ⟨D, N, hD, hn⟩ := scode_numbering_l I hZF hω
  exact scode_unique_l I hZF.1 hD hC ▸ ⟨N, hn⟩

end YesMetaZFC.SetTheory.Internal
