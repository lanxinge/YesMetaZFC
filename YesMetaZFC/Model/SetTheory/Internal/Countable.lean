import YesMetaZFC.Model.SetTheory.Internal.FormulaCode
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable

/-! # 全部内部公式码的可数性

指令字母表是 ω×(ω×ω)，合法程序属于其内部有限序列空间。给程序和根编号
配对得到所有公式的统一编号，包括地模型认为有限的非标准公式。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem scode_countable_l (hZF : M.Models ZF) {ω C} (hω : M.IsOmega ω) (hC : Scode_d I ω C) :
    M.CardinalLessOrEqual I C ω := by
  obtain ⟨T, hT⟩ := ZF.exists_identityBijection hZF I ω
  have hωc : M.CardinalLessOrEqual I ω ω := ⟨T, hT.1⟩
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I ω P
  have hc := ZF.countable_product_l I hZF hω hωc (ZF.countable_product_l I hZF hω hωc hωc hP) hQ
  obtain ⟨S, hS, hs⟩ := ZF.fseq_countable_space_l I hZF hω hc
  obtain ⟨A, hA⟩ := ZF.exists_cartesianProduct hZF I S ω
  obtain ⟨J, hJ⟩ := ZF.countable_product_l I hZF hω hs hωc hA
  obtain ⟨K, hK⟩ := ZF.exists_inclusionInjection hZF I (show M.MemberSubset C A from fun a ha => by
    obtain ⟨n, F, k, hcode, hF, hk⟩ := (hC a).mp ha
    have row i (hi : M.mem i n) := hω.transitive hZF n hF.1 i hi
    have hf : M.IsSetFunctionFromTo I F n Q := ⟨hF.2.1.2.1, hF.2.1.2.2, fun i hi => by
      obtain ⟨c, hic⟩ := (hF.2.1.2.2 i).mp hi
      exact ⟨c, sfm_node_mem_l I hZF hω hP hQ (row i hi) (hF.2.2 i c hic), hic⟩⟩
    exact (hA a).mpr ⟨F, (hS F).mpr ⟨n, hF.1, hf⟩, k, row k hk, hcode⟩)
  exact ZF.exists_compositionInjection hZF I hK hJ

/-- 直接构造全部内部公式码的集合及其到内部 ω 的实际单射图。 -/
theorem scode_numbering_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) :
    ∃ C N, Scode_d I ω C ∧ M.IsSetInjectionFromTo I N C ω := by
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨N, hN⟩ := scode_countable_l I hZF hω hC
  exact ⟨C, N, hC, hN⟩

end YesMetaZFC.SetTheory.Internal
