import YesMetaZFC.Model.SetTheory.Embedding.Elementary
import YesMetaZFC.Model.SetTheory.Reflection.RankSkolem
import YesMetaZFC.Model.SetTheory.Internal.Collapse
import YesMetaZFC.SetTheory.FinitaryClub
import YesMetaZFC.SetTheory.FinitaryTrace

/-! # 任意内部 κ 小种子的实际初等子模型

司寇伦选择、最小闭包、有限支撑和 Tarski–Vaught 已全部实现。入口直接返回
地模型内的载体、结构码及全内部语法的初等证书，不再要求调用者补交闭性或初等性。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem selem_hull_bound_l (hZFC : M.Models ZFC) {ω κ c X R A} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ)
    (hM : Smdl_d I c X R) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A κ) :
    ∃ N d S, Ssub_d I c d X R N S ∧ M.MemberSubset A N ∧ M.CardinalLessOrEqual I N κ ∧ Selem_d I ω c d := by
  obtain ⟨u, C, S, T, D, K, N, hK, hN, hn, hu, hc⟩ := ssk_hull_bound_l I hZFC hω hκ hM hA ha
  obtain ⟨d, Q, hQ, he⟩ := selem_of_skolem_l I (ZFC.models_zf_l hZFC) hω hM hK.codes hN.2.1 hu hc
  exact ⟨N, d, Q, hQ, hN.1, hn, he⟩

/-- 可数内部初等子模型是 κ=ω 的直接实例。 -/
theorem selem_hull_l (hZFC : M.Models ZFC) {ω c X R A} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ N d S, Ssub_d I c d X R N S ∧ M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧ Selem_d I ω c d := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨F, hF⟩ := ZF.exists_identityBijection hZF I ω
  exact selem_hull_bound_l I hZFC hω ⟨ZF.omega_cardinal_l I hZF hω, F, hF.1⟩ hM hA ha

/-- 从可数种子一次构造壳、可数传递坍塌和返回原结构的全内部初等嵌入。 -/
theorem selem_hull_collapse_l (hZFC : M.Models ZFC) {ω c U R A} (hω : M.IsOmega ω)
    (hU : M.TransitiveSet U) (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c U R)
    (hA : M.MemberSubset A U)
    (ha : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A ω) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ X d S B F j e T, Ssub_d I c d U R X S ∧ M.MemberSubset A X ∧
      M.CardinalLessOrEqual I X ω ∧ Selem_d I ω c d ∧ M.TransitiveSet B ∧ Mc_iso_d X B F ∧
      M.CardinalLessOrEqual I B ω ∧ (∀ x y, M.PairMember I y x j ↔ Rd_entry_d x y F) ∧
      Smem_d I e B T ∧ Smap_d I ω e c B U j := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨X, d, S, hs, hAX, hx, he⟩ := selem_hull_l I hZFC hω hm.1 hA ha
  obtain ⟨B, F, j, e, T, hB, hf, hj, hp, ht, hk⟩ := selem_collapse_l hZF hω hU hm hs he
  obtain ⟨v, hv⟩ := hx
  exact ⟨X, d, S, B, F, j, e, T, hs, hAX, ⟨v, hv⟩, he, hB, hf,
    ZF.exists_compositionInjection hZF I hj.1 hv, hp, ht, hk⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 指定内部 club 中的实际初等模型

先构造真实司寇伦图，再在给定 club 中闭合该图。因此同一个内部可数集合同时
具有 club 成员资格和完整内部初等性，供 proper 主条件与泛型提升共同使用。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem selem_club_hull_l (hZFC : M.Models ZFC) {ω c X R C A} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hC : Cc_club_d I ω X C) (hA : M.MemberSubset A X)
    (ha : M.CardinalLessOrEqual I A ω) : ∃ N d S,
      Ssub_d I c d X R N S ∧ Selem_d I ω c d ∧ M.MemberSubset A N ∧ M.mem N C := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨u, L, S, T, D, K, hK⟩ := ssk_exists_l I hZFC hω c hM.2.1
  obtain ⟨J, hJ⟩ := ZF.exists_identityBijection hZF I ω
  have ht := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hK.codes) ⟨J, hJ.1⟩ hK.labels
  obtain ⟨N, hN, hAN, hc⟩ := ZFC.fc_club_hull_l I hZFC hω hK.params hK.domain hK.graph ht hC hA ha
  obtain ⟨d, Q, hQ, he⟩ := selem_of_skolem_l I hZF hω hM hK.codes (hC.members N hN).1
    (hK.point_mem_l I hZF hω hM hc) (hK.closed_l I (hC.members N hN).1 hc)
  exact ⟨N, d, Q, hQ, he, hAN, hN⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部初等小模型在指定子集上的实际 club

固定一次司寇伦选择图后，最小闭包的交集组成真实 club。每个成员都给出一个
包含固定种子的内部可数初等模型见证，交集等式精确保留原成员，而非仅给出包含。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem selem_trace_club_l (hZFC : M.Models ZFC) {ω c H R A X} (hω : M.IsOmega ω)
    (hM : Smdl_d I c H R) (hA : M.MemberSubset A H) (ha : M.CardinalLessOrEqual I A ω)
    (hX : M.MemberSubset X H) : ∃ C, Cc_club_d I ω X C ∧
      ∀ Y, M.mem Y C → ∃ N d S, Ssub_d I c d H R N S ∧ Selem_d I ω c d ∧
        M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧ ∀ x, M.mem x Y ↔ M.mem x N ∧ M.mem x X := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨u, V, S, T, D, K, hK⟩ := ssk_exists_l I hZFC hω c hM.2.1
  obtain ⟨f, hf⟩ := ZF.exists_identityBijection hZF I ω
  have ht := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hK.codes) ⟨f, hf.1⟩ hK.labels
  obtain ⟨C, hC, hc⟩ := ZFC.fc_trace_club_l I hZFC hω hK.params hK.domain hK.graph ht hA ha hX
  refine ⟨C, hC, fun Y hY => ?_⟩
  obtain ⟨N, hn, hCount, he⟩ := (hc Y).mp hY
  obtain ⟨d, S', hSub, hElem⟩ := selem_of_skolem_l I hZF hω hM hK.codes hn.2.2.1
    (hK.point_mem_l I hZF hω hM hn.2.2.2.1) (hK.closed_l I hn.2.2.1 hn.2.2.2.1)
  exact ⟨N, d, S', hSub, hElem, hn.1, hCount, he⟩

end YesMetaZFC.SetTheory.Internal
