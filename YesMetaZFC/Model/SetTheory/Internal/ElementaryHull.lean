import YesMetaZFC.Model.SetTheory.Internal.Elementary
import YesMetaZFC.Model.SetTheory.Internal.Skolem
import YesMetaZFC.Model.SetTheory.Internal.Collapse

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
