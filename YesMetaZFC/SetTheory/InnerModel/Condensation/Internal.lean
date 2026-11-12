import YesMetaZFC.SetTheory.InnerModel.Condensation.Collapse
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Embedding.ElementaryTrace

/-! # 内部初等结构与实际 Skolem 壳的凝聚入口 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention}

/-- 完整内部初等证书直接产生原 J 层及实际坍塌图。 -/
theorem jc_internal_l (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {ω a U X c d R S : M.Domain} (hω : M.IsOmega ω) (ha : M.IsOrdinal a) (hU : Jh_value_d a U)
    (hm : Internal.Smem_d I c U R) (hs : Internal.Ssub_d I c d U R X S) (he : Internal.Selem_d I ω c d) :
    ∃ b B F, J_d b B ∧ Mc_iso_d X B F ∧
      ∀ x y, Rd_entry_d x y F ↔ M.mem x X ∧ Mc_value_d X x y :=
  jc_condensation_l (ZF.models_kpi_l hZF) ha hU (Internal.selem_sigma1_sub_l I hZF hω hm hs he)

/-- 可数壳及其 J 层坍塌，保留逆坍塌的全内部初等证书。 -/
theorem jc_countable_hull_l (hZFC : M.Models ZFC) {ω a U A : M.Domain} (hω : M.IsOmega ω)
    (ha : M.IsOrdinal a) (hU : Jh_value_d a U) (hn : ∃ x, M.mem x U) (hA : M.MemberSubset A U)
    (hc : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A ω) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ X b B F j c R e T, M.MemberSubset A X ∧ M.MemberSubset X U ∧
      M.CardinalLessOrEqual I X ω ∧ M.CardinalLessOrEqual I B ω ∧ J_d b B ∧ Mc_iso_d X B F ∧
      (∀ x y, M.PairMember I y x j ↔ Rd_entry_d x y F) ∧
      Internal.Smem_d I c U R ∧ Internal.Smem_d I e B T ∧ Internal.Smap_d I ω e c B U j := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, R, hm, hr⟩ := Internal.smdl_membership_l I hZF hn
  obtain ⟨X, d, S, B, F, j, e, T, hs, hAX, hx, he, hB, hf, hcB, hp, ht, hk⟩ :=
    Internal.selem_hull_collapse_l hZFC hω (jh_value_transitive_l (ZF.models_kpi_l hZF) hU) ⟨hm, hr⟩ hA hc
  obtain ⟨b, B', F', hb, hf', _⟩ := jc_internal_l I hZF hω ha hU ⟨hm, hr⟩ hs he
  have eq := (mc_map_unique_l (ZF.models_kpi_l hZF) hf.toMc_map_d hf'.toMc_map_d hB
    (jh_value_transitive_l (ZF.models_kpi_l hZF) hb.2)).1
  exact ⟨X, b, B, F, j, c, R, e, T, hAX, hs.subset, hx, hcB, eq.symm ▸ hb, hf, hp, ⟨hm, hr⟩, ht, hk⟩

end YesMetaZFC.SetTheory.InnerModel
