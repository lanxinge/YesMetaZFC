import YesMetaZFC.SetTheory.InnerModel.Condensation.Collapse
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure
import YesMetaZFC.Model.SetTheory.Internal.ElementaryHull

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

/-- 现有可数壳构造的完整实例；凝聚主定理本身没有可数性限制。 -/
theorem jc_countable_hull_l (hZFC : M.Models ZFC) {ω a U A : M.Domain} (hω : M.IsOmega ω)
    (ha : M.IsOrdinal a) (hU : Jh_value_d a U) (hn : ∃ x, M.mem x U) (hA : M.MemberSubset A U)
    (hc : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A ω) :
    ∃ X b B F, M.MemberSubset A X ∧ M.MemberSubset X U ∧
      M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X ω ∧ J_d b B ∧ Mc_iso_d X B F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, R, hm, hr⟩ := Internal.smdl_membership_l I hZF hn
  obtain ⟨X, d, S, hs, hAX, hx, he⟩ := Internal.selem_hull_l I hZFC hω hm hA hc
  obtain ⟨b, B, F, hb, hf, _⟩ := jc_internal_l I hZF hω ha hU ⟨hm, hr⟩ hs he
  exact ⟨X, b, B, F, hAX, hs.subset, hx, hb, hf⟩

end YesMetaZFC.SetTheory.InnerModel
