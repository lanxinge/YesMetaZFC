import YesMetaZFC.Model.SetTheory.Internal.Isomorphism
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.Collapse.Mostowski

/-! # Mostowski 图的完整内部初等性

直接消费已经构造的坍塌图，自动构造传递载体的隶属结构码与逆图。
两个方向都保持全部内部公式码，并可沿此回拉实际编码理论的模型性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem mc_smaps_l (hZF : M.Models ZF) {ω X B F c R} (hω : M.IsOmega ω)
    (hf : Mc_iso_d X B F) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) :
    ∃ d S j, Smem_d (kp_pair_l (ZF.modelsKP hZF)) d B S ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X B F ∧
      M.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP hZF)) j B X ∧
      (∀ x y, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) y x j ↔ Rd_entry_d x y F) ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c B X j := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨b, hb, _⟩ := hf.function.2.1 x hx
  obtain ⟨d, S, hd, hs⟩ := smdl_membership_l I hZF ⟨b, hb⟩
  have rel a b x y (ha : M.PairMember I a x F) (hb : M.PairMember I b y F) :
      M.PairMember I a b R ↔ M.PairMember I x y S := by
    have ha' := hf.function.bound_l ha
    have hb' := hf.function.bound_l hb
    exact (hm.2 a b).trans (Iff.trans
      ⟨fun h => ⟨ha'.2, hb'.2, (hf.member a b x y ha hb).mp h.2.2⟩,
        fun h => ⟨ha'.1, hb'.1, (hf.member a b x y ha hb).mpr h.2.2⟩⟩ (hs x y).symm)
  have bij := hf.bijection_l (ZF.modelsKP hZF)
  obtain ⟨j, hj, he⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  exact ⟨d, S, j, ⟨hd, hs⟩, smap_of_iso_l I hZF hω hm.1 hd bij rel, hj, fun x y => he y x,
    smap_of_iso_l I hZF hω hd hm.1 hj (fun x y a b ha hb =>
      (rel a b x y ((he x a).mp ha) ((he y b).mp hb)).symm)⟩

/-- 任意传递隶属结构的内部初等子模型，自动坍塌为带完整初等嵌入的传递模型。 -/
theorem selem_collapse_l (hZF : M.Models ZF) {ω c d U R X S} (hω : M.IsOmega ω)
    (hU : M.TransitiveSet U) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c U R)
    (hs : Ssub_d (kp_pair_l (ZF.modelsKP hZF)) c d U R X S)
    (he : Selem_d (kp_pair_l (ZF.modelsKP hZF)) ω c d) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ B F j e T, M.TransitiveSet B ∧ Mc_iso_d X B F ∧ M.IsSetBijectionFromTo I j B X ∧
      (∀ x y, M.PairMember I y x j ↔ Rd_entry_d x y F) ∧
      Smem_d I e B T ∧ Smap_d I ω e c B U j := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, F, hB, hf, _⟩ := mc_collapse_l (ZF.models_kpi_l hZF)
    ((selem_sigma1_sub_l I hZF hω hm hs he).extensional_l hZF.1 hU)
  obtain ⟨e, T, j, ht, _, hj, hp, hk⟩ := mc_smaps_l hZF hω hf (smem_sub_l I hm hs)
  exact ⟨B, F, j, e, T, hB, hf, hj, hp, ht, hk.target_sub_l I hZF.1 hs he⟩

end YesMetaZFC.SetTheory.Internal
