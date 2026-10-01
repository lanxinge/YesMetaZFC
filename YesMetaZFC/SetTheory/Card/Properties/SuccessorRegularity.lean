import YesMetaZFC.SetTheory.Card.Properties.Regularity
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication
import YesMetaZFC.SetTheory.Card.CountableUnion
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 内部后继基数的正则性

若 μ⁺ 有长度不超过 μ 的共尾序列，其值域由不超过 μ 个大小不超过 μ 的序数
组成；内部选择和 μ×μ≈μ 会把 μ⁺ 单射回 μ，与 Hartogs 性矛盾。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem hartogs_regular_l (hZFC : M.Models ZFC) {ω μ κ} (hω : M.IsOmega ω)
    (hμ : M.IsInfiniteCardinal I ω μ) (hκ : M.IsHartogsNumber I κ μ) : M.IsRegularCardinal I κ := by
  have hZF := models_zf_l hZFC
  have hw := ZF.omega_cardinal_l I hZF hω
  have hk := hκ.isCardinal hZF I
  obtain ⟨J, hJ⟩ := ZF.exists_identityBijection hZF I μ
  have hμκ := (hκ.2 μ hμ.1.1).mpr ⟨J, hJ.1⟩
  obtain ⟨K, hK⟩ := ZF.exists_inclusionInjection hZF I (hk.1.transitive.memberSubset hμκ)
  obtain ⟨W, hW⟩ := hμ.2
  have hlim := ZF.infiniteCardinal_isLimitOrdinal hZF I hω hw
    ⟨hk, ZF.exists_compositionInjection hZF I hW hK⟩
  refine ⟨hk, hlim.hasCofinalOrdinalSequence_self hZF I, fun δ ⟨F, hF⟩ => ?_⟩
  have hδ := hF.isIncreasing.1.1.1
  rcases Structure.IsOrdinal.trichotomy hZF.1 hk.1 hδ
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) κ δ) with he | hκδ | hδκ
  · exact Or.inl (hZF.1.eq_of_same_members κ δ he)
  · exact Or.inr hκδ
  · apply False.elim
    apply hκ.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    obtain ⟨A, hA, hU⟩ := hF.isLimit.2.2
    have hf := hF.isSetFunctionFromTo
    have hfA : M.IsSetFunctionFromTo I F δ A := ⟨hf.1, hf.2.1, fun i hi => by
      obtain ⟨α, _, hiα⟩ := hf.2.2 i hi
      exact ⟨α, (hA α).mpr ⟨i, hiα⟩, hiα⟩⟩
    have hAμ := ZF.ordinal_image_bound_l I hZF hμ.1.1 ((hκ.2 δ hδ).mp hδκ) hfA
      (fun α hα => (hA α).mp hα |>.elim fun i hi => ⟨i, hf.input_mem_of_pairMember hi, hi⟩)
    obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I μ μ
    obtain ⟨G, hG⟩ := union_bound_l I hZFC hAμ hU (fun α hα => by
      obtain ⟨i, hi⟩ := (hA α).mp hα
      have hακ := hf.output_mem_of_pairMember hi
      exact (hκ.2 α (hk.1.mem hακ)).mp hακ) hP
    obtain ⟨H, hH⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
      ⟨hμ.1, J, hJ⟩ hP (ZF.infiniteCardinal_selfMultiplication hZF I hω hw hμ)
    exact ZF.exists_compositionInjection hZF I hG hH

end YesMetaZFC.SetTheory.ZFC
