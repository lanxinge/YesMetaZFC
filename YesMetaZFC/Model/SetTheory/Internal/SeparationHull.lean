import YesMetaZFC.Model.SetTheory.Internal.Separation
import YesMetaZFC.Model.SetTheory.Internal.ElementaryHull
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 可数传递模型中的全内部代码分离

从极限 V 层与可数种子自动构造传递坍塌，保留种子的原像，再沿实际初等嵌入
回拉全部内部公式的分离集。可数壳需要 ZFC；分离回拉本身保留 ZF 强度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem v_separation_hull_l (hZFC : M.Models ZFC) {ω δ Y A} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hY : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ Y)
    (hA : M.MemberSubset A Y)
    (hc : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A ω) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ B c R d S j, M.TransitiveSet B ∧ M.CardinalLessOrEqual I B ω ∧
      Smem_d I c Y R ∧ Smem_d I d B S ∧ Smap_d I ω d c B Y j ∧
      (∀ x, M.mem x A → ∃ b, M.mem b B ∧ M.PairMember I b x j) ∧
      ∀ E F n r i f D, M.IsFunctionSpace I E ω B → Sfm_d I ω n F → M.mem r n → M.mem i ω →
        M.mem f E → M.mem D B → ∃ C, M.mem C B ∧ Ssep_d I B S E F n r i f D C := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨a, ha⟩ := hδ.2.1
  obtain ⟨c, R, hm, hR⟩ := smdl_membership_l I hZF ⟨a, ZF.v_ordinal_mem_l I hZF hY ha⟩
  have hYt := ZF.v_transitive_l I hZF hY
  obtain ⟨X, e, T, B, F, j, d, S, _, hAX, _, _, hB, hf, hb, hp, hs, hj⟩ :=
    selem_hull_collapse_l hZFC hω hYt ⟨hm, hR⟩ hA hc
  refine ⟨B, c, R, d, S, j, hB, hb, ⟨hm, hR⟩, hs, hj, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, hf⟩ := hf.function.2.1 x (hAX x hx)
    exact ⟨b, hb, (hp x b).mpr hf⟩
  · intro E F n r i f D hE hF hr hi hf hD
    obtain ⟨D', hDY, hDD⟩ := hj.1.1.2.2 D hD
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D'
    exact smap_separation_l I hZF hω hB hYt hs ⟨hm, hR⟩ hj hP
      (hYt P (ZF.v_power_mem_l I hZF hY hδ hDY hP)) hE hF hr hi hf hDD

end YesMetaZFC.SetTheory.Internal
