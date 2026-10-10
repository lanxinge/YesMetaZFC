import YesMetaZFC.Model.SetTheory.Internal.Uniformization
import YesMetaZFC.Model.SetTheory.Internal.ElementaryHull
import YesMetaZFC.SetTheory.HereditaryCover

/-! # 可数传递壳的全内部码分离、收集与统一化

从可数种子选择实际正则 H(χ) 环境，构造完整内部初等壳及传递坍塌。
三个结论对同一个真实模型、全部内部程序及赋值成立，种子元素有明确的嵌入原像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem h_uniform_hull_l (hZFC : M.Models ZFC) {ω A} (hω : M.IsOmega ω)
    (hc : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A ω) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ χ H B c R d S q, M.IsRegularCardinal I χ ∧ M.mem ω χ ∧ H_d I χ H ∧
      M.TransitiveSet B ∧ M.CardinalLessOrEqual I B ω ∧ Smem_d I c H R ∧ Smem_d I d B S ∧ Smap_d I ω d c B H q ∧
      (∀ x, M.mem x A → ∃ b, M.mem b B ∧ M.PairMember I b x q) ∧
      ∀ E F n r i f D, M.IsFunctionSpace I E ω B → Sfm_d I ω n F → M.mem r n → M.mem i ω → M.mem f E → M.mem D B →
        (∃ C, M.mem C B ∧ Ssep_d I B S E F n r i f D C) ∧
        ∀ j, M.mem j ω → Scollect_d I B S E F n r i j f D B →
          (∃ C, M.mem C B ∧ Scollect_d I B S E F n r i j f D C) ∧
          (i ≠ j → ∃ g C, M.mem g B ∧ M.mem C B ∧ Suniform_d I B S E F n r i j f D C g) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨χ, H, hχ, hωχ, hH, hAH⟩ := ZFC.h_cover_l I hZFC hω A
  have hHt := ZF.h_transitive_l I hZF hH
  obtain ⟨c, R, hm, hr⟩ := smdl_membership_l I hZF ⟨A, hAH⟩
  obtain ⟨X, e, T, B, F, q, d, S, _, hAX, _, _, hB, hf, hb, hp, hs, hq⟩ :=
    selem_hull_collapse_l hZFC hω hHt ⟨hm, hr⟩ (hHt A hAH) hc
  refine ⟨χ, H, B, c, R, d, S, q, hχ, hωχ, hH, hB, hb, ⟨hm, hr⟩, hs, hq, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, hf⟩ := hf.function.2.1 x (hAX x hx)
    exact ⟨b, hb, (hp x b).mpr hf⟩
  · intro E F n r i f D hE hF hrF hi hf hD
    refine ⟨?_, fun j hj hh => ⟨smap_collection_l I hZFC hω hχ hωχ hH hB hs ⟨hm, hr⟩ hq hE hF hrF hi hj hf hD hh,
      fun hij => smap_uniform_l hZFC hω hχ hωχ hH hB hs ⟨hm, hr⟩ hq hE hF hrF hi hj hij hf hD hh⟩⟩
    obtain ⟨D', hDH, hDD⟩ := hq.1.1.2.2 D hD
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D'
    exact smap_separation_l I hZF hω hB hHt hs ⟨hm, hr⟩ hq hP
      (fun C hCP => ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hDH C ((hP C).mp hCP)) hE hF hrF hi hf hDD

end YesMetaZFC.SetTheory.Internal
