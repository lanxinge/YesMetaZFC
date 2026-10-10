import YesMetaZFC.Model.SetTheory.Internal.UniversalClosure
import YesMetaZFC.Model.SetTheory.Internal.Uniformization
import YesMetaZFC.Model.SetTheory.Internal.SourceAlgebra

/-! # 源模型的全内部分离与有界集合代数

分离量化全部内部公式码和赋值；选择仅针对已有值域界内的关系。后继模型的保持
由全称闭包证明，因而覆盖新模型中不在旧嵌入像内的参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Sc_theory_d (ω X R : M.Domain) : Prop where
  separation : ∀ E F n r i f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem f E → M.mem D X → ∃ A, M.mem A X ∧ Ssep_d I X R E F n r i f D A
  algebra : Sc_algebra_d X

theorem sc_h_theory_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) (R : M.Domain) :
    Sc_theory_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨fun E F n r i f D _ _ _ _ _ hD => ?_,
    sc_h_algebra_l hZFC hω hχ hωχ hH⟩
  · obtain ⟨A, hA⟩ := ssep_exists_l I hZF H R E F n r i f D
    exact ⟨A, ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hD A (fun x hx => ((hA x).mp hx).1), hA⟩

theorem sc_v_theory_l (hZFC : M.Models ZFC) {δ V : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V) (ω R : M.Domain) :
    Sc_theory_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω V R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨fun E F n r i f D _ _ _ _ _ hD => ?_, sc_v_algebra_l hZFC hδ hV⟩
  obtain ⟨A, hA⟩ := ssep_exists_l I hZF V R E F n r i f D
  exact ⟨A, ZF.v_subset_mem_l I hZF hV hD (fun x hx => ((hA x).mp hx).1), hA⟩

theorem sc_source_theory_l (hZFC : M.Models ZFC) {ω χ c d X R H S q : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d H S)
    (hq : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d X H q) :
    Sc_theory_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨fun E F n r i f D hE hF hr hi hf hD => ?_,
    (sc_algebra_iff_l I hZF hω hX (ZF.h_transitive_l I hZF hH) hm hn hq).mpr (sc_h_algebra_l hZFC hω hχ hωχ hH)⟩
  · obtain ⟨D', hD', hDD⟩ := hq.1.1.2.2 D hD
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D'
    exact smap_separation_l I hZF hω hX (ZF.h_transitive_l I hZF hH) hm hn hq hP
      (fun A hA => ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hD' A ((hP A).mp hA)) hE hF hr hi hf hDD

theorem sc_separation_forward_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (source : Sc_theory_d I ω X R) {K F n r i g D : M.Domain}
    (hK : M.IsFunctionSpace I K ω Y) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hg : M.mem g K) (hD : M.mem D Y) : ∃ A, M.mem A Y ∧ Ssep_d I Y S K F n r i g D A := by
  obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, _, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hi
  obtain ⟨m, G, k, build, code⟩ := sfm_sep_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  -- 源中的分离模式先变成对全部赋值有效的单一内部程序。
  have valid f (hf : M.mem f E) : Ssat_d I X R E G m k f := by
    obtain ⟨D, hD, hsD⟩ := ((hE f).mp hf).2.2 s hs
    exact (code X R E c f D hX hm hE hf hsD).mpr (source.separation E F n r i f D hE hF hr hi hf hD)
  obtain ⟨g', update, hgf⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
  obtain ⟨A, hAY, hA⟩ := (code Y S K d g' D hY hn hK ((hK g').mpr hgf)
    ((update.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
    ((hq.valid_l I hZF hω hm.1 hn.1 build.program build.root hE hK).mp valid g' ((hK g').mpr hgf))
  exact ⟨A, hAY, (ssep_agree_l I hZF hF hb hr hi hK hg ((hK g').mpr hgf)
    (update.agree_l I hsb) (hY D hD)).mpr hA⟩

/-- 理论保持覆盖后继模型的全部参数，不要求它们具有旧参数原像。 -/
theorem Sc_theory_d.map_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (source : Sc_theory_d I ω X R) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q) : Sc_theory_d I ω Y S :=
  ⟨fun _ _ _ _ _ _ _ => sc_separation_forward_l I hZF hω hX hY hm hn hq source,
    (sc_algebra_iff_l I hZF hω hX hY hm hn hq).mp source.algebra⟩

/-- 分离模式的全称闭包沿完整初等图回拉，赋值仍允许内部非标准长度。 -/
theorem Sc_theory_d.pull_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (target : Sc_theory_d I ω Y S) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q) : Sc_theory_d I ω X R := by
  refine ⟨fun E F n r i f D hE hF hr hi hf hD => ?_,
    (sc_algebra_iff_l I hZF hω hX hY hm hn hq).mpr target.algebra⟩
  obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, _, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hi
  obtain ⟨m, G, k, build, code⟩ := sfm_sep_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  have valid g (hg : M.mem g K) : Ssat_d I Y S K G m k g := by
    obtain ⟨A, hA, hsA⟩ := ((hK g).mp hg).2.2 s hs
    exact (code Y S K d g A hY hn hK hg hsA).mpr (target.separation K F n r i g A hK hF hr hi hg hA)
  obtain ⟨f', update, hff⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs hD
  obtain ⟨A, hAX, hA⟩ := (code X R E c f' D hX hm hE ((hE f').mpr hff)
    ((update.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
    ((hq.valid_l I hZF hω hm.1 hn.1 build.program build.root hE hK).mpr valid f' ((hE f').mpr hff))
  exact ⟨A, hAX, (ssep_agree_l I hZF hF hb hr hi hE hf ((hE f').mpr hff)
    (update.agree_l I hsb) (hX D hD)).mpr hA⟩

end YesMetaZFC.SetTheory.Internal
