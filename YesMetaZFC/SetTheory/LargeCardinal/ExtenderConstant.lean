import YesMetaZFC.SetTheory.LargeCardinal.ExtenderElementary
import YesMetaZFC.Model.SetTheory.Internal.Extensionality

/-! # 源到整个有限支撑极限的常值初等嵌入

完整测度在源内的限制保持原商；常值嵌入与任一分量的极限嵌入复合。
结果仍保留源代表、商投影及带标签节点三者的精确图方程。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 常值箭头的实际代表证书，保留代表的源内定义域及源内值域界。 -/
def Ep_constants_d (X q i : M.Domain) : Prop := ∀ x E, Rd_entry_d x E i →
  ∃ u a B f D, M.mem D X ∧ Sfun_d X D f ∧ Rs_const_d D x f ∧ M.mem f B ∧ KPair_d M u a B ∧ Rd_entry_d u E q

theorem ep_constant_limit_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q c C V a d : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hF : Em_source_d ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S)
    (had : Rd_entry_d a d Z) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ b j n D U G r Y W, Smem_d I b X R ∧ Smap_d I ω b c X C j ∧
      M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R d G r Y W ∧
      ∀ x E, Rd_entry_d x E j ↔ M.mem x X ∧ ∃ f B u,
        M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B r ∧ KPair_d M u a B ∧ Rd_entry_d u E q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, _, models⟩ := h.models
  obtain ⟨n, D, U, G, r, Y, W, hn, ha, hD, haU, hG, hm⟩ := models a d had
  obtain ⟨b, hX⟩ := source.code
  obtain ⟨P, U', hP, hU', _, hm'⟩ := rs_restrict_model_l hZF source.omega source.transitive hX source.theory
    (source.space_mem_l hZF hn hD) (hF.at_l hZF.1 haU ha hD) hG hm
  obtain ⟨i, hi, is⟩ := rs_constant_embedding_l hZF source.omega source.transitive hX source.theory (source.uniform_l hZF hn hD)
    (source.space_mem_l hZF hn hD) hP hU' hG hm'
  obtain ⟨k, hk, ks⟩ := ep_stage_embedding_l hZF source.omega h limit elementary model had hm.code
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hi hk
  refine ⟨b, j, n, D, U, G, r, Y, W, hX, hj, hn, ha, hD, haU, hG, hm, fun x E =>
    (js x E).trans (and_congr_right fun hx => ?_)⟩
  constructor
  · rintro ⟨B, hxB, hBE⟩
    obtain ⟨_, f, hf, hc, hfr⟩ := (is x B).mp hxB
    obtain ⟨_, u, hu, huE⟩ := (ks B E).mp hBE
    exact ⟨f, B, u, hf, hc, hfr, hu, huE⟩
  · rintro ⟨f, B, u, hf, hc, hfr, hu, huE⟩
    exact ⟨B, (is x B).mpr ⟨hx, f, hf, hc, hfr⟩,
      (ks B E).mpr ⟨hm.map.projection.output_mem_of_pairMember hfr, u, hu, huE⟩⟩

/-- 原始商的常值图与外延性先于任何良基性或坍塌构造。 -/
theorem ep_constant_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q c C V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S) :
    ∃ b i, Smem_d (kp_pair_l (ZF.modelsKP hZF)) b X R ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω b c X C i ∧ Ep_constants_d X q i ∧ Wc_ext_d C V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := model.2.1
  obtain ⟨u, hu⟩ := (limit.range B).mp hB
  obtain ⟨a, ha, _⟩ := system.diagram.index.2.1 u (limit.projection.bound_l hu).1
  obtain ⟨_, hz, _⟩ := system.models
  obtain ⟨d, _, had⟩ := hz.2.1 a ha
  obtain ⟨b, i, n, D, U, G, r, E, Q, hm, hi, hn, ha, hD, haU, hG, md, spec⟩ :=
    ep_constant_limit_l hZF source family system limit model elementary had
  have constants : Ep_constants_d X q i := by
    intro x H hxH
    obtain ⟨_, f, B, u, hf, hc, hfr, hu, huH⟩ := (spec x H).mp hxH
    exact ⟨u, a, B, f, D, source.space_mem_l hZF hn hD,
      source.function_l hZF ((hG f).mp hf).1 ((hG f).mp hf).2,
      hc, md.map.representative_l I (family.at_l hZF.1 haU ha hD).base hfr, hu, huH⟩
  have extX : Wc_ext_d X R := fun x hx y hy same => hZF.1.eq_of_same_members x y (fun z =>
    ⟨fun hz => ((hm.2 z y).mp ((same z (source.transitive x hx z hz)).mp
      ((hm.2 z x).mpr ⟨source.transitive x hx z hz, hx, hz⟩))).2.2,
     fun hz => ((hm.2 z x).mp ((same z (source.transitive y hy z hz)).mpr
      ((hm.2 z y).mpr ⟨source.transitive y hy z hz, hy, hz⟩))).2.2⟩)
  exact ⟨b, i, hm, hi, constants, hi.extensional_l hZF source.omega hm.1 model extX⟩

end YesMetaZFC.SetTheory.LargeCardinal
