import YesMetaZFC.SetTheory.LargeCardinal.ExtenderElementary

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

theorem ep_constant_limit_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T S q c C V a d : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_family_d ω κ L F)
    (coherent : Es_coherent_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C V)
    (had : Rd_entry_d a d Z) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ b j n D U G r Y W, Smem_d I b X R ∧ Smap_d I ω b c X C j ∧
      M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R d G r Y W ∧
      ∀ x E, Rd_entry_d x E j ↔ M.mem x X ∧ ∃ f B u,
        M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B r ∧ KPair_d M u a B ∧ Rd_entry_d u E q := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, _, models⟩ := h.models
  obtain ⟨n, D, U, G, r, Y, W, hn, ha, hD, haU, hG, hm⟩ := models a d had
  obtain ⟨χ, b, e, H, Q, t, hχ, hωχ, hH, hX, hN, ht⟩ := source.presentation
  obtain ⟨P, U', hP, hU', _, hm'⟩ := rs_restrict_model_l hZFC source.omega hχ hωχ hH source.transitive hX hN ht
    (source.space_mem_l hZF hn hD) (hF.at_l hZF.1 haU ha hD) hG hm
  obtain ⟨i, hi, is⟩ := rs_constant_embedding_l hZFC source.omega hχ hωχ hH source.transitive hX hN ht
    (source.space_mem_l hZF hn hD) hP hU' hG hm'
  obtain ⟨k, hk, ks⟩ := ep_stage_embedding_l hZFC source hF coherent h limit model had hm.code
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

end YesMetaZFC.SetTheory.LargeCardinal
