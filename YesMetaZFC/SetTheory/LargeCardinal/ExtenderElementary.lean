import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTag

/-! # 有限支撑源系统的完整内部初等性

先在既有过渡图上识别源内部初等映射，再用标签同构接入通用定向极限定理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Ep_graph_d.elementary_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T S : M.Domain}
    (h : Ep_graph_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T S)
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_family_d ω κ L F)
    (coherent : Es_coherent_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F) :
    Di_elementary_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω O A p T S := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz, models⟩ := h.models
  intro a b c Y V d W U stage₀ stage₁ hab
  obtain ⟨ha, hb, q, m, n, hm, hn, hq, hnb, hqa⟩ := (h.order_spec a b).mp hab
  obtain ⟨c₀, _, hac⟩ := hz.2.1 a ha
  obtain ⟨c₁, _, hbd⟩ := hz.2.1 b hb
  obtain ⟨_, _, _, inj⟩ := (h.indices b).mp hb
  obtain ⟨j, C₀, S₀, C₁, S₁, hc₀, hc₁, _, elem, _, spec, _⟩ :=
    ep_map_l hZFC source hF coherent hm hn hq hnb inj hqa (models a c₀ hac) (models b c₁ hbd)
  obtain ⟨e, _, he, _, es, _⟩ := ep_tag_l hZF source.omega h stage₀ hac hc₀
  obtain ⟨_, u, _, hu, _, us⟩ := ep_tag_l hZF source.omega h stage₁ hbd hc₁
  obtain ⟨v, hv, vs⟩ := smap_comp_l I hZF he elem
  obtain ⟨w, hw, ws⟩ := smap_comp_l I hZF hv hu
  refine ⟨w, hw, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨hxY, D, hxD, hDy⟩ := (ws x y).mp hxy
    obtain ⟨_, B, hxB, hBD⟩ := (vs x D).mp hxD
    obtain ⟨_, hpx⟩ := (es x B).mp hxB
    obtain ⟨hyW, hpy⟩ := (us D y).mp hDy
    exact ⟨hxY, hyW, (h.arrow_l hpx hpy).mpr ⟨((stage₀.2.1 x).mp hxY).1,
      ((stage₁.2.1 y).mp hyW).1, ((spec B D).mp hBD).2.2⟩⟩
  · rintro ⟨hxY, hyW, hxy⟩
    obtain ⟨B, hpx, hat⟩ := h.label_l (((stage₀.2.1 x).mp hxY).2)
    obtain ⟨D, hpy, hbt⟩ := h.label_l (((stage₁.2.1 y).mp hyW).2)
    have hBD := (spec B D).mpr ⟨(ep_at_read_l hz hac hc₀.1).mp hat,
      (ep_at_read_l hz hbd hc₁.1).mp hbt, ((h.arrow_l hpx hpy).mp hxy).2.2⟩
    exact (ws x y).mpr ⟨hxY, D, (vs x D).mpr ⟨hxY, B, (es x B).mpr ⟨hxY, hpx⟩, hBD⟩,
      (us D y).mpr ⟨hyW, hpy⟩⟩

/-- 原分量类结构到实际极限的完整内部初等嵌入，并保留精确的带标签代表方程。 -/
theorem ep_stage_embedding_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T S q c C V a d D W : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_family_d ω κ L F)
    (coherent : Es_coherent_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C V)
    (had : Rd_entry_d a d Z) (stage : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d D W) :
    ∃ j, Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω d c D C j ∧
      ∀ B E, Rd_entry_d B E j ↔ M.mem B D ∧ ∃ u, KPair_d M u a B ∧ Rd_entry_d u E q := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := stage.2.1
  obtain ⟨u, hu⟩ := I.total a B
  have huA := (h.nodes u).mpr ⟨a, B, hu, d, D, W, had, stage.1, hB⟩
  obtain ⟨d', D', W', ht⟩ := di_stage_exists_l hZF h.diagram ((h.index u a B hu).mpr huA)
  obtain ⟨_, e, _, he, _, es⟩ := ep_tag_l hZF source.omega h.toEp_graph_d ht had stage
  obtain ⟨k, hk, ks⟩ := di_elementary_limit_l hZF source.omega h.diagram limit
    (h.toEp_graph_d.elementary_l hZFC source hF coherent) ht model
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF he hk
  refine ⟨j, hj, fun B E => (js B E).trans (and_congr_right fun hB => ?_)⟩
  apply exists_congr
  intro u
  refine ⟨fun ⟨hBu, huE⟩ => ⟨((es B u).mp hBu).2, ((ks u E).mp huE).2⟩, fun ⟨hu, huE⟩ => ?_⟩
  have huA := (h.nodes u).mpr ⟨a, B, hu, d, D, W, had, stage.1, hB⟩
  have huD := (ht.2.1 u).mpr ⟨huA, (h.index u a B hu).mpr huA⟩
  exact ⟨(es B u).mpr ⟨huD, hu⟩, (ks u E).mpr ⟨huD, huE⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
