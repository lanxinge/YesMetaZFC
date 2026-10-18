import YesMetaZFC.SetTheory.LargeCardinal.ExtenderGraphs

/-! # 有限支撑测度族的完整定向系统

对已经统一生成的真实图逐项核验函子律。所有过渡图同时作用于同一批规范
源分量；证明保留模型内部任意有限长度及全部坐标排列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Eg_graph_d.system_l (hZF : M.Models ZF) {ω κ L X J O Z A p T S : M.Domain}
    (hω : M.IsOmega ω) (h : Eg_graph_d ω κ L X J O Z A p T S)
    (reps : ∀ a B, Ep_at_d Z a B → ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
      (∃ f, M.mem f B) ∧ ∀ f, M.mem f B → Ep_fun_d κ X n f)
    (transition : Eg_transition_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X O Z) :
    Di_system_d J O A p T S ∧ ∀ u v a b B C,
      KPair_d M u a B → KPair_d M v b C → Rd_entry_d u v T → Ep_lift_d ω κ L X a b B C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz⟩ := h.codes
  have label u a (hua : Rd_entry_d u a p) : ∃ B, KPair_d M u a B ∧ Ep_at_d Z a B := by
    obtain ⟨b, B, hu, hat⟩ := (h.nodes u).mp (h.projection.bound_l hua).1
    have hub := (h.index u b B hu).mpr (h.projection.bound_l hua).1
    have e := (fn0_function_l (ZF.modelsKP hZF) h.projection).1.2 u b a hub hua
    exact ⟨B, e ▸ hu, e ▸ hat⟩
  have node a B (hat : Ep_at_d Z a B) : ∃ u, M.mem u A ∧ KPair_d M u a B ∧ Rd_entry_d u a p := by
    obtain ⟨u, hu⟩ := I.total a B
    have huA := (h.nodes u).mpr ⟨a, B, hu, hat⟩
    exact ⟨u, huA, hu, (h.index u a B hu).mpr huA⟩
  have bounds u v (huv : Rd_entry_d u v T) : M.mem u A ∧ M.mem v A :=
    ⟨((h.arrows u v).mp huv).1, ((h.arrows u v).mp huv).2.1⟩
  have forward u v a b (hua : Rd_entry_d u a p) (hvb : Rd_entry_d v b p) (huv : Rd_entry_d u v T) : Rd_entry_d a b O := by
    obtain ⟨B, hu, _⟩ := label u a hua
    obtain ⟨C, hv, _⟩ := label v b hvb
    obtain ⟨m, n, q, _, _, hm, hn, hq, hb, hqa, _⟩ := ((h.arrow_l hu hv).mp huv).2.2
    exact (h.order_spec a b).mpr ⟨(h.projection.bound_l hua).2, (h.projection.bound_l hvb).2,
      q, m, n, hm, hn, hq, hb, hqa⟩
  have maps a b (hab : Rd_entry_d a b O) : ∃ j c C V d D W,
      Rd_entry_d a c Z ∧ Rd_entry_d b d Z ∧ Smdl_d I c C V ∧ Smdl_d I d D W ∧
      M.IsSetInjectionFromTo I j C D ∧
      (∀ B E B' E', Rd_entry_d B B' j → Rd_entry_d E E' j → (Rd_entry_d B E V ↔ Rd_entry_d B' E' W)) ∧
      (∀ B E, Rd_entry_d B E j ↔ M.mem B C ∧ M.mem E D ∧ Ep_arrow_d ω κ L X a b B E) ∧
      ∀ B E, Rd_entry_d B E j → Ep_lift_d ω κ L X a b B E := by
    obtain ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, elem, spec, lift⟩ := transition a b hab
    exact ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, elem.1,
      fun B E B' E' hb he => elem.relation_l I hZF hω hc hd hb he, spec, lift⟩
  refine ⟨⟨h.order, h.projection, bounds, forward, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨a, B, huB, hat⟩ := (h.nodes u).mp hu
    obtain ⟨n, hn, hna, ⟨f, hf⟩, fs⟩ := reps a B hat
    obtain ⟨_, _, _, ha⟩ := (h.indices a).mp (h.projection.bound_l ((h.index u a B huB).mpr hu)).2
    obtain ⟨r, hr, hra⟩ := ec_factor_l hZF hna ⟨fn0_function_l (ZF.modelsKP hZF) hna, ha⟩ (fun i _ hi => ⟨i, hi⟩)
    have fixed i j (hij : Rd_entry_d i j r) : i = j := by
      obtain ⟨x, _, hix⟩ := hna.2.1 i (hr.bound_l hij).1
      exact ha i j x hix ((hra.value_l hr hna hij).mp hix)
    exact (h.arrow_l huB huB).mpr ⟨hu, hu, n, n, r, f, f, hn, hn, hr, hna, hra,
      hf, hf, ep_pull_id_l hZF.1 (fs f hf) fixed⟩
  · intro u v w huv hvw
    obtain ⟨a, B, hu, _⟩ := (h.nodes u).mp (bounds u v huv).1
    obtain ⟨b, C, hv, hvC⟩ := (h.nodes v).mp (bounds u v huv).2
    obtain ⟨c, D, hw, hwD⟩ := (h.nodes w).mp (bounds v w hvw).2
    have hvb := (h.index v b C hv).mpr (bounds u v huv).2
    have hwc := (h.index w c D hw).mpr (bounds v w hvw).2
    obtain ⟨j, c₀, C₀, V, c₁, C₁, W, hbc, hcc, mc₀, mc₁, _, _, spec, lift⟩ :=
      maps b c (forward v w b c hvb hwc hvw)
    have hCD := (spec C D).mpr ⟨(ep_at_read_l hz hbc mc₀.1).mp hvC,
      (ep_at_read_l hz hcc mc₁.1).mp hwD, ((h.arrow_l hv hw).mp hvw).2.2⟩
    obtain ⟨m, n, r, f, g, hm, hn, hr, hnb, hra, hf, hg, pull⟩ := ((h.arrow_l hu hv).mp huv).2.2
    obtain ⟨n', l, t, g', _, hl, ht, hlc, htb, hg', pull'⟩ := lift C D hCD g hg
    have eq := htb.1.domain_eq_l hZF.1 hnb
    subst n'
    obtain ⟨s, hs⟩ := cp0_exists_l (ZF.modelsKP hZF) hr ht
    exact (h.arrow_l hu hw).mpr ⟨(bounds u v huv).1, (bounds v w hvw).2, m, l, s, f, g',
      hm, hl, hs.1, hlc, Cp0_d.assoc_l ht hr hs hlc htb hra, hf, hg',
      ep_pull_comp_l (ZF.modelsKP hZF) hr ht hs pull pull'⟩
  · intro u a b hua hab
    obtain ⟨B, hu, hat⟩ := label u a hua
    obtain ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, hj, _, spec, _⟩ := maps a b hab
    have hBC := (ep_at_read_l hz hac hc.1).mp hat
    obtain ⟨E, hED, hBE⟩ := hj.1.2.2 B hBC
    obtain ⟨v, hvA, hv, hvb⟩ := node b E ⟨d, D, W, hbd, hd.1, hED⟩
    exact ⟨v, hvb, (h.arrow_l hu hv).mpr ⟨(h.projection.bound_l hua).1, hvA, ((spec B E).mp hBE).2.2⟩⟩
  · intro u v w b hvb hwb huv huw
    obtain ⟨a, _, hua⟩ := h.projection.2.1 u (bounds u v huv).1
    obtain ⟨B, hu, huB⟩ := label u a hua
    obtain ⟨C, hv, hvC⟩ := label v b hvb
    obtain ⟨D, hw, hwD⟩ := label w b hwb
    obtain ⟨j, c, E, V, d, G, W, hac, hbd, hc, hd, hj, _, spec, _⟩ := maps a b (forward u v a b hua hvb huv)
    have hBE := (ep_at_read_l hz hac hc.1).mp huB
    have hCG := (ep_at_read_l hz hbd hd.1).mp hvC
    have hDG := (ep_at_read_l hz hbd hd.1).mp hwD
    have e := hj.1.1.2 B C D ((spec B C).mpr ⟨hBE, hCG, ((h.arrow_l hu hv).mp huv).2.2⟩)
      ((spec B D).mpr ⟨hBE, hDG, ((h.arrow_l hu hw).mp huw).2.2⟩)
    exact kpair_unique_l M hZF.1 (e ▸ hv) hw
  · intro u v w a hua hva huw hvw
    obtain ⟨b, _, hwb⟩ := h.projection.2.1 w (bounds u w huw).2
    obtain ⟨B, hu, huB⟩ := label u a hua
    obtain ⟨C, hv, hvC⟩ := label v a hva
    obtain ⟨D, hw, hwD⟩ := label w b hwb
    obtain ⟨j, c, E, V, d, G, W, hac, hbd, hc, hd, hj, _, spec, _⟩ := maps a b (forward u w a b hua hwb huw)
    have hBE := (ep_at_read_l hz hac hc.1).mp huB
    have hCE := (ep_at_read_l hz hac hc.1).mp hvC
    have hDG := (ep_at_read_l hz hbd hd.1).mp hwD
    have e := hj.2 B C D ((spec B D).mpr ⟨hBE, hDG, ((h.arrow_l hu hw).mp huw).2.2⟩)
      ((spec C D).mpr ⟨hCE, hDG, ((h.arrow_l hv hw).mp hvw).2.2⟩)
    exact kpair_unique_l M hZF.1 (e ▸ hu) hv
  · intro u v huv
    obtain ⟨huA, hvA, a, B, C, hu, hv, _⟩ := (h.relations u v).mp huv
    exact ⟨a, (h.index u a B hu).mpr huA, (h.index v a C hv).mpr hvA⟩
  · intro u v a w z b hua hva hwb hzb huw hvz
    obtain ⟨B, hu, huB⟩ := label u a hua
    obtain ⟨C, hv, hvC⟩ := label v a hva
    obtain ⟨D, hw, hwD⟩ := label w b hwb
    obtain ⟨E, he, hzE⟩ := label z b hzb
    obtain ⟨j, c, G, V, d, H, W, hac, hbd, hc, hd, hj, rel, spec, _⟩ := maps a b (forward u w a b hua hwb huw)
    have hBG := (ep_at_read_l hz hac hc.1).mp huB
    have hCG := (ep_at_read_l hz hac hc.1).mp hvC
    have hDH := (ep_at_read_l hz hbd hd.1).mp hwD
    have hEH := (ep_at_read_l hz hbd hd.1).mp hzE
    have old : Rd_entry_d u v S ↔ Rd_entry_d B C V := (h.relation_l hu hv).trans
      ⟨fun hh => (ep_rel_read_l hz hac hc.1).mp hh.2.2, fun hh =>
        ⟨(h.projection.bound_l hua).1, (h.projection.bound_l hva).1, (ep_rel_read_l hz hac hc.1).mpr hh⟩⟩
    have new : Rd_entry_d w z S ↔ Rd_entry_d D E W := (h.relation_l hw he).trans
      ⟨fun hh => (ep_rel_read_l hz hbd hd.1).mp hh.2.2, fun hh =>
        ⟨(h.projection.bound_l hwb).1, (h.projection.bound_l hzb).1, (ep_rel_read_l hz hbd hd.1).mpr hh⟩⟩
    exact old.trans ((rel B C D E ((spec B D).mpr ⟨hBG, hDH, ((h.arrow_l hu hw).mp huw).2.2⟩)
      ((spec C E).mpr ⟨hCG, hEH, ((h.arrow_l hv he).mp hvz).2.2⟩)).trans new.symm)
  · intro u v a b B C hu hv huv
    have huA := (bounds u v huv).1
    have hvA := (bounds u v huv).2
    obtain ⟨j, c, E, V, d, G, W, hac, hbd, hc, hd, _, _, spec, lifts⟩ := maps a b
      (forward u v a b ((h.index u a B hu).mpr huA) ((h.index v b C hv).mpr hvA) huv)
    exact lifts B C ((spec B C).mpr ⟨(ep_at_read_l hz hac hc.1).mp (h.at_l huA hu),
      (ep_at_read_l hz hbd hd.1).mp (h.at_l hvA hv), ((h.arrow_l hu hv).mp huv).2.2⟩)

theorem Ep_graph_d.transition_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T S : M.Domain}
    (h : Ep_graph_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T S)
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F) :
    Eg_transition_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X O Z := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨_, hz⟩ := h.codes
  intro a b hab
  obtain ⟨ha, hb, q, m, n, hm, hn, hq, hnb, hqa⟩ := (h.order_spec a b).mp hab
  obtain ⟨c, _, hac⟩ := hz.2.1 a ha
  obtain ⟨d, _, hbd⟩ := hz.2.1 b hb
  obtain ⟨_, _, _, inj⟩ := (h.indices b).mp hb
  obtain ⟨j, C, V, D, W, hc, hd, _, elem, _, spec, any⟩ := ep_map_l hZFC source hF coherent hm hn hq hnb inj hqa
    (h.components a c hac) (h.components b d hbd)
  exact ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, elem, spec, fun B E hBE f hf =>
    (any B E hBE f hf).elim fun g hg => ⟨m, n, q, g, hm, hn, hq, hnb, hqa, hg⟩⟩

theorem Ep_graph_d.system_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T S : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_graph_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T S) :
    Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T S := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨diagram, lifts⟩ := h.toEg_graph_d.system_l hZF source.omega (fun a B hat => by
    obtain ⟨c, C, V, _, component, model, hB⟩ := ep_at_model_l hZF h.components hat
    obtain ⟨n, hn, ha, point, functions⟩ := ep_representatives_l _ hZF.1 hF component model hB
    exact ⟨n, hn, ha, point, fun f hf => (functions f hf).2⟩) (h.transition_l hZFC source hF coherent)
  exact ⟨h, diagram, lifts⟩

theorem ep_system_exists_l (hZFC : M.Models ZFC) {ω κ K L X R F : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hc : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (hωL : M.MemberSubset ω L) : ∃ J O Z A p T S,
      Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T S := by
  obtain ⟨J, O, Z, A, p, T, S, hg⟩ := ep_graphs_l hZFC h hF hωL
  exact ⟨J, O, Z, A, p, T, S, hg.system_l hZFC h hF hc⟩

end YesMetaZFC.SetTheory.LargeCardinal
