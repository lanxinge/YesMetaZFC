import YesMetaZFC.SetTheory.LargeCardinal.ExtenderArrows

/-! # 全分量图的代表读取及恒等、复合律 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem ep_representatives_l (hE : Extensional M) {ω κ L X R F a c C S B : M.Domain}
    (hF : Em_source_d ω κ L X F) (hm : Ep_component_d I ω κ L X R F a c)
    (hc : Smdl_d I c C S) (hB : M.mem B C) : ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
      (∃ f, M.mem f B) ∧ ∀ f, M.mem f B → M.mem f X ∧ Ep_fun_d κ X n f := by
  obtain ⟨n, D, U, G, p, C', S', hn, ha, hD, haU, hG, hp⟩ := hm
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hp.code hc
  have hu := (hF.at_l hE haU ha hD).base
  obtain ⟨f, hf⟩ := (hp.map.range B).mp hB
  refine ⟨n, hn, ha, ⟨f, hp.map.representative_l I hu hf⟩, fun g hg => ?_⟩
  have hgp := hp.map.member_l I hE hu hB hg
  have hgG := hp.map.projection.input_mem_of_pairMember hgp
  exact ⟨((hG g).mp hgG).1, D, hD, ((hG g).mp hgG).2⟩

theorem ep_relation_l (hE : Extensional M) {ω κ L X R F a c C S B D U f g : M.Domain}
    (hF : Em_source_d ω κ L X F) (hm : Ep_component_d I ω κ L X R F a c)
    (hc : Smdl_d I c C S) (hB : M.mem B C) (hD : M.mem D C) (hf : M.mem f B) (hg : M.mem g D)
    (haU : Rd_entry_d a U F) : M.PairMember I B D S ↔ Rp_rel_d I X U R f g := by
  obtain ⟨n, E, V, G, p, C', S', _, ha, hE', haV, _, hp⟩ := hm
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hp.code hc
  have eu := hF.function a V U haV haU
  subst V
  have hu := (hF.at_l hE haU ha hE').base
  exact hp.relation f g B D (hp.map.member_l I hE hu hB hf) (hp.map.member_l I hE hu hD hg)

theorem ep_arrow_id_l (hZF : M.Models ZF) {ω κ L X R F a c C S B : M.Domain}
    (hF : Em_source_d ω κ L X F) (ha : Ei_d ω L a) (hm : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c)
    (hc : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C S) (hB : M.mem B C) : Ep_arrow_d ω κ L X a a B B := by
  obtain ⟨_, _, _, inj⟩ := ha
  obtain ⟨n, hn, hna, ⟨f, hf⟩, functions⟩ := ep_representatives_l _ hZF.1 hF hm hc hB
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF hna ⟨fn0_function_l (ZF.modelsKP hZF) hna, inj⟩ (fun i _ hi => ⟨i, hi⟩)
  have idq i j (hij : Rd_entry_d i j q) : i = j := by
    obtain ⟨x, _, hix⟩ := hna.2.1 i (hq.bound_l hij).1
    exact inj i j x hix ((hqa.value_l hq hna hij).mp hix)
  exact ⟨n, n, q, f, f, hn, hn, hq, hna, hqa, hf, hf, ep_pull_id_l hZF.1 (functions f hf).2 idq⟩

theorem ep_arrow_comp_l (hZFC : M.Models ZFC) {ω κ K L X R F a b c v w B T C V x y z : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hco : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (hc : Ei_d ω L c)
    (hbM : Ep_component_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F b v)
    (hcM : Ep_component_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F c w)
    (hB : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) v B T)
    (hC : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) w C V)
    (hy : M.mem y B) (hz : M.mem z C) (hxy : Ep_arrow_d ω κ L X a b x y) (hyz : Ep_arrow_d ω κ L X b c y z) :
    Ep_arrow_d ω κ L X a c x z := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, _, _, inj⟩ := hc
  obtain ⟨m, n, q, f, g, hm, hn, hq, hnb, hqa, hf, hg, hfg⟩ := hxy
  have edge := hyz
  obtain ⟨n', l, r, _, _, _, hl, hr, hlc, hrb, _⟩ := hyz
  have en := hrb.1.domain_eq_l hZF.1 hnb
  subst n'
  obtain ⟨j, B', T', C', V', hb, hc, _, _, _, spec, any⟩ := ep_map_l hZFC h hF hco hn hl hr hlc inj hrb hbM hcM
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hb hB
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hc hC
  obtain ⟨g', hg', hgg'⟩ := any y z ((spec y z).mpr ⟨hy, hz, edge⟩) g hg
  obtain ⟨s, hs⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hr
  exact ⟨m, l, s, f, g', hm, hl, hs.1, hlc, Cp0_d.assoc_l hr hq hs hlc hrb hqa,
    hf, hg', ep_pull_comp_l (ZF.modelsKP hZF) hq hr hs hfg hgg'⟩

end YesMetaZFC.SetTheory.LargeCardinal
