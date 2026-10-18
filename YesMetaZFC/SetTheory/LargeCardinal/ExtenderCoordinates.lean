import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFactor

/-! # 每个支撑序数都有真实的坐标代表

先在 Vδ 中构造坐标函数，再把单点支撑送入既有全系统。因此长度以下的
每个序数确实属于原因子之像，无须预设目标已经包含这些极限元素。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ee_coordinate_l (hZF : M.Models ZF) {ω δ X A Y B j κ k L n D a i α : M.Domain}
    (hω : M.IsOmega ω) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
    (hn : M.mem n ω) (hD : Ep_space_d κ n D) (haY : M.mem a Y) (ha : Fn0_d n L a)
    (hi : Rd_entry_d i α a) : ∃ f, M.mem f X ∧ Fn0_d D X f ∧ Ee_value_d j a f α := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.v_transitive_l I hZF hV
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hnκ := hc.ordinal.transitive ω hωκ n hn
  have hDX := ZF.v_function_space_mem_l I hZF hV hδ hc.source (hc.ordinal.transitive n hnκ)
    (fun s => (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 2) .newest (.bound 1) }
  have sat s x : φ.denote ρ s x ↔ Rd_entry_d i x s := rd_entry0_sat_l hZF.1 ..
  obtain ⟨f, hf, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := κ)
    (fun s hs => (((hD s).mp hs).2.1 i (ha.bound_l hi).1).imp fun x hx => (sat s x).mpr hx.2)
    (fun s hs x y hx hy => (fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hs)).1.2 i x y
      ((sat s x).mp hx) ((sat s y).mp hy))
    (fun s x hs hx => (((hD s).mp hs).bound_l ((sat s x).mp hx)).2)
  obtain ⟨Z, hZX, hDZ, hκZ⟩ := ZF.v_joint_bound_l I hZF hV hDX hc.source
  have hfX : M.mem f X := ZF.v_relation_mem_l I hZF hV hδ hZX (fun p hp => by
    obtain ⟨s, x, hpx⟩ := hf.1.1 p hp
    exact ⟨s, hDZ s (hf.input_mem_of_pairMember ⟨p, hpx, hp⟩), x,
      hκZ x (hf.output_mem_of_pairMember ⟨p, hpx, hp⟩), hpx⟩)
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  let ψ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (.iff (rd_entry0_m (.bound 1) .newest (.bound 3)) (rd_entry0_m (.bound 2) .newest (.bound 1))))
  have tr := spred_delta_l I hZF hω h ht hY ψ (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
    ⟨Fin.cases i (Fin.cases f (Fin.cases κ (fun _ => D))), fun _ => D⟩
    ⟨Fin.cases i (Fin.cases f' (Fin.cases k (fun _ => D'))), fun _ => D'⟩
    (Fin.cases (hc.fixed i (hc.ordinal.transitive n hnκ i (ha.bound_l hi).1))
      (Fin.cases hjf (Fin.cases hc.image (fun _ => hjD))))
  simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1] at tr
  have read := tr.mp (fun s hs x _ => (fs s x).trans
    ((and_congr_right fun _ => sat s x).trans ⟨And.right, fun hx => ⟨hs, hx⟩⟩))
  have haD := es_seed_l I hZF hω h ht hY (hc.fixed n hnκ) hc.image hjD hD hL haY ha
  exact ⟨f, hfX, (fn0_of_function_l (ZF.modelsKP hZF) hf).mono_target_l (ht κ hc.source),
    f', hjf, (read a haD α (hL α (ha.bound_l hi).2)).mpr hi⟩

theorem ee_ordinal_node_l (hZF : M.Models ZF) {ω δ X A Y B j κ k L S F R J O Z D p T V q C W α : M.Domain}
    (hω : M.IsOmega ω) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (hα : M.mem α L) : ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u α := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨one, ⟨zero, hz, hs⟩, h1ω⟩ := hω.exists_ordinalOne_mem
  obtain ⟨a, ha, as⟩ := ZF.exists_constantFunction hZF I (source := one) hα
  have singleton i (hi : M.mem i one) : i = zero := ((hs i).mp hi).elim
    (fun he => (hz i he).elim) (hZF.1.eq_of_same_members i zero)
  have haJ := (system.indices a).mpr ⟨one, h1ω, fn0_of_function_l (ZF.modelsKP hZF) ha,
    fun i r x hi hr => (singleton i (ha.input_mem_of_pairMember hi)).trans (singleton r (ha.input_mem_of_pairMember hr)).symm⟩
  obtain ⟨_, hZ⟩ := system.codes
  have models := system.components
  obtain ⟨c, _, hac⟩ := hZ.2.1 a haJ
  obtain ⟨n, H, U, G, r, E, Q, hn, han, hH, haU, hG, model⟩ := models a c hac
  have eq := han.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) ha)
  subst n
  obtain ⟨f, hfX, hf, value⟩ := ee_coordinate_l hZF hω hV hδ h hY hc hL hn hH
    (hSY a ((hS a).mpr ⟨one, hn, ha⟩)) han ((as zero α).mpr ⟨hs.predecessor_mem, rfl⟩)
  obtain ⟨E₀, hE₀, hfE⟩ := model.map.projection.2.2 f ((hG f).mpr ⟨hfX, hf⟩)
  have ultra := (es_measures_l hZF hω hV hδ h hY hc hL hS hSY hF).at_l hZF.1 haU han hH
  obtain ⟨u, hu⟩ := I.total a E₀
  have huD := (system.nodes u).mpr ⟨a, E₀, hu, c, E, Q, hac, model.code.1, hE₀⟩
  obtain ⟨E₁, hE₁, huE₁⟩ := limit.projection.2.1 u huD
  exact ⟨E₁, u, hE₁, huE₁, a, E₀, f, hu, model.map.representative_l I ultra.1.base_l hfE, value⟩

end YesMetaZFC.SetTheory.LargeCardinal
