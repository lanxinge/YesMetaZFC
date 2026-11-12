import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.LargeCardinal.Extender.WellFounded
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SuccessorApplication
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 共同纤维保持超幂后继的枝反射

把全部相对无枝关系合并为一个可定义的带标签关系。源中的枝反射保证它
良基；同一扩展器系统的共同纤维把良基性传到目标，再读回目标的枝反射。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_branch_reflection_l (hZF : M.Models ZF)
    {ω κ K L X R F J O Z A p T S q c C W b Y V d j : M.Domain}
    (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (branches : Sc_branch_d ω X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) b X R)
    (family : Em_family_d ω κ L F) (coherent : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (complete : ∀ H f, Ef_levels_d ω κ H → Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f → ∃ g, Ef_fiber_d ω κ H g)
    (hωL : M.MemberSubset ω L) (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C W)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S)
    (hY : M.TransitiveSet Y) (hωY : M.mem ω Y) (algebra : Sc_algebra_d Y)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y V)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d C Y j)
    (onto : ∀ y, M.mem y Y → ∃ x, Rd_entry_d x y j) : Sc_branch_d ω Y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, U, Z', S', e, W', _, _, qs, us, system, lim, _, rel⟩ :=
    ep_formula_system_l hZF source hm (family.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) h limit model elementary hn.1 hj sb_bad_m sb_bad_closed_l
  have sourceRel u v (hu : M.mem u X) (hv : M.mem v X) : Rd_entry_d u v Q ↔ Sb_bad_d ω X u v :=
    (qs ⟨u, hu⟩ ⟨v, hv⟩).trans (sb_bad_sat_l hZF source.omega source.transitive source.omega_mem hm _)
  have targetRel u v (hu : M.mem u Y) (hv : M.mem v Y) : Rd_entry_d u v U ↔ Sb_bad_d ω Y u v :=
    (us ⟨u, hu⟩ ⟨v, hv⟩).trans (sb_bad_sat_l hZF source.omega hY hωY hn _)
  have wf := ep_limit_wf_l hZF source.omega hDC hωL family coherent complete system lim
    (sb_bad_wf_l hZF hDC branches sourceRel)
  have wfY := (wf_quotient_l hZF (fn0_of_function_l (ZF.modelsKP hZF) hj.1.1) onto
    (fun x y u v hx hy => (rel x y u v hx hy).symm)).mpr wf
  exact sb_bad_branch_l hZF source.omega hY algebra wfY targetRel

/-- 已有的实际后继证书直接取得枝反射；源数据、常值嵌入和共尾纤维均实际读取。 -/
theorem Ep_successor_d.branch_l (hZFC : M.Models ZFC) {ω κ K L X R F N S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R) (branches : Sc_branch_d ω X)
    (family : Em_family_d ω κ L F)
    (coherent : Es_coherent_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (complete : ∀ H f, Ef_levels_d ω κ H →
      Es_fiber_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L F H f → ∃ g, Ef_fiber_d ω κ H g)
    (hωL : M.MemberSubset ω L) (next : Ep_successor_d (ZFC.models_zf_l hZFC) ω κ L X R F N S) : Sc_branch_d ω N := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e, h, limit, model, target, ht, _, bij, he⟩ := next
  obtain ⟨B, hB⟩ := model.2.1
  obtain ⟨u, hu⟩ := (limit.range B).mp hB
  obtain ⟨a, ha, _⟩ := h.projection.2.1 u (limit.projection.bound_l hu).1
  obtain ⟨_, hz⟩ := h.codes
  obtain ⟨o, _, hao⟩ := hz.2.1 a ha
  have fs := family.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X
  have cs := coherent.source_l I X
  obtain ⟨b, i, _, _, _, _, _, _, _, hm, hi, _⟩ := ep_constant_limit_l hZF source fs h limit model
    (h.toEp_graph_d.elementary_l hZF source fs cs) hao
  obtain ⟨j, hj, _⟩ := smap_comp_l I hZF hi he
  have hωN := hj.1.1.output_mem_of_pairMember (hj.omega_l I hZF source.omega source.transitive ht hm target source.omega_mem)
  have algebra := (sc_algebra_iff_l I hZF source.omega source.transitive ht hm target hj).mp (source.algebra_l (ZF.modelsKP hZF))
  exact ep_branch_reflection_l hZF (ZFC.dc_l I hZFC source.omega) source branches hm family coherent complete hωL
    h limit model (h.toEp_graph_d.elementary_l hZF source fs cs) ht hωN algebra target he
    (fun y hy => (bij.2 y hy).imp fun _ h => h.2)

/-- 实际短扩展器自动生成带完整下一步不变量的同一个超幂节点。 -/
theorem Ex_short_d.node_l (hZFC : M.Models ZFC) {ω κ K L X R F : M.Domain}
    (ex : Ex_short_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (branches : Sc_branch_d ω X) (hierarchy : Sc_hierarchy_d X) (power : Sc_power_d X) (cover : Sc_cover_d X)
    (small : Sh_source_d (ZF.modelsKP (ZFC.models_zf_l hZFC)) ω X) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ N S b d j K', Ep_successor_d (ZFC.models_zf_l hZFC) ω κ L X R F N S ∧
      Smem_d I b X R ∧ Smem_d I d N S ∧ Smap_d I ω b d X N j ∧
      Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω ω K' N S ∧ Sc_branch_d ω N ∧
      Sc_hierarchy_d N ∧ Sc_power_d N ∧ Sc_cover_d N ∧ Sh_source_d (ZF.modelsKP (ZFC.models_zf_l hZFC)) ω N := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, h, limit, model, _, _, collapse⟩ := ex.limit_l hZFC source
  obtain ⟨_, b, i, N, e, _, d, S, j, hm, _, _, ht, wc, bij, hn, he, _, _, _, hj, _, K', target⟩ := collapse
  have next : Ep_successor_d hZF ω κ L X R F N S := ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e, h, limit, model, hn, ht, wc, bij, he⟩
  have hωL : M.MemberSubset ω L := fun x hx => ex.length.transitive κ ex.above x (ex.critical.1.transitive ω ex.uncountable x hx)
  exact ⟨N, S, b, d, j, K', next, hm, hn, hj, target,
    next.branch_l hZFC source branches ex.measures ex.coherent ex.countable hωL,
    (sc_hierarchy_iff_l hZF source.omega source.transitive ht hm hn hj).mp hierarchy,
    (sc_power_iff_l hZF source.omega source.transitive ht hm hn hj).mp power,
    (sc_cover_iff_l hZF source.omega source.transitive ht hm hn hj).mp cover,
    (sh_source_iff_l hZF source target hm hn hj).mp small⟩

end YesMetaZFC.SetTheory.LargeCardinal
