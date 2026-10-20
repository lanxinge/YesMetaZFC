import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceWellFounded
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBranchBound
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFormulaSystem

/-! # 内部所属扩展器保持实际后继的枝反射

在同一商和同一极限投影上观察原无枝标签公式。其任意下降链具有源内
标签包络，故有界代表回收与所属模型的共同纤维产生原无枝关系的下降链。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.branch_l {ω κ K X R K' Y R' L F P J O Z A p T S q c C W d N V j : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y R')
    (hDC : Dc_d I ω) (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hP : M.mem P Y) (owner_power : FilterZF.Source_d Y K' P)
    (loc : It_local_d ω Y κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S)
    (hN : M.TransitiveSet N) (hωN : M.mem ω N) (algebra : Sc_algebra_d N)
    (target : Smem_d I d N V) (hj : Smap_d I ω c d C N j)
    (onto : ∀ y, M.mem y N → ∃ x, Rd_entry_d x y j) : Sc_branch_d ω N := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory owner.finite hP owner_power)).transfer_l reverse
  have local_copy := loc
  obtain ⟨_, _, hL, hF, _⟩ := local_copy
  obtain ⟨b, code⟩ := source.code
  obtain ⟨Q, U, Z', S', e, W', _, _, qs, us, observed, observed_limit, _, rel⟩ :=
    ep_formula_system_l hZF source code family system limit model elementary target.1 hj sb_bad_m sb_bad_closed_l
  have sourceRel u v (hu : M.mem u X) (hv : M.mem v X) : Rd_entry_d u v Q ↔ Sb_bad_d ω X u v :=
    (qs ⟨u, hu⟩ ⟨v, hv⟩).trans (sb_bad_sat_l hZF source.omega source.transitive source.omega_mem code _)
  have targetRel u v (hu : M.mem u N) (hv : M.mem v N) : Rd_entry_d u v U ↔ Sb_bad_d ω N u v :=
    (us ⟨u, hu⟩ ⟨v, hv⟩).trans (sb_bad_sat_l hZF source.omega hN hωN target _)
  have wfX := sb_bad_wf_l hZF hDC branches sourceRel
  have wf : Wf_rel_d C W' := by
    apply wf_of_no_desc_l hZF hDC
    intro g fg dg
    obtain ⟨B, hB, bounded⟩ := ep_bad_desc_bound_l hZF source cover family system limit model elementary hN target hj
      (fun E H x y hx hy => (rel E H x y hx hy).trans
        (targetRel x y (hj.1.1.output_mem_of_pairMember hx) (hj.1.1.output_mem_of_pairMember hy))) fg dg
    obtain ⟨R₀, hR₀, _, read⟩ := sc_sb_relation_l hZF source.omega source.transitive source.omega_mem code source.theory hB
    have restriction x y (hx : M.mem x B) (hy : M.mem y B) : Rd_entry_d x y R₀ ↔ Rd_entry_d x y Q :=
      ((read x y).trans ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩).trans
        (sourceRel x y (source.transitive B hB x hx) (source.transitive B hB y hy)).symm
    obtain ⟨P₀, G, D, V₀, Q₀, s, pool, hV₀, _, _, edges, hs, fs, ds⟩ := ep_bounded_desc_l hZF hDC source branches power family
      (inside L hL) (inside F hF) hB hR₀ restriction observed observed_limit fg dg bounded
    obtain ⟨v, fv, dv⟩ := loc.realize_desc_l hZF source owner inside agree owner_branches hP owner_power hB hR₀ observed.indices pool hV₀ hs fs
      (fun i j u v hij hiu hjv => ((edges v u).mp (ds i j u v hij hiu hjv)).2.2)
    have wfB : Wf_rel_d B R₀ := by
      intro H sub ne
      obtain ⟨x, hx, minimal⟩ := wfX H (fun x hx => source.transitive B hB x (sub x hx)) ne
      exact ⟨x, hx, fun y hy hyx => minimal y hy ((restriction y x (sub y hy) (sub x hx)).mp hyx)⟩
    exact wf_no_desc_l hZF source.omega wfB fv dv
  have wfN := (wf_quotient_l hZF (fn0_of_function_l (ZF.modelsKP hZF) hj.1.1) onto
    (fun x y u v hx hy => (rel x y u v hx hy).symm)).mpr wf
  exact sb_bad_branch_l hZF source.omega hN algebra wfN targetRel

end YesMetaZFC.SetTheory.LargeCardinal
