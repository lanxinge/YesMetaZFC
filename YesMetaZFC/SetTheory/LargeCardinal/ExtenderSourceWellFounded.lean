import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceDescent
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceJointFiber
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderConstraintDescent

/-! # 所属模型内部短扩展器的实际施加良基性

外部下降链先在施加源中统一有界并回收为代表下降列；源内共同约束层再
送回所属模型。其内部共同纤维条件给出背景成员下降列，与基础公理矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一内部扩展器把源内代表下降图实现为原有界关系的下降图。 -/
theorem It_local_d.realize_desc_l {ω κ K X R K' Y R' L F V B R₀ J P₀ G D V₀ s : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y R')
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hV : M.mem V Y) (owner_power : FilterZF.Source_d Y K' V)
    (loc : It_local_d ω Y κ L F) (hB : M.mem B X) (hR₀ : M.mem R₀ X)
    (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) (pool : Eb_pool_d ω κ L X B J K P₀ G D) (hV₀ : M.mem V₀ X)
    (hs : M.mem s X) (fs : Fn0_d ω D s)
    (links : ∀ i j u v, M.SuccessorOf j i → Rd_entry_d i u s → Rd_entry_d j v s → Eb_link_d ω κ L B J K V₀ R₀ F G v u) :
    ∃ v, Fn0_d ω B v ∧ Wf_desc_d R₀ v := by
  have family := loc.measures_l hZF owner hV owner_power
  have local_copy := loc
  obtain ⟨_, _, hL, hF, _⟩ := local_copy
  obtain ⟨P, N, H, hP, hN, hH, fn, fh, large, constraints⟩ := eb_source_constraints_l hZF source (inside L hL) hB
    pool.indices pool.functions hV₀ hR₀ (inside F hF) pool.carrier hs fs family.function links
  obtain ⟨J', _, seq⟩ := source.sequences.space L (inside L hL)
  have supports : Fn0_d ω J' N := fn.retarget_l (fun i a hia => by
    obtain ⟨n, hn, ha, _⟩ := (indices a).mp (fn.bound_l hia).2
    exact (seq a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩)
  obtain ⟨e, h, _, _, fe, fh', _, realize⟩ := es_source_joint_fiber_l hZF source owner inside agree owner_branches loc
    hV owner_power hP hN hH seq supports fh large
  exact eb_desc_realize_l hZF source.omega pool fs fn fh fe fh' realize constraints

theorem It_local_d.source_wf_l {ω κ K X R K' Y R' L F V J O Z A p T S q c C W : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y R')
    (hDC : Dc_d I ω) (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hV : M.mem V Y) (owner_power : FilterZF.Source_d Y K' V)
    (loc : It_local_d ω Y κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S) : Wf_rel_d C W := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner hV owner_power).transfer_l reverse
  have local_copy := loc
  obtain ⟨_, _, hL, hF, _⟩ := local_copy
  apply wf_of_no_desc_l hZF hDC
  intro g fg dg
  obtain ⟨B, R₀, P₀, G, D, V₀, Q, s, hB, hR₀, membership, pool, hV₀, _, _, edges, hs, fs, ds⟩ :=
    ep_source_desc_l hZF hDC source branches cover power family (inside L hL) (inside F hF) system limit model elementary fg dg
  obtain ⟨v, fv, dv⟩ := loc.realize_desc_l hZF source owner inside agree owner_branches hV owner_power hB hR₀ system.indices pool hV₀ hs fs
    (fun i j u v hij hiu hjv => ((edges v u).mp (ds i j u v hij hiu hjv)).2.2)
  have wf : Wf_rel_d B R₀ := by
    intro A _ hn
    obtain ⟨a, ha, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) hn
    exact ⟨a, ha, fun b hb hba => minimal b hb ((membership b a).mp hba).2.2⟩
  exact wf_no_desc_l hZF source.omega wf fv dv

end YesMetaZFC.SetTheory.LargeCardinal
