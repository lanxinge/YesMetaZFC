import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceLimit
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource

/-! # 标签关系下降链的统一源内代表界

首项代表的值域放入源内标签包络。这个包络的有界规格沿常值嵌入及坍塌
传递到目标，使整条标签下降链落在同一个常值像中，再回到原代表上规范化。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_bad_desc_bound_l {ω κ K L X R F J O Z A p T S q c C W d Y V j W' g : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (cover : Sc_cover_d X) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S)
    (hY : M.TransitiveSet Y) (target : Smem_d I d Y V) (hj : Smap_d I ω c d C Y j)
    (relation : ∀ E H x y, Rd_entry_d E x j → Rd_entry_d H y j → (Rd_entry_d E H W' ↔ Sb_bad_d ω Y x y))
    (fn : Fn0_d ω C g) (desc : Wf_desc_d W' g) : ∃ B, M.mem B X ∧
      ∀ i E, Rd_entry_d i E g → ∃ n a D f, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧
        Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D B f ∧ Ep_repr_d q a f E := by
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨E₀, he₀, hzE⟩ := fn.2.1 z hzω
  obtain ⟨n, a, D, f, hn, haJ, ha, hD, hfX, hf, fv⟩ := ep_repr_surjective_l hZF family system limit he₀
  obtain ⟨P, hP, coords⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hfX
  obtain ⟨T₀, B, hT₀, hB, sub, hull⟩ := sc_sb_hull_l (ZF.modelsKP hZF) (source.algebra_l (ZF.modelsKP hZF)) cover hP
  obtain ⟨_, models⟩ := system.codes
  obtain ⟨o, _, hao⟩ := models.2.1 a haJ
  obtain ⟨b, k, m, D', U, G, r, C₀, V₀, code, hk, _, ha', hd', haU, functions, component, constants⟩ :=
    ep_constant_limit_l hZF source family system limit model elementary hao
  have en := ha'.domain_eq_l hZF.1 ha
  subst m
  have ed := hZF.1.eq_of_same_members D' D (fun s => (hd' s).trans (hD s).symm)
  subst D'
  have ultra := family.at_l hZF.1 haU ha hD
  obtain ⟨H, hH, hBH⟩ := hk.1.1.2.2 B hB
  obtain ⟨_, t, Q, u, htG, tc, htQ, hu, huH⟩ := (constants B H).mp hBH
  have tv : Ep_repr_d q a t H := ⟨u, Q, hu, component.map.representative_l I ultra.base htQ, huH⟩
  have ht := ((functions t).mp htG).2
  have initial : Rd_entry_d E₀ H W := (ep_repr_atoms_l hZF family system limit haU fv tv).2.mpr
    ⟨D, ultra.base.top, fun s hs => by
      obtain ⟨x, hx, hsx⟩ := hf.2.1 s hs
      exact ⟨x, hx, B, hB, hsx, tc s hs, (code.2 x B).mpr ⟨hx, hB, sub x (coords s x hsx).2⟩⟩⟩
  obtain ⟨σ, hσ, compose⟩ := smap_comp_l I hZF hk hj
  obtain ⟨T₁, hT₁, hTT⟩ := hσ.1.1.2.2 T₀ hT₀
  obtain ⟨H', hH', hHH⟩ := hj.1.1.2.2 H hH
  have hBH' := (compose B H').mpr ⟨hB, H, hBH, hHH⟩
  let ρ : Env (smdl_structure_l I (R := R) code.1.2.1) 2 :=
    ⟨Fin.cases ⟨B, hB⟩ (fun _ => ⟨T₀, hT₀⟩), fun _ => ⟨B, hB⟩⟩
  let η : Env (smdl_structure_l I (R := V) target.1.2.1) 2 :=
    ⟨Fin.cases ⟨H', hH'⟩ (fun _ => ⟨T₁, hT₁⟩), fun _ => ⟨H', hH'⟩⟩
  have hs : Formula.satisfies ρ (sb_hull_m (.bound 1) .newest) :=
    (smem_delta_image_l I code source.transitive (sb_hull_delta_l ..) ρ).mpr ((sb_hull_sat_l hZF.1 ..).mpr hull)
  have image := (smap_source_l I hZF source.omega code.1 target.1 hσ (sb_hull_m (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ η (Fin.cases hBH' (fun _ => hTT))).mp hs
  have hull' : Sb_hull_d T₁ H' := (sb_hull_sat_l hZF.1 ..).mp
    ((smem_delta_image_l I target hY (sb_hull_delta_l ..) η).mp image)
  have closed x y (hx : M.mem x C) (hy : M.mem y C) (hxy : Rd_entry_d x y W') (hyH : Rd_entry_d y H W) : Rd_entry_d x H W := by
    obtain ⟨x', hx', hxx⟩ := hj.1.1.2.2 x hx
    obtain ⟨y', hy', hyy⟩ := hj.1.1.2.2 y hy
    have hyH' := ((target.2 y' H').mp ((hj.relation_l I hZF source.omega model target.1 hyy hHH).mp hyH)).2.2
    obtain ⟨A₀, R₀, _, _, edge, _⟩ := (relation x y x' y' hxx hyy).mp hxy
    exact (hj.relation_l I hZF source.omega model target.1 hxx hHH).mpr
      ((target.2 x' H').mpr ⟨hx', hH', hull'.closed_l hZF.1 hyH' edge⟩)
  have all := wf_desc_invariant_l hZF source.omega fn desc hz hzE initial closed
  exact ⟨B, hB, fun i E hiE => ep_repr_bounded_l hZF source family system limit hn ha hD ht tc tv hB (all i E hiE)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 内部所属扩展器保持实际后继的枝反射

在同一商和同一极限投影上观察原无枝标签公式。其任意下降链具有源内
标签包络，故有界代表回收与所属模型的共同纤维产生原无枝关系的下降链。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.branch_l {ω κ K X R K' Y R' L F P J O Z A p T S q c C W d N V j : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y R')
    (hDC : Dc_d I ω) (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hP : M.mem P Y) (owner_power : FilterZF.Source_d Y K' P)
    (loc : It_local_d I ω Y R' κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S)
    (hN : M.TransitiveSet N) (hωN : M.mem ω N) (algebra : Sc_algebra_d N)
    (target : Smem_d I d N V) (hj : Smap_d I ω c d C N j)
    (onto : ∀ y, M.mem y N → ∃ x, Rd_entry_d x y j) : Sc_branch_d ω N := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP owner_power)).transfer_l reverse
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

/-! ## 内部所属扩展器的完整实际后继节点

同一次定向极限和坍塌同时给出实际超幂边及全部下一步不变量：源理论、
枝反射、相对层级、相对幂集、传递包络和小 Skolem 壳闭包。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.node_l {ω κ K X R K' Y R' L F P : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y R')
    (branches : Sc_branch_d ω X) (hierarchy : Sc_hierarchy_d X) (power : Sc_power_d X) (cover : Sc_cover_d X)
    (small : Sh_source_d (ZF.modelsKP hZF) ω X) (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hP : M.mem P Y) (owner_power : FilterZF.Source_d Y K' P)
    (loc : It_local_d I ω Y R' κ L F) : ∃ N S b d j K₀,
      Ep_successor_d hZF ω κ L X R F N S ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d j ∧
      Smem_d I b X R ∧ Smem_d I d N S ∧ Smap_d I ω b d X N j ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K₀ N S ∧
      Sc_branch_d ω N ∧ Sc_hierarchy_d N ∧ Sc_power_d N ∧ Sc_cover_d N ∧ Sh_source_d (ZF.modelsKP hZF) ω N := by
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, system, limit, model, _, elementary, collapse⟩ :=
    loc.limit_l hZFC source owner branches cover power inside agree owner_branches hP owner_power
  obtain ⟨_, b, i, N, e, _, d, S, j, hm, hi, constants, ht, wc, bij, hn, he, _, _, _, hj, js, K₀, target⟩ := collapse
  have next : Ep_successor_d hZF ω κ L X R F N S := ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e,
    system, limit, model, hn, ht, wc, bij, he⟩
  have ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d j := ⟨X, R, N, S, J, O, Z, A, p, T, V, q, c, C, W, i, e,
    hm, hn, system, limit, model, wc, bij, he, hi, constants, hj, hj.1.1.1.1,
    fun x y => (js x y).trans ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  exact ⟨N, S, b, d, j, K₀, next, ultra, hm, hn, hj, target,
    loc.branch_l hZF source owner (ZFC.dc_l I hZFC source.omega) branches cover power inside agree owner_branches hP owner_power
      system limit model elementary ht target.omega_mem (target.algebra_l (ZF.modelsKP hZF)) hn he (fun y hy => (bij.2 y hy).imp fun _ h => h.2),
    (sc_hierarchy_iff_l hZF source.omega source.transitive ht hm hn hj).mp hierarchy,
    (sc_power_iff_l hZF source.omega source.transitive ht hm hn hj).mp power,
    (sc_cover_iff_l hZF source.omega source.transitive ht hm hn hj).mp cover,
    (sh_source_iff_l hZF source target hm hn hj).mp small⟩

end YesMetaZFC.SetTheory.LargeCardinal
