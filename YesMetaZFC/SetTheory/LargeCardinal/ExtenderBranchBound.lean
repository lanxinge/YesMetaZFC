import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedDescent
import YesMetaZFC.Model.SetTheory.Internal.SourceBranchBound

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
    (source : Ep_source_d hZF ω κ K X R) (cover : Sc_cover_d X) (family : Em_source_d ω κ L X F)
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
  obtain ⟨P, hP, coords⟩ := source.theory.algebra.envelope_l hfX
  obtain ⟨T₀, B, hT₀, hB, sub, hull⟩ := sc_sb_hull_l (ZF.modelsKP hZF) source.theory.algebra cover hP
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
