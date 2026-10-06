import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRepresentative
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 任意超幂下降链的统一源内值域界

首项代表的值域有一个源内传递包络 B。常值像 j(B) 在未塌缩极限中仍然
传递，因而包含整条下降链；每一项再由共同支撑改成 B 值的源内代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_desc_bound_l {ω κ K L X R F J O Z A p T S q c C W g : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (cover : Sc_cover_d X) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S)
    (fn : Fn0_d ω C g) (desc : Wf_desc_d W g) : ∃ B, M.mem B X ∧ M.TransitiveSet B ∧
      ∀ i E, Rd_entry_d i E g → ∃ n a D f, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧
        Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D B f ∧ Ep_repr_d q a f E := by
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨E₀, he₀, hzE⟩ := fn.2.1 z hzω
  obtain ⟨n, a, D, f, hn, haJ, ha, hD, hfX, hf, fv⟩ := ep_repr_surjective_l hZF family system limit he₀
  obtain ⟨P, hP, coords⟩ := source.theory.algebra.envelope_l hfX
  obtain ⟨B, hB, bt, sub⟩ := cover P hP
  obtain ⟨_, models, _⟩ := system.models
  obtain ⟨o, _, hao⟩ := models.2.1 a haJ
  obtain ⟨b, j, m, D', U, G, r, Y, V, code, hj, _, ha', hd', haU, functions, component, constants⟩ :=
    ep_constant_limit_l hZF source family system limit model elementary hao
  have en := ha'.domain_eq_l hZF.1 ha
  subst m
  have ed := hZF.1.eq_of_same_members D' D (fun s => (hd' s).trans (hD s).symm)
  subst D'
  have ultra := family.at_l hZF.1 haU ha hD
  obtain ⟨H, hH, hBH⟩ := hj.1.1.2.2 B hB
  obtain ⟨_, t, Q, u, htG, tc, htQ, hu, huH⟩ := (constants B H).mp hBH
  have tv : Ep_repr_d q a t H := ⟨u, Q, hu, component.map.representative_l I ultra.base htQ, huH⟩
  have ht := ((functions t).mp htG).2
  have initial : Rd_entry_d E₀ H W := (ep_repr_atoms_l hZF family system limit haU fv tv).2.mpr
    ⟨D, ultra.base.top, fun s hs => by
      obtain ⟨x, hx, hsx⟩ := hf.2.1 s hs
      exact ⟨x, hx, B, hB, hsx, tc s hs, (code.2 x B).mpr ⟨hx, hB, sub x (coords s x hsx).2⟩⟩⟩
  -- 原公式的初等性在商结构自身中给出传递性，不预设商已良基或已塌缩。
  let ρ : Env (smdl_structure_l I (R := R) code.1.2.1) 1 := ⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩
  let η : Env (smdl_structure_l I (R := W) model.2.1) 1 := ⟨fun _ => ⟨H, hH⟩, fun _ => ⟨H, hH⟩⟩
  have hs : Formula.satisfies ρ (Formula.isTransitive .newest) :=
    (smem_delta_image_l I code source.transitive (.forallMem _ (.forallMem _ (.mem ..))) ρ).mpr
      ((Formula.satisfies_isTransitive_iff ..).mpr bt)
  have image := (smap_source_l I hZF source.omega code.1 model hj (Formula.isTransitive .newest)
    (by simp -implicitDefEqProofs) ρ η (fun _ => hBH)).mp hs
  have trans := (Formula.satisfies_isTransitive_iff η .newest).mp image
  have closed x y (hx : M.mem x C) (hy : M.mem y C) (hxy : Rd_entry_d x y W) (hyH : Rd_entry_d y H W) :
      Rd_entry_d x H W := trans ⟨y, hy⟩ hyH ⟨x, hx⟩ hxy
  have all := wf_desc_invariant_l hZF source.omega fn desc hz hzE initial closed
  exact ⟨B, hB, bt, fun i E hiE => ep_repr_bounded_l hZF source family system limit hn ha hD ht tc tv hB
    (all i E hiE)⟩

end YesMetaZFC.SetTheory.LargeCardinal
