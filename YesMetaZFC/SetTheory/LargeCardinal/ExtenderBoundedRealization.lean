import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedCollapse
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRaw
import YesMetaZFC.SetTheory.Collapse.RelationRealization

/-! # 所属源的有界坍塌直接识别原始商的低层

同一有界代表池一边取所属源中已构造的传递值，一边投影到原始关系超幂。
原常值像的传递性由初等性保证，故前驱覆盖完整；无需先坍塌整个施加超幂。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_collapse_d.raw_l {ω κ K K₀ L X R N R₀ F J O Z A p T S q c C W D₀ a₀ f₀ H B D Q Γ e : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (common : ∀ n D f, M.mem n ω → Ep_space_d κ n D → Fn0_d D B f → (M.mem f X ↔ M.mem f N))
    (hB : M.mem B X) (trans : M.TransitiveSet B) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀)
    (fv : Ep_repr_d q a₀ f₀ H) (owned : Eb_collapse_d ω κ L K₀ N B F D Q Γ e) :
    ∃ b i, Smem_d I b X R ∧ Smap_d I ω b c X C i ∧ Rd_entry_d B H i ∧
    ∃ k, M.IsSetInjectionFromTo I k Γ C ∧
      (∀ x E, Rd_entry_d x E k ↔ ∃ u, M.mem u D ∧ Rd_entry_d u x e ∧ Eb_value_d q u E) ∧
      (∀ E, Rd_entry_d E H W ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x E k) ∧
      (∀ x y E P, Rd_entry_d x E k → Rd_entry_d y P k → (M.mem x y ↔ Rd_entry_d E P W)) ∧
      ∀ x E, Rd_entry_d x E k → ∀ P, Rd_entry_d P E W ↔ ∃ y, M.mem y x ∧ Rd_entry_d y P k := by
  obtain ⟨J₀, P, G, U, V, pool, indices, _, _, _, _, range, membership, _, edges, map, exact⟩ := owned
  have eq := hZF.1.eq_of_same_members J₀ J (fun a => (indices a).trans (system.indices a).symm)
  subst J₀
  obtain ⟨v, vf, values, reads, covers⟩ := pool.raw_l hZF source owner common hB family system limit
    ff constant fv range membership edges
  obtain ⟨b, i, mx, hi, constants, ext⟩ := ep_constant_l hZF source family system limit model
    (system.toEp_graph_d.elementary_l hZFC source family coherent)
  obtain ⟨H', hH', hBH⟩ := hi.1.1.2.2 B hB
  obtain ⟨u, a', B', f', D', _, sf, fc, hfB, pair, huH⟩ := constants B H' hBH
  have eq := ep_repr_constant_l hZF source family system limit (sf.function_l source.transitive) ff
    fc constant ⟨u, B', pair, hfB, huH⟩ fv
  subst H'
  let ρ : Env (smdl_structure_l I (R := R) mx.1.2.1) 1 := ⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩
  let η : Env (smdl_structure_l I (R := W) model.2.1) 1 := ⟨fun _ => ⟨H, hH'⟩, fun _ => ⟨H, hH'⟩⟩
  have truth : Formula.satisfies ρ (Formula.isTransitive .newest) :=
    (smem_delta_image_l I mx source.transitive (Formula.isTransitive_delta0 _) ρ).mpr
      ((Formula.satisfies_isTransitive_iff ..).mpr trans)
  have moved := (smap_source_l I hZF source.omega mx.1 model hi (Formula.isTransitive .newest)
    (by simp -implicitDefEqProofs) ρ η (fun _ => hBH)).mp truth
  have down E P (hEH : Rd_entry_d E H W) (hPE : Rd_entry_d P E W) : Rd_entry_d P H W :=
    (Formula.satisfies_isTransitive_iff ..).mp moved
      ⟨E, (limit.bounded E H hEH).1⟩ hEH ⟨P, (limit.bounded P E hPE).1⟩ hPE
  obtain ⟨k, fk, spec, member, predecessor⟩ := map.realize_l hZF exact vf ext reads (fun u E huE P hPE =>
    (covers P).mpr (down E P ((covers E).mp ⟨u, (vf.bound_l huE).1, huE⟩) hPE))
  refine ⟨b, i, mx, hi, hBH, k, fk, fun x E => (spec x E).trans ?_, fun E => ?_, member, predecessor⟩
  · exact exists_congr fun u => and_congr_right fun hu => and_congr_right fun _ =>
      (values u E).trans ⟨And.right, fun value => ⟨hu, value⟩⟩
  · refine (covers E).symm.trans ⟨?_, ?_⟩
    · rintro ⟨u, hu, huE⟩
      obtain ⟨x, hx, hux⟩ := map.function.2.1 u hu
      exact ⟨x, hx, (spec x E).mpr ⟨u, hu, hux, huE⟩⟩
    · rintro ⟨x, _, hxE⟩
      obtain ⟨u, hu, _, huE⟩ := (spec x E).mp hxE
      exact ⟨u, hu, huE⟩

end YesMetaZFC.SetTheory.LargeCardinal
