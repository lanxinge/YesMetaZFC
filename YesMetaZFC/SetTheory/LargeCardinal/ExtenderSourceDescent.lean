import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedDescent
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedGraph
import YesMetaZFC.Model.SetTheory.Internal.SourceBranch
import YesMetaZFC.SetTheory.CountableChoice

/-! # 超幂外部下降链的源内回收

统一值域界后，下降链可提升到源内的有界代表关系。该关系逐对读取原极限，
因此已有枝反射给出源中实际存在的下降代表图，供内部共同纤维条件使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_bounded_desc_l {ω κ K L X R₀ R F J O Z A p T S q C W g B R' : M.Domain}
    (hDC : Dc_d I ω) (source : Ep_source_d hZF ω κ K X R₀)
    (branches : Sc_branch_d ω X) (power : Sc_power_d X) (family : Em_source_d ω κ L X F)
    (hL : M.mem L X) (hF : M.mem F X) (hB : M.mem B X) (hR : M.mem R' X)
    (relation : ∀ x y, M.mem x B → M.mem y B → (Rd_entry_d x y R' ↔ Rd_entry_d x y R))
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (fn : Fn0_d ω C g) (desc : Wf_desc_d W g)
    (bounded : ∀ i E, Rd_entry_d i E g → ∃ n a D f, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧
      Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D B f ∧ Ep_repr_d q a f E) : ∃ P G D V Q s,
      Eb_pool_d ω κ L X B J K P G D ∧ M.mem V X ∧ M.mem Q X ∧ M.IsRangeOf I V F ∧
      (∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K V R' F G u v) ∧
      M.mem s X ∧ Fn0_d ω D s ∧ Wf_desc_d Q s := by
  obtain ⟨P, G, D, V, Q, e, pool, hV, hQ, range, _, _, _, edges, quotient, covers⟩ :=
    eb_graph_l hZF source power family system limit hL hF hB hR relation
  let ρ : Env M 3 := ⟨Fin.cases C (Fin.cases g (fun _ => e)), fun _ => C⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (.conj (rd_entry0_m (.bound 2) .newest (.bound 4)) (rd_entry0_m (.bound 1) .newest (.bound 5))) }
  have sat i u : φ.denote ρ i u ↔ ∃ E, M.mem E C ∧ Rd_entry_d i E g ∧ Rd_entry_d u E e := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨f, hf, select⟩ := dc_uniformize_formula_l hZF φ ρ source.omega hDC (X := D) (fun i hi => by
    obtain ⟨E, he, hiE⟩ := fn.2.1 i hi
    obtain ⟨n, a, Y, f, hn, ha, hna, space, hfx, hfn, value⟩ := bounded i E hiE
    obtain ⟨u, hu, hue⟩ := covers n a Y f E hn ha hna space hfx hfn value
    exact ⟨u, hu, (sat i u).mpr ⟨E, he, hiE, hue⟩⟩)
  have decreasing : Wf_desc_d Q f := by
    intro i j u v hij hiu hjv
    obtain ⟨E, _, hiE, hue⟩ := (sat i u).mp (select i u hiu)
    obtain ⟨H, _, hjH, hvh⟩ := (sat j v).mp (select j v hjv)
    exact (quotient v u H E hvh hue).mpr (desc i j E H hij hiE hjH)
  obtain ⟨s, hs, sf, sd⟩ := branches D Q pool.carrier hQ ⟨f, hf, decreasing⟩
  exact ⟨P, G, D, V, Q, s, pool, hV, hQ, range, edges, hs, sf, sd⟩

theorem ep_source_desc_l {ω κ K L X R F J O Z A p T S q c C W g : M.Domain}
    (hDC : Dc_d I ω) (source : Ep_source_d hZF ω κ K X R)
    (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (family : Em_source_d ω κ L X F) (hL : M.mem L X) (hF : M.mem F X)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S)
    (fn : Fn0_d ω C g) (desc : Wf_desc_d W g) : ∃ B R' P G D V Q s,
      M.mem B X ∧ M.mem R' X ∧ (∀ x y, Rd_entry_d x y R' ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y) ∧
      Eb_pool_d ω κ L X B J K P G D ∧ M.mem V X ∧ M.mem Q X ∧ M.IsRangeOf I V F ∧
      (∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K V R' F G u v) ∧
      M.mem s X ∧ Fn0_d ω D s ∧ Wf_desc_d Q s := by
  obtain ⟨B, hB, _, bounded⟩ := ep_desc_bound_l hZF source cover family system limit model elementary fn desc
  obtain ⟨b, code⟩ := source.code
  let membership : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨R', hR, _, rel⟩ := sc_relation_source_l hZF source.omega source.transitive code source.theory membership (.mem ..)
    ⟨Fin.elim0, fun _ => B⟩ (fun i => Fin.elim0 i) hB hB
  have read x y : Rd_entry_d x y R' ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  have relation x y (hx : M.mem x B) (hy : M.mem y B) : Rd_entry_d x y R' ↔ Rd_entry_d x y R :=
    ⟨fun h => (code.2 x y).mpr ⟨source.transitive B hB x hx, source.transitive B hB y hy, ((read x y).mp h).2.2⟩,
      fun h => (read x y).mpr ⟨hx, hy, ((code.2 x y).mp h).2.2⟩⟩
  obtain ⟨P, G, D, V, Q, s, data⟩ := ep_bounded_desc_l hZF hDC source branches power family hL hF hB hR relation system limit fn desc bounded
  exact ⟨B, R', P, G, D, V, Q, s, hB, hR, read, data⟩

end YesMetaZFC.SetTheory.LargeCardinal
