import YesMetaZFC.SetTheory.LargeCardinal.ExtenderElementary
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceFormula
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.RelationChange

/-! # 同一个扩展器极限中的可定义关系

改换观察的原二元公式，源函数、商类、标签、过渡图和极限投影全部保留。
逐分量的 Łoś 方程把新关系识别为原公式的解释，供共同纤维证明良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_formula_system_l {ω κ K L X R F J O Z A p T S q c C W b Y V d j : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hm : Smem_d I b X R)
    (family : Em_source_d ω κ L X F) (h : Ep_system_d hZF ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) (model : Smdl_d I c C W)
    (elementary : Di_elementary_d I ω O A p T S) (hY : M.TransitiveSet Y) (hn : Smem_d I d Y V)
    (hj : Smap_d I ω c d C Y j) (φ : Formula 1 2) (hc : φ.FreeClosed) :
    ∃ Q U Z' S' e W', M.IsSetRelationOn I Q X ∧ M.IsSetRelationOn I U Y ∧
      (∀ x y : (smdl_structure_l I (R := R) hm.1.2.1).Domain, Rd_entry_d x.val y.val Q ↔
        Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.1.2.1) x y) φ) ∧
      (∀ x y : (smdl_structure_l I (R := V) hn.1.2.1).Domain, Rd_entry_d x.val y.val U ↔
        Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := V) hn.1.2.1) x y) φ) ∧
      Ep_system_d hZF ω κ L X Q F J O Z' A p T S' ∧ Di_limit_d A p T S' q C W' ∧ Smdl_d I e C W' ∧
      ∀ E H x y, Rd_entry_d E x j → Rd_entry_d H y j → (Rd_entry_d E H W' ↔ Rd_entry_d x y U) := by
  obtain ⟨Q, hQ, qs⟩ := smem_formula_relation_l hZF hm source.transitive φ hc
  obtain ⟨U, hU, us⟩ := smem_formula_relation_l hZF hn hY φ hc
  obtain ⟨e, W', newModel, jr⟩ := smdl_pull_l hZF model.2.1 hj.1.1 U
  obtain ⟨S', diagram, newLimit, sr⟩ := di_relation_change_l hZF h.diagram limit newModel
  obtain ⟨Q₀, hz, models⟩ := h.models
  obtain ⟨Z', Q₁, hz', models'⟩ := ep_components_l hZF source family
    (fun a ha => ((h.indices a).mp ha).elim fun n hn => ⟨n, hn.1, hn.2.1⟩) Q
  -- 同一代表族产生同一类集合；仅分量的关系码随公式改变。
  have carrier a B : Ep_at_d Z a B ↔ Ep_at_d Z' a B := by
    have move {Z₀ Z₁ Q₀ Q₁ R₀ R₁ : M.Domain} (hz₀ : Fn0_d J Q₀ Z₀) (hz₁ : Fn0_d J Q₁ Z₁)
        (m₀ : ∀ a c, Rd_entry_d a c Z₀ → Ep_component_d I ω κ L X R₀ F a c)
        (m₁ : ∀ a c, Rd_entry_d a c Z₁ → Ep_component_d I ω κ L X R₁ F a c)
        (ha : Ep_at_d Z₀ a B) : Ep_at_d Z₁ a B := by
      obtain ⟨c, C₀, R₀', hac, hca, hB⟩ := ha
      obtain ⟨d, _, had⟩ := hz₁.2.1 a (hz₀.bound_l hac).1
      obtain ⟨_, _, _, _, _, D, S₀, S₁, _, _, _, _, _, old, new⟩ :=
        ep_component_pair_l I hZF.1 family (m₀ a c hac) (m₁ a d had)
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hca old.code.1
      exact ⟨d, C₀, S₁, had, new.code.1, hB⟩
    exact ⟨move hz hz' models models', move hz' hz models' models⟩
  have nodes u : M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z' a B := by
    refine (h.nodes u).trans (exists_congr fun a => exists_congr fun B => ?_)
    exact and_congr Iff.rfl (carrier a B)
  have relation u v a B D (hu : KPair_d M u a B) (hv : KPair_d M v a D)
      (huA : M.mem u A) (hvA : M.mem v A) : Rd_entry_d u v S' ↔ Ep_rel_d Z' a B D := by
    have hua := (h.index u a B hu).mpr huA
    have hva := (h.index v a D hv).mpr hvA
    obtain ⟨c₀, _, hac⟩ := hz.2.1 a (h.projection.bound_l hua).2
    obtain ⟨c₁, _, had⟩ := hz'.2.1 a (h.projection.bound_l hua).2
    obtain ⟨n, E₀, M₀, G, r, D₀, R₀, R₁, hnω, ha, he₀, haM, hG, old, new⟩ :=
      ep_component_pair_l I hZF.1 family (models a c₀ hac) (models' a c₁ had)
    have hB := (ep_at_read_l hz hac old.code.1).mp (h.toEp_graph_d.at_l huA hu)
    have hD := (ep_at_read_l hz hac old.code.1).mp (h.toEp_graph_d.at_l hvA hv)
    obtain ⟨E, _, huE⟩ := limit.projection.2.1 u huA
    obtain ⟨H, _, hvH⟩ := limit.projection.2.1 v hvA
    obtain ⟨x, _, hEx⟩ := hj.1.1.2.2 E (limit.projection.bound_l huE).2
    obtain ⟨y, _, hHy⟩ := hj.1.1.2.2 H (limit.projection.bound_l hvH).2
    obtain ⟨k, hk, ks⟩ := ep_stage_embedding_l hZF source.omega h limit elementary model hac old.code
    obtain ⟨l, hl, ls⟩ := smap_comp_l I hZF hk hj
    have hBx := (ls B x).mpr ⟨hB, E, (ks B E).mpr ⟨hB, u, hu, huE⟩, hEx⟩
    have hDy := (ls D y).mpr ⟨hD, H, (ks D H).mpr ⟨hD, v, hv, hvH⟩, hHy⟩
    obtain ⟨f, hf⟩ := (old.map.range B).mp hB
    obtain ⟨g, hg⟩ := (old.map.range D).mp hD
    have los := rs_formula_relation_l hZF source.omega source.transitive hm source.theory
      (source.uniform_l hZF hnω he₀) (source.space_mem_l hZF hnω he₀)
      (family.at_l hZF.1 haM ha he₀) hG old hf hg φ hc qs
    have elem := smap_source_l I hZF source.omega old.code hn.1 hl φ hc
      (sr_pair_env_l (N := smdl_structure_l I (R := R₀) old.code.2.1) ⟨B, hB⟩ ⟨D, hD⟩)
      (sr_pair_env_l (N := smdl_structure_l I (R := V) hn.1.2.1)
        ⟨x, hj.1.1.output_mem_of_pairMember hEx⟩ ⟨y, hj.1.1.output_mem_of_pairMember hHy⟩)
      (Fin.cases hDy (fun _ => hBx))
    have eq := (new.relation f g B D hf hg).trans (los.symm.trans (elem.trans
      (us ⟨x, hj.1.1.output_mem_of_pairMember hEx⟩ ⟨y, hj.1.1.output_mem_of_pairMember hHy⟩).symm))
    exact (sr u v a E H hua hva huE hvH).trans ((jr E H x y hEx hHy).trans
      (eq.symm.trans (ep_rel_read_l hz' had new.code.1).symm))
  have graph : Ep_graph_d hZF ω κ L X Q F J O Z' A p T S' := {
    order := h.order, order_spec := h.order_spec, projection := h.projection, indices := h.indices
    models := ⟨Q₁, hz', models'⟩, nodes := nodes, index := h.index, arrows := h.arrows
    relations := fun u v => ⟨fun huv => by
      obtain ⟨a, hua, hva⟩ := diagram.locality u v huv
      obtain ⟨B, hu, _⟩ := h.toEp_graph_d.label_l hua
      obtain ⟨D, hv, _⟩ := h.toEp_graph_d.label_l hva
      exact ⟨(h.projection.bound_l hua).1, (h.projection.bound_l hva).1, a, B, D, hu, hv,
        (relation u v a B D hu hv (h.projection.bound_l hua).1 (h.projection.bound_l hva).1).mp huv⟩,
      fun ⟨huA, hvA, a, B, D, hu, hv, hr⟩ => (relation u v a B D hu hv huA hvA).mpr hr⟩ }
  exact ⟨Q, U, Z', S', e, W', hQ, hU, qs, us, ⟨graph, diagram, h.representatives⟩, newLimit, newModel, jr⟩

end YesMetaZFC.SetTheory.LargeCardinal
