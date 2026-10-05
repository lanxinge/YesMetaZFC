import YesMetaZFC.SetTheory.LargeCardinal.IterationProjection

/-! # 良基树枝极限的传递模型与整列嵌入

规范投影与 Mostowski 图复合，实际产生新模型及每条枝嵌入。
源理论、有限序列空间及 ω 的保持从任一枝结点传递，不重新假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_limit_cone_l {ω α T Q G B L A p H R q c C V d N W e : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (inside : M.MemberSubset B α)
    (s : It_system_d B L Q G A p H R) (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V) (target : Smdl_d I d N W)
    (he : Smap_d I ω c d C N e) (onto : ∀ y, M.mem y N → ∃ z, M.mem z C ∧ Rd_entry_d z y e) :
    ∃ P r, It_cone_d hZF ω B Q G d N W P ∧ Fn0_d A N r ∧
      (∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ z, Rd_entry_d a z q ∧ Rd_entry_d z y e) ∧
      ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f := by
  obtain ⟨r, hr, rs⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) limit.projection) he.1.1
  have leg i (hi : M.mem i B) : ∃ f, It_project_d r i f := by
    obtain ⟨b, X, S, hb, mx⟩ := h.model_l hZF (inside i hi)
    obtain ⟨f, _, hf⟩ := it_project_elementary_l hZF hω h s elementary limit model he rs hi hb mx
    exact ⟨f, hf⟩
  obtain ⟨P, pf, pd, ps⟩ := it_projects_l hZF leg
  have typed i f b X S (hf : Rd_entry_d i f P) (hb : Rd_entry_d i b Q) (mx : Smdl_d I b X S) :
      Smap_d I ω b d X N f := by
    obtain ⟨j, hj, js⟩ := it_project_elementary_l hZF hω h s elementary limit model he rs ((ps i f).mp hf).1 hb mx
    exact js.unique_l hZF.1 ((ps i f).mp hf).2 ▸ hj
  have commute i j f u v (hf : It_map_d G i j f) (hu : Rd_entry_d i u P) (hv : Rd_entry_d j v P)
      x y z (hxy : Rd_entry_d x y f) (hyz : Rd_entry_d y z v) : Rd_entry_d x z u := by
    obtain ⟨b, hb, hbr⟩ := (((ps j v).mp hv).2.2 y z).mp hyz
    obtain ⟨hbA, t, hbt, htz⟩ := (rs b z).mp hbr
    obtain ⟨c₀, X, S, hc, mx⟩ := h.model_l hZF (inside i ((ps i u).mp hu).1)
    obtain ⟨d₀, Y, W₀, hd, my⟩ := h.model_l hZF (inside j ((ps j v).mp hv).1)
    have ff := h.elementary i j f c₀ X S d₀ Y W₀ hf hc hd mx my
    obtain ⟨a, ha⟩ := (I).total i x
    have haA := (s.tags.nodes a).mpr ⟨i, x, ((ps i u).mp hu).1, ha,
      c₀, X, S, hc, mx.1, ff.1.1.input_mem_of_pairMember hxy⟩
    have hab := (s.arrows a b i j x y ha hb).mpr ⟨haA, hbA, f, hf, hxy⟩
    obtain ⟨t', _, hat⟩ := limit.projection.2.1 a haA
    have eq := limit.commute_l s.system hab hat hbt
    exact (((ps i u).mp hu).2.2 x z).mpr ⟨a, ha, (rs a z).mpr ⟨haA, t, eq ▸ hat, htz⟩⟩
  have cover y (hy : M.mem y N) : ∃ i f x, Rd_entry_d i f P ∧ Rd_entry_d x y f := by
    obtain ⟨z, hz, hzy⟩ := onto y hy
    obtain ⟨a, haz⟩ := (limit.range z).mp hz
    obtain ⟨i, x, hi, hp, _⟩ := (s.tags.nodes a).mp (limit.projection.bound_l haz).1
    obtain ⟨f, hf⟩ := (pd i).mp hi
    exact ⟨i, f, x, hf, (((ps i f).mp hf).2.2 x y).mpr
      ⟨a, hp, (rs a y).mpr ⟨(limit.projection.bound_l haz).1, z, haz, hzy⟩⟩⟩
  exact ⟨P, r, ⟨target, pf, pd, typed, commute, cover⟩, fn0_of_function_l (ZF.modelsKP hZF) hr, rs, ps⟩

theorem it_limit_model_l {ω α T Q G B L A p H R q c C V i b X S K : M.Domain}
    (h : It_diagram_d hZF ω α T Q G) (inside : M.MemberSubset B α)
    (s : It_system_d B L Q G A p H R) (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V) (wf : Wf_rel_d C V)
    (hi : M.mem i B) (hb : Rd_entry_d i b Q) (mx : Smem_d I b X S) (source : Ep_source_d hZF ω ω K X S) :
    ∃ d N W P e r, It_cone_d hZF ω B Q G d N W P ∧ It_source_d hZF ω d ∧
      Smem_d I d N W ∧ M.TransitiveSet N ∧ Wc_graph_d C V e ∧ M.IsSetBijectionFromTo I e C N ∧
      Smap_d I ω c d C N e ∧ Fn0_d A N r ∧
      (∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ z, Rd_entry_d a z q ∧ Rd_entry_d z y e) ∧
      ∀ k f, Rd_entry_d k f P ↔ M.mem k B ∧ It_project_d r k f := by
  obtain ⟨j, hj, _⟩ := it_stage_limit_l hZF source.omega h s elementary limit model hi hb mx.1
  have ext : Wc_ext_d X S := fun x hx y hy same => hZF.1.eq_of_same_members x y fun z =>
    ⟨fun hz => ((mx.2 z y).mp ((same z (source.transitive x hx z hz)).mp
      ((mx.2 z x).mpr ⟨source.transitive x hx z hz, hx, hz⟩))).2.2,
     fun hz => ((mx.2 z x).mp ((same z (source.transitive y hy z hz)).mpr
      ((mx.2 z y).mpr ⟨source.transitive y hy z hz, hy, hz⟩))).2.2⟩
  obtain ⟨N, e, _, d, W, ht, wc, bij, target, elem, _, _, _⟩ :=
    wc_smaps_l hZF source.omega model wf (hj.extensional_l hZF source.omega mx.1 model ext)
  obtain ⟨P, r, cone, hr, rs, ps⟩ := it_limit_cone_l hZF source.omega h inside s elementary limit model target.1 elem bij.2
  obtain ⟨f, hf⟩ := (cone.domain i).mp hi
  have ff := cone.elementary i f b X S hf hb mx.1
  have hωN := ff.1.1.output_mem_of_pairMember (ff.omega_l I hZF source.omega source.transitive ht mx target source.omega_mem)
  obtain ⟨K', next⟩ := source.successor_l hZF mx target ht ff hωN (fun _ hx => hx)
  exact ⟨d, N, W, P, e, r, cone, ⟨N, W, K', target, next⟩, target, ht, wc, bij, elem, hr, rs, ps⟩

end YesMetaZFC.SetTheory.LargeCardinal
