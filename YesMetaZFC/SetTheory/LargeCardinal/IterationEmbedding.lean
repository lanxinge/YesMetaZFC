import YesMetaZFC.SetTheory.LargeCardinal.IterationRealizer
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.ElementaryFactor
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Isomorphism

/-! # 共尾枝的完整初等因子与实际传递极限

相容初等嵌入列通过同一个带标号系统下降到直接极限。目标不要求由像覆盖。
目标是实际隶属结构时，先证明良基，再坍塌，并保留根嵌入的精确复合式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_embedding_factor_l {ω α T Q G B L A p H R q c C V d Y W P : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (inside : M.MemberSubset B α)
    (s : It_system_d B L Q G A p H R) (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V)
    (maps : It_embedding_d hZF ω B Q G d Y W P) :
    ∃ e, Smap_d I ω c d C Y e ∧ ∀ a i x f z y, KPair_d M a i x → Rd_entry_d i f P →
      Rd_entry_d a z q → Rd_entry_d x y f → Rd_entry_d z y e := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨r, hr, rs, comm⟩ := (maps.realizer_l hZF hω).map_l hZF h inside s
  have cone i b X S (stage : Di_stage_d I A p R i b X S) : ∃ f, Smap_d I ω b d X Y f ∧
      ∀ a y, Rd_entry_d a y f ↔ M.mem a X ∧ Rd_entry_d a y r := by
    obtain ⟨a, ha⟩ := stage.1.2.1
    have hi := (s.tags.projection.bound_l ((stage.2.1 a).mp ha).2).2
    obtain ⟨c₀, Z, U, hc, mz⟩ := h.model_l hZF (inside i hi)
    obtain ⟨g, hg⟩ := (maps.domain i).mp hi
    obtain ⟨t, _, ht, _, ts, _⟩ := it_tag_iso_l hZF hω s.tags hq stage hc mz
    obtain ⟨f, hf, fs⟩ := smap_comp_l I hZF ht (maps.elementary i g c₀ Z U hg hc mz)
    refine ⟨f, hf, fun a y => ⟨?_, ?_⟩⟩
    · intro hay
      obtain ⟨ha, x, hax, hxy⟩ := (fs a y).mp hay
      exact ⟨ha, (rs a y).mpr ⟨((stage.2.1 a).mp ha).1, i, x, g, ((ts a x).mp hax).2, hg, hxy⟩⟩
    · rintro ⟨ha, hay⟩
      obtain ⟨_, j, x, u, hp, hu, hxy⟩ := (rs a y).mp hay
      obtain ⟨x', hx'⟩ := s.tags.label_l (((stage.2.1 a).mp ha).2)
      obtain ⟨ej, ex⟩ := kpair_injective_l M hp hx'.1
      subst j x'
      exact (fs a y).mpr ⟨ha, x, (ts a x).mpr ⟨ha, hx'.1⟩, maps.function.2 i u g hu hg ▸ hxy⟩
  obtain ⟨e, he, law, _⟩ := di_factor_elementary_l hZF hω s.system limit elementary model maps.model hr comm cone
  exact ⟨e, he, fun a i x f z y hp hf hz hy => law a z y hz
    ((rs a y).mpr ⟨(limit.projection.bound_l hz).1, i, x, f, hp, hf, hy⟩)⟩

def It_return_at_d (ω z T Q G d Y π B : M.Domain) : Prop := ∃ L A p H R r c N V P σ,
  It_branch_d ω T B ∧ It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N V ∧
    Smem_d I c N V ∧ It_cone_d hZF ω B Q G c N V P ∧ It_source_d hZF ω c ∧
    Smap_d I ω c d N Y σ ∧ (∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f) ∧
    ∃ j, Rd_entry_d z j P ∧ It_comp_d j σ π

/-- 不指定分支的返回存在性。 -/
def It_return_d (ω z T Q G d Y π : M.Domain) : Prop := ∃ B, It_return_at_d hZF ω z T Q G d Y π B

/-- 任意长度的相容初等列都有实际传递极限，返回因子与每一条腿交换。 -/
theorem it_embedding_limit_l {ω α T Q G B z c₀ d Y W P : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (b : It_branch_d α T B)
    (hz : M.mem z B) (hc : Rd_entry_d z c₀ Q) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (maps : It_embedding_d hZF ω B Q G d Y W P) :
    ∃ L A p H R r c N V P' σ, It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N V ∧
      Smem_d I c N V ∧ It_cone_d hZF ω B Q G c N V P' ∧ It_source_d hZF ω c ∧
      Smap_d I ω c d N Y σ ∧ (∀ i f, Rd_entry_d i f P' ↔ M.mem i B ∧ It_project_d r i f) ∧
      ∀ i f j, Rd_entry_d i f P → Rd_entry_d i j P' → It_comp_d j σ f := by
  obtain ⟨X₀, V₀, K₀, mx, source⟩ := source
  have wf : Wf_rel_d Y W := fun Z _ ne => by
    obtain ⟨x, hx, least⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne
    exact ⟨x, hx, fun y hy hr => least y hy ((my.2 y x).mp hr).2.2⟩
  obtain ⟨L, A, p, H, R, q, c, C, V, _, s, elem, limit, model⟩ := it_branch_data_l hZF hω h b ⟨z, hz⟩
  have wfC := it_realizer_wf_l hZF h b.subset s limit (maps.realizer_l hZF hω) wf
  obtain ⟨e, N, S, P', v, r, cone, ready, mn, _, _, bij, hv, fr, rs, ps⟩ :=
    it_limit_model_l hZF h b.subset s elem limit model wfC hz hc mx source
  have next := di_limit_iso_l (ZF.modelsKP hZF) limit bij fr rs mn.1.2.2
    (fun _ _ _ _ hx hy => hv.relation_l I hZF hω model mn.1 hx hy)
  obtain ⟨σ, hs, law⟩ := it_embedding_factor_l hZF hω h b.subset s elem next mn.1 maps
  refine ⟨L, A, p, H, R, r, e, N, S, P', σ, s, next, mn, cone, ready, hs, ps, ?_⟩
  intro i π j root hj
  obtain ⟨a, X, U, ha, mdl⟩ := h.model_l hZF (b.subset i ((cone.domain i).mpr ⟨j, hj⟩))
  have pi := maps.elementary i π a X U root ha mdl
  have jj := cone.elementary i j a X U hj ha mdl
  have factor x v y (hxv : Rd_entry_d x v j) (hxy : Rd_entry_d x y π) : Rd_entry_d v y σ := by
    obtain ⟨a, hp, hav⟩ := (((ps i j).mp hj).2.2 x v).mp hxv
    exact law a i x π v y hp root hav hxy
  refine ⟨pi.1.1.1.1, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨v, _, hxv⟩ := jj.1.1.2.2 x (pi.1.1.input_mem_of_pairMember hxy)
    exact ⟨v, hxv, factor x v y hxv hxy⟩
  · rintro ⟨v, hxv, hvy⟩
    obtain ⟨u, _, hxu⟩ := pi.1.1.2.2 x (jj.1.1.input_mem_of_pairMember hxv)
    exact hs.1.1.1.2 v u y (factor x v u hxv hxu) hvy ▸ hxu

theorem it_embedding_return_l {ω T Q G B z c₀ d Y W P π : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω ω T Q G) (b : It_branch_d ω T B)
    (hz : M.mem z B) (hc : Rd_entry_d z c₀ Q) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (maps : It_embedding_d hZF ω B Q G d Y W P) (root : Rd_entry_d z π P) :
    It_return_d hZF ω z T Q G d Y π := by
  obtain ⟨L, A, p, H, R, r, c, N, V, P', σ, s, limit, mn, cone, ready, hs, ps, law⟩ :=
    it_embedding_limit_l hZF hω h b hz hc source my maps
  obtain ⟨j, hj⟩ := (cone.domain z).mp hz
  exact ⟨B, L, A, p, H, R, r, c, N, V, P', σ, b, s, limit, mn, cone, ready, hs, ps, j, hj, law z π j root hj⟩

end YesMetaZFC.SetTheory.LargeCardinal
