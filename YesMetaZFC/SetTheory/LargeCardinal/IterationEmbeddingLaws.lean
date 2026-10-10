import YesMetaZFC.SetTheory.LargeCardinal.IterationProjection

/-! # 实际复合图的结合律及相容返回列的复合式 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem It_comp_d.assoc_l {f g h p q r : M.Domain}
    (hp : It_comp_d f g p) (hq : It_comp_d g h q) (hr : It_comp_d f q r) : It_comp_d p h r := by
  refine ⟨hr.1, fun x z => ⟨?_, ?_⟩⟩
  · intro hxz
    obtain ⟨y, hxy, hyz⟩ := (hr.2 x z).mp hxz
    obtain ⟨v, hyv, hvz⟩ := (hq.2 y z).mp hyz
    exact ⟨v, (hp.2 x v).mpr ⟨y, hxy, hyv⟩, hvz⟩
  · rintro ⟨v, hxv, hvz⟩
    obtain ⟨y, hxy, hyv⟩ := (hp.2 x v).mp hxv
    exact (hr.2 x z).mpr ⟨y, hxy, (hq.2 y z).mpr ⟨v, hyv, hvz⟩⟩

theorem It_embedding_d.comp_l (hZF : M.Models ZF) {ω α T Q G B a A S P i j f u v : M.Domain}
    (diagram : It_diagram_d hZF ω α T Q G) (inside : M.MemberSubset B α)
    (maps : It_embedding_d hZF ω B Q G a A S P)
    (hf : It_map_d G i j f) (hu : Rd_entry_d i u P) (hv : Rd_entry_d j v P) : It_comp_d f v u := by
  obtain ⟨c, X, R, hc, mx⟩ := diagram.model_l hZF (inside i ((maps.domain i).mpr ⟨u, hu⟩))
  obtain ⟨d, Y, W, hd, my⟩ := diagram.model_l hZF (inside j ((maps.domain j).mpr ⟨v, hv⟩))
  have ff := (diagram.elementary i j f c X R d Y W hf hc hd mx my).1.1
  have uu := (maps.elementary i u c X R hu hc mx).1.1
  have vv := (maps.elementary j v d Y W hv hd my).1.1
  refine ⟨uu.1.1, fun x z => ⟨?_, fun ⟨y, hxy, hyz⟩ => maps.commute i j f u v hf hu hv x y z hxy hyz⟩⟩
  intro hxz
  obtain ⟨y, hy, hxy⟩ := ff.2.2 x (uu.input_mem_of_pairMember hxz)
  obtain ⟨z', _, hyz⟩ := vv.2.2 y hy
  have eq := uu.1.2 x z' z (maps.commute i j f u v hf hu hv x y z' hxy hyz) hxz
  exact ⟨y, hxy, eq ▸ hyz⟩

end YesMetaZFC.SetTheory.LargeCardinal
