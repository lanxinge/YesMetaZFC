import YesMetaZFC.Model.SetTheory.Internal.SourceTheory
import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

/-! # 严格相对秩段的集合代数与层级闭包

所有见证先由所属源构造，再用原递归历史给出精确的成员界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem Sc_algebra_d.rank_l {Z α V : M.Domain} (h : Sc_algebra_d Z) (hZ : M.TransitiveSet Z)
    (hV : M.mem V Z) (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α) : Sc_algebra_d V := by
  have vz := hZ V hV
  refine ⟨fun a b ha hb => ?_, fun a ha => ?_, fun a b ha hb => ?_, fun A B R hA hB hR total => ?_, fun R B hR hB => ?_⟩
  · obtain ⟨p, hp, eq⟩ := h.pair a b (vz a ha) (vz b hb)
    exact ⟨p, hv.pair_mem_l hZF hZ hV hα ha hb hp eq, eq⟩
  · obtain ⟨p, hp, eq⟩ := h.union a (vz a ha)
    exact ⟨p, hv.union_mem_l hZF hZ hV ha hp eq, eq⟩
  · obtain ⟨p, hp, eq⟩ := h.product a b (vz a ha) (vz b hb)
    exact ⟨p, hv.relation_mem_l hZF hZ hV hα ha hb hp (fun x hx => (eq x).mp hx), eq⟩
  · obtain ⟨f, hf, fn, sub⟩ := h.choice A B R (vz A hA) (vz B hB) (vz R hR) total
    exact ⟨f, hv.subset_mem_l hZ hV hR hf sub, fn, sub⟩
  · obtain ⟨T, hT, eq⟩ := h.fibers R B (vz R hR) (vz B hB)
    obtain ⟨U, hU, ru⟩ := h.union R (vz R hR)
    have huV := hv.union_mem_l hZF hZ hV hR hU ru
    obtain ⟨W, hW, uw⟩ := h.union U hU
    have hwV := hv.union_mem_l hZF hZ hV huV hW uw
    refine ⟨T, hv.subsets_mem_l hZ hV hα hwV hT (fun A hA x hx => ?_), eq⟩
    obtain ⟨b, _, fiber⟩ := (eq A).mp hA
    obtain ⟨p, hp, hpr⟩ := (fiber x).mp hx
    obtain ⟨t, ht, hxt⟩ := (kpair_union_l M hp x).mpr (Or.inl rfl)
    exact (uw x).mpr ⟨t, (ru t).mpr ⟨p, hpr, ht⟩, hxt⟩

/-- 较早层及其整张历史同时进入严格极限秩段。 -/
theorem Sc_hierarchy_d.rank_l {Z α V : M.Domain} (h : Sc_hierarchy_d Z) (hZ : M.TransitiveSet Z)
    (hV : M.mem V Z) (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α) : Sc_hierarchy_d V := by
  intro β hβ ho
  obtain ⟨W, hW, hw⟩ := h β (hZ V hV β hβ) ho
  exact ⟨W, hv.rank_l hZF hZ hV hα hβ hW hw⟩

end YesMetaZFC.SetTheory.Internal
