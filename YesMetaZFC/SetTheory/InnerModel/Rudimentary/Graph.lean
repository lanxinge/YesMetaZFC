import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Bounded

/-! # 十三项运算的统一 Δ₀ 图

有界表示与原成员规格双向等价，故后续收集与递归直接消费同一套运算。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rd_graph_m {n} : Rd_sym → Term n → Term n → Term n → Term n → Formula 1 n
  | .pair, x, y, _, w => pair0_m w x y
  | .diff, x, y, _, w => .conj (Formula.subset w x)
      (Formula.forallMem x (.iff (.mem .newest w.weaken) (.neg (.mem .newest y.weaken))))
  | .prod, x, y, _, w => ri_image_m .prod x y w
  | .mid, x, y, _, w => ri_image_m .mid x y w
  | .last, x, y, _, w => ri_image_m .last x y w
  | .union, x, _, _, w => .conj (Formula.forallMem x (Formula.subset .newest w.weaken))
      (Formula.forallMem w (Formula.existsMem x.weaken (.mem (.bound 1) .newest)))
  | .range, x, y, _, w => ri_image_m .range x y w
  | .mem, x, y, _, w => ri_image_m .mem x y w
  | .fibers, x, y, _, w => ri_image_m .fibers x y w
  | .opair, x, y, _, w => kpair0_m w x y
  | .triple, x, y, z, w => rd_triple0_m w x y z
  | .adj, x, y, z, w => Formula.existsMem w (.conj (kpair0_m .newest y.weaken z.weaken)
      (pair0_m w.weaken x.weaken .newest))
  | .fiber, x, y, _, w => rd_fiber0_m x y w

@[simp] theorem rd_graph_closed_l {n} (k : Rd_sym) (x y z w : Term n)
    (hx : x.freeSupport = []) (hy : y.freeSupport = []) (hz : z.freeSupport = []) (hw : w.freeSupport = []) :
    (rd_graph_m k x y z w).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [rd_graph_m, Definitional.Formula.FreeClosed, hx, hy, hz, hw]

theorem rd_graph_delta_l {n} (k : Rd_sym) (x y z w : Term n) : (rd_graph_m k x y z w).IsDelta0 := by
  cases k
  · exact pair0_delta_l ..
  · exact .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.neg (.mem _ _))))
  · exact ri_image_delta_l ..
  · exact ri_image_delta_l ..
  · exact ri_image_delta_l ..
  · exact .conj (.forallMem _ (.atom _ _ _)) (.forallMem _ (.existsMem _ (.mem _ _)))
  · exact ri_image_delta_l ..
  · exact ri_image_delta_l ..
  · exact ri_image_delta_l ..
  · exact kpair0_delta_l ..
  · exact rd_triple0_delta_l ..
  · exact .existsMem _ (.conj (kpair0_delta_l ..) (pair0_delta_l ..))
  · exact rd_fiber0_delta_l ..

theorem rd_graph_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Rd_sym) (x y z w : Term n) :
    Formula.satisfies ρ (rd_graph_m k x y z w) ↔ Rd_fun_d k (x.eval ρ) (y.eval ρ) (z.eval ρ) (w.eval ρ) := by
  let I := kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)
  have image (k : Ri_sym) := (ri_image_sat_l hKP ρ k x y w).trans
    (ri_image_value_l k (x.eval ρ) (y.eval ρ) (z.eval ρ) (w.eval ρ))
  cases k with
  | pair => exact pair0_sat_l hKP.1 ρ w x y
  | prod => exact image .prod
  | mid => exact image .mid
  | last => exact image .last
  | range => exact image .range
  | mem => exact image .mem
  | fibers => exact image .fibers
  | fiber => exact rd_fiber0_sat_l hKP.1 ρ x y w
  | diff =>
    simp only [rd_graph_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_neg_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact ⟨fun ⟨h, g⟩ t => ⟨fun ht => ⟨h t ht, (g t (h t ht)).mp ht⟩,
      fun ⟨ht, hn⟩ => (g t ht).mpr hn⟩, fun h => ⟨fun t ht => ((h t).mp ht).1,
      fun t ht => ⟨fun hw => ((h t).mp hw).2, fun hn => (h t).mpr ⟨ht, hn⟩⟩⟩⟩
  | union =>
    simp only [rd_graph_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, Formula.satisfies_mem_iff,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact ⟨fun ⟨h, g⟩ t => ⟨g t, fun ⟨a, ha, ht⟩ => h a ha t ht⟩,
      fun h => ⟨fun a ha t ht => (h t).mpr ⟨a, ha, ht⟩, fun t => (h t).mp⟩⟩
  | opair =>
    rw [rd_graph_m, kpair0_sat_l hKP.1]
    refine ⟨rd_opair_value_l hKP.1, fun h => ?_⟩
    obtain ⟨p, hp⟩ := I.total (x.eval ρ) (y.eval ρ)
    exact (rd_fun_unique_l hKP.1 (rd_opair_value_l hKP.1 hp) h) ▸ hp
  | triple =>
    rw [rd_graph_m, rd_triple0_sat_l hKP.1]
    refine ⟨rd_triple_value_l hKP.1, fun h => ?_⟩
    obtain ⟨q, hq⟩ := I.total (y.eval ρ) (z.eval ρ)
    obtain ⟨p, hp⟩ := I.total (x.eval ρ) q
    have hv := rd_triple_value_l hKP.1 (show Rd_triple_d p (x.eval ρ) (y.eval ρ) (z.eval ρ) from ⟨q, hq, hp⟩)
    exact (rd_fun_unique_l hKP.1 hv h) ▸ ⟨q, hq, hp⟩
  | adj =>
    simp only [rd_graph_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hKP.1, pair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    refine ⟨fun ⟨q, _, hq, hp⟩ => rd_adj_value_l hKP.1 hq hp, fun h => ?_⟩
    obtain ⟨q, hq⟩ := I.total (y.eval ρ) (z.eval ρ)
    obtain ⟨p, hp⟩ := KP.exists_pair hKP (x.eval ρ) q
    have he := rd_fun_unique_l hKP.1 (rd_adj_value_l hKP.1 hq hp) h
    exact ⟨q, he ▸ (hp q).mpr (Or.inr rfl), hq, he ▸ hp⟩

end YesMetaZFC.SetTheory.InnerModel
