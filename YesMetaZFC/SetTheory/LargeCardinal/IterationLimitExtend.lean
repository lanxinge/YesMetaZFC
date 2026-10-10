import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitDiagram

/-! # 极限处的迭代树扩张

新顶点的严格前驱恰是指定共尾树枝；旧模型、嵌入、扩展器操作与极限
条件逐项保留。当前长度是极限，故本次不添加扩展器或 pad 操作。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem it_tree_limit_l {ω c₀ α T Q G E B d N W P : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hl : M.IsLimitOrdinal α) (b : It_branch_d α T B)
    (cone : It_cone_d hZF ω B Q G d N W P) (source : It_source_d hZF ω d) :
    ∃ β U Q' G', M.SuccessorOf β α ∧ It_tree_d hZF ω c₀ β U Q' G' E ∧
      (∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)) ∧
      (∀ i c, Rd_entry_d i c Q' ↔ Rd_entry_d i c Q ∨ i = α ∧ c = d) ∧
      (∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f)) ∧
      ∀ i f, M.mem i α → (It_map_d G' i α f ↔ Rd_entry_d i f P) := by
  have h := tree.diagram
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  obtain ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs⟩ := it_limit_diagram_l hZF tree.omega h hl b cone
  have older i (hi : M.mem i β) : M.mem i α ∨ i = α := ((hβ i).mp hi).imp id (hZF.1.eq_of_same_members i α)
  have old i j (hj : M.mem j α) : Rd_entry_d i j U ↔ Rd_entry_d i j T := (us i j).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have qold i c (hi : M.mem i α) : Rd_entry_d i c Q' ↔ Rd_entry_d i c Q := (qs i c).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have gold i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have gtip i f (hi : M.mem i α) : It_map_d G' i α f ↔ Rd_entry_d i f P := (gs i α f).trans
    ⟨fun hh => hh.elim (fun hh => (no (h.order.bound i α (h.map_bound_l hZF hh)).2).elim)
      (fun hh => hh.2.elim (fun hh => (no (hh.1 ▸ hi)).elim) id), fun hh => Or.inr ⟨rfl, Or.inr hh⟩⟩
  have successor_old i j (hj : M.mem j β) (hs : M.SuccessorOf j i) : M.mem j α := by
    rcases older j hj with hj | rfl
    · exact hj
    · exact (it_successor_not_limit_l hZF.1 (h.order.ordinal.mem hs.predecessor_mem) hs hl).elim
  have domain i : (∃ p, Rd_entry_d i p E) ↔ ∃ j, M.mem j β ∧ M.SuccessorOf j i := (tree.move_domain i).trans
    ⟨fun ⟨j, hj, hs⟩ => ⟨j, (hβ j).mpr (Or.inl hj), hs⟩,
      fun ⟨j, hj, hs⟩ => ⟨j, successor_old i j hj hs, hs⟩⟩
  have steps i j (hj : M.mem j β) (hs : M.SuccessorOf j i) : It_step_d hZF ω U Q' G' E i j := by
    have hjα := successor_old i j hj hs
    obtain ⟨k, c, d, a, f, p, ⟨hkj, pred⟩, hc, hd, ha, hf, hp, valid⟩ := tree.steps i j hjα hs
    have hk := h.order.ordinal.transitive j hjα k hkj
    exact ⟨k, c, d, a, f, p, ⟨hkj, fun l => (old l j hjα).trans ((pred l).trans (or_congr Iff.rfl (old l k hk).symm))⟩,
      (qs i c).mpr (Or.inl hc), (qs k d).mpr (Or.inl hd), (qs j a).mpr (Or.inl ha),
      (gold k j f hjα).mpr hf, hp, valid⟩
  have limits δ (hδ : M.mem δ β) (limit : M.IsLimitOrdinal δ) : It_limit_d U Q' G' δ := by
    intro c X R hc hp y hy
    rcases older δ hδ with hδα | rfl
    · obtain ⟨i, hi, hiδ, f, hf, x, hxy⟩ := tree.limits δ hδα limit c X R ((qold δ c hδα).mp hc) hp y hy
      exact ⟨i, hi, (old i δ hδα).mpr hiδ, f, (gold i δ f hδα).mpr hf, x, hxy⟩
    · have eq : c = d := ((qs _ c).mp hc).elim
        (fun hh => (no ((h.model_domain _).mpr ⟨c, hh⟩)).elim) And.right
      subst c
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp cone.model.1
      obtain ⟨i, f, x, hf, hxy⟩ := cone.cover y hy
      have hiB := (cone.domain i).mpr ⟨f, hf⟩
      exact ⟨i, b.subset i hiB, (us i _).mpr (Or.inr ⟨rfl, Or.inr hiB⟩), f,
        (gtip i f (b.subset i hiB)).mpr hf, x, hxy⟩
  exact ⟨β, U, Q', G', hβ, ⟨tree.omega, diagram, fun z hz => (qs z c₀).mpr (Or.inl (tree.root z hz)),
    fun i c hc => ((qs i c).mp hc).elim (tree.sources i c) (fun hh => hh.2.symm ▸ source),
    tree.move_function, domain, steps, limits⟩, us, qs, gold, gtip⟩

end YesMetaZFC.SetTheory.LargeCardinal
