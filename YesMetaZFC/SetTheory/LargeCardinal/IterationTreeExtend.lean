import YesMetaZFC.SetTheory.LargeCardinal.IterationTree

/-! # 有效后继步自动扩张整棵迭代树

一次调用实际添加树序、模型、所有祖先嵌入和操作记录。已有后继步及
极限条件均由精确旧图方程保留；新步的施加证书与新边绑定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_tree_extend_l {ω c₀ α ξ T Q G E k c d b X R Y S j p : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smdl_d I d X R) (my : Smdl_d I b Y S)
    (hj : Smap_d I ω d b X Y j) (source : It_source_d hZF ω b)
    (step : ((∀ x, ¬ M.mem x p) ∧ k = ξ ∧ b = c ∧ ∀ x y, Rd_entry_d x y j → x = y) ∨ It_active_d hZF ω c d b j p) :
    ∃ β U Q' G' E', M.SuccessorOf β α ∧ It_tree_d hZF ω c₀ β U Q' G' E' ∧
      (∀ i l, Rd_entry_d i l U ↔ Rd_entry_d i l T ∨ l = α ∧ (i = α ∨ Rd_entry_d i k T)) ∧
      (∀ i a, Rd_entry_d i a Q' ↔ Rd_entry_d i a Q ∨ i = α ∧ a = b) ∧
      (∀ i l f, M.mem l α → (It_map_d G' i l f ↔ It_map_d G i l f)) ∧
      (∀ i a, Rd_entry_d i a E' ↔ Rd_entry_d i a E ∨ i = ξ ∧ a = p) ∧ It_map_d G' k α j := by
  have order := tree.diagram.order
  have no : ¬ M.mem α α := fun ha => order.ordinal.wellOrder.linear.irrefl α ha ha
  have hk := (tree.diagram.model_domain k).mpr ⟨d, hd⟩
  obtain ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs, edge⟩ :=
    it_diagram_extend_l hZF tree.omega tree.diagram hα hd mx my hj
  have fresh a (ha : Rd_entry_d ξ a E) : False := by
    obtain ⟨η, hη, hηξ⟩ := (tree.move_domain ξ).mp ⟨a, ha⟩
    exact no (Structure.SuccessorOf.eq hZF.1 hηξ hα ▸ hη)
  obtain ⟨E', ef, es⟩ := it_move_push_l (ZF.modelsKP hZF) tree.move_function fresh (p := p)
  have old i l (hl : M.mem l α) : Rd_entry_d i l U ↔ Rd_entry_d i l T :=
    (us i l).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hl)).elim), Or.inl⟩
  have qold i a (hi : M.mem i α) : Rd_entry_d i a Q' ↔ Rd_entry_d i a Q :=
    (qs i a).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have gold i l f (hl : M.mem l α) : It_map_d G' i l f ↔ It_map_d G i l f :=
    (gs i l f).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hl)).elim), Or.inl⟩
  have older η (hη : M.mem η β) : M.mem η α ∨ η = α :=
    ((hβ η).mp hη).imp_right (hZF.1.eq_of_same_members η α)
  have predecessor : It_pred_d U k α := ⟨hk, fun i => (us i α).trans
    ⟨fun hh => hh.elim (fun hh => (no (order.bound i α hh).2).elim)
        (fun hh => hh.2.imp_right ((old i k hk).mpr)),
      fun hh => Or.inr ⟨rfl, hh.imp_right ((old i k hk).mp)⟩⟩⟩
  have domain i : (∃ a, Rd_entry_d i a E') ↔ ∃ η, M.mem η β ∧ M.SuccessorOf η i := by
    constructor
    · rintro ⟨a, ha⟩
      rcases (es i a).mp ha with ha | ⟨rfl, _⟩
      · obtain ⟨η, hη, hηi⟩ := (tree.move_domain i).mp ⟨a, ha⟩
        exact ⟨η, (hβ η).mpr (Or.inl hη), hηi⟩
      · exact ⟨α, hβ.predecessor_mem, hα⟩
    · rintro ⟨η, hη, hηi⟩
      rcases older η hη with hη | rfl
      · obtain ⟨a, ha⟩ := (tree.move_domain i).mpr ⟨η, hη, hηi⟩
        exact ⟨a, (es i a).mpr (Or.inl ha)⟩
      · have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (order.ordinal.mem hηi.predecessor_mem) hηi hα
        exact ⟨p, (es i p).mpr (Or.inr ⟨eq, rfl⟩)⟩
  have steps i η (hη : M.mem η β) (hηi : M.SuccessorOf η i) : It_step_d hZF ω U Q' G' E' i η := by
    rcases older η hη with hη | rfl
    · obtain ⟨l, c, d, b, f, a, ⟨hlη, pred⟩, hc, hd, hb, hf, ha, valid⟩ := tree.steps i η hη hηi
      have hl := order.ordinal.transitive η hη l hlη
      exact ⟨l, c, d, b, f, a, ⟨hlη, fun x => (old x η hη).trans ((pred x).trans (or_congr Iff.rfl (old x l hl).symm))⟩,
        (qs i c).mpr (Or.inl hc), (qs l d).mpr (Or.inl hd), (qs η b).mpr (Or.inl hb),
        (gold l η f hη).mpr hf, (es i a).mpr (Or.inl ha), valid⟩
    · have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (order.ordinal.mem hηi.predecessor_mem) hηi hα
      subst i
      exact ⟨k, c, d, b, j, p, predecessor, (qs ξ c).mpr (Or.inl hc), (qs k d).mpr (Or.inl hd),
        (qs _ b).mpr (Or.inr ⟨rfl, rfl⟩), edge, (es ξ p).mpr (Or.inr ⟨rfl, rfl⟩), step⟩
  have limits δ (hδ : M.mem δ β) (hl : M.IsLimitOrdinal δ) : It_limit_d U Q' G' δ := by
    have hδα : M.mem δ α := (older δ hδ).elim id fun eq =>
      (it_successor_not_limit_l hZF.1 (order.ordinal.mem hα.predecessor_mem) hα (eq ▸ hl)).elim
    intro c X R hc hp y hy
    obtain ⟨i, hi, hiδ, f, hf, x, hxy⟩ := tree.limits δ hδα hl c X R ((qold δ c hδα).mp hc) hp y hy
    exact ⟨i, hi, (old i δ hδα).mpr hiδ, f, (gold i δ f hδα).mpr hf, x, hxy⟩
  refine ⟨β, U, Q', G', E', hβ, ⟨tree.omega, diagram, fun z hz => (qs z c₀).mpr (Or.inl (tree.root z hz)),
    ?_, ef, domain, steps, limits⟩, us, qs, gold, es, edge⟩
  intro i a ha
  rcases (qs i a).mp ha with ha | ⟨_, rfl⟩
  · exact tree.sources i a ha
  · exact source

end YesMetaZFC.SetTheory.LargeCardinal
