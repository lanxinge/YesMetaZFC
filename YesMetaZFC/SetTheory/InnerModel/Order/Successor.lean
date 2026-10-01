import YesMetaZFC.SetTheory.InnerModel.Order.Step

/-! # Jensen 微后继 S(U)=s(U∪{U}) 的规范良序

先将 U 本身放在旧序之后，再按固定运算菜单追加生成像。空序提供实际起点，
整个算子对任意集合输入有唯一输出；良序输入时输出良序并保持端延拓。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rw_empty_order_l (hKP : M.Models KP) {E : M.Domain} (he : ∀ x, ¬ M.mem x E) :
    M.IsSetCodedWellOrder (kp_pair_l hKP) E E := by
  refine ⟨⟨fun p hp => (he p hp).elim, ⟨fun p hp => (he p hp).elim, fun p hp => (he p hp).elim⟩,
    fun p hp => (he p hp).elim⟩, ?_⟩
  intro X hx hn
  obtain ⟨x, hxx⟩ := hn
  exact (he x (hx x hxx)).elim

theorem rw_singleton_order_l (hKP : M.Models KP) {a Y E : M.Domain}
    (hy : Pair_d M Y a a) (he : ∀ x, ¬ M.mem x E) : M.IsSetCodedWellOrder (kp_pair_l hKP) E Y := by
  have eq x hx : x = a := ((hy x).mp hx).elim id id
  have empty x y : ¬ Rd_entry_d x y E := fun ⟨p, _, hp⟩ => he p hp
  refine ⟨⟨fun p hp => (he p hp).elim, ⟨fun x _ => empty x x, fun x _ y _ z _ h => (empty x y h).elim⟩,
    fun x hx y hy => Or.inl ((eq x hx).trans (eq y hy).symm ▸ (fun _ => Iff.rfl))⟩, ?_⟩
  intro X hx hn
  obtain ⟨x, hxx⟩ := hn
  exact ⟨x, hxx, fun y hyy => Or.inl ((eq x (hx x hxx)).trans (eq y (hx y hyy)).symm ▸ (fun _ => Iff.rfl))⟩

def Rw_adjoin_d (U R V S : M.Domain) : Prop := ∃ Y E,
  Pair_d M Y U U ∧ (∀ x, ¬ M.mem x E) ∧ M.IsUnionOfTwo V U Y ∧ Rw_rel_d (Rw_append_d U R E) V S

theorem rw_adjoin_exists_l (hKP : M.Models KP) (U R : M.Domain) : ∃ V S, Rw_adjoin_d U R V S := by
  obtain ⟨Y, hy⟩ := KP.exists_pair hKP U U
  obtain ⟨E, he⟩ := KP.exists_empty hKP
  obtain ⟨V, S, hv, hs⟩ := rw_append_exists_l hKP U R Y E
  exact ⟨V, S, Y, E, hy, he, hv, hs⟩

theorem rw_adjoin_unique_l (hE : Extensional M) {U R V S V' S'} (h : Rw_adjoin_d (M := M) U R V S)
    (g : Rw_adjoin_d U R V' S') : V = V' ∧ S = S' := by
  obtain ⟨Y, E, hy, he, hv, hs⟩ := h
  obtain ⟨Y', E', hy', he', hv', hs'⟩ := g
  have heq := hE.eq_of_same_members Y Y' (fun x => (hy x).trans (hy' x).symm); subst Y'
  have heq := hE.eq_of_same_members E E' (fun x => iff_of_false (he x) (he' x)); subst E'
  have heq := hE.eq_of_same_members V V' (fun x => (hv x).trans (hv' x).symm); subst V'
  exact ⟨rfl, hs.unique_l hE hs'⟩

theorem rw_adjoin_carrier_l (hE : Extensional M) {U R V S : M.Domain} (h : Rw_adjoin_d U R V S) : M.SuccessorOf V U := by
  obtain ⟨Y, _, hy, _, hv, _⟩ := h
  intro x
  exact (hv x).trans (or_congr_right ((hy x).trans
    ⟨fun h => (h.elim id id) ▸ (fun _ => Iff.rfl), fun h => Or.inl (hE.eq_of_same_members _ _ h)⟩))

theorem rw_adjoin_bound_l (hKP : M.Models KP) {U R V S : M.Domain} (h : Rw_adjoin_d U R V S) :
    ∀ x y, Rd_entry_d x y S → M.mem x V ∧ M.mem y V := by
  obtain ⟨_, _, _, _, _, hs⟩ := h
  exact fun x y h => ⟨((hs.entry_l hKP).mp h).1, ((hs.entry_l hKP).mp h).2.1⟩

theorem rw_adjoin_correct_l (hKP : M.Models KP) {U R V S : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (h : Rw_adjoin_d U R V S) :
    M.IsSetCodedWellOrder (kp_pair_l hKP) S V ∧ Rw_end_d U R V S := by
  obtain ⟨Y, E, hy, he, hv, hs⟩ := h
  exact ⟨rw_append_wellorder_l hKP hr (rw_singleton_order_l hKP hy he) hv hs, rw_append_end_l hKP hv hs⟩

def Rw_successor_d (U R V S : M.Domain) : Prop := ∃ A Q, Rw_adjoin_d U R A Q ∧ Rw_step_d A Q V S
theorem rw_successor_exists_l (hKP : M.Models KP) (U R : M.Domain) : ∃ V S, Rw_successor_d U R V S := by
  obtain ⟨A, Q, ha⟩ := rw_adjoin_exists_l hKP U R
  obtain ⟨V, S, hv⟩ := rw_step_exists_l hKP A Q
  exact ⟨V, S, A, Q, ha, hv⟩
theorem rw_successor_unique_l (hE : Extensional M) {U R V S V' S'} (h : Rw_successor_d (M := M) U R V S)
    (g : Rw_successor_d U R V' S') : V = V' ∧ S = S' := by
  obtain ⟨A, Q, ha, h⟩ := h
  obtain ⟨A', Q', ha', g⟩ := g
  obtain ⟨rfl, rfl⟩ := rw_adjoin_unique_l hE ha ha'
  exact rw_step_unique_l hE h g

theorem rw_successor_correct_l (hKP : M.Models KP) {U R V S : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (h : Rw_successor_d U R V S) :
    (∃ A, M.SuccessorOf A U ∧ Rd_step_d A V) ∧
      M.IsSetCodedWellOrder (kp_pair_l hKP) S V ∧ Rw_end_d U R V S := by
  obtain ⟨A, Q, ha, hs⟩ := h
  have hA := rw_adjoin_correct_l hKP hr ha
  obtain ⟨hv, hS, he⟩ := rw_step_correct_l hKP hA.1 (rw_adjoin_bound_l hKP ha) hs
  exact ⟨⟨A, rw_adjoin_carrier_l hKP.1 ha, hv⟩, hS, rw_end_trans_l hA.2 he⟩

end YesMetaZFC.SetTheory.InnerModel
