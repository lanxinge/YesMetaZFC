import YesMetaZFC.SetTheory.InnerModel.Order.Image
import YesMetaZFC.SetTheory.InnerModel.Order.Append
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Step

/-! # 十三个生成像的规范追加

输入参数始终取自原集合 U，使用原良序 R；已加入的像只改变当前载体和当前序。
因此结果正好是已有的一步 rud 扩张，并且运算优先级由固定菜单确定。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_add_d (k : Rd_sym) (U R P V S W T : M.Domain) : Prop := ∃ Y Q,
  Rw_image_d k U P Y ∧ Rw_rel_d (Rw_cmp_d k U R P) Y Q ∧ M.IsUnionOfTwo W V Y ∧ Rw_rel_d (Rw_append_d V S Q) W T

theorem rw_add_exists_l (hKP : M.Models KP) (k : Rd_sym) {U R P V S : M.Domain} (hp : Rw_domain_d U P) :
    ∃ W T, Rw_add_d k U R P V S W T := by
  obtain ⟨Y, hy⟩ := rw_image_exists_l hKP k hp
  obtain ⟨Q, hq⟩ := rw_image_rel_exists_l hKP k U R P Y
  obtain ⟨W, T, hw, ht⟩ := rw_append_exists_l hKP V S Y Q
  exact ⟨W, T, Y, Q, hy, hq, hw, ht⟩

theorem rw_add_unique_l (hE : Extensional M) {k U R P V S W T W' T'}
    (h : Rw_add_d (M := M) k U R P V S W T) (g : Rw_add_d k U R P V S W' T') : W = W' ∧ T = T' := by
  obtain ⟨Y, Q, hy, hq, hw, ht⟩ := h
  obtain ⟨Y', Q', hy', hq', hw', ht'⟩ := g
  have he := hE.eq_of_same_members Y Y' (fun x => (hy x).trans (hy' x).symm); subst Y'
  have he := hq.unique_l hE hq'; subst Q'
  have he := hE.eq_of_same_members W W' (fun x => (hw x).trans (hw' x).symm); subst W'
  exact ⟨rfl, ht.unique_l hE ht'⟩

theorem rw_add_mem_l {k U R P V S W T} (h : Rw_add_d (M := M) k U R P V S W T) (x : M.Domain) :
    M.mem x W ↔ M.mem x V ∨ ∃ p, M.mem p P ∧ Rw_fun_d k U p x := by
  obtain ⟨Y, _, hy, _, hw, _⟩ := h
  exact (hw x).trans (or_congr Iff.rfl (hy x))

theorem rw_add_bound_l (hKP : M.Models KP) {k U R P V S W T} (h : Rw_add_d (M := M) k U R P V S W T) :
    ∀ x y, Rd_entry_d x y T → M.mem x W ∧ M.mem y W := by
  obtain ⟨_, _, _, _, _, ht⟩ := h
  exact fun x y h => ⟨((ht.entry_l hKP).mp h).1, ((ht.entry_l hKP).mp h).2.1⟩

theorem rw_add_correct_l (hKP : M.Models KP) {k U R P V S W T}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P)
    (hs : M.IsSetCodedWellOrder (kp_pair_l hKP) S V) (h : Rw_add_d k U R P V S W T) :
    M.IsSetCodedWellOrder (kp_pair_l hKP) T W ∧ Rw_end_d V S W T := by
  obtain ⟨Y, Q, hy, hq, hw, ht⟩ := h
  exact ⟨rw_append_wellorder_l hKP hs (rw_image_wellorder_l hKP hr hp hy hq) hw ht, rw_append_end_l hKP hw ht⟩

def Rw_fold_d (L : List Rd_sym) (U R P V S W T : M.Domain) : Prop := match L with
  | [] => W = V ∧ T = S
  | k :: L => ∃ A Q, Rw_add_d k U R P V S A Q ∧ Rw_fold_d L U R P A Q W T

theorem rw_fold_exists_l (hKP : M.Models KP) (L : List Rd_sym) {U R P : M.Domain} (hp : Rw_domain_d U P) (V S : M.Domain) :
    ∃ W T, Rw_fold_d L U R P V S W T := by
  induction L generalizing V S with
  | nil => exact ⟨V, S, rfl, rfl⟩
  | cons k L ih =>
    obtain ⟨A, Q, ha⟩ := rw_add_exists_l hKP k (R := R) (V := V) (S := S) hp
    obtain ⟨W, T, ht⟩ := ih A Q
    exact ⟨W, T, A, Q, ha, ht⟩

theorem rw_fold_unique_l (hE : Extensional M) {L U R P V S W T W' T'}
    (h : Rw_fold_d (M := M) L U R P V S W T) (g : Rw_fold_d L U R P V S W' T') : W = W' ∧ T = T' := by
  induction L generalizing V S with
  | nil => exact ⟨h.1.trans g.1.symm, h.2.trans g.2.symm⟩
  | cons k L ih =>
    obtain ⟨A, Q, ha, h⟩ := h
    obtain ⟨A', Q', ha', g⟩ := g
    obtain ⟨rfl, rfl⟩ := rw_add_unique_l hE ha ha'
    exact ih h g

theorem rw_fold_mem_l {L U R P V S W T} (h : Rw_fold_d (M := M) L U R P V S W T) (x : M.Domain) :
    M.mem x W ↔ M.mem x V ∨ ∃ k, k ∈ L ∧ ∃ p, M.mem p P ∧ Rw_fun_d k U p x := by
  induction L generalizing V S with
  | nil => rw [h.1]; simp only [List.not_mem_nil, false_and, exists_false, or_false]
  | cons k L ih =>
    obtain ⟨A, Q, ha, h⟩ := h
    rw [ih h, rw_add_mem_l ha x]
    constructor
    · rintro ((hx | hx) | ⟨j, hj, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨k, List.mem_cons_self .., hx⟩
      · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hx⟩
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact Or.inl (Or.inl hx)
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact Or.inl (Or.inr hx)
        · exact Or.inr ⟨j, hj, hx⟩

theorem rw_fold_correct_l (hKP : M.Models KP) {L U R P V S W T}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P)
    (hs : M.IsSetCodedWellOrder (kp_pair_l hKP) S V)
    (hb : ∀ x y, Rd_entry_d x y S → M.mem x V ∧ M.mem y V) (h : Rw_fold_d L U R P V S W T) :
    M.IsSetCodedWellOrder (kp_pair_l hKP) T W ∧ Rw_end_d V S W T := by
  induction L generalizing V S with
  | nil => obtain ⟨rfl, rfl⟩ := h; exact ⟨hs, rw_end_refl_l hb⟩
  | cons k L ih =>
    obtain ⟨A, Q, ha, h⟩ := h
    have hA := rw_add_correct_l hKP hr hp hs ha
    obtain ⟨hw, he⟩ := ih hA.1 (rw_add_bound_l hKP ha) h
    exact ⟨hw, rw_end_trans_l hA.2 he⟩

def Rw_step_d (U R V S : M.Domain) : Prop := ∃ P, Rw_domain_d U P ∧ Rw_fold_d rd_menu_l U R P U R V S
theorem rw_step_exists_l (hKP : M.Models KP) (U R : M.Domain) : ∃ V S, Rw_step_d U R V S := by
  obtain ⟨P, hp⟩ := rd_triples_exists_l hKP U U U
  obtain ⟨V, S, hs⟩ := rw_fold_exists_l hKP rd_menu_l (R := R) hp U R
  exact ⟨V, S, P, hp, hs⟩
theorem rw_step_unique_l (hE : Extensional M) {U R V S V' S'} (h : Rw_step_d (M := M) U R V S)
    (g : Rw_step_d U R V' S') : V = V' ∧ S = S' := by
  obtain ⟨P, hp, h⟩ := h
  obtain ⟨Q, hq, g⟩ := g
  have he := hE.eq_of_same_members P Q (fun p => (hp p).trans (hq p).symm); subst Q
  exact rw_fold_unique_l hE h g

theorem rw_step_carrier_l (hKP : M.Models KP) {U R V S : M.Domain} (h : Rw_step_d U R V S) : Rd_step_d U V := by
  obtain ⟨P, hp, h⟩ := h
  intro x
  rw [rw_fold_mem_l h x]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨k, _, p, _, a, ha, b, hb, c, hc, _, hx⟩
    exact ⟨k, a, b, c, ha, hb, hc, hx⟩
  · rintro ⟨k, a, b, c, ha, hb, hc, hx⟩
    obtain ⟨q, hq⟩ := (kp_pair_l hKP).total b c
    obtain ⟨p, hp'⟩ := (kp_pair_l hKP).total a q
    have ht : Rd_triple_d p a b c := ⟨q, hq, hp'⟩
    exact ⟨k, rd_menu_mem_l k, p, (hp p).mpr ⟨a, ha, b, hb, c, hc, ht⟩, a, ha, b, hb, c, hc, ht, hx⟩

theorem rw_step_correct_l (hKP : M.Models KP) {U R V S : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U)
    (hb : ∀ x y, Rd_entry_d x y R → M.mem x U ∧ M.mem y U) (h : Rw_step_d U R V S) :
    Rd_step_d U V ∧ M.IsSetCodedWellOrder (kp_pair_l hKP) S V ∧ Rw_end_d U R V S := by
  obtain ⟨P, hp, hf⟩ := h
  exact ⟨rw_step_carrier_l hKP ⟨P, hp, hf⟩, rw_fold_correct_l hKP hr hp hr hb hf⟩

end YesMetaZFC.SetTheory.InnerModel
