import YesMetaZFC.SetTheory.InnerModel.Order.Relation

/-! # 保留旧序并追加新对象

两个集合可以重叠；交叠对象只保留在旧部分，新部分为 Y\V。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_append_d (V R S x y : M.Domain) : Prop :=
  (M.mem x V ∧ (¬ M.mem y V ∨ Rd_entry_d x y R)) ∨ (¬ M.mem x V ∧ ¬ M.mem y V ∧ Rd_entry_d x y S)
def rw_append_s : Delta0BinarySchema 3 where
  body := .disj (.conj (.mem (.bound 1) (.bound 2))
    (.disj (.neg (.mem .newest (.bound 2))) (rd_entry0_m (.bound 1) .newest (.bound 3))))
    (.conj (.neg (.mem (.bound 1) (.bound 2)))
      (.conj (.neg (.mem .newest (.bound 2))) (rd_entry0_m (.bound 1) .newest (.bound 4))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.mem _ _) (.disj (.neg (.mem _ _)) (rd_entry0_delta_l ..)))
    (.conj (.neg (.mem _ _)) (.conj (.neg (.mem _ _)) (rd_entry0_delta_l ..)))
theorem rw_append_sat_l (hE : Extensional M) (ρ : Env M 3) (x y : M.Domain) :
    rw_append_s.toBinarySchema.denote ρ x y ↔ Rw_append_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) x y := by
  simp only [BinarySchema.denote, rw_append_s, Rw_append_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hE]; rfl

def Rw_end_d (U R V S : M.Domain) : Prop := M.MemberSubset U V ∧
  ∀ x y, M.mem y U → (Rd_entry_d x y S ↔ M.mem x U ∧ Rd_entry_d x y R)
theorem rw_end_refl_l {U R : M.Domain} (hr : ∀ x y, Rd_entry_d x y R → M.mem x U ∧ M.mem y U) : Rw_end_d U R U R :=
  ⟨fun _ h => h, fun x y _ => ⟨fun h => ⟨(hr x y h).1, h⟩, And.right⟩⟩
theorem rw_end_trans_l {U R V S W T : M.Domain} (h : Rw_end_d U R V S) (g : Rw_end_d V S W T) : Rw_end_d U R W T := by
  refine ⟨fun x hx => g.1 x (h.1 x hx), fun x y hy => ?_⟩
  rw [g.2 x y (h.1 y hy), h.2 x y hy]
  exact ⟨fun ⟨_, h⟩ => h, fun hx => ⟨h.1 x hx.1, hx⟩⟩

theorem rw_append_old_l {V R S x y : M.Domain} (hy : M.mem y V) : Rw_append_d V R S x y ↔ M.mem x V ∧ Rd_entry_d x y R := by
  refine ⟨?_, fun h => Or.inl ⟨h.1, Or.inr h.2⟩⟩
  rintro (⟨hx, h⟩ | ⟨_, hn, _⟩)
  · exact ⟨hx, h.elim (fun hn => (hn hy).elim) id⟩
  · exact (hn hy).elim

theorem rw_append_exists_l (hKP : M.Models KP) (V R Y S : M.Domain) :
    ∃ W T, M.IsUnionOfTwo W V Y ∧ Rw_rel_d (Rw_append_d V R S) W T := by
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo hKP V Y
  let ρ : Env M 3 := ⟨Fin.cases V (Fin.cases R (fun _ => S)), fun _ => V⟩
  obtain ⟨T, ht⟩ := rw_rel_exists_l hKP rw_append_s ρ W
  exact ⟨W, T, hw, fun p => (ht p).trans (exists_congr fun x => and_congr_right fun _ =>
    exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => rw_append_sat_l hKP.1 ρ x y)⟩

theorem rw_append_end_l (hKP : M.Models KP) {V R Y S W T : M.Domain}
    (hw : M.IsUnionOfTwo W V Y) (ht : Rw_rel_d (Rw_append_d V R S) W T) : Rw_end_d V R W T := by
  refine ⟨fun x hx => (hw x).mpr (Or.inl hx), fun x y hy => ?_⟩
  rw [ht.entry_l hKP, rw_append_old_l hy]
  exact ⟨fun h => h.2.2, fun h => ⟨(hw x).mpr (Or.inl h.1), (hw y).mpr (Or.inl hy), h⟩⟩

theorem rw_append_wellorder_l (hKP : M.Models KP) {V R Y S W T : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R V) (hs : M.IsSetCodedWellOrder (kp_pair_l hKP) S Y)
    (hw : M.IsUnionOfTwo W V Y) (ht : Rw_rel_d (Rw_append_d V R S) W T) :
    M.IsSetCodedWellOrder (kp_pair_l hKP) T W := by
  classical
  have fresh {x} (hx : M.mem x W) (hn : ¬ M.mem x V) : M.mem x Y := ((hw x).mp hx).elim (fun h => (hn h).elim) id
  apply ht.wellorder_l hKP
  · intro x hx h
    rcases h with ⟨hv, hn | he⟩ | ⟨hn, _, he⟩
    · exact hn hv
    · exact hr.linear.2.1.1 x hv he
    · exact hs.linear.2.1.1 x (fresh hx hn) he
  · intro x hx y hy z hz h g
    by_cases hxV : M.mem x V
    · refine Or.inl ⟨hxV, ?_⟩
      by_cases hzV : M.mem z V
      · obtain ⟨hyV, hyz⟩ := (rw_append_old_l hzV).mp g
        exact Or.inr (hr.linear.2.1.2 x hxV y hyV z hzV ((rw_append_old_l hyV).mp h).2 hyz)
      · exact Or.inl hzV
    · obtain ⟨hyV, hxy⟩ : ¬ M.mem y V ∧ Rd_entry_d x y S :=
        h.elim (fun h => (hxV h.1).elim) (fun h => h.2)
      obtain ⟨hzV, hyz⟩ : ¬ M.mem z V ∧ Rd_entry_d y z S :=
        g.elim (fun h => (hyV h.1).elim) (fun h => h.2)
      exact Or.inr ⟨hxV, hzV, hs.linear.2.1.2 x (fresh hx hxV) y (fresh hy hyV) z (fresh hz hzV) hxy hyz⟩
  · intro x hx y hy
    by_cases hxV : M.mem x V <;> by_cases hyV : M.mem y V
    · exact ((hr.linear.2.2 x hxV y hyV).imp_left (hKP.1.eq_of_same_members _ _)).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl (Or.inl ⟨hxV, Or.inr h⟩))) (fun h => Or.inr (Or.inr (Or.inl ⟨hyV, Or.inr h⟩))))
    · exact Or.inr (Or.inl (Or.inl ⟨hxV, Or.inl hyV⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hyV, Or.inl hxV⟩))
    · exact ((hs.linear.2.2 x (fresh hx hxV) y (fresh hy hyV)).imp_left (hKP.1.eq_of_same_members _ _)).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl (Or.inr ⟨hxV, hyV, h⟩))) (fun h => Or.inr (Or.inr (Or.inr ⟨hyV, hxV, h⟩))))
  · intro X hx hn
    obtain ⟨A, ha⟩ := KP.intersection_exists_d hKP X V
    by_cases hA : ∃ a, M.mem a A
    · obtain ⟨a, haA, hm⟩ := hr.least A (fun a haA => ((ha a).mp haA).2) hA
      obtain ⟨haX, haV⟩ := (ha a).mp haA
      refine ⟨a, haX, fun b hbX => ?_⟩
      by_cases hbV : M.mem b V
      · exact (hm b ((ha b).mpr ⟨hbX, hbV⟩)).elim (fun he => Or.inl (hKP.1.eq_of_same_members _ _ he))
          (fun he => Or.inr (Or.inl ⟨haV, Or.inr he⟩))
      · exact Or.inr (Or.inl ⟨haV, Or.inl hbV⟩)
    · have outside x hxX : ¬ M.mem x V := fun hxV => hA ⟨x, (ha x).mpr ⟨hxX, hxV⟩⟩
      obtain ⟨a, haX, hm⟩ := hs.least X (fun x hxX => fresh (hx x hxX) (outside x hxX)) hn
      exact ⟨a, haX, fun b hbX => (hm b hbX).elim (fun he => Or.inl (hKP.1.eq_of_same_members _ _ he))
        (fun he => Or.inr (Or.inr ⟨outside a haX, outside b hbX, he⟩))⟩

end YesMetaZFC.SetTheory.InnerModel
