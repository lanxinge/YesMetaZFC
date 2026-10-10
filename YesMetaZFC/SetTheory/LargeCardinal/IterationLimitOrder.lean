import YesMetaZFC.SetTheory.LargeCardinal.IterationBranch

/-! # 在极限长度上沿共尾树枝添入新顶点 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

theorem it_limit_order_l {α T B : M.Domain} (h : It_order_d α T)
    (hl : M.IsLimitOrdinal α) (b : It_branch_d α T B) : ∃ β U, M.SuccessorOf β α ∧ It_order_d β U ∧
      ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B) := by
  obtain ⟨β, hβ⟩ := KP.exists_successor hKP α
  have no : ¬ M.mem α α := fun ha => h.ordinal.wellOrder.linear.irrefl α ha ha
  have sc i : M.mem i β ↔ M.mem i α ∨ i = α := (hβ i).trans
    (or_congr Iff.rfl ⟨hKP.1.eq_of_same_members i α, fun e => e ▸ fun _ => Iff.rfl⟩)
  let ρ : Env M 3 := ⟨Fin.cases α (Fin.cases B (fun _ => T)), fun _ => α⟩
  let φ : Delta0BinarySchema 3 := {
    body := .disj (rd_entry0_m (.bound 1) .newest (.bound 4))
      (.conj (Formula.extensionalEq .newest (.bound 2))
        (.disj (Formula.extensionalEq (.bound 1) (.bound 2)) (.mem (.bound 1) (.bound 3))))
    delta0 := .disj (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (.disj (.atom _ _ _) (.mem _ _))) }
  have sat i j : φ.toBinarySchema.denote ρ i j ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨U, ur⟩ := rw_rel_exists_l hKP φ ρ β
  have us i j := ur.entry_l hKP (x := i) (y := j)
  have bound i j (hr : Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)) : M.mem i β ∧ M.mem j β := by
    rcases hr with hr | ⟨rfl, rfl | hi⟩
    · exact ⟨(sc i).mpr (Or.inl (h.bound i j hr).1), (sc j).mpr (Or.inl (h.bound i j hr).2)⟩
    · exact ⟨hβ.predecessor_mem, hβ.predecessor_mem⟩
    · exact ⟨(sc i).mpr (Or.inl (b.subset i hi)), hβ.predecessor_mem⟩
  have read i j : Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B) :=
    (us i j).trans ⟨fun hh => (sat i j).mp hh.2.2,
      fun hh => ⟨(bound i j hh).1, (bound i j hh).2, (sat i j).mpr hh⟩⟩
  have old i j (hj : M.mem j α) : Rd_entry_d i j U ↔ Rd_entry_d i j T := (read i j).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have tip i : Rd_entry_d i α U ↔ i = α ∨ M.mem i B := (read i α).trans
    ⟨fun hh => hh.elim (fun hh => (no (h.bound i α hh).2).elim) And.right, fun hh => Or.inr ⟨rfl, hh⟩⟩
  have bounds i j (hij : Rd_entry_d i j U) := bound i j ((read i j).mp hij)
  refine ⟨β, U, hβ, ⟨KP.successor_isOrdinal hKP h.ordinal hβ, fun p hp => ?_, bounds,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, read⟩
  · obtain ⟨i, _, j, _, hp, _⟩ := (ur p).mp hp
    exact ⟨i, j, hp⟩
  · intro i hi
    rcases (sc i).mp hi with hi | rfl
    · exact (read i i).mpr (Or.inl (h.refl i hi))
    · exact (tip _).mpr (Or.inl rfl)
  · intro i j k hij hjk
    rcases (sc k).mp (bounds j k hjk).2 with hk | rfl
    · have hjk := (old j k hk).mp hjk
      exact (old i k hk).mpr (h.trans i j k ((old i j (h.bound j k hjk).1).mp hij) hjk)
    · rcases (tip j).mp hjk with rfl | hj
      · exact hij
      · exact (tip i).mpr (Or.inr (b.down i j ((old i j (b.subset j hj)).mp hij) hj))
  · intro i j hij
    rcases (read i j).mp hij with hij | ⟨rfl, rfl | hi⟩
    · exact h.forward i j hij
    · exact Or.inl rfl
    · exact Or.inr (b.subset i hi)
  · intro i j k hik hjk
    rcases (sc k).mp (bounds i k hik).2 with hk | rfl
    · exact (h.chain i j k ((old i k hk).mp hik) ((old j k hk).mp hjk)).imp
        (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
    · rcases (tip i).mp hik with rfl | hi
      · exact Or.inr hjk
      · rcases (tip j).mp hjk with rfl | hj
        · exact Or.inl hik
        · exact (b.chain i j hi hj).imp (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
  · intro i j hj hs
    rcases (sc j).mp hj with hj | rfl
    · obtain ⟨k, hk, pred⟩ := h.predecessor i j hj hs
      exact ⟨k, hk, fun l => (old l j hj).trans ((pred l).trans
        (or_congr Iff.rfl (old l k (h.ordinal.transitive j hj k hk)).symm))⟩
    · exact (it_successor_not_limit_l hKP.1 (h.ordinal.mem hs.predecessor_mem) hs hl).elim
  · intro δ hδ limit i hi
    rcases (sc δ).mp hδ with hδ | rfl
    · obtain ⟨j, hj, hjδ, above⟩ := h.cofinal δ hδ limit i hi
      exact ⟨j, hj, (old j δ hδ).mpr hjδ, above⟩
    · obtain ⟨j, hj, above⟩ := b.cofinal i hi
      exact ⟨j, b.subset j hj, (tip j).mpr (Or.inr hj), above⟩

end YesMetaZFC.SetTheory.LargeCardinal
