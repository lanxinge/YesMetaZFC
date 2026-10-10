import YesMetaZFC.SetTheory.LargeCardinal.IterationOrder

/-! # 序数上的实际自反线性迭代序

同一个规范序同时服务于 padding 树和弱迭代的极限取并。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem it_linear_order_l (hKP : M.Models KP) {α : M.Domain} (ho : M.IsOrdinal α) : ∃ T, It_order_d α T ∧
    (∀ i j, Rd_entry_d i j T ↔ M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j)) ∧
    ∀ i j, M.mem j α → M.SuccessorOf j i → It_pred_d T i j := by
  let φ : Delta0BinarySchema 0 := {
    body := .disj (Formula.extensionalEq (.bound 1) .newest) (.mem (.bound 1) .newest)
    delta0 := .disj (.atom _ _ _) (.mem _ _) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => α⟩
  obtain ⟨T, ts⟩ := rw_rel_exists_l hKP φ ρ α
  have sat i j : φ.toBinarySchema.denote ρ i j ↔ i = j ∨ M.mem i j := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_mem_iff]; rfl
  have read i j : Rd_entry_d i j T ↔ M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j) :=
    (ts.entry_l hKP).trans (and_congr_right fun _ => and_congr_right fun _ => sat i j)
  have ht : M.IsSetRelationOn (kp_pair_l hKP) T α := ⟨fun p hp => by
    obtain ⟨i, _, j, _, hp, _⟩ := (ts p).mp hp
    exact ⟨i, j, hp⟩, fun i j hij => ⟨((read i j).mp hij).1, ((read i j).mp hij).2.1⟩⟩
  have refl i hi := (read i i).mpr ⟨hi, hi, Or.inl rfl⟩
  have pred i j (hj : M.mem j α) (hs : M.SuccessorOf j i) : It_pred_d T i j := by
    have hi := ho.transitive j hj i hs.predecessor_mem
    refine ⟨hs.predecessor_mem, fun k => ⟨?_, ?_⟩⟩
    · intro hk
      obtain ⟨hkα, _, eq | hkj⟩ := (read k j).mp hk
      · exact Or.inl eq
      · rcases (hs k).mp hkj with hki | eq
        · exact Or.inr ((read k i).mpr ⟨hkα, hi, Or.inr hki⟩)
        · exact Or.inr ((read k i).mpr ⟨hkα, hi, Or.inl (hKP.1.eq_of_same_members k i eq)⟩)
    · rintro (rfl | hk)
      · exact refl _ hj
      · obtain ⟨hkα, _, rfl | hki⟩ := (read k i).mp hk
        · exact (read _ j).mpr ⟨hkα, hj, Or.inr hs.predecessor_mem⟩
        · exact (read k j).mpr ⟨hkα, hj, Or.inr ((hs k).mpr (Or.inl hki))⟩
  refine ⟨T, ⟨ho, ht.1, ht.2, refl, ?_, fun i j hij => ((read i j).mp hij).2.2, ?_,
    fun i j hj hs => ⟨i, pred i j hj hs⟩, ?_⟩, read, pred⟩
  · intro i j k hij hjk
    obtain ⟨hi, _, rfl | hij⟩ := (read i j).mp hij
    · exact hjk
    · obtain ⟨_, hk, rfl | hjk⟩ := (read j k).mp hjk
      · exact (read i _).mpr ⟨hi, hk, Or.inr hij⟩
      · exact (read i k).mpr ⟨hi, hk, Or.inr ((ho.mem hk).transitive j hjk i hij)⟩
  · intro i j k hik hjk
    have hi := (ht.2 i k hik).1
    have hj := (ht.2 j k hjk).1
    rcases ho.wellOrder.linear.compare i hi j hj with eq | hij | hji
    · exact Or.inl ((read i j).mpr ⟨hi, hj, Or.inl (hKP.1.eq_of_same_members i j eq)⟩)
    · exact Or.inl ((read i j).mpr ⟨hi, hj, Or.inr hij⟩)
    · exact Or.inr ((read j i).mpr ⟨hj, hi, Or.inr hji⟩)
  · intro δ hδ _ i hi
    exact ⟨i, hi, (read i δ).mpr ⟨ho.transitive δ hδ i hi, hδ, Or.inr hi⟩, Or.inl rfl⟩

end YesMetaZFC.SetTheory.LargeCardinal
