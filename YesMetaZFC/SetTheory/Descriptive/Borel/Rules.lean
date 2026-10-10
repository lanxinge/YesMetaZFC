import YesMetaZFC.SetTheory.Descriptive.Borel.Evaluation

/-! # Borel 码的节点方程与三条求值规则 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 节点方程：叶真值、子值并的否定、子值并。 -/
theorem bsem_node_l {T R N F x V a : M.Domain} (hv : Bsem_d I T R N F x V) (ha : M.mem a T) :
    M.mem a V ↔ Blit_d I F x a ∨
      (M.mem a N ∧ ¬ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V) ∨
      (Buni_d I N F a ∧ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V) := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  refine (hV.2 a ha).trans ?_
  simp only [Br_step_d, hL a, hU a, ha, true_and]
  exact or_congr Iff.rfl (or_congr (and_congr_right fun _ =>
    ⟨fun h ⟨b, hb, hr, hv⟩ => h b hb hr hv, fun h b hb hr hv => h ⟨b, hb, hr, hv⟩⟩) Iff.rfl)

theorem bsem_leaf_l {T R N F x V a s : M.Domain} (hv : Bsem_d I T R N F x V)
    (hf : M.IsSetFunction I F) (ha : M.mem a T) (hn : ¬ M.mem a N) (hs : M.PairMember I a s F) :
    M.mem a V ↔ M.MemberSubset s x := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  have hu : ¬ M.mem a U := fun h => ((hU a).mp h).2.2 ⟨s, hs⟩
  have hl : M.mem a L ↔ M.MemberSubset s x := (hL a).trans
    ⟨fun ⟨_, t, ht, htx⟩ => (hf.2 a t s ht hs) ▸ htx, fun h => ⟨ha, s, hs, h⟩⟩
  exact (hV.2 a ha).trans (by simp only [Br_step_d, hn, hu, false_and, or_false]; exact hl)

theorem bsem_neg_l {T R N F x V a b : M.Domain} (hv : Bsem_d I T R N F x V)
    (ha : M.mem a T) (hn : M.mem a N) (hf : ¬ ∃ s, M.PairMember I a s F)
    (hb : M.mem b T) (hr : Rd_entry_d b a R)
    (hu : ∀ c, M.mem c T → Rd_entry_d c a R → c = b) : M.mem a V ↔ ¬ M.mem b V := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  have hl : ¬ M.mem a L := fun h => ((hL a).mp h).2.elim fun s hs => hf ⟨s, hs.1⟩
  have hnU : ¬ M.mem a U := fun h => ((hU a).mp h).2.1 hn
  refine (hV.2 a ha).trans ?_
  simp only [Br_step_d, hl, hn, hnU, false_or, true_and, false_and, or_false]
  exact ⟨fun h => h b hb hr, fun h c hc hca hv => h (hu c hc hca ▸ hv)⟩

theorem bsem_union_l {T R N F x V a : M.Domain} (hv : Bsem_d I T R N F x V)
    (ha : M.mem a T) (hn : ¬ M.mem a N) (hf : ¬ ∃ s, M.PairMember I a s F) :
    M.mem a V ↔ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  have hl : ¬ M.mem a L := fun h => ((hL a).mp h).2.elim fun s hs => hf ⟨s, hs.1⟩
  have hu := (hU a).mpr ⟨ha, hn, hf⟩
  simpa only [Br_step_d, hl, hn, hu, false_or, false_and, true_and] using hV.2 a ha

end YesMetaZFC.SetTheory.Descriptive
