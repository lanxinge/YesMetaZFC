import YesMetaZFC.SetTheory.InnerModel.Order.Relation
import YesMetaZFC.SetTheory.MembershipInduction

/-! # 对象模型内的迭代树序及后继添枝

树序存储自反闭包。前驱集线性，树边沿序数递增；序数后继有树前驱，
非零极限的严格前驱共尾。添枝允许挂在任意旧结点，完整保留旧前驱集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def It_pred_d (T k j : M.Domain) : Prop := M.mem k j ∧
  ∀ i, Rd_entry_d i j T ↔ i = j ∨ Rd_entry_d i k T

structure It_order_d (α T : M.Domain) : Prop where
  ordinal : M.IsOrdinal α
  relation : ∀ p, M.mem p T → ∃ i j, KPair_d M p i j
  bound : ∀ i j, Rd_entry_d i j T → M.mem i α ∧ M.mem j α
  refl : ∀ i, M.mem i α → Rd_entry_d i i T
  trans : ∀ i j k, Rd_entry_d i j T → Rd_entry_d j k T → Rd_entry_d i k T
  forward : ∀ i j, Rd_entry_d i j T → i = j ∨ M.mem i j
  chain : ∀ i j k, Rd_entry_d i k T → Rd_entry_d j k T → Rd_entry_d i j T ∨ Rd_entry_d j i T
  predecessor : ∀ i j, M.mem j α → M.SuccessorOf j i → ∃ k, It_pred_d T k j
  cofinal : ∀ δ, M.mem δ α → M.IsLimitOrdinal δ → ∀ i, M.mem i δ →
    ∃ j, M.mem j δ ∧ Rd_entry_d j δ T ∧ (i = j ∨ M.mem i j)

/-- 每个实际结点都在空序数根之上；证明也覆盖非标准长度和极限结点。 -/
theorem It_order_d.root_l (hZF : M.Models ZF) {α T z : M.Domain} (h : It_order_d α T)
    (hz : ∀ x, ¬ M.mem x z) : ∀ i, M.mem i α → Rd_entry_d z i T := by
  let ρ : Env M 3 := ⟨Fin.cases α (Fin.cases z (fun _ => T)), fun _ => T⟩
  let φ : UnarySchema 3 := { body := .imp (.mem .newest (.bound 1)) (rd_entry0_m (.bound 2) .newest (.bound 3)) }
  have sat i : φ.denote ρ i ↔ M.mem i α → Rd_entry_d z i T := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1]; rfl
  intro i hi
  apply (sat i).mp (ZF.mem_ind_l M hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ ?_ i) hi
  intro i ih
  apply (sat i).mpr
  intro hi
  have prev j (hj : M.mem j i) := (sat j).mp (ih j hj) (h.ordinal.transitive i hi j hj)
  rcases (h.ordinal.mem hi).classify hZF.1 with empty | ⟨j, _, succ⟩ | limit
  · have eq := hZF.1.eq_of_same_members i z (fun x => iff_of_false (empty x) (hz x))
    exact eq ▸ h.refl i hi
  · obtain ⟨k, hk, pred⟩ := h.predecessor j i hi succ
    exact (pred z).mpr (Or.inr (prev k hk))
  · obtain ⟨j, hj⟩ := limit.2.1
    obtain ⟨k, hk, edge, _⟩ := h.cofinal i hi limit j hj
    exact h.trans z k i (prev k hk) edge

theorem it_successor_not_limit_l (hE : Extensional M) {α ξ : M.Domain} (ho : M.IsOrdinal ξ) (hs : M.SuccessorOf α ξ) : ¬ M.IsLimitOrdinal α := by
  intro hl
  obtain ⟨j, hj, hξj⟩ := hl.2.2 ξ hs.predecessor_mem
  rcases (hs j).mp hj with hjξ | eq
  · have self := ho.transitive j hjξ ξ hξj
    exact ho.wellOrder.linear.irrefl ξ self self
  · have eq := hE.eq_of_same_members j ξ eq
    exact ho.wellOrder.linear.irrefl ξ (eq ▸ hξj) (eq ▸ hξj)

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

theorem it_order_extend_l {α ξ T k : M.Domain} (h : It_order_d α T)
    (hα : M.SuccessorOf α ξ) (hk : M.mem k α) : ∃ β U, M.SuccessorOf β α ∧ It_order_d β U ∧
      ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T) := by
  obtain ⟨β, hβ⟩ := KP.exists_successor hKP α
  have no : ¬ M.mem α α := fun ha => h.ordinal.wellOrder.linear.irrefl α ha ha
  have sc i : M.mem i β ↔ M.mem i α ∨ i = α := (hβ i).trans
    (or_congr Iff.rfl ⟨hKP.1.eq_of_same_members i α, fun e => e ▸ fun _ => Iff.rfl⟩)
  let ρ : Env M 3 := ⟨Fin.cases α (Fin.cases k (fun _ => T)), fun _ => α⟩
  let φ : Delta0BinarySchema 3 := {
    body := .disj (rd_entry0_m (.bound 1) .newest (.bound 4))
      (.conj (Formula.extensionalEq .newest (.bound 2))
        (.disj (Formula.extensionalEq (.bound 1) (.bound 2)) (rd_entry0_m (.bound 1) (.bound 3) (.bound 4))))
    delta0 := .disj (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (.disj (.atom _ _ _) (rd_entry0_delta_l ..))) }
  have sat i j : φ.toBinarySchema.denote ρ i j ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1]; rfl
  obtain ⟨U, ur⟩ := rw_rel_exists_l hKP φ ρ β
  have us i j := ur.entry_l hKP (x := i) (y := j)
  have rel : M.IsSetRelationOn I U β := ⟨fun p hp => by
    obtain ⟨i, _, j, _, hp, _⟩ := (ur p).mp hp
    exact ⟨i, j, hp⟩,
    fun i j hij => ⟨((us i j).mp hij).1, ((us i j).mp hij).2.1⟩⟩
  have bounds i j (hr : Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T)) : M.mem i β ∧ M.mem j β := by
    rcases hr with hr | ⟨rfl, rfl | hr⟩
    · exact ⟨(sc i).mpr (Or.inl (h.bound i j hr).1), (sc j).mpr (Or.inl (h.bound i j hr).2)⟩
    · exact ⟨hβ.predecessor_mem, hβ.predecessor_mem⟩
    · exact ⟨(sc i).mpr (Or.inl (h.bound i k hr).1), hβ.predecessor_mem⟩
  have read i j : Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T) :=
    (us i j).trans ⟨fun hh => (sat i j).mp hh.2.2, fun hh => ⟨(bounds i j hh).1, (bounds i j hh).2, (sat i j).mpr hh⟩⟩
  have old i j (hj : M.mem j α) : Rd_entry_d i j U ↔ Rd_entry_d i j T :=
    (read i j).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have tip i : Rd_entry_d i α U ↔ i = α ∨ Rd_entry_d i k T :=
    (read i α).trans ⟨fun hh => hh.elim (fun hh => (no (h.bound i α hh).2).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  have limit_old δ (hδ : M.mem δ β) (limit : M.IsLimitOrdinal δ) : M.mem δ α := by
    rcases (sc δ).mp hδ with hl | rfl
    · exact hl
    · exact (it_successor_not_limit_l hKP.1 (h.ordinal.mem hα.predecessor_mem) hα limit).elim
  refine ⟨β, U, hβ, ⟨KP.successor_isOrdinal hKP h.ordinal hβ, rel.1, rel.2, ?_, ?_, ?_, ?_, ?_, ?_⟩, read⟩
  · intro i hi
    rcases (sc i).mp hi with hi | rfl
    · exact (read i i).mpr (Or.inl (h.refl i hi))
    · exact (tip _).mpr (Or.inl rfl)
  · intro i j l hij hjl
    rcases (sc l).mp (rel.2 j l hjl).2 with hl | rfl
    · have hjl := (old j l hl).mp hjl
      exact (old i l hl).mpr (h.trans i j l ((old i j (h.bound j l hjl).1).mp hij) hjl)
    · rcases (tip j).mp hjl with rfl | hjk
      · exact hij
      · exact (tip i).mpr (Or.inr (h.trans i j k ((old i j (h.bound j k hjk).1).mp hij) hjk))
  · intro i j hij
    rcases (read i j).mp hij with hij | ⟨rfl, rfl | hik⟩
    · exact h.forward i j hij
    · exact Or.inl rfl
    · exact Or.inr (h.bound i k hik).1
  · intro i j l hil hjl
    rcases (sc l).mp (rel.2 i l hil).2 with hl | rfl
    · exact (h.chain i j l ((old i l hl).mp hil) ((old j l hl).mp hjl)).imp
        (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
    · rcases (tip i).mp hil with rfl | hik
      · exact Or.inr hjl
      · rcases (tip j).mp hjl with rfl | hjk
        · exact Or.inl hil
        · exact (h.chain i j k hik hjk).imp (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
  · intro i j hj hs
    rcases (sc j).mp hj with hj | rfl
    · obtain ⟨p, hp, ps⟩ := h.predecessor i j hj hs
      exact ⟨p, hp, fun l => (old l j hj).trans ((ps l).trans (or_congr Iff.rfl (old l p (h.ordinal.transitive j hj p hp)).symm))⟩
    · exact ⟨k, hk, fun l => (tip l).trans (or_congr Iff.rfl (old l k hk).symm)⟩
  · intro δ hδ hl i hi
    have hδα := limit_old δ hδ hl
    obtain ⟨j, hj, hjδ, above⟩ := h.cofinal δ hδα hl i hi
    exact ⟨j, hj, (old j δ hδα).mpr hjδ, above⟩

end YesMetaZFC.SetTheory.LargeCardinal
