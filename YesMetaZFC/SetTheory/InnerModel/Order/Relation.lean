import YesMetaZFC.SetTheory.InnerModel.Order.Tuple

/-! # 有界关系的实际集合表及良序接口 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_rel_d (r : M.Domain → M.Domain → Prop) (X S : M.Domain) : Prop :=
  ∀ p, M.mem p S ↔ ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧ KPair_d M p x y ∧ r x y

def Rw_bound_d (U R : M.Domain) : Prop :=
  ∀ p, M.mem p R → ∃ x, M.mem x U ∧ ∃ y, M.mem y U ∧ KPair_d M p x y
theorem Rw_bound_d.entry_l {U R : M.Domain} (h : Rw_bound_d U R) {x y} (he : Rd_entry_d x y R) :
    M.mem x U ∧ M.mem y U := by
  obtain ⟨p, hp, hpR⟩ := he
  obtain ⟨a, ha, b, hb, hq⟩ := h p hpR
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hq hp
  exact ⟨ha, hb⟩
theorem Rw_rel_d.bounded_l {r : M.Domain → M.Domain → Prop} {U R} (h : Rw_rel_d r U R) : Rw_bound_d U R := by
  intro p hp
  obtain ⟨x, hx, y, hy, hp, _⟩ := (h p).mp hp
  exact ⟨x, hx, y, hy, hp⟩

theorem Rw_rel_d.congr_l {r s : M.Domain → M.Domain → Prop} {X S : M.Domain}
    (h : Rw_rel_d r X S) (he : ∀ x y, r x y ↔ s x y) : Rw_rel_d s X S := fun p =>
  (h p).trans (exists_congr fun x => and_congr_right fun _ => exists_congr fun y =>
    and_congr_right fun _ => and_congr_right fun _ => he x y)

def rw_slice_s {n} (φ : Delta0BinarySchema n) : Delta0UnarySchema (n + 1) where
  body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
    (.conj (kpair0_m (.bound 2) (.bound 1) .newest)
      (binary_pred_m φ.toBinarySchema (fun i => .bound ⟨i.val + 4, by omega⟩) (.bound 1) .newest)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (φ.delta0.bind_l _)))

theorem rw_slice_sat_l (hE : Extensional M) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (X p : M.Domain) :
    Formula.satisfies ((ρ.push X).push p) (rw_slice_s φ).body ↔
      ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧ KPair_d M p x y ∧ φ.toBinarySchema.denote ρ x y := by
  simp only [rw_slice_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, binary_pred_sat_l]; rfl

theorem rw_rel_exists_l (hKP : M.Models KP) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (X : M.Domain) :
    ∃ S, Rw_rel_d (φ.toBinarySchema.denote ρ) X S := by
  obtain ⟨P, hp⟩ := KP.kprod_exists_l hKP X X
  obtain ⟨S, hs⟩ := KP.separation_exists_d hKP (rw_slice_s φ) (ρ.push X) P
  refine ⟨S, fun p => ?_⟩
  rw [hs p, rw_slice_sat_l hKP.1]
  exact ⟨And.right, fun h => ⟨h.elim (fun x hx => hx.2.elim (fun y hy => (hp p).mpr ⟨x, hx.1, y, hy.1, hy.2.1⟩)), h⟩⟩

theorem Rw_rel_d.entry_l (hKP : M.Models KP) {r : M.Domain → M.Domain → Prop} {X S x y : M.Domain} (hs : Rw_rel_d r X S) :
    Rd_entry_d x y S ↔ M.mem x X ∧ M.mem y X ∧ r x y := by
  constructor
  · rintro ⟨p, hp, hpS⟩
    obtain ⟨a, ha, b, hb, he, h⟩ := (hs p).mp hpS
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M he hp
    exact ⟨ha, hb, h⟩
  · rintro ⟨hx, hy, h⟩
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total x y
    exact ⟨p, hp, (hs p).mpr ⟨x, hx, y, hy, hp, h⟩⟩

theorem Rw_rel_d.unique_l (hE : Extensional M) {r : M.Domain → M.Domain → Prop} {X S T : M.Domain}
    (hs : Rw_rel_d r X S) (ht : Rw_rel_d r X T) : S = T := hE.eq_of_same_members S T (fun p => (hs p).trans (ht p).symm)

theorem Rw_rel_d.wellorder_l (hKP : M.Models KP) {r : M.Domain → M.Domain → Prop} {X S : M.Domain}
    (hs : Rw_rel_d r X S) (hi : ∀ x, M.mem x X → ¬ r x x)
    (ht : ∀ x, M.mem x X → ∀ y, M.mem y X → ∀ z, M.mem z X → r x y → r y z → r x z)
    (hc : ∀ x, M.mem x X → ∀ y, M.mem y X → x = y ∨ r x y ∨ r y x)
    (hm : ∀ Y, M.MemberSubset Y X → (∃ y, M.mem y Y) → Po_min_d r Y) :
    M.IsSetCodedWellOrder (kp_pair_l hKP) S X := by
  have entry x y : M.PairMember (kp_pair_l hKP) x y S ↔ M.mem x X ∧ M.mem y X ∧ r x y := hs.entry_l hKP
  refine ⟨⟨?_, ⟨fun x hx h => hi x hx ((entry x x).mp h).2.2, ?_⟩, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, _, y, _, hp, _⟩ := (hs p).mp hp
    exact ⟨x, y, hp⟩
  · intro x hx y hy z hz h g
    exact (entry x z).mpr ⟨hx, hz, ht x hx y hy z hz ((entry x y).mp h).2.2 ((entry y z).mp g).2.2⟩
  · intro x hx y hy
    exact (hc x hx y hy).elim (fun he => Or.inl (he ▸ (fun _ => Iff.rfl))) (fun h =>
      h.elim (fun h => Or.inr (Or.inl ((entry x y).mpr ⟨hx, hy, h⟩))) (fun h => Or.inr (Or.inr ((entry y x).mpr ⟨hy, hx, h⟩))))
  · intro Y hy hn
    obtain ⟨x, hx, h⟩ := hm Y hy hn
    exact ⟨x, hx, fun y hyy => (h y hyy).elim (fun he => Or.inl (he ▸ (fun _ => Iff.rfl)))
      (fun he => Or.inr ((entry x y).mpr ⟨hy x hx, hy y hyy, he⟩))⟩

end YesMetaZFC.SetTheory.InnerModel
