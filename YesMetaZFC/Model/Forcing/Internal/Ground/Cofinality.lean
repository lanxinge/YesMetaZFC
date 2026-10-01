import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.SetTheory.Card.Cofinality.Countable

/-! # 旧集合嵌入下的序数反射与共尾集保持

成员完全的单射可将目标的序数良序性回拉到所有旧子集；正向良序性使用目标基础公理。
共尾集的传输只核验极限性、包含及并集，不预设任何共尾度保持。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include hi he

theorem image_ordinal_reflect_l (hEN : Extensional N) {α} (hα : N.IsOrdinal (e α)) : M.IsOrdinal α := by
  have eq {a b} (h : N.SameMembers (e a) (e b)) : M.SameMembers a b := by
    have h := hi (hEN.eq_of_same_members (e a) (e b) h)
    exact h ▸ fun _ => Iff.rfl
  have mem {a b} := image_member_l e hi he (a := a) (b := b)
  refine ⟨fun x hx y hy => mem.mp (hα.transitive (e x) (mem.mpr hx) (e y) (mem.mpr hy)), ⟨?_, ?_⟩⟩
  · refine ⟨fun x hx hxx => hα.wellOrder.linear.irrefl (e x) (mem.mpr hx) (mem.mpr hxx),
      fun x hx y hy z hz hxy hyz => mem.mp (hα.wellOrder.linear.trans (e x) (mem.mpr hx)
        (e y) (mem.mpr hy) (e z) (mem.mpr hz) (mem.mpr hxy) (mem.mpr hyz)), ?_⟩
    intro x hx y hy
    rcases hα.wellOrder.linear.compare (e x) (mem.mpr hx) (e y) (mem.mpr hy) with h | h | h
    · exact Or.inl (eq h)
    · exact Or.inr (Or.inl (mem.mp h))
    · exact Or.inr (Or.inr (mem.mp h))
  · intro X hX hn
    obtain ⟨x, hx⟩ := hn
    obtain ⟨y, hy, hm⟩ := hα.wellOrder.least (e X) (by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := (he X y).mp hy
      exact mem.mpr (hX a ha)) ⟨e x, mem.mpr hx⟩
    obtain ⟨a, ha, rfl⟩ := (he X y).mp hy
    exact ⟨a, ha, fun b hb => (hm (e b) (mem.mpr hb)).elim (fun h => Or.inl (eq h)) (fun h => Or.inr (mem.mp h))⟩

theorem image_cofinal_subset_l (hEM : Extensional M)
    (hF : ∀ X, (∃ x, N.mem x X) → ∃ x, N.mem x X ∧ ∀ y, N.mem y X → ¬ N.mem y x)
    {A α} (hA : M.IsCofinalSubset A α) : N.IsCofinalSubset (e A) (e α) := by
  have mem {a b} := image_member_l e hi he (a := a) (b := b)
  have hα := image_ordinal_l e hi he hEM hF hA.1.1
  refine ⟨⟨hα, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hA.1.2.1
    exact ⟨e x, mem.mpr hx⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (he α y).mp hy
    obtain ⟨z, hz, hxz⟩ := hA.1.2.2 x hx
    exact ⟨e z, mem.mpr hz, mem.mpr hxz⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (he A y).mp hy
    exact mem.mpr (hA.2.1 x hx)
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := (he α y).mp hy
      obtain ⟨z, hz, hxz⟩ := (hA.2.2 x).mp hx
      exact ⟨e z, mem.mpr hz, mem.mpr hxz⟩
    · rintro ⟨z, hz, hyz⟩
      obtain ⟨a, ha, rfl⟩ := (he A z).mp hz
      exact hα.transitive (e a) (mem.mpr (hA.2.1 a ha)) y hyz

end YesMetaZFC.Model.Forcing.Internal
