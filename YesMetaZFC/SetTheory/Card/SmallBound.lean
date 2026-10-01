import YesMetaZFC.SetTheory.Card.Cofinality.Boundedness
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication
import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.FunctionRetraction

/-! # 序数内的小基数公共界

有限多个小序数由同一个更低的无限基数控制。共尾度的有界性直接消费单射界，
避免要求调用者额外构造集合的基数代表。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem common_cardinal_l (hZF : M.Models ZF) {ω κ a b}
    (hκ : M.IsOrdinal κ) (hωκ : M.mem ω κ) (ha : M.mem a κ) (hb : M.mem b κ) :
    ∃ ν, M.mem ν κ ∧ M.IsInfiniteCardinal I ω ν ∧
      M.CardinalLessOrEqual I a ν ∧ M.CardinalLessOrEqual I b ν := by
  have merge {a b} (ha : M.mem a κ) (hb : M.mem b κ) :
      ∃ c, M.mem c κ ∧ M.MemberSubset a c ∧ M.MemberSubset b c := by
    rcases hκ.wellOrder.linear.compare a ha b hb with he | hab | hba
    · exact ⟨b, hb, fun x hx => (he x).mp hx, fun _ h => h⟩
    · exact ⟨b, hb, (hκ.mem hb).transitive.memberSubset hab, fun _ h => h⟩
    · exact ⟨a, ha, fun _ h => h, (hκ.mem ha).transitive.memberSubset hba⟩
  obtain ⟨c, hc, hac, hbc⟩ := merge ha hb
  obtain ⟨d, hd, hcd, hωd⟩ := merge hc hωκ
  obtain ⟨ν, hν, _⟩ := ordinalCardinal_existsUnique hZF I (hκ.mem hd)
  have hνκ : M.mem ν κ := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 hν.1.1 (hκ.mem hd)
        (KP.difference_exists_d (modelsKP hZF)) (KP.intersection_exists_d (modelsKP hZF) ν d) with he | hνd | hdν
    · exact (hZF.1.eq_of_same_members ν d he).symm ▸ hd
    · exact hκ.transitive d hd ν hνd
    · exact (hν.1.2 d hdν (hν.2.symm hZF I)).elim
  obtain ⟨F, hF⟩ := hν.2.symm hZF I
  have bound {x} (hx : M.MemberSubset x d) : M.CardinalLessOrEqual I x ν := by
    obtain ⟨G, hG⟩ := exists_inclusionInjection hZF I hx
    exact exists_compositionInjection hZF I hG hF.1
  exact ⟨ν, hνκ, ⟨hν.1, bound hωd⟩, bound (fun x hx => hcd x (hac x hx)), bound (fun x hx => hcd x (hbc x hx))⟩

/-- 小于共尾度的单射大小界已经足以推出序数子集有界。 -/
theorem small_subset_bounded_l (hZF : M.Models ZF) {κ cf Y μ}
    (hcf : M.IsCofinality I cf κ) (hY : M.MemberSubset Y κ)
    (hμ : M.mem μ cf) (hy : M.CardinalLessOrEqual I Y μ) : M.IsBoundedSubsetOfOrdinal Y κ := by
  obtain ⟨G, hG⟩ := hy
  obtain ⟨Q, hQ⟩ := hcf.hasCofinalSequence
  obtain ⟨a, ha⟩ := hQ.isLimitOrdinal.2.1
  obtain ⟨F, hF, hf⟩ := injection_retract_l I hZF hG hY ha
  obtain ⟨D, hD⟩ := exists_range_of_setFunction hZF I hF.1 hF.2.1
  obtain ⟨b, hb, hDb⟩ := (hcf.range_bounded_of_domain_mem hZF I hμ hF hD).exists_bound
  refine ⟨hQ.isLimitOrdinal.1, hY, b, hb, fun y hy => ?_⟩
  obtain ⟨i, _, hiy⟩ := hG.1.2.2 y hy
  exact hDb y ((hD y).mpr ⟨i, hf y i hiy⟩)

end YesMetaZFC.SetTheory.ZF
