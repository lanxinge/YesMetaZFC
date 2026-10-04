import YesMetaZFC.SetTheory.Card.PowerBound
import YesMetaZFC.SetTheory.Card.OrdinalCardinality
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 小集合的最小序数枚举

从实际单射界取像的序型，再取其初始序数；所有枚举图由已有双射复合构造。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem small_enumeration_l (hZF : M.Models ZF) {δ X ξ : M.Domain} (hδ : M.IsCardinal I δ)
    (hξ : M.mem ξ δ) (hX : M.CardinalLessOrEqual I X ξ) : ∃ μ g,
      M.mem μ δ ∧ M.IsCardinal I μ ∧ M.IsSetBijectionFromTo I g μ X := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨S, hs⟩ := exists_range_of_setFunction hZF I hf.1.1 hf.1.2.1
  have sub : M.MemberSubset S ξ := fun y hy => ((hs y).mp hy).elim fun _ hx => hf.1.output_mem_of_pairMember hx
  have bij : M.IsSetBijectionFromTo I f X S := ⟨⟨⟨hf.1.1, hf.1.2.1, fun x hx =>
    (hf.1.2.2 x hx).imp fun y hy => ⟨(hs y).mpr ⟨x, hy.2⟩, hy.2⟩⟩, hf.2⟩,
      fun y hy => ((hs y).mp hy).imp fun x hx => ⟨hf.1.input_mem_of_pairMember hx, hx⟩⟩
  obtain ⟨R, θ, _, ho, ht⟩ := exists_membershipWellOrderType_of_subsetOrdinal hZF I (hδ.1.mem hξ) sub
  obtain ⟨μ, hμ, _⟩ := ordinalCardinal_existsUnique hZF I (ht.isOrdinal hZF I ho)
  have eq := (show M.Equinumerous I X S from ⟨f, bij⟩).trans hZF I
    ((ht.equinumerous hZF I ho).trans hZF I (hμ.2.symm hZF I))
  obtain ⟨g, hg⟩ := eq.symm hZF I
  have μξ := exists_compositionInjection hZF I hg.1 hf
  have bound : M.mem μ δ := by
    rcases hμ.1.1.trichotomy hZF.1 (hδ.1.mem hξ) (KP.difference_exists_d (modelsKP hZF))
      (KP.intersection_exists_d (modelsKP hZF) μ ξ) with same | hμξ | hξμ
    · exact (hZF.1.eq_of_same_members μ ξ same).symm ▸ hξ
    · exact hδ.1.transitive ξ hξ μ hμξ
    · obtain ⟨k, hk⟩ := exists_inclusionInjection hZF I (hμ.1.1.transitive ξ hξμ)
      exact (hμ.1.2 ξ hξμ (equinumerous_of_cardinalLessOrEqual hZF I ⟨k, hk⟩ μξ)).elim
  exact ⟨μ, g, bound, hμ.1, hg⟩

theorem enumeration_minimal_l (hZF : M.Models ZF) {μ X g ν f : M.Domain}
    (hμ : M.IsCardinal I μ) (hg : M.IsSetBijectionFromTo I g μ X) (hν : M.IsOrdinal ν)
    (hf : M.IsSetFunctionFromTo I f ν X) (onto : M.IsSetSurjectiveOnto I f ν X) : M.MemberSubset μ ν := by
  obtain ⟨id, hid⟩ := exists_identityBijection hZF I ν
  obtain ⟨k, hk⟩ := ordinal_image_bound_l I hZF hν ⟨id, hid.1⟩ hf onto
  have μν := exists_compositionInjection hZF I hg.1 hk
  rcases hμ.1.trichotomy hZF.1 hν (KP.difference_exists_d (modelsKP hZF))
    (KP.intersection_exists_d (modelsKP hZF) μ ν) with same | hμν | hνμ
  · exact fun x hx => (same x).mp hx
  · exact hν.transitive μ hμν
  · obtain ⟨e, he⟩ := exists_inclusionInjection hZF I (hμ.1.transitive ν hνμ)
    exact (hμ.2 ν hνμ (equinumerous_of_cardinalLessOrEqual hZF I ⟨e, he⟩ μν)).elim

end YesMetaZFC.SetTheory.ZF
