import YesMetaZFC.SetTheory.Card.Cofinality.OrderType
import YesMetaZFC.SetTheory.Card.Properties.Basic

/-! # 强极限基数以下的实际幂集大小界 -/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 严格小于一个序数的可良序集合，已有一个严格较小的序数单射界。 -/
theorem ordinal_small_bound_l (hZF : M.Models ZF) {X κ : M.Domain} (hκ : M.IsOrdinal κ)
    (h : M.CardinalLess I X κ) : ∃ μ, M.mem μ κ ∧ M.CardinalLessOrEqual I X μ := by
  obtain ⟨F, hf⟩ := h.1
  obtain ⟨S, hs⟩ := exists_range_of_setFunction hZF I hf.1.1 hf.1.2.1
  have sub : M.MemberSubset S κ := fun y hy => ((hs y).mp hy).elim fun _ hx => hf.1.output_mem_of_pairMember hx
  have bij : M.IsSetBijectionFromTo I F X S := ⟨⟨⟨hf.1.1, hf.1.2.1, fun x hx =>
    (hf.1.2.2 x hx).imp fun y hy => ⟨(hs y).mpr ⟨x, hy.2⟩, hy.2⟩⟩, hf.2⟩,
      fun y hy => ((hs y).mp hy).imp fun x hx => ⟨hf.1.input_mem_of_pairMember hx, hx⟩⟩
  obtain ⟨R, μ, _, ho, ht⟩ := exists_membershipWellOrderType_of_subsetOrdinal hZF I hκ sub
  have hm := ht.isOrdinal hZF I ho
  have eq := (show M.Equinumerous I X S from ⟨F, bij⟩).trans hZF I (ht.equinumerous hZF I ho)
  rcases hm.trichotomy hZF.1 hκ (KP.difference_exists_d (modelsKP hZF))
      (KP.intersection_exists_d (modelsKP hZF) μ κ) with same | hμκ | hκμ
  · exact (h.2 (hZF.1.eq_of_same_members μ κ same ▸ eq)).elim
  · exact ⟨μ, hμκ, eq.elim fun g hg => ⟨g, hg.1⟩⟩
  · obtain ⟨g, hg⟩ := exists_inclusionInjection hZF I (hm.transitive κ hκμ)
    obtain ⟨k, hk⟩ := eq.symm hZF I
    exact (h.2 (equinumerous_of_cardinalLessOrEqual hZF I h.1 (exists_compositionInjection hZF I hg hk.1))).elim

/-- 单射沿直接像诱导幂集间的单射；空集情形不需另选基点。 -/
theorem power_injection_l (hZF : M.Models ZF) {X Y P Q F : M.Domain}
    (hP : M.IsPowerSetOf P X) (hQ : M.IsPowerSetOf Q Y) (hf : M.IsSetInjectionFromTo I F X Y) :
    M.CardinalLessOrEqual I P Q := by
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := .forallE (.iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 2) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 4)))) }
  have sat A B : φ.denote ρ A B ↔ ∀ y, M.mem y B ↔ ∃ x, M.mem x A ∧ M.PairMember I x y F := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  apply exists_setInjectionFromTo_of_denote hZF I φ ρ
  · intro A _
    let ψ : UnarySchema 2 := {
      body := Formula.existsMem (.bound 1) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3)) }
    obtain ⟨B, hb⟩ := separation_exists_d hZF ψ (ρ.push A) Y
    have read y : ψ.denote (ρ.push A) y ↔ ∃ x, M.mem x A ∧ M.PairMember I x y F := by
      simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
    exact ⟨B, (sat A B).mpr fun y => (hb y).trans ((and_congr_right fun _ => read y).trans
      ⟨And.right, fun h => ⟨h.elim fun _ hx => hf.1.output_mem_of_pairMember hx.2, h⟩⟩)⟩
  · intro A _ B C hb hc
    exact hZF.1.eq_of_same_members B C fun y => ((sat A B).mp hb y).trans ((sat A C).mp hc y).symm
  · intro A B _ hb
    exact (hQ B).mpr fun y hy => (((sat A B).mp hb y).mp hy).elim fun _ hx => hf.1.output_mem_of_pairMember hx.2
  · intro A B C ha hb hA hB
    have sub D E (hD : M.MemberSubset D X)
        (d : ∀ y, M.mem y C ↔ ∃ x, M.mem x D ∧ M.PairMember I x y F)
        (e : ∀ y, M.mem y C ↔ ∃ x, M.mem x E ∧ M.PairMember I x y F) : M.MemberSubset D E := by
      intro x hx
      obtain ⟨y, _, hxy⟩ := hf.1.2.2 x (hD x hx)
      obtain ⟨z, hz, hzy⟩ := (e y).mp ((d y).mpr ⟨x, hx, hxy⟩)
      exact hf.2 z x y hzy hxy ▸ hz
    exact hZF.1.eq_of_same_members A B fun x => ⟨sub A B ((hP A).mp ha) ((sat A C).mp hA) ((sat B C).mp hB) x,
      sub B A ((hP B).mp hb) ((sat B C).mp hB) ((sat A C).mp hA) x⟩

theorem strong_power_bound_l (hZF : M.Models ZF) {κ X μ P : M.Domain}
    (hκ : M.IsStrongLimitCardinal I κ) (hμ : M.mem μ κ) (hX : M.CardinalLessOrEqual I X μ)
    (hP : M.IsPowerSetOf P X) : ∃ ν, M.mem ν κ ∧ M.CardinalLessOrEqual I P ν := by
  obtain ⟨Q, hQ⟩ := exists_powerSet hZF μ
  obtain ⟨ν, hν, g, hg⟩ := ordinal_small_bound_l I hZF hκ.1.1 (hκ.2 μ hμ Q hQ)
  obtain ⟨f, hf⟩ := hX
  obtain ⟨k, hk⟩ := power_injection_l I hZF hP hQ hf
  exact ⟨ν, hν, exists_compositionInjection hZF I hk hg⟩

end YesMetaZFC.SetTheory.ZF
