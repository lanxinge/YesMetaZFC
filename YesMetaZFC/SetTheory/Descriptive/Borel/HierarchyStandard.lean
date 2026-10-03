import YesMetaZFC.SetTheory.Descriptive.Borel.StandardRank

/-! # 与通常 Borel 层级递归的对应

可数开闭基把开集规范地写成可数个闭柱集的并。
所以 α > 1 时，Σ⁰α 恰为较低 Π 层的可数并；尤其 Σ⁰₂ 恰为 Fσ。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem open_closed_union_l (hZF : M.Models ZF) {ω X S B K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I S ω) (ho : Open_d S B K) :
    ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → Cl_d S B C := by
  obtain ⟨E, he⟩ := hc
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF B
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω P
  let ρ : Env M 4 := (((⟨fun _ => S, fun _ => S⟩ : Env M 1).push E).push B).push K
  let φ : BinarySchema 4 := { body := Formula.existsMem (.bound 5) (.conj
    (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 5)) (.conj
    (bcover_m (.bound 4) (.bound 3) .newest) (cyl_m (.bound 4) .newest (.bound 1)))) }
  have ep i C : φ.denote ρ i C ↔ ∃ s, M.mem s S ∧ M.PairMember I s i E ∧ Bcover_d B K s ∧ Cyl_d B s C := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, bcover_sat_l, cyl_sat_l]; rfl
  obtain ⟨H, hh, eh⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair i C : M.PairMember I i C H ↔ ∃ s, M.mem s S ∧ M.PairMember I s i E ∧ Bcover_d B K s ∧ Cyl_d B s C := by
    refine ((eh i C).trans (and_congr_right fun _ => and_congr_right fun _ => ep i C)).trans ⟨fun h => h.2.2, ?_⟩
    rintro ⟨s, hs, hi, hk, hC⟩
    exact ⟨(hw i).mpr (Or.inl (he.1.output_mem_of_pairMember hi)),
      (hw C).mpr (Or.inr ((hp C).mpr (fun x hx => ((hC x).mp hx).1))), s, hs, hi, hk, hC⟩
  refine ⟨H, ⟨⟨hh.1, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro i C D hc hd
    obtain ⟨s, _, hi, _, hC⟩ := (pair i C).mp hc
    obtain ⟨t, _, hj, _, hD⟩ := (pair i D).mp hd
    have e := he.2 t s i hj hi
    exact hZF.1.eq_of_same_members C D (fun x => (hC x).trans (e ▸ hD x).symm)
  · intro i C h
    obtain ⟨_, _, hi, _, _⟩ := (pair i C).mp h
    exact he.1.output_mem_of_pairMember hi
  · intro x
    constructor
    · intro hx
      obtain ⟨s, hs, sub, cover⟩ := ho.2 x hx
      obtain ⟨C, hC⟩ := cyl_exists_l (ZF.modelsKP hZF) B s
      obtain ⟨i, _, hi⟩ := he.1.2.2 s hs
      exact ⟨i, C, (pair i C).mpr ⟨s, hs, hi, cover, hC⟩, (hC x).mpr ⟨ho.1 x hx, sub⟩⟩
    · rintro ⟨i, C, hi, hx⟩
      obtain ⟨s, _, _, cover, hC⟩ := (pair i C).mp hi
      exact cover x ((hC x).mp hx).1 ((hC x).mp hx).2
  · intro i C hi
    obtain ⟨s, hs, _, _, hC⟩ := (pair i C).mp hi
    obtain ⟨ho, hc⟩ := ds_cyl_clopen_l I hZF hω hB hS hs hC
    exact ⟨ho.1, hc⟩

/-- 正序数大于一时的标准递归方程；包括内部极限序数。 -/
theorem bsig_standard_l (hZF : M.Models ZF) {ω X S B o α K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I S ω) (ho : M.IsOrdinalOne o) (hα : M.IsOrdinal α) (hoα : M.mem o α) :
    Bsig_d I ω S B α K ↔ ∃ H, Bu_d I ω H K ∧
      ∀ i C, M.PairMember I i C H → ∃ β, M.mem β α ∧ Bpi_d I ω S B β C := by
  constructor
  · intro h
    obtain ⟨_, _, hopen | h⟩ := (bsig_unfold_l I hZF hα).mp h
    · obtain ⟨H, hu, eh⟩ := open_closed_union_l I hZF hω hB hS hc hopen
      exact ⟨H, hu, fun i C hi => ⟨o, hoα, (bpi_one_l I hZF ho).mpr (eh i C hi)⟩⟩
    · exact h
  · exact fun ⟨H, hu, eh⟩ => bsig_union_l I hZF hα ⟨o, hoα⟩ hu eh

theorem bsig_two_l (hZF : M.Models ZF) {ω X S B o t K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I S ω) (ho : M.IsOrdinalOne o) (ht : M.SuccessorOf t o) :
    Bsig_d I ω S B t K ↔ ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → Cl_d S B C := by
  have htord := KP.successor_isOrdinal (ZF.modelsKP hZF) (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) ho) ht
  refine (bsig_standard_l I hZF hω hB hS hc ho htord ht.predecessor_mem).trans (exists_congr fun H => and_congr_right fun _ =>
    forall_congr' fun i => forall_congr' fun C => imp_congr_right fun _ => ⟨?_, ?_⟩)
  · rintro ⟨β, hb, hpi⟩
    rcases (ht β).mp hb with hb | hb
    · obtain ⟨z, hz, hs⟩ := ho
      rcases (hs β).mp hb with hb | hb
      · exact (hz β hb).elim
      · obtain ⟨L, hl, _⟩ := hpi
        obtain ⟨γ, hγ⟩ := bsig_nonempty_l I hl
        exact (hz γ (hZF.1.eq_of_same_members β z hb ▸ hγ)).elim
    · exact (bpi_one_l I hZF ho).mp (hZF.1.eq_of_same_members β o hb ▸ hpi)
  · exact fun h => ⟨o, ht.predecessor_mem, (bpi_one_l I hZF ho).mpr h⟩

end YesMetaZFC.SetTheory.Descriptive
