import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion

/-! # 满射沿内部有限列的提升

有限多个非空纤维可逐项选择；证明在实际可分离公式上作内部 ω 归纳，故只需 ZF，
且不要求序列在外部有限。此接口用于泛型求值图上的名称参数回拉。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 内部有限列沿实际满射提升，同时保留全部坐标的交换方程。 -/
theorem fseq_lift_l (hZF : M.Models ZF) {ω X Y F n s} (hω : M.IsOmega ω)
    (hF : M.IsSetSurjectiveOnto I F X Y) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n Y) :
    ∃ t, M.IsSetFunctionFromTo I t n X ∧ ∀ i x y,
      M.PairMember I i x t → M.PairMember I i y s → M.PairMember I x y F := by
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push X).push Y
  let φ : UnarySchema 3 := { body := .forallE (.imp
    (Formula.isFunctionFromTo 𝒞 .newest (.bound 1) (.bound 2)) (.existsE (.conj
      (Formula.isFunctionFromTo 𝒞 .newest (.bound 2) (.bound 4))
      (.forallE (.forallE (.forallE (.imp
        (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 3)) (.imp
          (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 4))
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 8)))))))))) }
  have hφ n : φ.denote ρ n ↔ ∀ s, M.IsSetFunctionFromTo I s n Y →
      ∃ t, M.IsSetFunctionFromTo I t n X ∧ ∀ i x y,
        M.PairMember I i x t → M.PairMember I i y s → M.PairMember I x y F := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  apply hω.induction (fun n => ∀ s, M.IsSetFunctionFromTo I s n Y →
    ∃ t, M.IsSetFunctionFromTo I t n X ∧ ∀ i x y,
      M.PairMember I i x t → M.PairMember I i y s → M.PairMember I x y F) ?_ ?_ ?_ n hn s hs
  · obtain ⟨D, hD⟩ := separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
  · intro e he s hs
    exact ⟨s, ⟨hs.1, hs.2.1, fun i hi => (he i hi).elim⟩,
      fun i _ _ hi _ => (he i (hs.input_mem_of_pairMember hi)).elim⟩
  · intro m hm ih n hn s hs
    obtain ⟨r, hr⟩ := exists_restriction hZF I s m
    have hrY := hr.isSetFunctionFromTo hs (fun i hi => (hn i).mpr (Or.inl hi))
    obtain ⟨t, ht, hc⟩ := ih r hrY
    obtain ⟨y, hy, hsy⟩ := hs.2.2 m hn.predecessor_mem
    obtain ⟨x, hx, hxy⟩ := hF y hy
    obtain ⟨v, hv, hvt⟩ := Structure.IsSequenceOfLength.exists_append (value := x)
      (modelsKP hZF) I ⟨(hω.isOrdinal hZF).mem hm, ht.1, ht.2.1⟩
      (KP.successor_isOrdinal (modelsKP hZF) ((hω.isOrdinal hZF).mem hm) hn) hn
    refine ⟨v, ⟨hv.2.1, hv.2.2, fun i hi => ?_⟩, fun i a b ha hb => ?_⟩
    · obtain ⟨a, ha⟩ := (hv.2.2 i).mp hi
      refine ⟨a, ?_, ha⟩
      rcases (hvt i a).mp ha with ha | ⟨_, rfl⟩
      · exact ht.output_mem_of_pairMember ha
      · exact hx
    · rcases (hvt i a).mp ha with ha | ⟨rfl, rfl⟩
      · exact hc i a b ha ((hr.2 i b).mpr ⟨ht.input_mem_of_pairMember ha, hb⟩)
      · exact hs.1.2 _ y b hsy hb ▸ hxy

end YesMetaZFC.SetTheory.ZF
