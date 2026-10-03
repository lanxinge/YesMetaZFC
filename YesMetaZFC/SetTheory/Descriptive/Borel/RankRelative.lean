import YesMetaZFC.SetTheory.Descriptive.Borel.HierarchyStandard
import YesMetaZFC.SetTheory.Descriptive.Trace

/-! # 标准 Borel 层级与秩的子空间限制

内部可数族逐项取迹有唯一实际函数图。沿内部序数归纳得到 Σ、Π 不升层，
故子空间中的标准秩不超过原秩；子空间无需闭、解析或有任何额外选择性质。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bu_trace_l (hZF : M.Models ZF) {ω X H K L} (hu : Bu_d I ω H K) (ht : Tr_d X K L) :
    ∃ G, Bu_d I ω G L ∧ ∀ i D, M.PairMember I i D G ↔ ∃ C, M.PairMember I i C H ∧ Tr_d X C D := by
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF X
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω P
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push H
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (tr_m (.bound 4) .newest (.bound 1))) }
  have ep i D : φ.denote ρ i D ↔ ∃ C, M.PairMember I i C H ∧ Tr_d X C D := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, tr_sat_l]; rfl
  obtain ⟨G, hg, eg⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair i D : M.PairMember I i D G ↔ ∃ C, M.PairMember I i C H ∧ Tr_d X C D := by
    refine ((eg i D).trans (and_congr_right fun _ => and_congr_right fun _ => ep i D)).trans ⟨fun h => h.2.2, ?_⟩
    rintro ⟨C, hi, hd⟩
    exact ⟨(hw i).mpr (Or.inl (hu.2.1 i C hi)), (hw D).mpr (Or.inr ((hp D).mpr (fun x hx => ((hd x).mp hx).1))), C, hi, hd⟩
  refine ⟨G, ⟨⟨hg.1, ?_⟩, ?_, ?_⟩, pair⟩
  · intro i C D hc hd
    obtain ⟨V, hi, hv⟩ := (pair i C).mp hc
    obtain ⟨U, hj, hw⟩ := (pair i D).mp hd
    exact tr_unique_l hZF.1 hv (hu.1.2 i U V hj hi ▸ hw)
  · intro i D hd
    obtain ⟨C, hi, _⟩ := (pair i D).mp hd
    exact hu.2.1 i C hi
  · intro x
    constructor
    · intro hx
      obtain ⟨hxX, hxK⟩ := (ht x).mp hx
      obtain ⟨i, C, hi, hxC⟩ := (hu.2.2 x).mp hxK
      obtain ⟨D, hd⟩ := tr_exists_l (ZF.modelsKP hZF) X C
      exact ⟨i, D, (pair i D).mpr ⟨C, hi, hd⟩, (hd x).mpr ⟨hxX, hxC⟩⟩
    · rintro ⟨i, D, hi, hx⟩
      obtain ⟨C, hi, hd⟩ := (pair i D).mp hi
      obtain ⟨hxX, hxC⟩ := (hd x).mp hx
      exact (ht x).mpr ⟨hxX, (hu.2.2 x).mpr ⟨i, C, hi, hxC⟩⟩

theorem bh_trace_l (hZF : M.Models ZF) {ω S B X α} (hX : M.MemberSubset X B) (hα : M.IsOrdinal α) :
    ∀ K L, Tr_d X K L →
      (Bsig_d I ω S B α K → Bsig_d I ω S X α L) ∧
      (Bpi_d I ω S B α K → Bpi_d I ω S X α L) := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push S).push B).push X
  let φ : UnarySchema 4 := { body := .forallE (.forallE (.imp (tr_m (.bound 3) (.bound 1) .newest) (.conj
    (.imp (bsig_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 1))
      (bsig_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 3) (.bound 2) .newest))
    (.imp (bpi_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 1))
      (bpi_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 3) (.bound 2) .newest))))) }
  have ep β : φ.denote ρ β ↔ ∀ K L, Tr_d X K L →
      (Bsig_d I ω S B β K → Bsig_d I ω S X β L) ∧ (Bpi_d I ω S B β K → Bpi_d I ω S X β L) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      tr_sat_l, Formula.satisfies_conj_iff, bsig_sat_l I hZF.1, bpi_sat_l I hZF.1]; rfl
  apply (ep α).mp
  apply hα.induction (φ.denote ρ)
  · obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF φ.neg ρ α
    exact ⟨C, fun β => by simpa only [UnarySchema.neg, UnarySchema.denote, Formula.satisfies_neg_iff] using hc β⟩
  · intro β hβ ih
    have sig K L (ht : Tr_d X K L) (hs : Bsig_d I ω S B β K) : Bsig_d I ω S X β L := by
      obtain ⟨_, ne, ho | ⟨H, hu, eh⟩⟩ := (bsig_unfold_l I hZF hβ).mp hs
      · apply bsig_open_l I hZF hβ ne
        refine ⟨fun x hx => ((ht x).mp hx).1, fun x hx => ?_⟩
        obtain ⟨s, hs, sub, cover⟩ := ho.2 x ((ht x).mp hx).2
        exact ⟨s, hs, sub, fun y hy hsy => (ht y).mpr ⟨hy, cover y (hX y hy) hsy⟩⟩
      · obtain ⟨G, hg, eg⟩ := bu_trace_l I hZF hu ht
        apply bsig_union_l I hZF hβ ne hg
        intro i D hi
        obtain ⟨C, hc, tr⟩ := (eg i D).mp hi
        obtain ⟨γ, hγ, hpi⟩ := eh i C hc
        exact ⟨γ, hγ, ((ep γ).mp (ih γ hγ) C D tr).2 hpi⟩
    apply (ep β).mpr
    intro K L ht
    refine ⟨sig K L ht, fun ⟨C, hc, cm⟩ => ?_⟩
    obtain ⟨D, hd⟩ := tr_exists_l (ZF.modelsKP hZF) X C
    exact ⟨D, sig C D hd hc, tr_compl_l hX cm hd ht⟩

theorem bsr_trace_l (hZF : M.Models ZF) {ω S B X K L α} (hX : M.MemberSubset X B)
    (ht : Tr_d X K L) (hr : Bsr_d I ω S B K α) :
    ∃ β, Bsr_d I ω S X L β ∧ M.MemberSubset β α := by
  have tr := bh_trace_l I hZF (ω := ω) (S := S) hX (blev_ordinal_l I hr.1) K L ht
  exact bsr_min_l I hZF (hr.1.elim (fun h => Or.inl (tr.1 h)) (fun h => Or.inr (tr.2 h)))

/-- 一个码在任意内部子空间的解释同样具有唯一的内部可数标准秩。 -/
theorem bsr_relative_exists_l (hZF : M.Models ZF) {ω D A S B X K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω D) (hS : Fseq_space_d I ω D S)
    (hc : M.CardinalLessOrEqual I A ω) (hX : M.MemberSubset X B) (hK : Borel_d I ω A S X K) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsr_d I ω S X K α ∧
      ∀ β, Bsr_d I ω S X K β → β = α := by
  obtain ⟨c, code, den⟩ := hK
  obtain ⟨C, hcC, _⟩ := bden_exists_unique_l I hZF ω A S B c
  have tr : Tr_d X C K := by
    intro x
    exact (den x).trans (and_congr_right fun hx =>
      ⟨fun h => (hcC x).mpr ⟨hX x hx, h⟩, fun h => ((hcC x).mp h).2⟩)
  obtain ⟨β, _, ⟨E, he⟩, hb, _⟩ := bsr_exists_l I hZF hω hB hS hc ⟨c, code, hcC⟩
  obtain ⟨α, ha, sub⟩ := bsr_trace_l I hZF hX tr hb
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I sub
  exact ⟨α, blev_ordinal_l I ha.1, ZF.exists_compositionInjection hZF I hd he, ha, fun β h => bsr_unique_l I hZF.1 h ha⟩

end YesMetaZFC.SetTheory.Descriptive
