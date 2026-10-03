import YesMetaZFC.SetTheory.Descriptive.Projective.CountableStep

/-! # 可数实数行族的 Borel 初始矩阵 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem array_base_l (hZF : M.Models ZF) {ω A B J H z} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hH : Bfam_d I ω A A H) (hz : ∀ x, ¬ M.mem x z) (b : Bool) :
    ∃ c, Bcode_d I ω A A c ∧ ∀ w, M.mem w B → (Bsat_d I ω A A c w ↔ Aw_d I b ω A B J z H w) := by
  obtain ⟨E, he⟩ := ha
  obtain ⟨D, _, hD⟩ := family_domain_l I hZF (fun i c hc => (hH.2 i c hc).1)
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push H).push E
  let φ : BinarySchema 6 := { body := .existsE (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 5)) (.conj
    (rmap_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 3) .newest)
    (bpull_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 4) .newest (.bound 1) (.bound 2))))) }
  have hp i d : φ.denote ρ i d ↔ ∃ c f, M.PairMember I i c H ∧ Rmap_d I B J i f ∧ Bpull_d I ω A E f c d := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rmap_sat_l I hZF.1, bpull_sat_l I hZF.1]; rfl
  have total i (hi : M.mem i D) : ∃ d, φ.denote ρ i d := by
    obtain ⟨c, hc⟩ := (hD i).mp hi
    obtain ⟨f, hf, _⟩ := rmap_exists_l I hZF hB hA hJ (hH.2 i c hc).1
    obtain ⟨d, hd, _⟩ := bpull_exists_l I hZF (f := f) hB.1 hA he (hH.2 i c hc).2
    exact ⟨d, (hp i d).mpr ⟨c, f, hc, hf, hd⟩⟩
  have unique i (_ : M.mem i D) d e (hd : φ.denote ρ i d) (he' : φ.denote ρ i e) : d = e := by
    obtain ⟨c, f, hc, hf, hd⟩ := (hp i d).mp hd
    obtain ⟨c', f', hc', hf', he'⟩ := (hp i e).mp he'
    exact bpull_unique_l I hZF.1 hd (hH.1.2 i c' c hc' hc ▸ rmap_unique_l I hZF.1 hf' hf ▸ he')
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ ρ D total unique
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun i d hi hd => (hC d).mpr ⟨i, hi, hd⟩)
  have data i d (hd : M.PairMember I i d G) : ∃ c f, M.PairMember I i c H ∧
      Rmap_d I B J i f ∧ Bpull_d I ω A E f c d := (hp i d).mp ((eg i d).mp hd).2
  have fam : Bfam_d I ω A A G := by
    refine ⟨hg.1, fun i d hd => ?_⟩
    obtain ⟨c, f, hc, _, hcd⟩ := data i d hd
    obtain ⟨e, he', hec⟩ := bpull_exists_l I hZF (f := f) hB.1 hA he (hH.2 i c hc).2
    exact ⟨(hH.2 i c hc).1, bpull_unique_l I hZF.1 he' hcd ▸ hec⟩
  have value i c d w x (hc : M.PairMember I i c H) (hd : M.PairMember I i d G)
      (hw : M.mem w B) (hr : Row_d I J i w x) : Bsat_d I ω A A d w ↔ Pm_d I ω A B J z c x := by
    obtain ⟨c', f, hc', hf, hcd⟩ := data i d hd
    have ec := hH.1.2 i c' c hc' hc
    subst c'
    obtain ⟨f', hf', hfC⟩ := rmap_exists_l I hZF hB hA hJ (hH.2 i c hc).1
    have e := rmap_unique_l I hZF.1 hf' hf
    subst f'
    have hx := row_mem_l I hZF hB hJ (hH.2 i c hc).1 hw hr
    exact (bpull_correct_l I hZF hB.1 hA he hfC (hH.2 i c hc).2 hcd w x ((hf.2 w x).mpr ⟨hw, hr⟩)).trans
      ((pm_zero_l I hZF hB.1 hz).trans ⟨And.right, fun h => ⟨hx, h⟩⟩).symm
  cases b
  · obtain ⟨c, hc, cv⟩ := bcode_countable_inter_l I hZF hB.1 hA fam
    refine ⟨c, hc, fun w hw => (cv w).trans ⟨?_, ?_⟩⟩
    · intro hall i d x hid hr
      obtain ⟨e, _, he'⟩ := hg.2.2 i ((hD i).mpr ⟨d, hid⟩)
      exact (value i d e w x hid he' hw hr).mp (hall i e he')
    · intro hall i d hid
      obtain ⟨c, f, hic, hf, _⟩ := data i d hid
      obtain ⟨x, _, hfx⟩ := hf.1.2.2 w hw
      have hr := ((hf.2 w x).mp hfx).2
      exact (value i c d w x hic hid hw hr).mpr (hall i c x hic hr)
  · obtain ⟨c, hc, cv⟩ := bcode_union_l I hZF hB.1 hA fam
    refine ⟨c, hc, fun w hw => (cv w).trans ⟨?_, ?_⟩⟩
    · rintro ⟨i, d, hid, hd⟩
      obtain ⟨c, f, hic, hf, _⟩ := data i d hid
      obtain ⟨x, _, hfx⟩ := hf.1.2.2 w hw
      have hr := ((hf.2 w x).mp hfx).2
      exact ⟨i, c, x, hic, hr, (value i c d w x hic hid hw hr).mp hd⟩
    · rintro ⟨i, c, x, hic, hr, hx⟩
      obtain ⟨d, _, hid⟩ := hg.2.2 i ((hD i).mpr ⟨c, hic⟩)
      exact ⟨i, d, hid, (value i c d w x hic hid hw hr).mpr hx⟩

end YesMetaZFC.SetTheory.Descriptive
