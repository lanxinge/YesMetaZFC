import YesMetaZFC.SetTheory.Descriptive.Borel.Operations

/-! # Borel 码的二元布尔运算 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_union_two_l (hZF : M.Models ZF) {ω A S c d} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) (hd : Bcode_d I ω A S d) :
    ∃ e, Bcode_d I ω A S e ∧ ∀ x, Bsat_d I ω A S e x ↔ Bsat_d I ω A S c x ∨ Bsat_d I ω A S d x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  have hzo : z ≠ o := fun e => hz z (e.symm ▸ ho.predecessor_mem)
  obtain ⟨p, hp⟩ := I.total z c
  obtain ⟨q, hq⟩ := I.total o d
  obtain ⟨H, hH⟩ := KP.exists_pair (ZF.modelsKP hZF) p q
  have pair i a : M.PairMember I i a H ↔ (i = z ∧ a = c) ∨ (i = o ∧ a = d) := by
    constructor
    · rintro ⟨r, hr, hrH⟩
      exact ((hH r).mp hrH).elim (fun e => Or.inl (I.injective (e ▸ hr) hp))
        (fun e => Or.inr (I.injective (e ▸ hr) hq))
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨p, hp, (hH p).mpr (Or.inl rfl)⟩
      · exact ⟨q, hq, (hH q).mpr (Or.inr rfl)⟩
  have family : Bfam_d I ω A S H := by
    refine ⟨⟨fun r hr => ((hH r).mp hr).elim (fun e => ⟨z, c, e.symm ▸ hp⟩) (fun e => ⟨o, d, e.symm ▸ hq⟩), ?_⟩, ?_⟩
    · intro i a b ha hb
      rcases (pair i a).mp ha with ha | ha <;> rcases (pair i b).mp hb with hb | hb
      · exact ha.2.trans hb.2.symm
      · exact (hzo (ha.1.symm.trans hb.1)).elim
      · exact (hzo (hb.1.symm.trans ha.1)).elim
      · exact ha.2.trans hb.2.symm
    · intro i a ha
      exact ((pair i a).mp ha).elim (fun h => ⟨h.1.symm ▸ hzω, h.2.symm ▸ hc⟩)
        (fun h => ⟨h.1.symm ▸ hoω, h.2.symm ▸ hd⟩)
  obtain ⟨e, he, hv⟩ := bcode_union_l I hZF hω hA family
  refine ⟨e, he, fun x => (hv x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨i, a, ha, hx⟩
    exact ((pair i a).mp ha).elim (fun h => Or.inl (h.2 ▸ hx)) (fun h => Or.inr (h.2 ▸ hx))
  · exact fun h => h.elim (fun h => ⟨z, c, (pair z c).mpr (Or.inl ⟨rfl, rfl⟩), h⟩)
      (fun h => ⟨o, d, (pair o d).mpr (Or.inr ⟨rfl, rfl⟩), h⟩)

theorem bcode_inter_l (hZF : M.Models ZF) {ω A S c d} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) (hd : Bcode_d I ω A S d) :
    ∃ e, Bcode_d I ω A S e ∧ ∀ x, Bsat_d I ω A S e x ↔ Bsat_d I ω A S c x ∧ Bsat_d I ω A S d x := by
  classical
  obtain ⟨c', hc', hcv⟩ := bcode_compl_l I hZF hω hA hc
  obtain ⟨d', hd', hdv⟩ := bcode_compl_l I hZF hω hA hd
  obtain ⟨u, hu, huv⟩ := bcode_union_two_l I hZF hω hA hc' hd'
  obtain ⟨e, he, hev⟩ := bcode_compl_l I hZF hω hA hu
  exact ⟨e, he, fun x => by simp only [hev x, huv x, hcv x, hdv x, not_or, Classical.not_not]⟩

end YesMetaZFC.SetTheory.Descriptive
