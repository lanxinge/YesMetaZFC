import YesMetaZFC.SetTheory.Descriptive.Analytic.SeparationTree
import YesMetaZFC.SetTheory.Descriptive.Borel.Universe

/-! # 分离码的递归算子：逐行交，再对行取并 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Se_d (ω J U E G b a i d : M.Domain) : Prop := ∃ v q,
  M.mem v U ∧ Step_d I ω b v ∧ Fp_d I ω J q a v ∧ M.PairMember I v i E ∧ M.PairMember I q d G
def se_m {d} (ω J U E G b a i c : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.mem (.bound 1) U.weaken.weaken) (.conj (step_m (𝒞 := 𝒞) ω.weaken.weaken b.weaken.weaken (.bound 1)) (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken .newest a.weaken.weaken (.bound 1)) (.conj
  (Formula.orderedPairMem 𝒞 (.bound 1) i.weaken.weaken E.weaken.weaken)
  (Formula.orderedPairMem 𝒞 .newest c.weaken.weaken G.weaken.weaken))))))
derive_free_closed se_m
theorem se_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U E G b a i c : Term d) :
    Formula.satisfies ρ (se_m (𝒞 := 𝒞) ω J U E G b a i c) ↔
      Se_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (b.eval ρ) (a.eval ρ) (i.eval ρ) (c.eval ρ) := by
  simp only [se_m, Se_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    step_sat_l I hE, fp_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Sr_d (ω J U E G b a c : M.Domain) : Prop := ∃ H, M.IsSetRelation I H ∧
  (∀ i d, M.PairMember I i d H ↔ Se_d I ω J U E G b a i d) ∧ Binf_d I ω H c
def sr_m {d} (ω J U E G b a c : Term d) : Formula 1 d := .existsE (.conj (Formula.isRelation 𝒞 .newest) (.conj
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (se_m (𝒞 := 𝒞) ω.weaken.weaken.weaken J.weaken.weaken.weaken U.weaken.weaken.weaken E.weaken.weaken.weaken
      G.weaken.weaken.weaken b.weaken.weaken.weaken a.weaken.weaken.weaken (.bound 1) .newest))))
  (binf_m (𝒞 := 𝒞) ω.weaken .newest c.weaken)))
derive_free_closed sr_m
theorem sr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U E G b a c : Term d) :
    Formula.satisfies ρ (sr_m (𝒞 := 𝒞) ω J U E G b a c) ↔
      Sr_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (b.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [sr_m, Sr_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    se_sat_l I hE, binf_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem sr_unique_l (hE : Extensional M) {ω J U E G b a c d}
    (h : Sr_d I ω J U E G b a c) (k : Sr_d I ω J U E G b a d) : c = d := by
  obtain ⟨H, hh, he, hc⟩ := h
  obtain ⟨F, hf, fe, hd⟩ := k
  have e := hf.eq_of_pairMember_iff hE hh (fun i c => (fe i c).trans (he i c).symm)
  subst F
  exact binf_unique_l I hE hc hd

def So_d (ω J T U E G a b i c : M.Domain) : Prop := ∃ u,
  M.mem u T ∧ Step_d I ω a u ∧ M.PairMember I u i E ∧ Sr_d I ω J U E G b u c
def so_m {d} (ω J T U E G a b i c : Term d) : Formula 1 d := Formula.existsMem T (.conj
  (step_m (𝒞 := 𝒞) ω.weaken a.weaken .newest) (.conj
  (Formula.orderedPairMem 𝒞 .newest i.weaken E.weaken)
  (sr_m (𝒞 := 𝒞) ω.weaken J.weaken U.weaken E.weaken G.weaken b.weaken .newest c.weaken)))
derive_free_closed so_m
theorem so_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T U E G a b i c : Term d) :
    Formula.satisfies ρ (so_m (𝒞 := 𝒞) ω J T U E G a b i c) ↔
      So_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (a.eval ρ) (b.eval ρ) (i.eval ρ) (c.eval ρ) := by
  simp only [so_m, So_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    step_sat_l I hE, sr_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Sm_d (ω J T U E G a b c : M.Domain) : Prop := ∃ H, M.IsSetRelation I H ∧
  (∀ i d, M.PairMember I i d H ↔ So_d I ω J T U E G a b i d) ∧ Bsup_d I ω H c
def sm_m {d} (ω J T U E G a b c : Term d) : Formula 1 d := .existsE (.conj (Formula.isRelation 𝒞 .newest) (.conj
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (so_m (𝒞 := 𝒞) ω.weaken.weaken.weaken J.weaken.weaken.weaken T.weaken.weaken.weaken U.weaken.weaken.weaken E.weaken.weaken.weaken
      G.weaken.weaken.weaken a.weaken.weaken.weaken b.weaken.weaken.weaken (.bound 1) .newest))))
  (bsup_m (𝒞 := 𝒞) ω.weaken .newest c.weaken)))
derive_free_closed sm_m
theorem sm_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T U E G a b c : Term d) :
    Formula.satisfies ρ (sm_m (𝒞 := 𝒞) ω J T U E G a b c) ↔
      Sm_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) := by
  simp only [sm_m, Sm_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    so_sat_l I hE, bsup_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem sm_unique_l (hE : Extensional M) {ω J T U E G a b c d}
    (h : Sm_d I ω J T U E G a b c) (k : Sm_d I ω J T U E G a b d) : c = d := by
  obtain ⟨H, hh, he, hc⟩ := h
  obtain ⟨F, hf, fe, hd⟩ := k
  have e := hf.eq_of_pairMember_iff hE hh (fun i c => (fe i c).trans (he i c).symm)
  subst F
  exact bsup_unique_l I hE hc hd

theorem sr_exists_l (hZF : M.Models ZF) {ω A J U E G b a} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hG : M.IsSetFunction I G)
    (hU : M.MemberSubset U A) (bound : ∀ v q d, M.mem v U → Step_d I ω b v →
      Fp_d I ω J q a v → M.PairMember I q d G → Bcode_d I ω A A d) :
    ∃ c, Sr_d I ω J U E G b a c ∧ Bcode_d I ω A A c ∧ ∀ x,
      Bsat_d I ω A A c x ↔ ∀ v q d, M.mem v U → Step_d I ω b v →
        Fp_d I ω J q a v → M.PairMember I q d G → Bsat_d I ω A A d x := by
  let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push U).push E).push G).push b).push a
  let φ : BinarySchema 7 := { body := se_m (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp i d : φ.denote ρ i d ↔ Se_d I ω J U E G b a i d := se_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _
  obtain ⟨H, hf, pair⟩ := bf_defined_l I hZF φ ρ (by
    intro i c d hc hd
    obtain ⟨v, q, _, _, ⟨_, _, _, _, hq⟩, hi, hc⟩ := (hp i c).mp hc
    obtain ⟨w, r, _, _, ⟨_, _, _, _, hr⟩, hj, hd⟩ := (hp i d).mp hd
    have e := he.2 w v i hj hi
    subst w
    exact hG.2 q c d hc (rp_unique_l I hZF.1 hr hq ▸ hd)) (by
    intro i d hd
    obtain ⟨v, q, hv, hs, hq, hi, hd⟩ := (hp i d).mp hd
    exact ⟨he.1.output_mem_of_pairMember hi, bound v q d hv hs hq hd⟩)
  have ep i d := (pair i d).trans (hp i d)
  obtain ⟨c, hc, hf', cv⟩ := binf_exists_l I hZF hω hA hf
  refine ⟨c, ⟨H, hf.1.1, ep, hc⟩, hf', fun x => (cv x).trans ⟨?_, ?_⟩⟩
  · intro hall v q d hv hs hq hd
    obtain ⟨i, _, hi⟩ := he.1.2.2 v (hU v hv)
    exact hall i d ((ep i d).mpr ⟨v, q, hv, hs, hq, hi, hd⟩)
  · intro hall i d hd
    obtain ⟨v, q, hv, hs, hq, _, hd⟩ := (ep i d).mp hd
    exact hall v q d hv hs hq hd

theorem sm_exists_l (hZF : M.Models ZF) {ω A J T U E G a b} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hG : M.IsSetFunction I G)
    (hT : M.MemberSubset T A) (hU : M.MemberSubset U A)
    (bound : ∀ u v q d, M.mem u T → Step_d I ω a u → M.mem v U → Step_d I ω b v →
      Fp_d I ω J q u v → M.PairMember I q d G → Bcode_d I ω A A d) :
    ∃ c, Sm_d I ω J T U E G a b c ∧ Bcode_d I ω A A c ∧ ∀ x,
      Bsat_d I ω A A c x ↔ ∃ u, M.mem u T ∧ Step_d I ω a u ∧
        ∀ v q d, M.mem v U → Step_d I ω b v → Fp_d I ω J q u v → M.PairMember I q d G → Bsat_d I ω A A d x := by
  let ρ : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T).push U).push E).push G).push a).push b
  let φ : BinarySchema 8 := { body := so_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp i d : φ.denote ρ i d ↔ So_d I ω J T U E G a b i d := so_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _ _
  have row u (hu : M.mem u T) (hs : Step_d I ω a u) := sr_exists_l I hZF hω hA he hG hU (bound u · · · hu hs)
  obtain ⟨H, hf, pair⟩ := bf_defined_l I hZF φ ρ (by
    intro i c d hc hd
    obtain ⟨u, _, _, hi, hc⟩ := (hp i c).mp hc
    obtain ⟨v, _, _, hj, hd⟩ := (hp i d).mp hd
    exact sr_unique_l I hZF.1 hc (he.2 v u i hj hi ▸ hd)) (by
    intro i d hd
    obtain ⟨u, hu, hs, hi, hd⟩ := (hp i d).mp hd
    obtain ⟨c, hc, ht, _⟩ := row u hu hs
    exact ⟨he.1.output_mem_of_pairMember hi, sr_unique_l I hZF.1 hc hd ▸ ht⟩)
  have ep i d := (pair i d).trans (hp i d)
  obtain ⟨c, hc, hf', cv⟩ := bsup_exists_l I hZF hω hA hf
  refine ⟨c, ⟨H, hf.1.1, ep, hc⟩, hf', fun x => (cv x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨i, d, hd, hx⟩
    obtain ⟨u, hu, hs, _, hd⟩ := (ep i d).mp hd
    obtain ⟨e, he, _, ev⟩ := row u hu hs
    exact ⟨u, hu, hs, (ev x).mp (sr_unique_l I hZF.1 hd he ▸ hx)⟩
  · rintro ⟨u, hu, hs, hx⟩
    obtain ⟨d, hd, _, dv⟩ := row u hu hs
    obtain ⟨i, _, hi⟩ := he.1.2.2 u (hT u hu)
    exact ⟨i, d, (ep i d).mpr ⟨u, hu, hs, hi, hd⟩, (dv x).mpr hx⟩

end YesMetaZFC.SetTheory.Descriptive
