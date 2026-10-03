import YesMetaZFC.SetTheory.Descriptive.Borel.Countable

/-! # 可数并交的规范码算子

规范性是语法码的唯一性，因而递归中逐行构造码族不需要选择公理。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bsup_d (ω H c : M.Domain) : Prop := ∃ z, (∀ x, ¬ M.mem x z) ∧ Bjoin_d I ω z H z c
def bsup_m {d} (ω H c : Term d) : Formula 1 d := .existsE (.conj (Formula.isEmpty .newest)
  (bjoin_m (𝒞 := 𝒞) ω.weaken .newest H.weaken .newest c.weaken))
derive_free_closed bsup_m
theorem bsup_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H c : Term d) :
    Formula.satisfies ρ (bsup_m (𝒞 := 𝒞) ω H c) ↔ Bsup_d I (ω.eval ρ) (H.eval ρ) (c.eval ρ) := by
  simp only [bsup_m, Bsup_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isEmpty_iff, bjoin_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem bsup_unique_l (hE : Extensional M) {ω H c d} (h : Bsup_d I ω H c) (k : Bsup_d I ω H d) : c = d := by
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨w, hw, k⟩ := k
  have e := hE.eq_of_same_members w z (fun x => iff_of_false (hw x) (hz x))
  subst w
  exact bjoin_unique_l I hE h k
theorem bsup_exists_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Bsup_d I ω H c ∧ Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨c, hc, ht, hv⟩ := bjoin_exists_l I hZF hω hA hz hzω hH (E := z) (fun h => (hz z h).elim)
  exact ⟨c, ⟨z, hz, hc⟩, ht, fun x => by
    simpa only [hz z, false_and, not_false_eq_true, true_and, false_or] using hv x⟩

def Bdual_d (ω H G : M.Domain) : Prop := M.IsSetRelation I G ∧ ∀ i d,
  M.PairMember I i d G ↔ ∃ c, M.PairMember I i c H ∧ Bneg_d I ω c d
def bdual_m {d} (ω H G : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 G)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken)
    (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest H.weaken.weaken.weaken)
      (bneg_m (𝒞 := 𝒞) ω.weaken.weaken.weaken .newest (.bound 1)))))))
derive_free_closed bdual_m
theorem bdual_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H G : Term d) :
    Formula.satisfies ρ (bdual_m (𝒞 := 𝒞) ω H G) ↔ Bdual_d I (ω.eval ρ) (H.eval ρ) (G.eval ρ) := by
  simp only [bdual_m, Bdual_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, bneg_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem bdual_unique_l (hE : Extensional M) {ω H G F} (h : Bdual_d I ω H G) (k : Bdual_d I ω H F) : G = F :=
  h.1.eq_of_pairMember_iff hE k.1 (fun i d => (h.2 i d).trans (k.2 i d).symm)

theorem bdual_exists_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ G, Bdual_d I ω H G ∧ Bfam_d I ω A S G ∧ ∀ x,
      (∃ i d, M.PairMember I i d G ∧ Bsat_d I ω A S d x) ↔
        ¬ ∀ i c, M.PairMember I i c H → Bsat_d I ω A S c x := by
  classical
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push H
  let φ : BinarySchema 2 := { body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
    (bneg_m (𝒞 := 𝒞) (.bound 4) .newest (.bound 1))) }
  have hp i d : φ.denote ρ i d ↔ ∃ c, M.PairMember I i c H ∧ Bneg_d I ω c d := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, bneg_sat_l I hZF.1]; rfl
  obtain ⟨D, _, hD⟩ := family_domain_l I hZF (fun i c hc => (hH.2 i c hc).1)
  have total i (hi : M.mem i D) : ∃ d, φ.denote ρ i d :=
    ((hD i).mp hi).elim fun c hc => (bneg_exists_l I hZF hω hA (hH.2 i c hc).2).imp
      fun d hd => (hp i d).mpr ⟨c, hc, hd.1⟩
  have unique i (_ : M.mem i D) c d (hc : φ.denote ρ i c) (hd : φ.denote ρ i d) : c = d := by
    obtain ⟨a, ha, hc⟩ := (hp i c).mp hc
    obtain ⟨b, hb, hd⟩ := (hp i d).mp hd
    exact bneg_unique_l I hZF.1 hc (hH.1.2 i b a hb ha ▸ hd)
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ ρ D total unique
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := C)
    total unique (fun i d hi hd => (hC d).mpr ⟨i, hi, hd⟩)
  have dual : Bdual_d I ω H G := ⟨hg.1.1, fun i d => ((eg i d).trans
    (and_congr_right fun _ => hp i d)).trans ⟨And.right, fun h => ⟨(hD i).mpr (h.imp fun _ h => h.1), h⟩⟩⟩
  have value i d (hd : M.PairMember I i d G) : ∃ c, M.PairMember I i c H ∧ Bcode_d I ω A S d ∧
      ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
    obtain ⟨c, hc, hn⟩ := (dual.2 i d).mp hd
    obtain ⟨e, he, he', hev⟩ := bneg_exists_l I hZF hω hA (hH.2 i c hc).2
    exact ⟨c, hc, bneg_unique_l I hZF.1 he hn ▸ he', bneg_unique_l I hZF.1 he hn ▸ hev⟩
  refine ⟨G, dual, ⟨hg.1, fun i d hd => (value i d hd).elim fun c hc => ⟨(hH.2 i c hc.1).1, hc.2.1⟩⟩, fun x => ?_⟩
  constructor
  · rintro ⟨i, d, hd, hx⟩ hall
    obtain ⟨c, hc, _, hv⟩ := value i d hd
    exact (hv x).mp hx (hall i c hc)
  · intro hn
    obtain ⟨i, c, hc, hx⟩ : ∃ i c, M.PairMember I i c H ∧ ¬ Bsat_d I ω A S c x := by
      exact Classical.byContradiction (fun h => hn (fun i c hc =>
        Classical.byContradiction (fun hx => h ⟨i, c, hc, hx⟩)))
    obtain ⟨d, hd, _, hv⟩ := bneg_exists_l I hZF hω hA (hH.2 i c hc).2
    exact ⟨i, d, (dual.2 i d).mpr ⟨c, hc, hd⟩, (hv x).mpr hx⟩

def Binf_d (ω H c : M.Domain) : Prop := ∃ G u, Bdual_d I ω H G ∧ Bsup_d I ω G u ∧ Bneg_d I ω u c
def binf_m {d} (ω H c : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (bdual_m (𝒞 := 𝒞) ω.weaken.weaken H.weaken.weaken (.bound 1)) (.conj
  (bsup_m (𝒞 := 𝒞) ω.weaken.weaken (.bound 1) .newest) (bneg_m (𝒞 := 𝒞) ω.weaken.weaken .newest c.weaken.weaken))))
derive_free_closed binf_m
theorem binf_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H c : Term d) :
    Formula.satisfies ρ (binf_m (𝒞 := 𝒞) ω H c) ↔ Binf_d I (ω.eval ρ) (H.eval ρ) (c.eval ρ) := by
  simp only [binf_m, Binf_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bdual_sat_l I hE, bsup_sat_l I hE, bneg_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem binf_unique_l (hE : Extensional M) {ω H c d} (h : Binf_d I ω H c) (k : Binf_d I ω H d) : c = d := by
  obtain ⟨G, u, hg, hu, hc⟩ := h
  obtain ⟨F, v, hf, hv, hd⟩ := k
  have e := bdual_unique_l I hE hf hg
  subst F
  exact bneg_unique_l I hE hc (bsup_unique_l I hE hv hu ▸ hd)
theorem binf_exists_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Binf_d I ω H c ∧ Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔ ∀ i d, M.PairMember I i d H → Bsat_d I ω A S d x := by
  obtain ⟨G, hg, hf, hv⟩ := bdual_exists_l I hZF hω hA hH
  obtain ⟨u, hu, hf, uv⟩ := bsup_exists_l I hZF hω hA hf
  obtain ⟨c, hc, hf, cv⟩ := bneg_exists_l I hZF hω hA hf
  exact ⟨c, ⟨G, u, hg, hu, hc⟩, hf, fun x => (cv x).trans
    ((not_congr ((uv x).trans (hv x))).trans Classical.not_not)⟩

/-- 可数交的解释直接由规范交码给出。 -/
theorem bcode_countable_inter_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Bcode_d I ω A S c ∧ ∀ x, Bsat_d I ω A S c x ↔
      ∀ i d, M.PairMember I i d H → Bsat_d I ω A S d x := by
  obtain ⟨c, _, hc, hv⟩ := binf_exists_l I hZF hω hA hH
  exact ⟨c, hc, hv⟩

end YesMetaZFC.SetTheory.Descriptive
