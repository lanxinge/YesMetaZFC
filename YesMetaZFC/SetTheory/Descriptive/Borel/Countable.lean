import YesMetaZFC.SetTheory.Descriptive.Borel.Operations

/-! # 可逐项调用的唯一补码与内部可数交 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bneg_d (ω c d : M.Domain) : Prop := ∃ z E H p,
  (∀ x, ¬ M.mem x z) ∧ (∀ x, M.mem x E ↔ x = z) ∧ I.Codes p z c ∧
  (∀ x, M.mem x H ↔ x = p) ∧ Bjoin_d I ω z H E d
def bneg_m {d} (ω c e : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (Formula.isEmpty (.bound 3)) (.conj (Formula.isSingleton (.bound 2) (.bound 3)) (.conj
    (𝒞.code .newest (.bound 3) c.weaken.weaken.weaken.weaken) (.conj
    (Formula.isSingleton (.bound 1) .newest)
    (bjoin_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 2) e.weaken.weaken.weaken.weaken))))))))
derive_free_closed bneg_m
theorem bneg_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c e : Term d) :
    Formula.satisfies ρ (bneg_m (𝒞 := 𝒞) ω c e) ↔ Bneg_d I (ω.eval ρ) (c.eval ρ) (e.eval ρ) := by
  simp only [bneg_m, Bneg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isSingleton_iff hE, I.satisfies_code_iff,
    bjoin_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bneg_unique_l (hE : Extensional M) {ω c d e} (h : Bneg_d I ω c d) (k : Bneg_d I ω c e) : d = e := by
  obtain ⟨z, E, H, p, hz, he, hp, hh, hd⟩ := h
  obtain ⟨z', E', H', p', hz', he', hp', hh', hk⟩ := k
  have e := hE.eq_of_same_members z' z (fun x => iff_of_false (hz' x) (hz x))
  subst z'
  have e := I.unique hp' hp
  subst p'
  have e := hE.eq_of_same_members E' E (fun x => (he' x).trans (he x).symm)
  subst E'
  have e := hE.eq_of_same_members H' H (fun x => (hh' x).trans (hh x).symm)
  subst H'
  exact bjoin_unique_l I hE hd hk

theorem bneg_exists_l (hZF : M.Models ZF) {ω A S c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) :
    ∃ d, Bneg_d I ω c d ∧ Bcode_d I ω A S d ∧ ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨E, he⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  obtain ⟨p, hp⟩ := I.total z c
  obtain ⟨H, hh⟩ := KP.exists_singleton (ZF.modelsKP hZF) p
  have pair i d : M.PairMember I i d H ↔ i = z ∧ d = c :=
    ⟨fun ⟨q, hq, hqH⟩ => I.injective ((hh q).mp hqH ▸ hq) hp,
      fun ⟨rfl, rfl⟩ => ⟨p, hp, (hh p).mpr rfl⟩⟩
  have fam : Bfam_d I ω A S H := ⟨⟨fun q hq => ⟨z, c, ((hh q).mp hq).symm ▸ hp⟩,
    fun i d e hd he => ((pair i d).mp hd).2.trans ((pair i e).mp he).2.symm⟩,
    fun i d hd => ⟨((pair i d).mp hd).1.symm ▸ hzω, ((pair i d).mp hd).2.symm ▸ hc⟩⟩
  obtain ⟨d, hd, hc', hv⟩ := bjoin_exists_l I hZF hω hA hz hzω fam
    (E := E) (fun _ => ⟨z, c, (pair z c).mpr ⟨rfl, rfl⟩, fun j d h => ((pair j d).mp h).1⟩)
  refine ⟨d, ⟨z, E, H, p, hz, he, hp, hh, hd⟩, hc', fun x => ?_⟩
  have ex : (∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x) ↔ Bsat_d I ω A S c x :=
    ⟨fun ⟨i, d, hd, hv⟩ => ((pair i d).mp hd).2 ▸ hv, fun h => ⟨z, c, (pair z c).mpr ⟨rfl, rfl⟩, h⟩⟩
  simpa only [ex, (he z).mpr rfl, true_and, not_true, false_and, or_false] using hv x

theorem family_domain_l (hZF : M.Models ZF) {ω H} (hH : ∀ i c, M.PairMember I i c H → M.mem i ω) :
    ∃ D, M.MemberSubset D ω ∧ M.IsDomainOf I D H := by
  let ρ : Env M 1 := ⟨fun _ => H, fun _ => H⟩
  let φ : UnarySchema 1 := { body := .existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)) }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ ω
  have hp i : φ.denote ρ i ↔ ∃ c, M.PairMember I i c H := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  exact ⟨D, fun i hi => ((hD i).mp hi).1, fun i => ((hD i).trans (and_congr_right fun _ => hp i)).trans
    ⟨And.right, fun ⟨c, hc⟩ => ⟨hH i c hc, c, hc⟩⟩⟩

theorem bcode_countable_inter_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Bcode_d I ω A S c ∧ ∀ x, Bsat_d I ω A S c x ↔
      ∀ i d, M.PairMember I i d H → Bsat_d I ω A S d x := by
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
  have value i d (hd : M.PairMember I i d G) : ∃ c, M.PairMember I i c H ∧ Bcode_d I ω A S d ∧
      ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
    obtain ⟨c, hc, hn⟩ := (hp i d).mp ((eg i d).mp hd).2
    obtain ⟨e, he, he', hev⟩ := bneg_exists_l I hZF hω hA (hH.2 i c hc).2
    exact ⟨c, hc, bneg_unique_l I hZF.1 he hn ▸ he', bneg_unique_l I hZF.1 he hn ▸ hev⟩
  have fam : Bfam_d I ω A S G := ⟨hg.1, fun i d hd => (value i d hd).elim fun c hc => ⟨(hH.2 i c hc.1).1, hc.2.1⟩⟩
  obtain ⟨u, hu, uv⟩ := bcode_union_l I hZF hω hA fam
  obtain ⟨c, _, hc, cv⟩ := bneg_exists_l I hZF hω hA hu
  refine ⟨c, hc, fun x => (cv x).trans ((not_congr (uv x)).trans ⟨?_, ?_⟩)⟩
  · intro hn i d hd
    obtain ⟨e, _, he⟩ := hg.2.2 i ((hD i).mpr ⟨d, hd⟩)
    obtain ⟨d', hd', _, hev⟩ := value i e he
    have en := hH.1.2 i d' d hd' hd
    exact Classical.byContradiction (fun h => hn ⟨i, e, he, (hev x).mpr (en.symm ▸ h)⟩)
  · intro hall ⟨i, d, hd, hx⟩
    obtain ⟨e, he, _, hv⟩ := value i d hd
    exact (hv x).mp hx (hall i e he)

end YesMetaZFC.SetTheory.Descriptive
