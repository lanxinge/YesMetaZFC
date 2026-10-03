import YesMetaZFC.SetTheory.Descriptive.Projective.Countable

/-! # 指定层号与极性的内部射影码族 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pf_d (ω A n t H : M.Domain) : Prop := M.mem n ω ∧
  ((∀ x, ¬ M.mem x t) ∨ M.IsOrdinalOne t) ∧ M.IsSetFunction I H ∧
  ∀ i p, M.PairMember I i p H → M.mem i ω ∧ ∃ c, Ppack_d I p n t c ∧ Bcode_d I ω A A c
def pf_m {d} (ω A n t H : Term d) : Formula 1 d := .conj (.mem n ω) (.conj
  (.disj (Formula.isEmpty t) (Formula.isOrdinalOne t)) (.conj (Formula.isFunction 𝒞 H)
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken)
    (.conj (.mem (.bound 1) ω.weaken.weaken) (.existsE (.conj
      (ppack_m (𝒞 := 𝒞) (.bound 1) n.weaken.weaken.weaken t.weaken.weaken.weaken .newest)
      (bcode_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken A.weaken.weaken.weaken .newest)))))))))
derive_free_closed pf_m
theorem pf_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A n t H : Term d) :
    Formula.satisfies ρ (pf_m (𝒞 := 𝒞) ω A n t H) ↔ Pf_d I (ω.eval ρ) (A.eval ρ) (n.eval ρ) (t.eval ρ) (H.eval ρ) := by
  simp only [pf_m, Pf_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isOrdinalOne_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, ppack_sat_l I, bcode_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem pf_code_l {ω A n t H i p} (h : Pf_d I ω A n t H) (hp : M.PairMember I i p H) : Pc_d I ω A n t p :=
  ⟨h.1, h.2.1, (h.2.2.2 i p hp).2⟩

theorem pf_matrix_l (hZF : M.Models ZF) {ω A n t H} (h : Pf_d I ω A n t H) :
    ∃ G, Bfam_d I ω A A G ∧ ∀ i c, M.PairMember I i c G ↔ ∃ p, M.PairMember I i p H ∧ Ppack_d I p n t c := by
  obtain ⟨D, _, hD⟩ := family_domain_l I hZF (fun i p hp => (h.2.2.2 i p hp).1)
  let ρ : Env M 3 := ((⟨fun _ => H, fun _ => H⟩ : Env M 1).push n).push t
  let φ : BinarySchema 3 := { body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 5))
    (ppack_m (𝒞 := 𝒞) .newest (.bound 4) (.bound 3) (.bound 1))) }
  have hp i c : φ.denote ρ i c ↔ ∃ p, M.PairMember I i p H ∧ Ppack_d I p n t c := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, ppack_sat_l I]; rfl
  have total i (hi : M.mem i D) : ∃ c, φ.denote ρ i c := by
    obtain ⟨p, hip⟩ := (hD i).mp hi
    obtain ⟨c, hc, _⟩ := (h.2.2.2 i p hip).2
    exact ⟨c, (hp i c).mpr ⟨p, hip, hc⟩⟩
  have unique i (_ : M.mem i D) c d (hc : φ.denote ρ i c) (hd : φ.denote ρ i d) : c = d := by
    obtain ⟨p, hip, hc⟩ := (hp i c).mp hc
    obtain ⟨q, hiq, hd⟩ := (hp i d).mp hd
    exact (ppack_unique_l I hc (h.2.2.1.2 i q p hiq hip ▸ hd)).2.2
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ ρ D total unique
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun i c hi hc => (hC c).mpr ⟨i, hi, hc⟩)
  have eqn i c : M.PairMember I i c G ↔ ∃ p, M.PairMember I i p H ∧ Ppack_d I p n t c :=
    ((eg i c).trans (and_congr_right fun _ => hp i c)).trans
      ⟨And.right, fun ⟨p, hip, hc⟩ => ⟨(hD i).mpr ⟨p, hip⟩, p, hip, hc⟩⟩
  refine ⟨G, ⟨hg.1, fun i c hic => ?_⟩, eqn⟩
  obtain ⟨p, hip, hc⟩ := (eqn i c).mp hic
  obtain ⟨hi, d, hd, hd'⟩ := h.2.2.2 i p hip
  exact ⟨hi, (ppack_unique_l I hd hc).2.2 ▸ hd'⟩

def Pev_d (ω A B J p x : M.Domain) : Prop := ∃ K, Pden_d I ω A B J p K ∧ M.mem x K
def pev_m {d} (ω A B J p x : Term d) : Formula 1 d := .existsE (.conj
  (pden_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken p.weaken .newest) (.mem x.weaken .newest))
derive_free_closed pev_m
theorem pev_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J p x : Term d) :
    Formula.satisfies ρ (pev_m (𝒞 := 𝒞) ω A B J p x) ↔
      Pev_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (p.eval ρ) (x.eval ρ) := by
  simp only [pev_m, Pev_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    pden_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem pev_mem_l (hZF : M.Models ZF) {ω A B J p K x} (hω : M.IsOmega ω) (h : Pden_d I ω A B J p K) :
    M.mem x K ↔ Pev_d I ω A B J p x :=
  ⟨fun hx => ⟨K, h, hx⟩, fun ⟨_, hl, hx⟩ => pden_unique_l I hZF hω hl h ▸ hx⟩

theorem pev_matrix_l (hZF : M.Models ZF) {ω A B J n t p c x} (hω : M.IsOmega ω)
    (hc : Pc_d I ω A n t p) (hp : Ppack_d I p n t c) (hx : M.mem x B) :
    Pev_d I ω A B J p x ↔ ((∀ y, ¬ M.mem y t) ∧ Pm_d I ω A B J n c x) ∨
      (M.IsOrdinalOne t ∧ ¬ Pm_d I ω A B J n c x) := by
  obtain ⟨K, hk, _⟩ := pden_exists_unique_l I hZF (B := B) (J := J) hω (pc_code_l I hc)
  have mem := pev_mem_l I hZF (x := x) hω hk
  obtain ⟨n', t', c', C, D, hq, hC, hv, ht⟩ := hk
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hq hp
  subst n' t' c'
  rcases ht with ⟨hz, e⟩ | ⟨ho, hm⟩
  · subst K
    exact mem.symm.trans ((pm_mem_l I hZF hω hC hv).trans
      ⟨fun h => Or.inl ⟨hz, h⟩, fun h => h.elim And.right (fun h => (ptag_disjoint_l hz h.1).elim)⟩)
  · exact mem.symm.trans ((hm x).trans ⟨fun h => Or.inr ⟨ho, (not_congr (pm_mem_l I hZF hω hC hv)).mp h.2⟩,
      fun h => ⟨hx, h.elim (fun h => (ptag_disjoint_l h.1 ho).elim)
        (fun h => (not_congr (pm_mem_l I hZF hω hC hv)).mpr h.2)⟩⟩)

end YesMetaZFC.SetTheory.Descriptive
