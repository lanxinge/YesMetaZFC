import YesMetaZFC.SetTheory.Descriptive.Projective.CodeMaps

/-! # 实际码族的解释函数图及 Δ 层可数运算

Δ 输入由同一内部集合族的 Σ、Π 两组码提供。两组解释必须是同一实际函数图，
因而不把逐项有码冒充已经选择好的一族码。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fd_d (ω A B J H V : M.Domain) : Prop := M.IsSetFunction I V ∧ ∀ i K,
  M.PairMember I i K V ↔ ∃ p, M.PairMember I i p H ∧ Pden_d I ω A B J p K
def fd_m {d} (ω A B J H V : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 V) (.forallE (.forallE
  (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest V.weaken.weaken) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest H.weaken.weaken.weaken)
    (pden_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken .newest (.bound 1)))))))
derive_free_closed fd_m
theorem fd_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J H V : Term d) :
    Formula.satisfies ρ (fd_m (𝒞 := 𝒞) ω A B J H V) ↔
      Fd_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (H.eval ρ) (V.eval ρ) := by
  simp only [fd_m, Fd_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, pden_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem fd_exists_l (hZF : M.Models ZF) {ω A B J n t H} (hω : M.IsOmega ω) (h : Pf_d I ω A n t H) :
    ∃ V, Fd_d I ω A B J H V := by
  obtain ⟨D, _, hD⟩ := family_domain_l I hZF (fun i p hp => (h.2.2.2 i p hp).1)
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push H
  let φ : BinarySchema 5 := { body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
    (pden_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))) }
  have hp i K : φ.denote ρ i K ↔ ∃ p, M.PairMember I i p H ∧ Pden_d I ω A B J p K := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, pden_sat_l I hZF.1]; rfl
  have total i (hi : M.mem i D) : ∃ K, φ.denote ρ i K := by
    obtain ⟨p, hip⟩ := (hD i).mp hi
    obtain ⟨K, hk, _⟩ := pden_exists_unique_l I hZF (B := B) (J := J) hω (pc_code_l I (pf_code_l I h hip))
    exact ⟨K, (hp i K).mpr ⟨p, hip, hk⟩⟩
  have unique i (_ : M.mem i D) K L (hk : φ.denote ρ i K) (hl : φ.denote ρ i L) : K = L := by
    obtain ⟨p, hip, hk⟩ := (hp i K).mp hk
    obtain ⟨q, hiq, hl⟩ := (hp i L).mp hl
    exact pden_unique_l I hZF hω hk (h.2.2.1.2 i q p hiq hip ▸ hl)
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ ρ D total unique
  obtain ⟨V, hv, ev⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun i K hi hk => (hC K).mpr ⟨i, hi, hk⟩)
  exact ⟨V, hv.1, fun i K => ((ev i K).trans (and_congr_right fun _ => hp i K)).trans
    ⟨And.right, fun ⟨p, hip, hk⟩ => ⟨(hD i).mpr ⟨p, hip⟩, p, hip, hk⟩⟩⟩

theorem fd_op_l (hZF : M.Models ZF) {ω A B J n t H V x} (hω : M.IsOmega ω)
    (h : Pf_d I ω A n t H) (hv : Fd_d I ω A B J H V) (b : Bool) :
    (if b then ∃ i p, M.PairMember I i p H ∧ Pev_d I ω A B J p x
     else ∀ i p, M.PairMember I i p H → Pev_d I ω A B J p x) ↔
    (if b then ∃ i K, M.PairMember I i K V ∧ M.mem x K
     else ∀ i K, M.PairMember I i K V → M.mem x K) := by
  cases b
  · refine ⟨fun hall i K hi => ?_, fun hall i p hip => ?_⟩
    · obtain ⟨p, hip, hk⟩ := (hv.2 i K).mp hi
      exact (pev_mem_l I hZF hω hk).mpr (hall i p hip)
    · obtain ⟨K, hk, _⟩ := pden_exists_unique_l I hZF (B := B) (J := J) hω (pc_code_l I (pf_code_l I h hip))
      exact (pev_mem_l I hZF hω hk).mp (hall i K ((hv.2 i K).mpr ⟨p, hip, hk⟩))
  · exact ⟨fun ⟨i, p, hip, K, hk, hx⟩ => ⟨i, K, (hv.2 i K).mpr ⟨p, hip, hk⟩, hx⟩,
      fun ⟨i, K, hi, hx⟩ => ((hv.2 i K).mp hi).elim fun p hp => ⟨i, p, hp.1, K, hp.2, hx⟩⟩

theorem pd_countable_l (hZF : M.Models ZF) {ω A B J n z o H G V} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Rcc_d I ω B) (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o)
    (hH : Pf_d I ω A n z H) (hG : Pf_d I ω A n o G)
    (hv : Fd_d I ω A B J H V) (hv' : Fd_d I ω A B J G V) (b : Bool) :
    ∃ p q K, Pc_d I ω A n z p ∧ Pc_d I ω A n o q ∧ Pden_d I ω A B J p K ∧
      Pden_d I ω A B J q K ∧ Pd_d I ω A B J n K ∧ ∀ x, M.mem x K ↔ M.mem x B ∧
        (if b then ∃ i L, M.PairMember I i L V ∧ M.mem x L else ∀ i L, M.PairMember I i L V → M.mem x L) := by
  obtain ⟨p, K, hp, hk, ek⟩ := pf_countable_l I hZF hB hA ha hJ hcc hH b
  obtain ⟨q, L, hq, hl, el⟩ := pf_countable_l I hZF hB hA ha hJ hcc hG b
  have memK x := (ek x).trans (and_congr_right fun _ => fd_op_l I hZF hB.1 hH hv b)
  have memL x := (el x).trans (and_congr_right fun _ => fd_op_l I hZF hB.1 hG hv' b)
  have e := hZF.1.eq_of_same_members L K (fun x => (memL x).trans (memK x).symm)
  subst L
  exact ⟨p, q, K, hp, hq, hk, hl, ⟨(pc_sigma_l I hH.1 hz).mpr ⟨p, hp, hk⟩,
    (pc_pi_l I hG.1 ho).mpr ⟨q, hq, hl⟩⟩, memK⟩

theorem pd_standard_l (hZF : M.Models ZF) {ω A B J k n K} (hω : M.IsOmega ω) (hn : Num_d k n) :
    Pd_d I ω A B J n K ↔
      (∃ c, Bcode_d I ω A A c ∧ ∀ x, M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k true c x) ∧
      (∃ c, Bcode_d I ω A A c ∧ ∀ x, M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k false c x) :=
  and_congr (ps_standard_l I hZF hω hn) (pp_standard_l I hZF hω hn)

end YesMetaZFC.SetTheory.Descriptive
