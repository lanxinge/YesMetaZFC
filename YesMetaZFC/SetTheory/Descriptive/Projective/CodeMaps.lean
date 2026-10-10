import YesMetaZFC.SetTheory.Descriptive.Projective.Standard
import YesMetaZFC.SetTheory.Descriptive.Projective.Relative

/-! # 保持极性的升层、连续逆像与子空间解释 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pc_raise_l (hZF : M.Models ZF) {ω A B J n m t p K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hm : M.mem m ω) (hnm : n = m ∨ M.mem n m) (hc : Pc_d I ω A n t p) (hk : Pden_d I ω A B J p K) :
    ∃ q, Pc_d I ω A m t q ∧ Pden_d I ω A B J q K := by
  rcases hnm with rfl | hnm
  · exact ⟨p, hc, hk⟩
  · rcases hc.2.1 with ht | ht
    · exact (pc_sigma_l I hm ht).mp (ps_mono_l I hZF hB hA ha hJ m hm n K hnm
        ((pc_sigma_l I hc.1 ht).mpr ⟨p, hc, hk⟩))
    · exact (pc_pi_l I hm ht).mp (pp_mono_l I hZF hB hA ha hJ hm hnm
        ((pc_pi_l I hc.1 ht).mpr ⟨p, hc, hk⟩))

theorem pc_pull_l (hZF : M.Models ZF) {ω A B J n t p K f} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hc : Pc_d I ω A n t p) (hk : Pden_d I ω A B J p K) (hf : Cont_d I A B f) :
    ∃ q V, Pc_d I ω A n t q ∧ Pden_d I ω A B J q V ∧ Ip_d I B f K V := by
  obtain ⟨n', t', c, C, D, hp, hC, hD, ht⟩ := hk
  obtain ⟨c', hp', hc'⟩ := hc.2.2
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp hp'
  subst n' t' c'
  obtain ⟨E, he⟩ := ha
  obtain ⟨X, L, hL⟩ := lgraph_exists_l I hZF hB hJ
  obtain ⟨d, hd, hd'⟩ := ppull_exists_l I hZF hB hA he hL hf.1 hc.1 hc'
  obtain ⟨C', hC', _⟩ := bden_exists_unique_l I hZF ω A A B d
  obtain ⟨D', hD', _⟩ := pval_exists_unique_l I hZF (J := J) hB.1 hc.1 (fun x hx => ((hC' x).mp hx).1)
  have pull := ppull_value_l I hZF hB hA hJ he hL hf hc.1 hc' hd hC hC' hD hD'
  obtain ⟨q, hq⟩ := ppack_exists_l I n t d
  obtain ⟨V, hv⟩ := ip_exists_l I hZF B f K
  refine ⟨q, V, ⟨hc.1, hc.2.1, d, hq, hd'⟩, ⟨n, t, d, C', D', hq, hC', hD', ?_⟩, hv⟩
  exact ht.elim (fun h => Or.inl ⟨h.1, ip_unique_l I hZF.1 (h.2 ▸ pull) hv⟩)
    (fun h => Or.inr ⟨h.1, ip_compl_l I hf.1 pull hv h.2⟩)

def Prden_d (ω A B J X p K : M.Domain) : Prop := ∃ L, Pden_d I ω A B J p L ∧ Tr_d X L K
def prden_m {d} (ω A B J X p K : Term d) : Formula 1 d := .existsE (.conj
  (pden_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken p.weaken .newest) (tr_m X.weaken .newest K.weaken))
derive_free_closed prden_m
theorem prden_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J X p K : Term d) :
    Formula.satisfies ρ (prden_m (𝒞 := 𝒞) ω A B J X p K) ↔
      Prden_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (X.eval ρ) (p.eval ρ) (K.eval ρ) := by
  simp only [prden_m, Prden_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    pden_sat_l I hE, tr_sat_l, Definitional.Term.eval_weaken]; rfl

theorem prden_exists_unique_l (hZF : M.Models ZF) {ω A B J X p} (hω : M.IsOmega ω) (hp : Pcode_d I ω A p) :
    ∃ K, Prden_d I ω A B J X p K ∧ ∀ L, Prden_d I ω A B J X p L → L = K := by
  obtain ⟨U, hu, uniq⟩ := pden_exists_unique_l I hZF (B := B) (J := J) hω hp
  obtain ⟨K, hk⟩ := tr_exists_l (ZF.modelsKP hZF) X U
  exact ⟨K, ⟨U, hu, hk⟩, fun L ⟨V, hv, hl⟩ => tr_unique_l hZF.1 (uniq V hv ▸ hl) hk⟩

theorem prden_mem_l (hZF : M.Models ZF) {ω A B J X p K x} (hω : M.IsOmega ω) (h : Prden_d I ω A B J X p K) :
    M.mem x K ↔ M.mem x X ∧ Pev_d I ω A B J p x := by
  obtain ⟨L, hl, hk⟩ := h
  exact (hk x).trans (and_congr_right fun _ => pev_mem_l I hZF hω hl)

theorem prden_compl_l (hKP : M.Models KP) {ω A B J X p q K L} (hX : M.MemberSubset X B)
    (he : Pedit_d I false p q) (hk : Prden_d I ω A B J X p K) (hl : Cm_d X K L) : Prden_d I ω A B J X q L := by
  obtain ⟨U, hu, hk⟩ := hk
  obtain ⟨V, hv⟩ := cm_exists_l hKP B U
  obtain ⟨W, hw⟩ := tr_exists_l hKP X V
  exact ⟨V, pedit_compl_l I hKP.1 he hu hv, cm_unique_l hKP.1 (tr_compl_l hX hv hk hw) hl ▸ hw⟩

/-- 先作内部并交，再取迹；任意子空间均可，包括 Cantor 空间。 -/
theorem pf_relative_countable_l (hZF : M.Models ZF) {ω A B J n t H X} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Rcc_d I ω B) (hH : Pf_d I ω A n t H) (hX : M.MemberSubset X B) (b : Bool) :
    ∃ q K, Pc_d I ω A n t q ∧ Prden_d I ω A B J X q K ∧ ∀ x, M.mem x K ↔ M.mem x X ∧
      (if b then ∃ i p L, M.PairMember I i p H ∧ Prden_d I ω A B J X p L ∧ M.mem x L
       else ∀ i p L, M.PairMember I i p H → Prden_d I ω A B J X p L → M.mem x L) := by
  obtain ⟨q, U, hq, hu, val⟩ := pf_countable_l I hZF hB hA ha hJ hcc hH b
  obtain ⟨K, hk⟩ := tr_exists_l (ZF.modelsKP hZF) X U
  refine ⟨q, K, hq, ⟨U, hu, hk⟩, fun x => (hk x).trans (and_congr_right fun hx => ?_)⟩
  refine ((val x).trans ⟨And.right, fun h => ⟨hX x hx, h⟩⟩).trans ?_
  cases b
  · refine ⟨fun h i p L hip hl => (prden_mem_l I hZF hB.1 hl).mpr ⟨hx, h i p hip⟩, fun h i p hip => ?_⟩
    obtain ⟨L, hl, _⟩ := prden_exists_unique_l I hZF (B := B) (J := J) (X := X) hB.1 (pc_code_l I (pf_code_l I hH hip))
    exact ((prden_mem_l I hZF hB.1 hl).mp (h i p L hip hl)).2
  · refine ⟨fun ⟨i, p, hip, hv⟩ => ?_, fun ⟨i, p, L, hip, hl, hx⟩ => ⟨i, p, hip, ((prden_mem_l I hZF hB.1 hl).mp hx).2⟩⟩
    obtain ⟨L, hl, _⟩ := prden_exists_unique_l I hZF (B := B) (J := J) (X := X) hB.1 (pc_code_l I (pf_code_l I hH hip))
    exact ⟨i, p, L, hip, hl, (prden_mem_l I hZF hB.1 hl).mpr ⟨hx, hv⟩⟩

end YesMetaZFC.SetTheory.Descriptive
