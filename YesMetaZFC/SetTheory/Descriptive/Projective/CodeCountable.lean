import YesMetaZFC.SetTheory.Descriptive.Projective.Family

/-! # Σ、Π 层实际码族的同层可数并交 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pf_countable_with_l (hZF : M.Models ZF) {ω A B J n t H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Fcc_d I B H) (hH : Pf_d I ω A n t H) (b : Bool) :
    ∃ q K, Pc_d I ω A n t q ∧ Pden_d I ω A B J q K ∧ ∀ x, M.mem x K ↔ M.mem x B ∧
      (if b then ∃ i p, M.PairMember I i p H ∧ Pev_d I ω A B J p x
       else ∀ i p, M.PairMember I i p H → Pev_d I ω A B J p x) := by
  classical
  obtain ⟨G, hg, eg⟩ := pf_matrix_l I hZF hH
  have choice : Fcc_d I B G := by
    intro D hd
    apply hcc D
    intro i
    refine (hd i).trans ⟨fun ⟨c, hc⟩ => ((eg i c).mp hc).elim fun p hp => ⟨p, hp.1⟩, fun ⟨p, hp⟩ => ?_⟩
    obtain ⟨c, hc, _⟩ := (hH.2.2.2 i p hp).2
    exact ⟨c, (eg i c).mpr ⟨p, hp, hc⟩⟩
  have build (a : Bool) : ∃ d q K, Bcode_d I ω A A d ∧ Ppack_d I q n t d ∧ Pc_d I ω A n t q ∧
      Pden_d I ω A B J q K ∧ ∀ x, Pm_d I ω A B J n d x ↔ M.mem x B ∧
        (if a then ∃ i c, M.PairMember I i c G ∧ Pm_d I ω A B J n c x
         else ∀ i c, M.PairMember I i c G → Pm_d I ω A B J n c x) := by
    obtain ⟨d, hd, val⟩ := pm_countable_l I hZF hB hA ha hJ choice hH.1 hg a
    obtain ⟨q, hq⟩ := ppack_exists_l I n t d
    have code : Pc_d I ω A n t q := ⟨hH.1, hH.2.1, d, hq, hd⟩
    obtain ⟨K, hk, _⟩ := pden_exists_unique_l I hZF (B := B) (J := J) hB.1 (pc_code_l I code)
    exact ⟨d, q, K, hd, hq, code, hk, val⟩
  rcases hH.2.1 with ht | ht
  · obtain ⟨d, q, K, _, hq, hcode, hk, val⟩ := build b
    have ev {p c x} (hc : Pc_d I ω A n t p) (hp : Ppack_d I p n t c) (hx : M.mem x B) :
        Pev_d I ω A B J p x ↔ Pm_d I ω A B J n c x :=
      (pev_matrix_l I hZF hB.1 hc hp hx).trans ⟨fun h => h.elim And.right (fun h => (ptag_disjoint_l ht h.1).elim), fun h => Or.inl ⟨ht, h⟩⟩
    refine ⟨q, K, hcode, hk, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      have hxB := pden_subset_l I hk x hx
      have hv := ((val x).mp ((ev hcode hq hxB).mp ((pev_mem_l I hZF hB.1 hk).mp hx))).2
      refine ⟨hxB, ?_⟩
      cases b
      · intro i p hip
        obtain ⟨c, hc, _⟩ := (hH.2.2.2 i p hip).2
        exact (ev (pf_code_l I hH hip) hc hxB).mpr (hv i c ((eg i c).mpr ⟨p, hip, hc⟩))
      · obtain ⟨i, c, hic, hv⟩ := hv
        obtain ⟨p, hip, hc⟩ := (eg i c).mp hic
        exact ⟨i, p, hip, (ev (pf_code_l I hH hip) hc hxB).mpr hv⟩
    · rintro ⟨hxB, hv⟩
      apply (pev_mem_l I hZF hB.1 hk).mpr
      apply (ev hcode hq hxB).mpr
      apply (val x).mpr
      refine ⟨hxB, ?_⟩
      cases b
      · intro i c hic
        obtain ⟨p, hip, hc⟩ := (eg i c).mp hic
        exact (ev (pf_code_l I hH hip) hc hxB).mp (hv i p hip)
      · obtain ⟨i, p, hip, hv⟩ := hv
        obtain ⟨c, hc, _⟩ := (hH.2.2.2 i p hip).2
        exact ⟨i, c, (eg i c).mpr ⟨p, hip, hc⟩, (ev (pf_code_l I hH hip) hc hxB).mp hv⟩
  · obtain ⟨d, q, K, _, hq, hcode, hk, val⟩ := build (!b)
    have ev {p c x} (hc : Pc_d I ω A n t p) (hp : Ppack_d I p n t c) (hx : M.mem x B) :
        Pev_d I ω A B J p x ↔ ¬ Pm_d I ω A B J n c x :=
      (pev_matrix_l I hZF hB.1 hc hp hx).trans ⟨fun h => h.elim (fun h => (ptag_disjoint_l h.1 ht).elim) And.right, fun h => Or.inr ⟨ht, h⟩⟩
    refine ⟨q, K, hcode, hk, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      have hxB := pden_subset_l I hk x hx
      have hv := (ev hcode hq hxB).mp ((pev_mem_l I hZF hB.1 hk).mp hx)
      refine ⟨hxB, ?_⟩
      cases b
      · intro i p hip
        obtain ⟨c, hc, _⟩ := (hH.2.2.2 i p hip).2
        exact (ev (pf_code_l I hH hip) hc hxB).mpr (fun h => hv ((val x).mpr ⟨hxB, i, c, (eg i c).mpr ⟨p, hip, hc⟩, h⟩))
      · apply Classical.byContradiction
        intro he
        apply hv ((val x).mpr ⟨hxB, ?_⟩)
        intro i c hic
        obtain ⟨p, hip, hc⟩ := (eg i c).mp hic
        exact Classical.byContradiction (fun h => he ⟨i, p, hip, (ev (pf_code_l I hH hip) hc hxB).mpr h⟩)
    · rintro ⟨hxB, hv⟩
      apply (pev_mem_l I hZF hB.1 hk).mpr
      apply (ev hcode hq hxB).mpr
      intro hd
      have h := ((val x).mp hd).2
      cases b
      · obtain ⟨i, c, hic, h⟩ := h
        obtain ⟨p, hip, hc⟩ := (eg i c).mp hic
        exact (ev (pf_code_l I hH hip) hc hxB).mp (hv i p hip) h
      · obtain ⟨i, p, hip, hv⟩ := hv
        obtain ⟨c, hc, _⟩ := (hH.2.2.2 i p hip).2
        exact (ev (pf_code_l I hH hip) hc hxB).mp hv (h i c ((eg i c).mpr ⟨p, hip, hc⟩))

/-- 通常的可数码族入口；只调用当前实数空间的可数选择。 -/
theorem pf_countable_l (hZF : M.Models ZF) {ω A B J n t H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Rcc_d I ω B) (hH : Pf_d I ω A n t H) (b : Bool) :
    ∃ q K, Pc_d I ω A n t q ∧ Pden_d I ω A B J q K ∧ ∀ x, M.mem x K ↔ M.mem x B ∧
      (if b then ∃ i p, M.PairMember I i p H ∧ Pev_d I ω A B J p x
       else ∀ i p, M.PairMember I i p H → Pev_d I ω A B J p x) :=
  pf_countable_with_l I hZF hB hA ha hJ (fcc_real_l I hcc (fun i p hp => (hH.2.2.2 i p hp).1)) hH b

/-- 并交码的对象语言运算关系；等义码可以不同，解释由 Pden 唯一确定。 -/
def Pjoin_d (b : Bool) (ω A B J n t H q : M.Domain) : Prop := Pc_d I ω A n t q ∧ ∀ x,
  Pev_d I ω A B J q x ↔ M.mem x B ∧ (if b then ∃ i p, M.PairMember I i p H ∧ Pev_d I ω A B J p x
    else ∀ i p, M.PairMember I i p H → Pev_d I ω A B J p x)
def pjoin_m (b : Bool) {d} (ω A B J n t H q : Term d) : Formula 1 d := .conj (pc_m (𝒞 := 𝒞) ω A n t q)
  (.forallE (.iff (pev_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken q.weaken .newest)
    (.conj (.mem .newest B.weaken) (if b then .existsE (.existsE (.conj
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken)
      (pev_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken .newest (.bound 2))))
     else .forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken)
      (pev_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken .newest (.bound 2))))))))
@[simp] theorem pjoin_closed_l (b : Bool) {d} (ω A B J n t H q : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hB : B.freeSupport = []) (hJ : J.freeSupport = [])
    (hn : n.freeSupport = []) (ht : t.freeSupport = []) (hH : H.freeSupport = []) (hq : q.freeSupport = []) :
    (pjoin_m (𝒞 := 𝒞) b ω A B J n t H q).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [pjoin_m, Definitional.Formula.FreeClosed, hω, hA, hB, hJ, hn, ht, hH, hq]
theorem pjoin_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω A B J n t H q : Term d) :
    Formula.satisfies ρ (pjoin_m (𝒞 := 𝒞) b ω A B J n t H q) ↔
      Pjoin_d I b (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (t.eval ρ) (H.eval ρ) (q.eval ρ) := by
  cases b <;> simp only [pjoin_m, Pjoin_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_conj_iff, pc_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    pev_sat_l I hE, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_imp_iff, Definitional.Term.eval_weaken] <;> rfl

theorem pjoin_exists_l (hZF : M.Models ZF) {ω A B J n t H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Fcc_d I B H) (hH : Pf_d I ω A n t H) (b : Bool) : ∃ q, Pjoin_d I b ω A B J n t H q := by
  obtain ⟨q, K, hq, hk, val⟩ := pf_countable_with_l I hZF hB hA ha hJ hcc hH b
  exact ⟨q, hq, fun x => (pev_mem_l I hZF hB.1 hk).symm.trans (val x)⟩

end YesMetaZFC.SetTheory.Descriptive
