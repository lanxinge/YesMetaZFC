import YesMetaZFC.SetTheory.Descriptive.Projective.CountableBase
import YesMetaZFC.SetTheory.Descriptive.Tree.Trace
import YesMetaZFC.Model.SetTheory.Internal.Quotient
import YesMetaZFC.SetTheory.Descriptive.Analytic.UniversalClosed

/-! # 全部内部层号上的可数并交矩阵

同时归纳并、交两种矩阵；后继交换二者，故没有外部层号递归。
最后沿常行对角取连续逆像，得到作用于同一个自由实数的并交码。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Jc_d (b : Bool) (ω A B J n H c : M.Domain) : Prop := Bcode_d I ω A A c ∧
  ∀ C K, Bden_d I ω A A B c C → Pval_d I ω B J n C K → Aj_d I b ω A B J n H K
def jc_m (b : Bool) {d} (ω A B J n H c : Term d) : Formula 1 d := .conj (bcode_m (𝒞 := 𝒞) ω A A c)
  (.forallE (.forallE (.imp
    (bden_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken A.weaken.weaken B.weaken.weaken c.weaken.weaken (.bound 1)) (.imp
    (pval_m (𝒞 := 𝒞) ω.weaken.weaken B.weaken.weaken J.weaken.weaken n.weaken.weaken (.bound 1) .newest)
    (aj_m (𝒞 := 𝒞) b ω.weaken.weaken A.weaken.weaken B.weaken.weaken J.weaken.weaken n.weaken.weaken H.weaken.weaken .newest)))))
derive_free_closed jc_m
theorem jc_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω A B J n H c : Term d) :
    Formula.satisfies ρ (jc_m (𝒞 := 𝒞) b ω A B J n H c) ↔
      Jc_d I b (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (H.eval ρ) (c.eval ρ) := by
  simp only [jc_m, Jc_d, Formula.satisfies_conj_iff, bcode_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, bden_sat_l I hE, pval_sat_l I hE, aj_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem jc_pair_l (hZF : M.Models ZF) {ω A B J H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Fcc_d I B H) (hH : Bfam_d I ω A A H) : ∀ n, M.mem n ω →
      ∃ c d, Jc_d I true ω A B J n H c ∧ Jc_d I false ω A B J n H d := by
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push H
  let φ : UnarySchema 5 := { body := .existsE (.existsE (.conj
    (jc_m (𝒞 := 𝒞) true (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1))
    (jc_m (𝒞 := 𝒞) false (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 3) .newest))) }
  have hp n : φ.denote ρ n ↔ ∃ c d, Jc_d I true ω A B J n H c ∧ Jc_d I false ω A B J n H d := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, jc_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨T, fun n => (hT n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz
    have base b : ∃ c, Jc_d I b ω A B J z H c := by
      obtain ⟨c, hc, hv⟩ := array_base_l I hZF hB hA ha hJ hH hz b
      refine ⟨c, hc, fun C K hC hK => ?_⟩
      have e := (pval_zero_l I hZF hB.1 hz (fun x hx => ((hC x).mp hx).1)).mp hK
      subst K
      exact fun w => (hC w).trans (and_congr_right fun hw => hv w hw)
    obtain ⟨c, hc⟩ := base true
    obtain ⟨d, hd⟩ := base false
    exact ⟨c, d, hc, hd⟩
  · rintro n hn ⟨c, d, hc, hd⟩ m hm
    have next {b c} (hc : Jc_d I b ω A B J n H c) : Jc_d I (!b) ω A B J m H c := by
      refine ⟨hc.1, fun C K hC hK => ?_⟩
      obtain ⟨D, hd, hk⟩ := (pval_succ_l I hZF hB.1 hn hm).mp hK
      exact aj_step_l I hZF hB hJ hcc hH hn hm (hc.2 C D hC hd) hk
    exact ⟨d, c, next hd, next hc⟩

/-- 输入实际内部 Borel 矩阵族，在任意内部 Σ 层构造同层并码或交码。 -/
theorem pm_countable_l (hZF : M.Models ZF) {ω A B J n H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hcc : Fcc_d I B H) (hn : M.mem n ω) (hH : Bfam_d I ω A A H) (b : Bool) :
    ∃ d, Bcode_d I ω A A d ∧ ∀ x, Pm_d I ω A B J n d x ↔ M.mem x B ∧
      (if b then ∃ i c, M.PairMember I i c H ∧ Pm_d I ω A B J n c x
       else ∀ i c, M.PairMember I i c H → Pm_d I ω A B J n c x) := by
  obtain ⟨c, c', hc, hc'⟩ := jc_pair_l I hZF hB hA ha hJ hcc hH n hn
  have matrix : ∃ c, Jc_d I b ω A B J n H c := by cases b; exact ⟨c', hc'⟩; exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := matrix
  obtain ⟨f, hf, diag⟩ := array_diag_l I hZF hB hA hJ
  obtain ⟨X, L, hL⟩ := lgraph_exists_l I hZF hB hJ
  obtain ⟨E, he⟩ := ha
  obtain ⟨d, hd, hd'⟩ := ppull_exists_l I hZF hB hA he hL hf.1 hn hc.1
  obtain ⟨C, hC, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨D, hD, _⟩ := bden_exists_unique_l I hZF ω A A B d
  obtain ⟨K, hK, _⟩ := pval_exists_unique_l I hZF (J := J) hB.1 hn (fun x hx => ((hC x).mp hx).1)
  obtain ⟨V, hV, _⟩ := pval_exists_unique_l I hZF (J := J) hB.1 hn (fun x hx => ((hD x).mp hx).1)
  have pull := ppull_value_l I hZF hB hA hJ he hL hf hn hc.1 hd hC hD hK hV
  have hj := hc.2 C K hC hK
  refine ⟨d, hd', fun x => (pm_mem_l I hZF hB.1 hD hV).symm.trans ((pull x).trans (and_congr_right fun hx => ?_))⟩
  obtain ⟨w, hw, hxw⟩ := hf.1.2.2 x hx
  have mem : (∃ y, M.PairMember I x y f ∧ M.mem y K) ↔ Aw_d I b ω A B J n H w := by
    refine ⟨fun ⟨y, hy, hk⟩ => ((hj w).mp (hf.1.1.2 x y w hy hxw ▸ hk)).2,
      fun h => ⟨w, hxw, (hj w).mpr ⟨hw, h⟩⟩⟩
  refine mem.trans ?_
  cases b
  · exact ⟨fun h i c hic => h i c x hic (diag x w hxw i (hH.2 i c hic).1),
      fun h i c y hic hr => (row_unique_l I hZF.1 (diag x w hxw i (hH.2 i c hic).1) hr) ▸ h i c hic⟩
  · exact ⟨fun ⟨i, c, y, hic, hr, hy⟩ => ⟨i, c, hic,
      row_unique_l I hZF.1 hr (diag x w hxw i (hH.2 i c hic).1) ▸ hy⟩,
      fun ⟨i, c, hic, hx⟩ => ⟨i, c, x, hic, diag x w hxw i (hH.2 i c hic).1, hx⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 指定层号与极性的内部射影码族 -/
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

/-! ## Σ、Π 层实际码族的同层可数并交 -/
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

/-! ## 相对射影点类的补对偶 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- Σ、Π 层的补对偶与对子空间取迹相容。 -/
theorem rclass_compl_l (hKP : M.Models KP) {ω A B J n X S P K L}
    (hX : M.MemberSubset X B) (hS : ∀ C, M.mem C S ↔ Ps_d I ω A B J n C)
    (hP : ∀ C, M.mem C P ↔ Pp_d I ω A B J n C) (hK : M.MemberSubset K X) (h : Cm_d X K L) :
    Rclass_d X S K ↔ Rclass_d X P L := by
  constructor
  · rintro ⟨C, hc, hk⟩
    obtain ⟨D, hd⟩ := cm_exists_l hKP B C
    obtain ⟨V, hv⟩ := tr_exists_l hKP X D
    have e := cm_unique_l hKP.1 (tr_compl_l hX hd hk hv) h
    exact ⟨D, (hP D).mpr ⟨C, (hS C).mp hc, hd⟩, e ▸ hv⟩
  · rintro ⟨D, hd, hl⟩
    obtain ⟨C, hc, hD⟩ := (hP D).mp hd
    obtain ⟨U, hu⟩ := tr_exists_l hKP X C
    have hcU := tr_compl_l hX hD hu hl
    have e := cm_unique_l hKP.1 (cm_symm_l (fun x hx => ((hu x).mp hx).1) hcU) (cm_symm_l hK h)
    exact ⟨C, (hS C).mpr hc, e ▸ hu⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 标准有限层数与交替实数量词正规形

Qn_d 是宿主给出的有限个交替量词的展开式，底层是实际 Borel 码。
只在标准数码 Num_d k n 处与内部层对照，不把内部 ω 假定为标准模型。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Qn_d (ω A B J : M.Domain) : Nat → Bool → M.Domain → M.Domain → Prop
  | 0, b, c, x => if b then Bsat_d I ω A A c x else ¬ Bsat_d I ω A A c x
  | k+1, true, c, x => ∃ y z, M.mem y B ∧ M.mem z B ∧ Rp_d I J x y z ∧ Qn_d ω A B J k false c z
  | k+1, false, c, x => ∀ y z, M.mem y B → M.mem z B → Rp_d I J x y z → Qn_d ω A B J k true c z

def qn_m : (k : Nat) → (b : Bool) → {d : Nat} → (ω A B J c x : Term d) → Formula 1 d
  | 0, b, _, ω, A, _, _, c, x => if b then bsat_m (𝒞 := 𝒞) ω A A c x else .neg (bsat_m (𝒞 := 𝒞) ω A A c x)
  | k+1, true, _, ω, A, B, J, c, x => .existsE (.existsE (.conj (.mem (.bound 1) B.weaken.weaken) (.conj
      (.mem .newest B.weaken.weaken) (.conj (rp_m (𝒞 := 𝒞) J.weaken.weaken x.weaken.weaken (.bound 1) .newest)
      (qn_m k false ω.weaken.weaken A.weaken.weaken B.weaken.weaken J.weaken.weaken c.weaken.weaken .newest)))))
  | k+1, false, _, ω, A, B, J, c, x => .forallE (.forallE (.imp (.mem (.bound 1) B.weaken.weaken) (.imp
      (.mem .newest B.weaken.weaken) (.imp (rp_m (𝒞 := 𝒞) J.weaken.weaken x.weaken.weaken (.bound 1) .newest)
      (qn_m k true ω.weaken.weaken A.weaken.weaken B.weaken.weaken J.weaken.weaken c.weaken.weaken .newest)))))
@[simp] theorem qn_closed_l (k : Nat) (b : Bool) {d} (ω A B J c x : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hB : B.freeSupport = [])
    (hJ : J.freeSupport = []) (hc : c.freeSupport = []) (hx : x.freeSupport = []) :
    (qn_m (𝒞 := 𝒞) k b ω A B J c x).FreeClosed := by
  induction k generalizing b d with
  | zero => cases b <;> simp -implicitDefEqProofs [qn_m, Definitional.Formula.FreeClosed, hω, hA, hc, hx]
  | succ k ih => cases b <;> simp -implicitDefEqProofs [qn_m, Definitional.Formula.FreeClosed, ih, hω, hA, hB, hJ, hc, hx]

theorem qn_sat_l (hE : Extensional M) (k : Nat) (b : Bool) {d} (ρ : Env M d) (ω A B J c x : Term d) :
    Formula.satisfies ρ (qn_m (𝒞 := 𝒞) k b ω A B J c x) ↔
      Qn_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) k b (c.eval ρ) (x.eval ρ) := by
  induction k generalizing b d with
  | zero => cases b <;> simp only [qn_m, Qn_d, Bool.false_eq_true, ↓reduceIte,
      Formula.satisfies_neg_iff, bsat_sat_l I hE]
  | succ k ih => cases b <;> simp only [qn_m, Qn_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rp_sat_l I, ih, Definitional.Term.eval_weaken] <;> rfl

theorem qn_dual_l (ω A B J : M.Domain) (k : Nat) (c x : M.Domain) :
    Qn_d I ω A B J k false c x ↔ ¬ Qn_d I ω A B J k true c x := by
  classical
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    constructor
    · intro h ⟨y, z, hy, hz, hp, hn⟩
      exact (ih z).mp hn (h y z hy hz hp)
    · intro h y z hy hz hp
      exact Classical.byContradiction (fun hn => h ⟨y, z, hy, hz, hp, (ih z).mpr hn⟩)

theorem pm_standard_l (hZF : M.Models ZF) {ω A B J k n c x} (hω : M.IsOmega ω) (hn : Num_d k n) :
    Pm_d I ω A B J n c x ↔ M.mem x B ∧ Qn_d I ω A B J k true c x := by
  induction k generalizing n x with
  | zero => exact pm_zero_l I hZF hω hn
  | succ k ih =>
    obtain ⟨m, hm, hnm⟩ := hn
    refine (pm_succ_l I hZF hω (num_mem_l hZF.1 hω hm) hnm).trans (and_congr_right fun _ => ?_)
    apply exists_congr; intro y
    apply exists_congr; intro z
    exact and_congr_right fun _ => and_congr_right fun hz => and_congr_right fun _ =>
      ((not_congr ((ih hm).trans ⟨And.right, fun h => ⟨hz, h⟩⟩)).trans (qn_dual_l I ω A B J k c z).symm)

/-- 标准 Σ¹_k 恰为 k 个交替实数量词作用于 Borel 矩阵所得的集合。 -/
theorem ps_standard_l (hZF : M.Models ZF) {ω A B J k n K} (hω : M.IsOmega ω) (hn : Num_d k n) :
    Ps_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x,
      M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k true c x := by
  constructor
  · rintro ⟨c, C, hc, hC, hv⟩
    exact ⟨c, hc, fun x => (pm_mem_l I hZF hω hC hv).trans (pm_standard_l I hZF hω hn)⟩
  · rintro ⟨c, hc, hk⟩
    obtain ⟨C, hC, _⟩ := bden_exists_unique_l I hZF ω A A B c
    obtain ⟨L, hL, _⟩ := pval_exists_unique_l I hZF (J := J) hω (num_mem_l hZF.1 hω hn) (fun x hx => ((hC x).mp hx).1)
    have e := hZF.1.eq_of_same_members L K (fun x => (pm_mem_l I hZF hω hC hL).trans
      ((pm_standard_l I hZF hω hn).trans (hk x).symm))
    exact ⟨c, C, hc, hC, e ▸ hL⟩

/-- 标准 Π¹_k 由同长度的全称起始交替式刻画。 -/
theorem pp_standard_l (hZF : M.Models ZF) {ω A B J k n K} (hω : M.IsOmega ω) (hn : Num_d k n) :
    Pp_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x,
      M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k false c x := by
  constructor
  · rintro ⟨L, hl, hk⟩
    obtain ⟨c, hc, hv⟩ := (ps_standard_l I hZF hω hn).mp hl
    exact ⟨c, hc, fun x => (hk x).trans (and_congr_right fun hx =>
      (not_congr ((hv x).trans ⟨And.right, fun h => ⟨hx, h⟩⟩)).trans (qn_dual_l I ω A B J k c x).symm)⟩
  · rintro ⟨c, hc, hk⟩
    obtain ⟨L, hl⟩ := cm_exists_l (ZF.modelsKP hZF) B K
    have sub : M.MemberSubset K B := fun x hx => ((hk x).mp hx).1
    refine ⟨L, (ps_standard_l I hZF hω hn).mpr ⟨c, hc, fun x => ?_⟩, cm_symm_l sub hl⟩
    classical
    refine (hl x).trans (and_congr_right fun hx => ?_)
    simpa only [Classical.not_not] using
      (not_congr (((hk x).trans ⟨And.right, fun h => ⟨hx, h⟩⟩).trans (qn_dual_l I ω A B J k c x)))

/-- 对每个标准 k 实际给出唯一内部层号，并同时返回 Σ、Π 的对应。 -/
theorem standard_level_l (hZF : M.Models ZF) {ω A B J} (hω : M.IsOmega ω) (k : Nat) :
    ∃ n, Num_d k n ∧ M.mem n ω ∧ (∀ m, Num_d k m → m = n) ∧ ∀ K,
      (Ps_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x, M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k true c x) ∧
      (Pp_d I ω A B J n K ↔ ∃ c, Bcode_d I ω A A c ∧ ∀ x, M.mem x K ↔ M.mem x B ∧ Qn_d I ω A B J k false c x) := by
  obtain ⟨n, hn⟩ := num_exists_l (ZF.modelsKP hZF) k
  exact ⟨n, hn, num_mem_l hZF.1 hω hn, fun _ h => num_unique_l hZF.1 h hn,
    fun _ => ⟨ps_standard_l I hZF hω hn, pp_standard_l I hZF hω hn⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 保持极性的升层、连续逆像与子空间解释 -/
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

/-! ## 实际码族的解释函数图及 Δ 层可数运算

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

/-! ## 同极性量词的合并

正层 Σ 对投影封闭，正层 Π 对全称实数量词封闭。相邻的两个存在见证
通过既有配对重括号合成一个；这里不使用可数选择。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ac_graph_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ f, Cont_d I A B f ∧
      ∀ p q, M.PairMember I p q f ↔ M.mem p B ∧ Ac_d I ω J ω p q := by
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J
  let φ : BinarySchema 2 := { body := ac_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 3) (.bound 1) .newest }
  have hp p q : φ.denote ρ p q ↔ Ac_d I ω J ω p q := ac_sat_l I hZF.1 _ _ _ _ _ _
  obtain ⟨f, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := B)
    (fun p hpB => (ac_exists_l I hZF hJ ((hB.2 p).mp hpB)).imp fun q h => (hp p q).mpr h.2)
    (fun _ _ _ _ h k => ac_unique_l I hZF.1 hJ ((hp _ _).mp h) ((hp _ _).mp k))
    (by
      intro p q hpB hq
      obtain ⟨r, hr, hr'⟩ := ac_exists_l I hZF hJ ((hB.2 p).mp hpB)
      exact ac_unique_l I hZF.1 hJ hr' ((hp p q).mp hq) ▸ (hB.2 r).mpr hr)
  have eqn p q : M.PairMember I p q f ↔ M.mem p B ∧ Ac_d I ω J ω p q :=
    (ef p q).trans (and_congr_right fun _ => hp p q)
  refine ⟨f, ⟨hf, fun p q s hpq hs hsq => ?_⟩, eqn⟩
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  have hpf := (hB.2 p).mp (hf.input_mem_of_pairMember hpq)
  have hqf := (hB.2 q).mp (hf.output_mem_of_pairMember hpq)
  obtain ⟨t, ht, hr, _⟩ := ds_prefix_l I hZF hB.1 hpf hn
  have htp := (ds_restrict_iff_l I ht hpf.1).mp hr
  obtain ⟨u, hu, htu⟩ := ac_exists_l I hZF hJ ht
  have eu := ((ds_restrict_iff_l I hu hqf.1).mpr (ac_sub_l I hJ htu ((eqn p q).mp hpq).2 htp)).eq hZF.1
    ((ds_restrict_iff_l I hs hqf.1).mpr hsq)
  exact ⟨t, (hA t).mpr ⟨n, hn, ht⟩, htp,
    fun p' q' hpq' htp' => eu ▸ ac_sub_l I hJ htu ((eqn p' q').mp hpq').2 htp'⟩

theorem ps_pull_l (hZF : M.Models ZF) {ω A B J n f K V} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hf : Cont_d I A B f) (hk : Ps_d I ω A B J n K) (hv : Ip_d I B f K V) : Ps_d I ω A B J n V := by
  obtain ⟨z, hz, _⟩ := hB.1.1.1
  obtain ⟨p, hp, hk⟩ := (pc_sigma_l I hn hz).mp hk
  obtain ⟨q, L, hq, hl, hv'⟩ := pc_pull_l I hZF hB hA ha hJ hp hk hf
  exact ip_unique_l I hZF.1 hv' hv ▸ (pc_sigma_l I hn hz).mpr ⟨q, hq, hl⟩

theorem pp_pull_l (hZF : M.Models ZF) {ω A B J n f K V} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hf : Cont_d I A B f) (hk : Pp_d I ω A B J n K) (hv : Ip_d I B f K V) : Pp_d I ω A B J n V := by
  obtain ⟨o, ho, _⟩ := hB.1.exists_ordinalOne_mem
  obtain ⟨p, hp, hk⟩ := (pc_pi_l I hn ho).mp hk
  obtain ⟨q, L, hq, hl, hv'⟩ := pc_pull_l I hZF hB hA ha hJ hp hk hf
  exact ip_unique_l I hZF.1 hv' hv ▸ (pc_pi_l I hn ho).mpr ⟨q, hq, hl⟩

theorem ps_project_l (hZF : M.Models ZF) {ω A B J n m K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hk : Ps_d I ω A B J m K) (hl : Pr_d I B J K L) : Ps_d I ω A B J m L := by
  obtain ⟨R, hr, hRK⟩ := (ps_succ_l I hZF hB.1 hn hm).mp hk
  obtain ⟨f, hf, ef⟩ := ac_graph_l I hZF hB hA hJ
  obtain ⟨S, hs⟩ := ip_exists_l I hZF B f R
  refine (ps_succ_l I hZF hB.1 hn hm).mpr ⟨S, pp_pull_l I hZF hB hA ha hJ hn hf hr hs, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨hxB, y, p, hyB, hpB, hxy, hpK⟩ := (hl x).mp hx
    obtain ⟨_, z, q, hzB, hqB, hpz, hqR⟩ := (hRK p).mp hpK
    have hxf := (hB.2 x).mp hxB
    have hyf := (hB.2 y).mp hyB
    have hzf := (hB.2 z).mp hzB
    obtain ⟨w, hw, hyz⟩ := rp_exists_l I hZF hJ hyf hzf
    obtain ⟨r, hrf, hxw⟩ := rp_exists_l I hZF hJ hxf hw
    have hrB := (hB.2 r).mpr hrf
    have hfr := (ef r q).mpr ⟨hrB, x, y, z, w, p, hxf, hyf, hzf, hw, (hB.2 p).mp hpB, hyz, hxw, hxy, hpz⟩
    exact ⟨hxB, w, r, (hB.2 w).mpr hw, hrB, hxw, (hs r).mpr ⟨hrB, q, hfr, hqR⟩⟩
  · rintro ⟨hxB, w, r, hwB, _, hxw, hrS⟩
    obtain ⟨_, q, hrq, hqR⟩ := (hs r).mp hrS
    obtain ⟨_, x', y, z, w', p, hx, hy, hz, hw, hp, hyz, hxw', hxy, hpz⟩ := (ef r q).mp hrq
    obtain ⟨ex, ew⟩ := rp_injective_l I hZF.1 hJ hx hw ((hB.2 x).mp hxB) ((hB.2 w).mp hwB) hxw' hxw
    subst x' w'
    have hpK := (hRK p).mpr ⟨(hB.2 p).mpr hp, z, q, (hB.2 z).mpr hz, hf.1.output_mem_of_pairMember hrq, hpz, hqR⟩
    exact (hl x).mpr ⟨hxB, y, p, (hB.2 y).mpr hy, (hB.2 p).mpr hp, hxy, hpK⟩

theorem pp_all_l (hZF : M.Models ZF) {ω A B J n m K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hk : Pp_d I ω A B J m K) (hl : All_d I B J K L) : Pp_d I ω A B J m L := by
  obtain ⟨D, hd, hk⟩ := hk
  obtain ⟨V, hv⟩ := pr_exists_l I hZF B J D
  obtain ⟨U, hu⟩ := cm_exists_l (ZF.modelsKP hZF) B V
  have hall := all_compl_l I (cm_symm_l (ps_subset_l I hd) hk) hv hu
  exact all_unique_l I hZF.1 hall hl ▸ ⟨V, ps_project_l I hZF hB hA ha hJ hn hm hd hv, hu⟩

/-- 对已有正层 Σ 码加存在量词，直接返回同层实际码和解释。 -/
theorem pc_project_l (hZF : M.Models ZF) {ω A B J n m z p K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hz : ∀ x, ¬ M.mem x z)
    (hp : Pc_d I ω A m z p) (hk : Pden_d I ω A B J p K) :
    ∃ q L, Pc_d I ω A m z q ∧ Pden_d I ω A B J q L ∧ Pr_d I B J K L := by
  obtain ⟨L, hl⟩ := pr_exists_l I hZF B J K
  obtain ⟨q, hq, hv⟩ := (pc_sigma_l I hp.1 hz).mp
    (ps_project_l I hZF hB hA ha hJ hn hm ((pc_sigma_l I hp.1 hz).mpr ⟨p, hp, hk⟩) hl)
  exact ⟨q, L, hq, hv, hl⟩

/-- 对已有正层 Π 码加全称量词，也直接返回同层实际码。 -/
theorem pc_all_l (hZF : M.Models ZF) {ω A B J n m o p K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (ho : M.IsOrdinalOne o)
    (hp : Pc_d I ω A m o p) (hk : Pden_d I ω A B J p K) :
    ∃ q L, Pc_d I ω A m o q ∧ Pden_d I ω A B J q L ∧ All_d I B J K L := by
  obtain ⟨L, hl⟩ := all_exists_l I hZF B J K
  obtain ⟨q, hq, hv⟩ := (pc_pi_l I hp.1 ho).mp
    (pp_all_l I hZF hB hA ha hJ hn hm ((pc_pi_l I hp.1 ho).mpr ⟨p, hp, hk⟩) hl)
  exact ⟨q, L, hq, hv, hl⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## ZF 中各层的二元布尔码运算

二元指标上的见证选择由两次存在消去直接构造；不调用 AC_ω(B)。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem fcc_empty_l {B H : M.Domain} (hh : ∀ x, ¬ M.mem x H) : Fcc_d I B H := by
  intro D hd R _
  have he i : ¬ M.mem i D := fun hi => ((hd i).mp hi).elim fun _ hp => hp.elim fun p hp => hh p hp.2
  exact ⟨D, ds_empty_fun_l I he, fun i x h => (he i ((ds_empty_fun_l I (X := B) he).input_mem_of_pairMember h)).elim⟩

theorem two_family_l (hKP : M.Models KP) {z o : M.Domain} (hzo : z ≠ o) (p q : M.Domain) :
    ∃ H, M.IsSetFunction I H ∧ ∀ i r, M.PairMember I i r H ↔ (i = z ∧ r = p) ∨ (i = o ∧ r = q) := by
  obtain ⟨a, ha⟩ := I.total z p
  obtain ⟨b, hb⟩ := I.total o q
  obtain ⟨H, hh⟩ := KP.exists_pair hKP a b
  have pair i r : M.PairMember I i r H ↔ (i = z ∧ r = p) ∨ (i = o ∧ r = q) :=
    ⟨fun ⟨c, hc, hcH⟩ => ((hh c).mp hcH).elim (fun e => Or.inl (I.injective (e ▸ hc) ha))
      (fun e => Or.inr (I.injective (e ▸ hc) hb)), fun h => h.elim
      (fun ⟨rfl, rfl⟩ => ⟨a, ha, (hh a).mpr (Or.inl rfl)⟩) (fun ⟨rfl, rfl⟩ => ⟨b, hb, (hh b).mpr (Or.inr rfl)⟩)⟩
  refine ⟨H, ⟨fun c hc => ((hh c).mp hc).elim (fun e => ⟨z, p, e.symm ▸ ha⟩) (fun e => ⟨o, q, e.symm ▸ hb⟩), ?_⟩, pair⟩
  intro i r s hr hs
  rcases (pair i r).mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases (pair _ s).mp hs with ⟨hi, rfl⟩ | ⟨hi, rfl⟩
  · rfl
  · exact (hzo hi).elim
  · exact (hzo hi.symm).elim
  · rfl

theorem fcc_two_l (hKP : M.Models KP) {B H z o p q} (hzo : z ≠ o)
    (hh : ∀ i r, M.PairMember I i r H ↔ (i = z ∧ r = p) ∨ (i = o ∧ r = q)) : Fcc_d I B H := by
  intro D hd R total
  have hz := (hd z).mpr ⟨p, (hh z p).mpr (Or.inl ⟨rfl, rfl⟩)⟩
  have ho := (hd o).mpr ⟨q, (hh o q).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  obtain ⟨a, ha, hza⟩ := total z hz
  obtain ⟨b, hb, hob⟩ := total o ho
  obtain ⟨F, hf, ef⟩ := two_family_l I hKP hzo a b
  have dom : M.IsDomainOf I D F := fun i => (hd i).trans
    ⟨fun ⟨r, hr⟩ => ((hh i r).mp hr).elim (fun h => ⟨a, (ef i a).mpr (Or.inl ⟨h.1, rfl⟩)⟩)
      (fun h => ⟨b, (ef i b).mpr (Or.inr ⟨h.1, rfl⟩)⟩),
      fun ⟨r, hr⟩ => ((ef i r).mp hr).elim (fun h => ⟨p, (hh i p).mpr (Or.inl ⟨h.1, rfl⟩)⟩)
        (fun h => ⟨q, (hh i q).mpr (Or.inr ⟨h.1, rfl⟩)⟩)⟩
  refine ⟨F, ⟨hf, dom, fun i hi => ?_⟩, fun i r hr => ?_⟩
  · obtain ⟨r, hr⟩ := (dom i).mp hi
    exact ⟨r, ((ef i r).mp hr).elim (fun h => h.2.symm ▸ ha) (fun h => h.2.symm ▸ hb), hr⟩
  · exact ((ef i r).mp hr).elim (fun ⟨e, h⟩ => e.symm ▸ h.symm ▸ hza) (fun ⟨e, h⟩ => e.symm ▸ h.symm ▸ hob)

theorem pc_binary_l (hZF : M.Models ZF) {ω A B J n t p q} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hp : Pc_d I ω A n t p) (hq : Pc_d I ω A n t q) (b : Bool) :
    ∃ r K, Pc_d I ω A n t r ∧ Pden_d I ω A B J r K ∧ ∀ x, M.mem x K ↔ M.mem x B ∧
      (if b then Pev_d I ω A B J p x ∨ Pev_d I ω A B J q x else Pev_d I ω A B J p x ∧ Pev_d I ω A B J q x) := by
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  obtain ⟨o, ho, hoω⟩ := hB.1.1.2 z hzω
  have hzo : z ≠ o := fun e => hz z (e.symm ▸ ho.predecessor_mem)
  obtain ⟨H, hh, eh⟩ := two_family_l I (ZF.modelsKP hZF) hzo p q
  have fam : Pf_d I ω A n t H := ⟨hp.1, hp.2.1, hh, fun i r hr => ((eh i r).mp hr).elim
    (fun ⟨e, h⟩ => ⟨e.symm ▸ hzω, h.symm ▸ hp.2.2⟩) (fun ⟨e, h⟩ => ⟨e.symm ▸ hoω, h.symm ▸ hq.2.2⟩)⟩
  obtain ⟨r, K, hr, hk, val⟩ := pf_countable_with_l I hZF hB hA ha hJ (fcc_two_l I (ZF.modelsKP hZF) hzo eh) fam b
  refine ⟨r, K, hr, hk, fun x => (val x).trans (and_congr_right fun _ => ?_)⟩
  cases b
  · exact ⟨fun h => ⟨h z p ((eh z p).mpr (Or.inl ⟨rfl, rfl⟩)), h o q ((eh o q).mpr (Or.inr ⟨rfl, rfl⟩))⟩,
      fun h i s hs => ((eh i s).mp hs).elim (fun e => e.2.symm ▸ h.1) (fun e => e.2.symm ▸ h.2)⟩
  · exact ⟨fun ⟨i, s, hs, hx⟩ => ((eh i s).mp hs).elim (fun e => Or.inl (e.2 ▸ hx)) (fun e => Or.inr (e.2 ▸ hx)),
      fun h => h.elim (fun h => ⟨z, p, (eh z p).mpr (Or.inl ⟨rfl, rfl⟩), h⟩)
        (fun h => ⟨o, q, (eh o q).mpr (Or.inr ⟨rfl, rfl⟩), h⟩)⟩

/-- 空并为空，空交为全空间；任意内部层号都不需要选择公理。 -/
theorem pc_empty_family_l (hZF : M.Models ZF) {ω A B J n t H} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (ht : (∀ x, ¬ M.mem x t) ∨ M.IsOrdinalOne t)
    (hh : ∀ x, ¬ M.mem x H) (b : Bool) : ∃ q K, Pc_d I ω A n t q ∧ Pden_d I ω A B J q K ∧
      ∀ x, M.mem x K ↔ b = false ∧ M.mem x B := by
  have no_pair i p : ¬ M.PairMember I i p H := fun ⟨r, _, hr⟩ => hh r hr
  have fam : Pf_d I ω A n t H := ⟨hn, ht, (ds_empty_fun_l I (X := ω) hh).1,
    fun i p hp => (no_pair i p hp).elim⟩
  obtain ⟨q, K, hq, hk, val⟩ := pf_countable_with_l I hZF hB hA ha hJ (fcc_empty_l I hh) fam b
  refine ⟨q, K, hq, hk, fun x => ?_⟩
  cases b <;> simpa [no_pair] using val x

theorem pd_binary_l (hZF : M.Models ZF) {ω A B J n K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hk : Pd_d I ω A B J n K) (hl : Pd_d I ω A B J n L) (b : Bool) :
    ∃ V, Pd_d I ω A B J n V ∧ ∀ x, M.mem x V ↔
      (if b then M.mem x K ∨ M.mem x L else M.mem x K ∧ M.mem x L) := by
  obtain ⟨z, hz, _⟩ := hB.1.1.1
  obtain ⟨o, ho, _⟩ := hB.1.exists_ordinalOne_mem
  obtain ⟨p, hp, hpk⟩ := (pc_sigma_l I hn hz).mp hk.1
  obtain ⟨q, hq, hql⟩ := (pc_sigma_l I hn hz).mp hl.1
  obtain ⟨r, hr, hrk⟩ := (pc_pi_l I hn ho).mp hk.2
  obtain ⟨s, hs, hsl⟩ := (pc_pi_l I hn ho).mp hl.2
  obtain ⟨a, U, hau, hu, eu⟩ := pc_binary_l I hZF hB hA ha hJ hp hq b
  obtain ⟨c, V, hcv, hv, ev⟩ := pc_binary_l I hZF hB hA ha hJ hr hs b
  have uv x : M.mem x U ↔ M.mem x V := by
    rw [eu x, ev x, ← pev_mem_l I hZF hB.1 hpk, ← pev_mem_l I hZF hB.1 hql,
      ← pev_mem_l I hZF hB.1 hrk, ← pev_mem_l I hZF hB.1 hsl]
  have e := hZF.1.eq_of_same_members V U (fun x => (uv x).symm)
  subst V
  refine ⟨U, ⟨(pc_sigma_l I hn hz).mpr ⟨a, hau, hu⟩, (pc_pi_l I hn ho).mpr ⟨c, hcv, hv⟩⟩, fun x => ?_⟩
  rw [eu x, ← pev_mem_l I hZF hB.1 hpk, ← pev_mem_l I hZF hB.1 hql]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  cases b
  · exact ps_subset_l I hk.1 x h.1
  · exact h.elim (ps_subset_l I hk.1 x) (ps_subset_l I hl.1 x)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 解析子空间上的相对 Suslin 定理

环境只要求解析，未加强为闭或 Borel。先把两个相对解析迹恢复为实际解析集，
再用分离码；输出仍是现有 Borel 码在子空间上的解释。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem an_inter_l (hZF : M.Models ZF) {ω A B J K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hk : An_d I ω A B J K) (hl : An_d I ω A B J L) :
    ∃ V, An_d I ω A B J V ∧ Tr_d K L V := by
  obtain ⟨o, ho, hoω⟩ := hB.1.exists_ordinalOne_mem
  obtain ⟨z, hz, _⟩ := hB.1.1.1
  obtain ⟨p, hp, hv⟩ := (pc_sigma_l I hoω hz).mp ((ps_one_l I hZF hB.1 hA ho).mpr hk)
  obtain ⟨q, hq, hw⟩ := (pc_sigma_l I hoω hz).mp ((ps_one_l I hZF hB.1 hA ho).mpr hl)
  obtain ⟨r, V, hr, hv', eqn⟩ := pc_binary_l I hZF hB hA ha hJ hp hq false
  refine ⟨V, (ps_one_l I hZF hB.1 hA ho).mp ((pc_sigma_l I hoω hz).mpr ⟨r, hr, hv'⟩), fun x => ?_⟩
  have e : M.mem x V ↔ M.mem x B ∧ (M.mem x K ∧ M.mem x L) := (eqn x).trans
    (and_congr_right fun _ => and_congr (pev_mem_l I hZF hB.1 hv).symm (pev_mem_l I hZF hB.1 hw).symm)
  exact e.trans ⟨And.right, fun h => ⟨((an_proj_l I).mp hk).elim (fun _ k => ((k.2 x).mp h.1).1), h⟩⟩

theorem anrel_analytic_l (hZF : M.Models ZF) {ω A B J X K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hX : An_d I ω A B J X) (hk : Anrel_d I ω A B J X K) : An_d I ω A B J K := by
  obtain ⟨L, hl, tr⟩ := hk
  obtain ⟨V, hv, tv⟩ := an_inter_l I hZF hB hA ha hJ hX hl
  exact tr_unique_l hZF.1 tv tr ▸ hv

theorem suslin_relative_l (hZF : M.Models ZF) {ω A B J X K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hX : An_d I ω A B J X) : Borel_d I ω A A X K ↔
      Anrel_d I ω A B J X K ∧ ∃ L, Cm_d X K L ∧ Anrel_d I ω A B J X L := by
  have subX : M.MemberSubset X B := ((an_proj_l I).mp hX).elim fun _ h => fun x hx => ((h.2 x).mp hx).1
  have to_rel {K} (hk : Borel_d I ω A A X K) : Anrel_d I ω A B J X K := by
    obtain ⟨c, hc, hk⟩ := hk
    obtain ⟨C, hC, _⟩ := bden_exists_unique_l I hZF ω A A B c
    exact ⟨C, borel_an_l I hZF hB hA ha hJ ⟨c, hc, hC⟩, fun x => (hk x).trans
      (and_congr_right fun hx => ((hC x).trans ⟨And.right, fun h => ⟨subX x hx, h⟩⟩).symm)⟩
  constructor
  · intro hk
    obtain ⟨L, hl, hb⟩ := borel_compl_l I hZF hB.1 hA hk
    exact ⟨to_rel hk, L, hl, to_rel hb⟩
  · rintro ⟨hk, L, hl, hr⟩
    obtain ⟨C, ⟨c, hc, hC⟩, sub, disj⟩ := an_separation_l I hZF hB hA ha hJ
      (anrel_analytic_l I hZF hB hA ha hJ hX hk) (anrel_analytic_l I hZF hB hA ha hJ hX hr)
      (fun x ⟨hx, hy⟩ => ((hl x).mp hy).2 hx)
    have subK : M.MemberSubset K X := hk.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
    refine ⟨c, hc, fun x => ⟨fun hx => ⟨subK x hx, ((hC x).mp (sub x hx)).2⟩, ?_⟩⟩
    rintro ⟨hx, hv⟩
    exact Classical.byContradiction (fun hn => disj x ⟨(hC x).mpr ⟨subX x hx, hv⟩, (hl x).mpr ⟨hx, hn⟩⟩)

/-- 同一相对集合的 Σ¹₁、Π¹₁ 两码直接产生该子空间上的 Borel 码。 -/
theorem prden_suslin_l (hZF : M.Models ZF) {ω A B J X K z o p q} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hX : An_d I ω A B J X) (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o)
    (hp : Pc_d I ω A o z p) (hq : Pc_d I ω A o o q)
    (hk : Prden_d I ω A B J X p K) (hk' : Prden_d I ω A B J X q K) : Borel_d I ω A A X K := by
  obtain ⟨C, hc, trC⟩ := hk
  obtain ⟨D, hd, trD⟩ := hk'
  have hc := (ps_one_l I hZF hB.1 hA ho).mp ((pc_sigma_l I hp.1 hz).mpr ⟨p, hp, hc⟩)
  obtain ⟨R, hr, compl⟩ := (pp_one_l I hZF hB.1 hA ho).mp ((pc_pi_l I hq.1 ho).mpr ⟨q, hq, hd⟩)
  obtain ⟨L, trL⟩ := tr_exists_l (ZF.modelsKP hZF) X R
  have subX : M.MemberSubset X B := ((an_proj_l I).mp hX).elim fun _ h => fun x hx => ((h.2 x).mp hx).1
  exact (suslin_relative_l I hZF hB hA ha hJ hX).mpr ⟨⟨C, hc, trC⟩, L,
    cm_symm_l (fun x hx => ((trL x).mp hx).1) (tr_compl_l subX compl trL trD), R, hr, trL⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 全部正射影层的实际通用集

起点来自通用闭集的投影；后继先补、逆重括号、再投影。
存在性用原公式对内部 ω 归纳，覆盖非标准模型的非标准有限层号。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Us_d (ω A B J n U : M.Domain) : Prop := Ps_d I ω A B J n U ∧
  ∀ K, Ps_d I ω A B J n K → ∃ p, Sect_d I B J U p K
def us_m {d} (ω A B J n U : Term d) : Formula 1 d := .conj
  (ps_m (𝒞 := 𝒞) ω A B J n U) (.forallE (.imp
  (ps_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken n.weaken .newest)
  (.existsE (sect_m (𝒞 := 𝒞) B.weaken.weaken J.weaken.weaken U.weaken.weaken .newest (.bound 1)))))
derive_free_closed us_m
theorem us_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n U : Term d) :
    Formula.satisfies ρ (us_m (𝒞 := 𝒞) ω A B J n U) ↔
      Us_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (U.eval ρ) := by
  simp only [us_m, Us_d, Formula.satisfies_conj_iff, ps_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, sect_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem universal_an_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∃ U, An_d I ω A B J U ∧ ∀ K, An_d I ω A B J K → ∃ p, Sect_d I B J U p K := by
  obtain ⟨C, hc, universal⟩ := universal_closed_l I hZF hB hA ha hJ
  obtain ⟨T, _, body⟩ := (closed_tree_l (ZF.modelsKP hZF)).mp hc
  have cb := tree_body_borel_l I hZF hB.1 hA ha body
  obtain ⟨f, hf, ef⟩ := ai_graph_l I hZF hB hA hJ
  obtain ⟨D, hd⟩ := ip_exists_l I hZF B f C
  obtain ⟨U, hu⟩ := pr_exists_l I hZF B J D
  refine ⟨U, (an_proj_l I).mpr ⟨D, borel_pull_l I hZF hB.1 hA ha hf cb hd, hu⟩, fun K hk => ?_⟩
  obtain ⟨R, hr, hp⟩ := (an_closed_l I hZF hB hA ha hJ).mp hk
  obtain ⟨p, hs⟩ := universal R hr
  exact ⟨p, sect_project_l I hZF hB hJ ef hd hu hs hp⟩

theorem us_one_l (hZF : M.Models ZF) {ω A B J o} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (ho : M.IsOrdinalOne o) : ∃ U, Us_d I ω A B J o U := by
  obtain ⟨U, hu, hs⟩ := universal_an_l I hZF hB hA ha hJ
  exact ⟨U, (ps_one_l I hZF hB.1 hA ho).mpr hu,
    fun K hk => hs K ((ps_one_l I hZF hB.1 hA ho).mp hk)⟩

theorem us_succ_l (hZF : M.Models ZF) {ω A B J n m U} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (h : Us_d I ω A B J n U) : ∃ V, Us_d I ω A B J m V := by
  obtain ⟨C, hc⟩ := cm_exists_l (ZF.modelsKP hZF) B U
  obtain ⟨f, hf, ef⟩ := ai_graph_l I hZF hB hA hJ
  obtain ⟨D, hd⟩ := ip_exists_l I hZF B f C
  obtain ⟨V, hv⟩ := pr_exists_l I hZF B J D
  refine ⟨V, (ps_succ_l I hZF hB.1 hn hm).mpr ⟨D,
    pp_pull_l I hZF hB hA ha hJ hn hf ⟨U, h.1, hc⟩ hd, hv⟩, fun K hk => ?_⟩
  obtain ⟨L, ⟨R, hr, hl⟩, hp⟩ := (ps_succ_l I hZF hB.1 hn hm).mp hk
  obtain ⟨p, hs⟩ := h.2 R hr
  exact ⟨p, sect_project_l I hZF hB hJ ef hd hv (sect_compl_l I hZF hB hJ hs hc hl) hp⟩

theorem us_positive_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∀ n, M.mem n ω → ∀ m, M.SuccessorOf m n → ∃ U, Us_d I ω A B J m U := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := { body := .forallE (.imp (Formula.isSuccessor .newest (.bound 1))
    (.existsE (us_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest))) }
  have hp n : φ.denote ρ n ↔ ∀ m, M.SuccessorOf m n → ∃ U, Us_d I ω A B J m U := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isSuccessor_iff, Formula.satisfies_exists_iff, us_sat_l I hZF.1]; rfl
  apply hB.1.induction (fun n => ∀ m, M.SuccessorOf m n → ∃ U, Us_d I ω A B J m U)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨C, fun n => (hC n).trans (and_congr_right fun _ => hp n)⟩
  · exact fun z hz m hm => us_one_l I hZF hB hA ha hJ ⟨z, hz, hm⟩
  · intro n hn ih m hm k hk
    obtain ⟨U, hu⟩ := ih m hm
    obtain ⟨m', hm', hmω⟩ := hB.1.1.2 n hn
    exact us_succ_l I hZF hB hA ha hJ (Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hmω) hk hu

/-- 非零内部层号的自动接口，不要求调用者先提供通用集。 -/
theorem universal_ps_l (hZF : M.Models ZF) {ω A B J n} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hne : ∃ i, M.mem i n) : ∃ U, Us_d I ω A B J n U := by
  obtain ⟨k, hk, hs⟩ := hB.1.exists_predecessor_of_mem_of_nonempty hZF hn hne
  exact us_positive_l I hZF hB hA ha hJ k hk n hs

theorem universal_pp_l (hZF : M.Models ZF) {ω A B J n} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hne : ∃ i, M.mem i n) :
    ∃ U, Pp_d I ω A B J n U ∧ ∀ K, Pp_d I ω A B J n K → ∃ p, Sect_d I B J U p K := by
  obtain ⟨V, hv⟩ := universal_ps_l I hZF hB hA ha hJ hn hne
  obtain ⟨U, hu⟩ := cm_exists_l (ZF.modelsKP hZF) B V
  refine ⟨U, ⟨V, hv.1, hu⟩, fun K ⟨L, hl, hk⟩ => ?_⟩
  obtain ⟨p, hp⟩ := hv.2 L hl
  exact ⟨p, sect_compl_l I hZF hB hJ hp hu hk⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 射影层次严格性

通用 Σ 集的负对角截面属于 Π 而不属于 Σ。第一投影给出相邻层的交叉包含，
于是 Σ、Π 每一步严格上升，Δ 从第一层以后严格上升；Δ₀=Δ₁=Borel。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pp_step_ps_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hk : Pp_d I ω A B J n K) : Ps_d I ω A B J m K := by
  obtain ⟨f, hf, ef⟩ := fst_graph_l I hZF hB hA hJ
  obtain ⟨V, hv⟩ := ip_exists_l I hZF B f K
  have bound : M.MemberSubset K B := hk.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
  refine (ps_succ_l I hZF hB.1 hn hm).mpr ⟨V, pp_pull_l I hZF hB hA ha hJ hn hf hk hv, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have hxf := (hB.2 x).mp (bound x hx)
    obtain ⟨p, hp, pair⟩ := rp_exists_l I hZF hJ hxf hxf
    have hpB := (hB.2 p).mpr hp
    exact ⟨bound x hx, x, p, bound x hx, hpB, pair,
      (ip_mem_l I hf.1 hv ((ef p x).mpr ⟨hpB, bound x hx, x, bound x hx, pair⟩)).mpr hx⟩
  · rintro ⟨hx, y, p, hy, hp, pair, hpV⟩
    exact (ip_mem_l I hf.1 hv ((ef p x).mpr ⟨hp, hx, y, hy, pair⟩)).mp hpV

theorem ps_step_pp_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hk : Ps_d I ω A B J n K) : Pp_d I ω A B J m K := by
  obtain ⟨L, hl⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  exact ⟨L, pp_step_ps_l I hZF hB hA ha hJ hn hm ⟨K, hk, hl⟩, cm_symm_l (ps_subset_l I hk) hl⟩

theorem ps_step_pd_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hk : Ps_d I ω A B J n K) : Pd_d I ω A B J m K :=
  ⟨ps_next_l I hZF hB hA ha hJ n hn m K hm hk, ps_step_pp_l I hZF hB hA ha hJ hn hm hk⟩

theorem pp_step_pd_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hk : Pp_d I ω A B J n K) : Pd_d I ω A B J m K := by
  obtain ⟨L, hl, hc⟩ := hk
  exact ⟨pp_step_ps_l I hZF hB hA ha hJ hn hm ⟨L, hl, hc⟩,
    L, ps_next_l I hZF hB hA ha hJ n hn m L hm hl, hc⟩

/-- 通用集的实际对角逆像及其补；该输入由 universal_ps_l 在所有正层构造。 -/
theorem us_diagonal_l (hZF : M.Models ZF) {ω A B J n U} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hu : Us_d I ω A B J n U) :
    ∃ S P, Ps_d I ω A B J n S ∧ ¬ Pp_d I ω A B J n S ∧
      Pp_d I ω A B J n P ∧ ¬ Ps_d I ω A B J n P ∧ Cm_d B S P := by
  obtain ⟨f, hf, ef⟩ := dg_graph_l I hZF hB hA hJ
  obtain ⟨S, hs⟩ := ip_exists_l I hZF B f U
  obtain ⟨P, hp⟩ := cm_exists_l (ZF.modelsKP hZF) B S
  have sk := ps_pull_l I hZF hB hA ha hJ hn hf hu.1 hs
  have np : ¬ Ps_d I ω A B J n P := by
    intro pk
    obtain ⟨p, hpB, sect⟩ := hu.2 P pk
    obtain ⟨q, _, pair⟩ := rp_exists_l I hZF hJ ((hB.2 p).mp hpB) ((hB.2 p).mp hpB)
    have ep := (ip_mem_l I hf.1 hs ((ef p q).mpr ⟨hpB, pair⟩)).trans (sect p q hpB pair)
    have no : ¬ M.mem p P := fun h => ((hp p).mp h).2 (ep.mpr h)
    exact no ((hp p).mpr ⟨hpB, fun h => no (ep.mp h)⟩)
  exact ⟨S, P, sk, fun h => np ((ps_pp_compl_l I hZF.1 (fun x hx => ((hp x).mp hx).1)
    (cm_symm_l (ps_subset_l I sk) hp)).mpr h), ⟨S, sk, hp⟩, np, hp⟩

/-- 每个非零内部层均有 Σ\Π、Π\Σ 的实际集合见证。 -/
theorem projective_nonselfdual_l (hZF : M.Models ZF) {ω A B J n} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hne : ∃ i, M.mem i n) :
    ∃ S P, Ps_d I ω A B J n S ∧ ¬ Pp_d I ω A B J n S ∧
      Pp_d I ω A B J n P ∧ ¬ Ps_d I ω A B J n P ∧ Cm_d B S P := by
  obtain ⟨U, hu⟩ := universal_ps_l I hZF hB hA ha hJ hn hne
  exact us_diagonal_l I hZF hB hA ha hJ hn hu

/-- Σ、Π 在每个内部后继层严格增长，包含第零层到第一层。 -/
theorem projective_strict_l (hZF : M.Models ZF) {ω A B J n m} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) :
    (∀ K, Ps_d I ω A B J n K → Pd_d I ω A B J m K) ∧
    (∀ K, Pp_d I ω A B J n K → Pd_d I ω A B J m K) ∧
    (∃ S, Ps_d I ω A B J m S ∧ ¬ Ps_d I ω A B J n S) ∧
    ∃ P, Pp_d I ω A B J m P ∧ ¬ Pp_d I ω A B J n P := by
  obtain ⟨m', hm', hmω⟩ := hB.1.1.2 n hn
  have hmω := Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hmω
  obtain ⟨S, P, hs, ns, hp, np, _⟩ := projective_nonselfdual_l I hZF hB hA ha hJ hmω ⟨n, hm.predecessor_mem⟩
  exact ⟨fun _ => ps_step_pd_l I hZF hB hA ha hJ hn hm, fun _ => pp_step_pd_l I hZF hB hA ha hJ hn hm,
    ⟨S, hs, fun h => ns (ps_step_pp_l I hZF hB hA ha hJ hn hm h)⟩,
    P, hp, fun h => np (pp_step_ps_l I hZF hB hA ha hJ hn hm h)⟩

theorem pd_strict_l (hZF : M.Models ZF) {ω A B J n m} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hn : M.mem n ω) (hne : ∃ i, M.mem i n) (hm : M.SuccessorOf m n) :
    (∀ K, Pd_d I ω A B J n K → Pd_d I ω A B J m K) ∧
      ∃ K, Pd_d I ω A B J m K ∧ ¬ Pd_d I ω A B J n K := by
  obtain ⟨_, P, _, _, hp, np, _⟩ := projective_nonselfdual_l I hZF hB hA ha hJ hn hne
  exact ⟨fun K hk => ps_step_pd_l I hZF hB hA ha hJ hn hm hk.1,
    P, pp_step_pd_l I hZF hB hA ha hJ hn hm hp, fun h => np h.1⟩

theorem an_non_borel_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∃ K, An_d I ω A B J K ∧ ¬ Borel_d I ω A A B K := by
  obtain ⟨o, ho, hoω⟩ := hB.1.exists_ordinalOne_mem
  obtain ⟨z, _, hz⟩ := ho
  obtain ⟨S, _, hs, ns, _⟩ := projective_nonselfdual_l I hZF hB hA ha hJ hoω ⟨z, hz.predecessor_mem⟩
  exact ⟨S, (ps_one_l I hZF hB.1 hA ⟨z, ‹∀ x, ¬ M.mem x z›, hz⟩).mp hs,
    fun h => ns (borel_pd_one_l I hZF hB hA ha hJ ⟨z, ‹∀ x, ¬ M.mem x z›, hz⟩ h).2⟩

end YesMetaZFC.SetTheory.Descriptive
