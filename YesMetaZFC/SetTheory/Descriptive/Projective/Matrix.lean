import YesMetaZFC.SetTheory.Descriptive.Projective.Pullback
import YesMetaZFC.SetTheory.Descriptive.Borel.Countable
import YesMetaZFC.SetTheory.Descriptive.RealChoice

/-! # 射影矩阵求值及可数行族的合取、析取 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pm_d (ω A B J n c x : M.Domain) : Prop := ∃ C K,
  Bden_d I ω A A B c C ∧ Pval_d I ω B J n C K ∧ M.mem x K
def pm_m {d} (ω A B J n c x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (bden_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken A.weaken.weaken B.weaken.weaken c.weaken.weaken (.bound 1)) (.conj
  (pval_m (𝒞 := 𝒞) ω.weaken.weaken B.weaken.weaken J.weaken.weaken n.weaken.weaken (.bound 1) .newest)
  (.mem x.weaken.weaken .newest))))
derive_free_closed pm_m
theorem pm_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n c x : Term d) :
    Formula.satisfies ρ (pm_m (𝒞 := 𝒞) ω A B J n c x) ↔
      Pm_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [pm_m, Pm_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bden_sat_l I hE, pval_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem pm_mem_l (hZF : M.Models ZF) {ω A B J n c C K x} (hω : M.IsOmega ω)
    (hc : Bden_d I ω A A B c C) (hk : Pval_d I ω B J n C K) : M.mem x K ↔ Pm_d I ω A B J n c x := by
  refine ⟨fun hx => ⟨C, K, hc, hk, hx⟩, fun ⟨D, L, hd, hl, hx⟩ => ?_⟩
  have e := hZF.1.eq_of_same_members D C (fun x => (hd x).trans (hc x).symm)
  exact pval_unique_l I hZF hω (e ▸ hl) hk ▸ hx

theorem pm_set_l (hZF : M.Models ZF) {ω A B J n c} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ K, ∀ x, M.mem x K ↔ Pm_d I ω A B J n c x := by
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨K, hk, _⟩ := pval_exists_unique_l I hZF (J := J) hω hn (fun x hx => ((hc x).mp hx).1)
  exact ⟨K, fun _ => pm_mem_l I hZF hω hc hk⟩

theorem pm_subset_l {ω A B J n c x} (h : Pm_d I ω A B J n c x) : M.mem x B := by
  obtain ⟨_, K, _, hv, hx⟩ := h
  obtain ⟨H, hH, hn⟩ := hv
  exact hH.bound n K hn x hx

theorem pm_zero_l (hZF : M.Models ZF) {ω A B J z c x} (hω : M.IsOmega ω) (hz : ∀ v, ¬ M.mem v z) :
    Pm_d I ω A B J z c x ↔ M.mem x B ∧ Bsat_d I ω A A c x := by
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  have hv := (pval_zero_l I hZF (J := J) hω hz (fun x hx => ((hc x).mp hx).1)).mpr rfl
  exact (pm_mem_l I hZF hω hc hv).symm.trans (hc x)

theorem pm_succ_l (hZF : M.Models ZF) {ω A B J n m c x} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) : Pm_d I ω A B J m c x ↔ M.mem x B ∧ ∃ y z,
      M.mem y B ∧ M.mem z B ∧ Rp_d I J x y z ∧ ¬ Pm_d I ω A B J n c z := by
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨K, hk, _⟩ := pval_exists_unique_l I hZF (J := J) hω hn (fun x hx => ((hc x).mp hx).1)
  obtain ⟨D, hd⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  obtain ⟨L, hl⟩ := pr_exists_l I hZF B J D
  have hv := (pval_succ_l I hZF hω hn hm).mpr ⟨K, hk, D, hd, hl⟩
  refine (pm_mem_l I hZF hω hc hv).symm.trans ((hl x).trans (and_congr_right fun _ =>
    exists_congr fun y => exists_congr fun z => and_congr_right fun _ => and_congr_right fun hz => and_congr_right fun _ => ?_))
  exact (hd z).trans ⟨fun h => (not_congr (pm_mem_l I hZF hω hc hk)).mp h.2,
    fun h => ⟨hz, (not_congr (pm_mem_l I hZF hω hc hk)).mpr h⟩⟩

def Aw_d (b : Bool) (ω A B J n H w : M.Domain) : Prop := if b then
  ∃ i c x, M.PairMember I i c H ∧ Row_d I J i w x ∧ Pm_d I ω A B J n c x
  else ∀ i c x, M.PairMember I i c H → Row_d I J i w x → Pm_d I ω A B J n c x
def aw_m (b : Bool) {d} (ω A B J n H w : Term d) : Formula 1 d := if b then
  .existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) H.weaken.weaken.weaken) (.conj
    (row_m (𝒞 := 𝒞) J.weaken.weaken.weaken (.bound 2) w.weaken.weaken.weaken .newest)
    (pm_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken (.bound 1) .newest)))))
  else .forallE (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) H.weaken.weaken.weaken) (.imp
    (row_m (𝒞 := 𝒞) J.weaken.weaken.weaken (.bound 2) w.weaken.weaken.weaken .newest)
    (pm_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken (.bound 1) .newest)))))
@[simp] theorem aw_closed_l (b : Bool) {d} (ω A B J n H w : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hB : B.freeSupport = []) (hJ : J.freeSupport = [])
    (hn : n.freeSupport = []) (hH : H.freeSupport = []) (hw : w.freeSupport = []) : (aw_m (𝒞 := 𝒞) b ω A B J n H w).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [aw_m, Definitional.Formula.FreeClosed, hω, hA, hB, hJ, hn, hH, hw]
theorem aw_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω A B J n H w : Term d) :
    Formula.satisfies ρ (aw_m (𝒞 := 𝒞) b ω A B J n H w) ↔
      Aw_d I b (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (H.eval ρ) (w.eval ρ) := by
  cases b <;> simp only [aw_m, Aw_d, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, row_sat_l I, pm_sat_l I hE, Definitional.Term.eval_weaken] <;> rfl

def Aj_d (b : Bool) (ω A B J n H K : M.Domain) : Prop := ∀ w, M.mem w K ↔ M.mem w B ∧ Aw_d I b ω A B J n H w
def aj_m (b : Bool) {d} (ω A B J n H K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (aw_m (𝒞 := 𝒞) b ω.weaken A.weaken B.weaken J.weaken n.weaken H.weaken .newest)))
derive_free_closed aj_m
theorem aj_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω A B J n H K : Term d) :
    Formula.satisfies ρ (aj_m (𝒞 := 𝒞) b ω A B J n H K) ↔
      Aj_d I b (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (H.eval ρ) (K.eval ρ) := by
  simp only [aj_m, Aj_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, aw_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Descriptive
