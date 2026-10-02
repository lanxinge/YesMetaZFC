import YesMetaZFC.SetTheory.Descriptive.Projection

/-! # 沿内部 ω 的射影求值

在 P(B) 上实际构造“补后投影”自映射，再沿内部 ω 迭代。序列的存在性和
唯一性都在模型内验证；层号不是 Lean 的 Nat，因此包含非标准有限层。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Pseq_d (ω B J C H : M.Domain) : Prop where
  fn : M.IsSetFunction I H
  dom : M.IsDomainOf I ω H
  bound : ∀ n D, M.PairMember I n D H → M.MemberSubset D B
  zero : ∀ z, (∀ x, ¬ M.mem x z) → M.PairMember I z C H
  step : ∀ n m D E, M.SuccessorOf m n → M.PairMember I n D H → M.PairMember I m E H → Pstep_d I B J D E

def pseq_m {d} (ω B J C H : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 H)
  (.conj (Formula.isDomain 𝒞 ω H) (.conj
    (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken)
      (Formula.subset .newest B.weaken.weaken)))) (.conj
    (.forallE (.imp (Formula.isEmpty .newest) (Formula.orderedPairMem 𝒞 .newest C.weaken H.weaken)))
    (.forallE (.forallE (.forallE (.forallE (.imp (Formula.isSuccessor (.bound 2) (.bound 3))
      (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken)
        (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest H.weaken.weaken.weaken.weaken)
          (pstep_m (𝒞 := 𝒞) B.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken (.bound 1) .newest)))))))))))
derive_free_closed pseq_m
theorem pseq_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B J C H : Term d) :
    Formula.satisfies ρ (pseq_m (𝒞 := 𝒞) ω B J C H) ↔
      Pseq_d I (ω.eval ρ) (B.eval ρ) (J.eval ρ) (C.eval ρ) (H.eval ρ) := by
  simp only [pseq_m, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isSuccessor_iff, pstep_sat_l I, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.fn, h.dom, h.bound, h.zero, h.step⟩⟩

theorem pseq_exists_l (hZF : M.Models ZF) {ω B J C} (hω : M.IsOmega ω) (hC : M.MemberSubset C B) :
    ∃ H, Pseq_d I ω B J C H := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push J
  let φ : BinarySchema 2 := { body := pstep_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp D E : φ.denote ρ D E ↔ Pstep_d I B J D E := pstep_sat_l I _ _ _ _ _
  obtain ⟨F, hF, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := P)
    (fun D _ => (pstep_exists_l I hZF B J D).imp fun E h => (hp D E).mpr h)
    (fun D _ E V h k => pstep_unique_l I hZF.1 ((hp D E).mp h) ((hp D V).mp k))
    (fun D E _ h => (hP E).mpr (((hp D E).mp h).elim fun _ h => fun x hx => ((h.2 x).mp hx).1))
  obtain ⟨H, hH, hz, hs⟩ := ZFC.iterate_l I hZF hω hF ((hP C).mpr hC)
  exact ⟨H, hH.1, hH.2.1, fun n D h => (hP D).mp (hH.output_mem_of_pairMember h), hz,
    fun n m D E hnm hD hE => (hp D E).mp ((he D E).mp (hs n m D E hnm hD hE)).2⟩

/-- 比较性质本身先分离为内部集合，再使用内部归纳。 -/
theorem pseq_agree_l (hZF : M.Models ZF) {ω B J C H G} (hω : M.IsOmega ω)
    (hH : Pseq_d I ω B J C H) (hG : Pseq_d I ω B J C G) :
    ∀ n, M.mem n ω → ∀ D E, M.PairMember I n D H → M.PairMember I n E G → D = E := by
  let ρ : Env M 2 := (⟨fun _ => H, fun _ => H⟩ : Env M 1).push G
  let φ : UnarySchema 2 := {
    body := .forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4))
      (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (Formula.extensionalEq (.bound 1) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ D E, M.PairMember I n D H → M.PairMember I n E G → D = E := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  apply hω.induction (fun n => ∀ D E, M.PairMember I n D H → M.PairMember I n E G → D = E)
  · obtain ⟨X, hX⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨X, fun n => (hX n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz D E hD hE
    exact (hH.fn.2 z D C hD (hH.zero z hz)).trans (hG.fn.2 z C E (hG.zero z hz) hE)
  · intro n hn ih m hmn D E hD hE
    obtain ⟨K, hK⟩ := (hH.dom n).mp hn
    obtain ⟨L, hL⟩ := (hG.dom n).mp hn
    exact pstep_unique_l I hZF.1 (hH.step n m K D hmn hK hD) (ih K L hK hL ▸ hG.step n m L E hmn hL hE)

def Pval_d (ω B J n C D : M.Domain) : Prop := ∃ H, Pseq_d I ω B J C H ∧ M.PairMember I n D H
def pval_m {d} (ω B J n C D : Term d) : Formula 1 d := .existsE (.conj
  (pseq_m (𝒞 := 𝒞) ω.weaken B.weaken J.weaken C.weaken .newest)
  (Formula.orderedPairMem 𝒞 n.weaken D.weaken .newest))
derive_free_closed pval_m

theorem pval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B J n C D : Term d) :
    Formula.satisfies ρ (pval_m (𝒞 := 𝒞) ω B J n C D) ↔
      Pval_d I (ω.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (C.eval ρ) (D.eval ρ) := by
  simp only [pval_m, Pval_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    pseq_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem pval_exists_unique_l (hZF : M.Models ZF) {ω B J n C} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hC : M.MemberSubset C B) :
    ∃ D, Pval_d I ω B J n C D ∧ ∀ E, Pval_d I ω B J n C E → E = D := by
  obtain ⟨H, hH⟩ := pseq_exists_l I hZF (J := J) hω hC
  obtain ⟨D, hD⟩ := (hH.dom n).mp hn
  exact ⟨D, ⟨H, hH, hD⟩, fun E ⟨G, hG, hE⟩ => pseq_agree_l I hZF hω hG hH n hn E D hE hD⟩

theorem pval_unique_l (hZF : M.Models ZF) {ω B J n C D E} (hω : M.IsOmega ω)
    (h : Pval_d I ω B J n C D) (k : Pval_d I ω B J n C E) : D = E := by
  obtain ⟨H, hH, hD⟩ := h
  obtain ⟨G, hG, hE⟩ := k
  exact pseq_agree_l I hZF hω hH hG n ((hH.dom n).mpr ⟨D, hD⟩) D E hD hE

theorem pval_zero_l (hZF : M.Models ZF) {ω B J z C D} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (hC : M.MemberSubset C B) :
    Pval_d I ω B J z C D ↔ D = C := by
  constructor
  · rintro ⟨H, hH, hD⟩
    exact hH.fn.2 z D C hD (hH.zero z hz)
  · intro e
    obtain ⟨H, hH⟩ := pseq_exists_l I hZF (J := J) hω hC
    exact ⟨H, hH, e.symm ▸ hH.zero z hz⟩

theorem pval_succ_l (hZF : M.Models ZF) {ω B J n m C E} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) : Pval_d I ω B J m C E ↔
      ∃ D, Pval_d I ω B J n C D ∧ Pstep_d I B J D E := by
  constructor
  · rintro ⟨H, hH, hE⟩
    obtain ⟨D, hD⟩ := (hH.dom n).mp hn
    exact ⟨D, ⟨H, hH, hD⟩, hH.step n m D E hm hD hE⟩
  · rintro ⟨D, ⟨H, hH, hD⟩, hs⟩
    obtain ⟨m', hm', hmω⟩ := hω.1.2 n hn
    have hmω := Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hmω
    obtain ⟨E', hE⟩ := (hH.dom m).mp hmω
    exact ⟨H, hH, pstep_unique_l I hZF.1 (hH.step n m D E' hm hD hE) hs ▸ hE⟩

end YesMetaZFC.SetTheory.Descriptive
