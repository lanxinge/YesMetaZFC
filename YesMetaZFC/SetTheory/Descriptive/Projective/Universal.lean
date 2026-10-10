import YesMetaZFC.SetTheory.Descriptive.Analytic.UniversalClosed
import YesMetaZFC.SetTheory.Descriptive.Projective.ProjectionClosure

/-! # 全部正射影层的实际通用集

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
