import YesMetaZFC.SetTheory.Descriptive.Projective.Universal

/-! # 射影层次严格性

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
