import YesMetaZFC.SetTheory.Descriptive.Projective.Delta

/-! # 同极性量词的合并

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
