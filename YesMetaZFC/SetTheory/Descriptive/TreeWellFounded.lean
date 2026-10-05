import YesMetaZFC.SetTheory.Descriptive.Normal.Witness
import YesMetaZFC.SetTheory.Descriptive.TreeBounded

/-! # 可数前缀树的内部良基性

非空无死节点树用最小子编号生成分支；因此无分支与反向子边内部良基等价。
全程在 ZF 内选择自然数最小元，不假设模型外良基，也不调用依赖选择。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem tree_pruned_branch_l (hZF : M.Models ZF) {ω A B T} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (ht : Tree_d A T)
    (hne : ∃ s, M.mem s T) (hs : ∀ s, M.mem s T → ∃ t, M.mem t T ∧ Step_d I ω s t) :
    ∃ f, M.mem f B ∧ Branch_d A T f := by
  obtain ⟨E, he⟩ := ha
  obtain ⟨R, hr⟩ := tree_edges_l I hZF ω T
  let ρ : Env M 3 := ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push E).push T
  let φ : BinarySchema 3 := { body := .conj (.mem .newest (.bound 2)) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))
    (nj_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest))) }
  have hp s t : φ.denote ρ s t ↔ M.mem t T ∧ ∃ j, M.PairMember I t j E ∧ Nj_d I R E T s j := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, nj_sat_l I hZF.1]; rfl
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := T) (target := T)
    (by
      intro s hsT
      obtain ⟨t, htT, hst⟩ := hs s hsT
      obtain ⟨j, hj⟩ := nj_exists_l I hZF he.1 ⟨t, ht.1 t htT, (hr.2 s t).mpr ⟨hsT, htT, hst⟩, htT⟩
      obtain ⟨u, hu, _, huj⟩ := hj.1
      exact ⟨u, (hp s u).mpr ⟨hu, j, huj, hj⟩⟩)
    (by
      intro s _ t u ht' hu'
      obtain ⟨_, j, htj, hj⟩ := (hp s t).mp ht'
      obtain ⟨_, k, huk, hk⟩ := (hp s u).mp hu'
      exact he.2 t u j htj (nj_unique_l I hZF.1 (hB.1.isOrdinal hZF) he.1 hk hj ▸ huk))
    (fun s t _ ht' => ((hp s t).mp ht').1)
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  have hzA := (hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩
  have hzT := hne.elim fun s hs => ht.2 s hs z hzA (fun p hp => (hz p hp).elim)
  obtain ⟨f, hff, path⟩ := ds_path_l I hZF hB.1 (fun s hs => (hA s).mp (ht.1 s hs)) hf hz hzT (by
    intro s t hst
    obtain ⟨_, j, htj, hj⟩ := (hp s t).mp ((ef s t).mp hst).2
    obtain ⟨u, _, hus, huj⟩ := hj.1
    exact he.2 u t j huj htj ▸ ((hr.2 s u).mp hus).2.2)
  refine ⟨f, (hB.2 f).mpr hff, (tree_branch_l I hZF hB.1 hA hff).mpr ?_⟩
  intro n hn
  obtain ⟨s, hs, hsf, hsub⟩ := path n hn
  exact ⟨s, hs, (ds_restrict_iff_l I hsf hff.1).mpr hsub⟩

theorem tree_wf_of_no_branch_l (hZF : M.Models ZF) {ω A B T R} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (ht : Tree_d A T)
    (hr : Edge_d I ω T R) (hn : ∀ f, M.mem f B → ¬ Branch_d A T f) : Wf_rel_d T R := by
  classical
  intro Q hQT hQ
  apply Classical.byContradiction
  intro hmin
  have next q (hq : M.mem q Q) : ∃ v, M.mem v Q ∧ Step_d I ω q v := by
    apply Classical.byContradiction
    intro h
    exact hmin ⟨q, hq, fun v hv hvr => h ⟨v, hv, ((hr.2 q v).mp hvr).2.2⟩⟩
  obtain ⟨P, hP⟩ := ktree_exists_l (ZF.modelsKP hZF) A Q
  have sub : M.MemberSubset P T := fun s hs => ((hP s).mp hs).2.elim fun q hq =>
    ht.2 q (hQT q hq.1) s ((hP s).mp hs).1 hq.2
  have tree : Tree_d A P := ⟨fun s hs => ((hP s).mp hs).1, fun s hs t ht hts => by
    obtain ⟨_, q, hq, hsq⟩ := (hP s).mp hs
    exact (hP t).mpr ⟨ht, q, hq, fun p hp => hsq p (hts p hp)⟩⟩
  have pruned s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Step_d I ω s t := by
    obtain ⟨hsA, q, hqQ, hsq⟩ := (hP s).mp hs
    obtain ⟨v, hvQ, hqv⟩ := next q hqQ
    obtain ⟨n, hn, hsf⟩ := (hA s).mp hsA
    obtain ⟨l, hl, hqf⟩ := (hA q).mp (ht.1 q (hQT q hqQ))
    obtain ⟨m, hm, hvf⟩ := (hA v).mp (ht.1 v (hQT v hvQ))
    obtain ⟨hml, hqv⟩ := (tree_step_iff_l I hZF hB.1 hl hm hqf hvf).mp hqv
    have hnl : M.MemberSubset n l := fun i hi => by
      obtain ⟨a, _, hia⟩ := hsf.2.2 i hi
      exact hqf.input_mem_of_pairMember (hia.elim fun p hp => ⟨p, hp.1, hsq p hp.2⟩)
    have hnm : M.mem n m := by
      rcases (hB.1.isOrdinal hZF).wellOrder.linear.compare n hn l hl with e | e | e
      · exact (hZF.1.eq_of_same_members n l e).symm ▸ hml.predecessor_mem
      · exact (hml n).mpr (Or.inl e)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (hnl l e)).elim
    obtain ⟨u, hu, huω⟩ := hB.1.1.2 n hn
    have hum : M.MemberSubset u m := fun i hi => ((hu i).mp hi).elim
      (fun hi => (hml i).mpr (Or.inl (hnl i hi))) (fun e => (hZF.1.eq_of_same_members i n e).symm ▸ hnm)
    obtain ⟨t, htv⟩ := ZF.exists_restriction hZF I v u
    have htf := htv.isSetFunctionFromTo hvf hum
    have hst := ds_prefix_mono_l I hsf htf.1 ((ds_restrict_iff_l I hsf hvf.1).mpr
      (fun p hp => hqv p (hsq p hp))) htv (fun i hi => (hu i).mpr (Or.inl hi))
    exact ⟨t, (hP t).mpr ⟨(hA t).mpr ⟨u, huω, htf⟩, v, hvQ, (ds_restrict_iff_l I htf hvf.1).mp htv⟩,
      (tree_step_iff_l I hZF hB.1 hn huω hsf htf).mpr ⟨hu, hst⟩⟩
  have hne : ∃ s, M.mem s P := hQ.elim fun q hq => ⟨q, (hP q).mpr ⟨ht.1 q (hQT q hq), q, hq, fun _ => id⟩⟩
  obtain ⟨f, hf, hbranch⟩ := tree_pruned_branch_l I hZF hB hA ha tree hne pruned
  exact hn f hf (fun s hs hsf => sub s (hbranch s hs hsf))

theorem tree_wf_iff_l (hZF : M.Models ZF) {ω A B T R} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (ht : Tree_d A T) (hr : Edge_d I ω T R) :
    Wf_rel_d T R ↔ ∀ f, M.mem f B → ¬ Branch_d A T f := by
  exact ⟨fun hw f hf hb => tree_branch_not_wf_l I hZF hB.1 hA ((hB.2 f).mp hf) hb hr hw,
    tree_wf_of_no_branch_l I hZF hB hA ha ht hr⟩

end YesMetaZFC.SetTheory.Descriptive
