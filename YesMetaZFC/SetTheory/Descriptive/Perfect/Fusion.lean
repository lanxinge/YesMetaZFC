import YesMetaZFC.SetTheory.Descriptive.Perfect.Closed

/-! # 严格增长的内部前缀链之并

每一步至少增长一个内部坐标，因而第 n 个节点已经覆盖 n。
这同时给出无限函数图及任意有限前缀的阶段界。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem split_iter_length_l (hZF : M.Models ZF) {ω A J U L R F a H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (hH : It_d I ω U F a H) (step : ∀ b c, M.PairMember I b c F → M.PairMember I b c L ∨ M.PairMember I b c R) :
    ∀ n, M.mem n ω → ∀ b m, M.PairMember I n b H → M.IsSetFunctionFromTo I b m ω → M.MemberSubset n m := by
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push H
  let φ : UnarySchema 2 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 3)) (.imp
    (Formula.isFunctionFromTo 𝒞 (.bound 1) .newest (.bound 4)) (Formula.subset (.bound 2) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ b m, M.PairMember I n b H → M.IsSetFunctionFromTo I b m ω → M.MemberSubset n m := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_subset_iff]; rfl
  apply hω.induction
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => hp n)⟩
  · exact fun z hz _ _ _ _ i hi => (hz i hi).elim
  · intro n hn ih j hj b m hb hbf
    obtain ⟨c, hc, hnc⟩ := hH.1.2.2 n hn
    obtain ⟨k, hk, hcf⟩ := (hA c).mp (hs.1 c hc)
    obtain ⟨m', hm', hbf'⟩ := (hA b).mp (hs.1 b (hH.1.output_mem_of_pairMember hb))
    have e := hbf'.2.1.eq hZF.1 hbf.2.1
    subst m'
    have hkm := split_grow_l I hZF hω hJ hs hk hm' hcf hbf (step c b (hH.2.2 n j c b hj hnc hb))
    have hnk := ih c k hnc hcf
    have hnm : M.mem n m := by
      rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn k hk with e | e | e
      · exact (hZF.1.eq_of_same_members n k e).symm ▸ hkm
      · exact ((hω.isOrdinal hZF).mem hm').transitive k hkm n e
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (hnk k e)).elim
    exact fun i hi => ((hj i).mp hi).elim
      (fun hi => ((hω.isOrdinal hZF).mem hm').transitive k hkm i (hnk i hi))
      (fun e => (hZF.1.eq_of_same_members i n e).symm ▸ hnm)

theorem split_fusion_l (hZF : M.Models ZF) {ω A J U L R F a H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (hH : It_d I ω U F a H) (step : ∀ b c, M.PairMember I b c F → M.PairMember I b c L ∨ M.PairMember I b c R) :
    ∃ f, M.IsSetFunctionFromTo I f ω ω ∧ Cc_union_d I H f ∧
      ∀ s, M.mem s A → M.MemberSubset s f → ∃ n b, M.PairMember I n b H ∧ M.MemberSubset s b := by
  have len := split_iter_length_l I hZF hω hA hJ hs hH step
  have inc := ZF.cc_increasing_of_successor_l I hZF hω hH.1 (fun i j b c hij hb hc =>
    split_extend_l I hs (step b c (hH.2.2 i j b c hij hb hc)))
  obtain ⟨V, hv⟩ := ZF.exists_range_of_setFunction hZF I hH.1.1 hH.1.2.1
  obtain ⟨f, hf⟩ := KP.exists_union (ZF.modelsKP hZF) V
  have union : Cc_union_d I H f := fun p => (hf p).trans ⟨fun ⟨b, hb, hp⟩ =>
    ((hv b).mp hb).elim fun n hn => ⟨n, b, hn, hp⟩, fun ⟨n, b, hb, hp⟩ => ⟨b, (hv b).mpr ⟨n, hb⟩, hp⟩⟩
  have sub {n b} (hb : M.PairMember I n b H) : M.MemberSubset b f := fun p hp => (union p).mpr ⟨n, b, hb, hp⟩
  have nodes {n b} (hb : M.PairMember I n b H) := (hA b).mp (hs.1 b (hH.1.output_mem_of_pairMember hb))
  have pair i v : M.PairMember I i v f ↔ ∃ n b, M.PairMember I n b H ∧ M.PairMember I i v b := by
    exact ⟨fun ⟨p, hp, hpf⟩ => ((union p).mp hpf).elim fun n h => h.elim fun b h => ⟨n, b, h.1, p, hp, h.2⟩,
      fun ⟨n, b, hb, p, hp, hpb⟩ => ⟨p, hp, sub hb p hpb⟩⟩
  have total i (hi : M.mem i ω) : ∃ v, M.mem v ω ∧ M.PairMember I i v f := by
    obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
    obtain ⟨b, _, hb⟩ := hH.1.2.2 n hnω
    obtain ⟨m, _, hbf⟩ := nodes hb
    obtain ⟨v, hv, hiv⟩ := hbf.2.2 i (len n hnω b m hb hbf i hn.predecessor_mem)
    exact ⟨v, hv, (pair i v).mpr ⟨n, b, hb, hiv⟩⟩
  have ff : M.IsSetFunctionFromTo I f ω ω := by
    refine ⟨⟨fun p hp => ((union p).mp hp).elim fun n h => h.elim fun b h =>
      (nodes h.1).elim fun m h' => h'.2.1.1 p h.2, ?_⟩, fun i => ⟨fun hi => (total i hi).imp fun _ h => h.2, ?_⟩, total⟩
    · intro i v w hv hw
      obtain ⟨n, b, hb, hv⟩ := (pair i v).mp hv
      obtain ⟨m, c, hc, hw⟩ := (pair i w).mp hw
      obtain ⟨_, _, hbf⟩ := nodes hb
      obtain ⟨_, _, hcf⟩ := nodes hc
      have lift {b c} (h : M.MemberSubset b c) {v} (hv : M.PairMember I i v b) : M.PairMember I i v c :=
        hv.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
      rcases (hω.isOrdinal hZF).wellOrder.linear.compare n (hH.1.input_mem_of_pairMember hb) m (hH.1.input_mem_of_pairMember hc) with e | e | e
      · have eqn := hH.1.1.2 m b c (hZF.1.eq_of_same_members n m e ▸ hb) hc
        exact hcf.1.2 i v w (eqn ▸ hv) hw
      · exact hcf.1.2 i v w (lift (inc n m b c e hb hc) hv) hw
      · exact hbf.1.2 i v w hv (lift (inc m n c b e hc hb) hw)
    · rintro ⟨v, hv⟩
      obtain ⟨n, b, hb, hv⟩ := (pair i v).mp hv
      obtain ⟨m, hm, hbf⟩ := nodes hb
      exact hω.transitive hZF m hm i (hbf.input_mem_of_pairMember hv)
  refine ⟨f, ff, union, fun s hs hsf => ?_⟩
  obtain ⟨n, hn, hsn⟩ := (hA s).mp hs
  obtain ⟨b, _, hb⟩ := hH.1.2.2 n hn
  obtain ⟨m, _, hbm⟩ := nodes hb
  exact ⟨n, b, hb, ds_prefix_mono_l I hsn hbm.1 ((ds_restrict_iff_l I hsn ff.1).mpr hsf)
    ((ds_restrict_iff_l I hbm ff.1).mpr (sub hb)) (len n hn b m hb hbm)⟩

theorem fusion_projection_l (hZF : M.Models ZF) {ω A J U H f x y p} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (hU : M.MemberSubset U A) (hH : M.IsSetFunctionFromTo I H ω U)
    (hf : Cc_union_d I H f) (hx : M.IsSetFunctionFromTo I x ω ω) (hy : M.IsSetFunctionFromTo I y ω ω)
    (hp : M.IsSetFunctionFromTo I p ω ω) (pair : Rp_d I J p y f)
    (pre : ∀ n b, M.PairMember I n b H → Pre_d I ω J b x) : p = x := by
  have sub : M.MemberSubset p x := by
    intro q hq
    obtain ⟨i, a, hqa⟩ := hp.1.1 q hq
    have hi := hp.input_mem_of_pairMember ⟨q, hqa, hq⟩
    obtain ⟨b, hb, hib⟩ := hy.2.2 i hi
    obtain ⟨v, _, hv⟩ := np_total_l I hJ (hp.output_mem_of_pairMember ⟨q, hqa, hq⟩) hb
    obtain ⟨r, hr, hrf⟩ := (pair.2 i v).mpr ⟨a, b, ⟨q, hqa, hq⟩, hib, hv⟩
    obtain ⟨n, s, hs, hrs⟩ := (hf r).mp hrf
    obtain ⟨t, u, ps⟩ := fp_decode_l I hZF hA hJ (hU s (hH.output_mem_of_pairMember hs))
    have ps' : Rp_d I J t u s := ps.elim fun _ h => h.2.2.2
    obtain ⟨c, d, hic, _, hcd⟩ := (ps'.2 i v).mp ⟨r, hr, hrs⟩
    have ep := (np_injective_l I hJ hcd hv).1
    have sub := (pre_iff_l I hZF.1 hJ ps).mp (pre n s hs)
    obtain ⟨q', hq', hq'x⟩ := hic
    exact (I.unique hqa (ep ▸ hq')).symm ▸ sub q' hq'x
  exact ((ds_restrict_iff_l I hp hx.1).mpr sub).eq hZF.1 ((ds_restrict_iff_l I hx hx.1).mpr (fun _ => id))

end YesMetaZFC.SetTheory.Descriptive
