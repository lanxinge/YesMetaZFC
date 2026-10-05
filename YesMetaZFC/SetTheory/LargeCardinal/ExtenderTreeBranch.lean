import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelationCode
import YesMetaZFC.SetTheory.Descriptive.TreeBounded

/-! # 实际源中任意字母表的树枝绝对性

先在源内分离真实子边，再用塌缩与可数枝闭包取得源内下降节点列。
其全部前缀构成无死节点树；最后逐坐标读取节点列，得到源内的总分支图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.tree_edges_l {ω κ K X R A J T : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hA : M.mem A X) (hT : M.mem T X)
    (hJ : Fseq_space_d I ω A J) (tree : Tree_d J T) : ∃ E, M.mem E X ∧ Edge_d I ω T E := by
  obtain ⟨P, hPX, hp⟩ := source.square_l hZF hT
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 3 := ⟨Fin.cases T (Fin.cases ω (fun _ => A)), fun _ => T⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
    (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (tb_step_m (.bound 4) (.bound 5) .newest (.bound 1)))) }
  have sat p : φ.denote ρ p ↔ ∃ t, M.mem t T ∧ ∃ s, M.mem s T ∧ KPair_d M p t s ∧ Tb_step_d ω A s t := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, tb_step_sat_l hZF.1]; rfl
  obtain ⟨E, hEX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (tb_step_delta_l ..))))
    ρ (Fin.cases hT (Fin.cases source.omega_mem (fun _ => hA))) hPX
  refine ⟨E, hEX, fun p he => (hp p).mp ((spec p).mp he).1 |>.elim fun t ht => ht.2.elim fun s hs => ⟨t, s, hs.2⟩, ?_⟩
  intro s t
  constructor
  · rintro ⟨p, hpair, he⟩
    obtain ⟨u, hu, v, hv, hp', hs⟩ := (sat p).mp ((spec p).mp he).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hpair hp'
    exact ⟨hv, hu, (tb_step_l hZF source.omega hJ (tree.1 s hv) (tree.1 t hu)).mp hs⟩
  · rintro ⟨hs, ht, hst⟩
    obtain ⟨p, hpair⟩ := (I).total t s
    exact ⟨p, hpair, (spec p).mpr ⟨(hp p).mpr ⟨t, ht, s, hs, hpair⟩,
      (sat p).mpr ⟨t, ht, s, hs, hpair, (tb_step_l hZF source.omega hJ (tree.1 s hs) (tree.1 t ht)).mpr hst⟩⟩⟩

theorem Ep_source_d.tree_branch_l {ω κ K X R A J T f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hA : M.mem A X) (hT : M.mem T X)
    (hJ : Fseq_space_d I ω A J) (tree : Tree_d J T) (hf : M.IsSetFunctionFromTo I f ω A)
    (branch : Branch_d J T f) : ∃ g, M.mem g X ∧ M.IsSetFunctionFromTo I g ω A ∧ Branch_d J T g := by
  have hω := source.omega
  -- 子边在源内实际存在；良基绝对性与源的枝闭包给出真实内部节点列。
  obtain ⟨E, hEX, edges⟩ := source.tree_edges_l hZF hA hT hJ tree
  obtain ⟨G, hGX, hG, desc⟩ := source.branch T E hT hEX (fun hw =>
    tree_branch_not_wf_l I hZF hω hJ hf branch edges ((source.collapse.wf_absolute_l (ZF.modelsKP hZF) hT hEX).mp hw))
  have fn := fn0_function_l (ZF.modelsKP hZF) hG
  have next i j s t (hs : M.SuccessorOf j i) (hi : Rd_entry_d i s G) (hj : Rd_entry_d j t G) : Step_d I ω s t :=
    ((edges.2 s t).mp (desc i j s t hs hi hj)).2.2
  have inc := ZF.cc_increasing_of_successor_l I hZF hω fn (fun i j s t hs hi hj => by
    obtain ⟨n, hn, hsn⟩ := (hJ s).mp (tree.1 s (hG.bound_l hi).2)
    obtain ⟨m, hm, htm⟩ := (hJ t).mp (tree.1 t (hG.bound_l hj).2)
    exact ((tree_step_iff_l I hZF hω hn hm hsn htm).mp (next i j s t hs hi hj)).2)
  obtain ⟨J', hJX, specJ⟩ := source.sequences A hA
  have eqJ := hZF.1.eq_of_same_members J' J (fun s => (specJ s).trans (hJ s).symm)
  have hJX : M.mem J X := eqJ ▸ hJX
  obtain ⟨c, hc⟩ := source.code
  -- 收集节点列的全部前缀，允许下降链从非空节点开始。
  let ρ : Env M 3 := ⟨Fin.cases ω (Fin.cases T (fun _ => G)), fun _ => ω⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 5)) (Formula.subset (.bound 2) .newest))) }
  have sat s : φ.denote ρ s ↔ ∃ i, M.mem i ω ∧ ∃ q, M.mem q T ∧ Rd_entry_d i q G ∧ M.MemberSubset s q := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff]; rfl
  obtain ⟨P, hPX, spec⟩ := sc_separate_source_l I hZF hω source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.atom _ _ _))))
    ρ (Fin.cases source.omega_mem (Fin.cases hT (fun _ => hGX))) hJX
  have read s : M.mem s P ↔ M.mem s J ∧ ∃ i, M.mem i ω ∧ ∃ q, M.mem q T ∧ Rd_entry_d i q G ∧ M.MemberSubset s q :=
    (spec s).trans (and_congr_right fun _ => sat s)
  have sub s (hs : M.mem s P) : M.mem s T := by
    obtain ⟨hsJ, _, _, q, hq, _, hsq⟩ := (read s).mp hs
    exact tree.2 q hq s hsJ hsq
  have pruned s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Tb_step_d ω A s t := by
    obtain ⟨hsJ, i, hi, q, hq, hiq, hsq⟩ := (read s).mp hs
    obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
    obtain ⟨v, hv, hjv⟩ := hG.2.1 j hjω
    obtain ⟨n, hn, hsn⟩ := (hJ s).mp hsJ
    obtain ⟨l, hl, hql⟩ := (hJ q).mp (tree.1 q hq)
    obtain ⟨m, hm, hvm⟩ := (hJ v).mp (tree.1 v hv)
    obtain ⟨hml, hqv⟩ := (tree_step_iff_l I hZF hω hl hm hql hvm).mp (next i j q v hj hiq hjv)
    have hnl : M.MemberSubset n l := fun a ha => by
      obtain ⟨b, _, hab⟩ := hsn.2.2 a ha
      exact hql.input_mem_of_pairMember (hab.elim fun p hp => ⟨p, hp.1, hsq p hp.2⟩)
    have hnm : M.mem n m := by
      rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn l hl with e | e | e
      · exact (hZF.1.eq_of_same_members n l e).symm ▸ hml.predecessor_mem
      · exact (hml n).mpr (Or.inl e)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (hnl l e)).elim
    obtain ⟨u, hu, huω⟩ := hω.1.2 n hn
    have hum : M.MemberSubset u m := fun a ha => ((hu a).mp ha).elim
      (fun ha => (hml a).mpr (Or.inl (hnl a ha))) (fun e => (hZF.1.eq_of_same_members a n e).symm ▸ hnm)
    obtain ⟨t, htv⟩ := ZF.exists_restriction hZF I v u
    have htu := htv.isSetFunctionFromTo hvm hum
    have hst := ds_prefix_mono_l I hsn htu.1 ((ds_restrict_iff_l I hsn hvm.1).mpr
      (fun p hp => hqv p (hsq p hp))) htv (fun a ha => (hu a).mpr (Or.inl ha))
    exact ⟨t, (read t).mpr ⟨(hJ t).mpr ⟨u, huω, htu⟩, j, hjω, v, hv, hjv,
      (ds_restrict_iff_l I htu hvm.1).mp htv⟩,
      n, hn, u, huω, fn0_of_function_l (ZF.modelsKP hZF) hsn, fn0_of_function_l (ZF.modelsKP hZF) htu, hu, hst⟩
  let η : Env M 3 := ⟨Fin.cases P (Fin.cases ω (fun _ => A)), fun _ => P⟩
  -- 先用无死节点性得到每个长度的前缀，再在源内逐坐标收集同一条枝。
  let ψ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 2)) (tb_step_m (.bound 3) (.bound 4) (.bound 1) .newest) }
  have choose s t : ψ.denote η s t ↔ M.mem t P ∧ Tb_step_d ω A s t := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, tb_step_sat_l hZF.1]; rfl
  obtain ⟨F, C, _, _, hF, select⟩ := sc_uniform_source_l hZF hω source.transitive hc source.theory ψ
    (.conj (.mem _ _) (tb_step_delta_l ..)) η (Fin.cases hPX (Fin.cases source.omega_mem (fun _ => hA))) hPX
    (fun s hs => (pruned s hs).imp fun t ht => ⟨source.transitive P hPX t ht.1, (choose s t).mpr ht⟩)
  have fnF := fn0_function_l (ZF.modelsKP hZF) (hF.retarget_l (fun s t h => ((choose s t).mp (select s t h)).1))
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨q, hq, hzq⟩ := hG.2.1 z hzω
  have hzP := (read z).mpr ⟨(hJ z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩, z, hzω, q, hq, hzq, fun p hp => (hz p hp).elim⟩
  obtain ⟨f₀, _, path⟩ := ds_path_l I hZF hω (fun s hs => (hJ s).mp ((read s).mp hs).1) fnF hz hzP
    (fun s t h => (tb_step_l hZF hω hJ ((read s).mp (hF.bound_l h).1).1
      ((read t).mp ((choose s t).mp (select s t h)).1).1).mp ((choose s t).mp (select s t h)).2)
  -- 原图列中的节点两两相容；逐坐标统一化不会改变任何已出现的值。
  have unique i n m s t x y (hs : Rd_entry_d n s G) (ht : Rd_entry_d m t G)
      (hx : Rd_entry_d i x s) (hy : Rd_entry_d i y t) : x = y := by
    obtain ⟨_, _, hsn⟩ := (hJ s).mp (tree.1 s (hG.bound_l hs).2)
    obtain ⟨_, _, htm⟩ := (hJ t).mp (tree.1 t (hG.bound_l ht).2)
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare n (hG.bound_l hs).1 m (hG.bound_l ht).1 with e | e | e
    · have en := hZF.1.eq_of_same_members n m e
      subst m
      exact htm.1.2 i x y (fn.1.2 n s t hs ht ▸ hx) hy
    · exact htm.1.2 i x y (hx.elim fun p hp => ⟨p, hp.1, inc n m s t e hs ht p hp.2⟩) hy
    · exact hsn.1.2 i x y hx (hy.elim fun p hp => ⟨p, hp.1, inc m n t s e ht hs p hp.2⟩)
  let ξ : BinarySchema 3 := { body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 6)) (rd_entry0_m (.bound 3) (.bound 2) .newest))) }
  have value i x : ξ.denote ρ i x ↔ ∃ n, M.mem n ω ∧ ∃ s, M.mem s T ∧ Rd_entry_d n s G ∧ Rd_entry_d i x s := by
    simp only [ξ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨g, D, hgX, _, hg, val⟩ := sc_uniform_source_l hZF hω source.transitive hc source.theory ξ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
    ρ (Fin.cases source.omega_mem (Fin.cases hT (fun _ => hGX))) source.omega_mem (fun i hi => by
      obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
      obtain ⟨p, hp, hpn, _⟩ := path j hjω
      obtain ⟨x, hx, hix⟩ := hpn.2.2 i hj.predecessor_mem
      obtain ⟨_, n, hn, s, hs, hns, hps⟩ := (read p).mp hp
      exact ⟨x, source.transitive A hA x hx, (value i x).mpr
        ⟨n, hn, s, hs, hns, hix.elim fun p hp => ⟨p, hp.1, hps p hp.2⟩⟩⟩)
  have hga := hg.retarget_l (C := A) (fun i x h => by
    obtain ⟨_, _, s, hs, _, his⟩ := (value i x).mp (val i x h)
    obtain ⟨_, _, hf⟩ := (hJ s).mp (tree.1 s hs)
    exact hf.output_mem_of_pairMember his)
  have gfn := fn0_function_l (ZF.modelsKP hZF) hga
  refine ⟨g, hgX, gfn, (Descriptive.tree_branch_l I hZF hω hJ gfn).mpr ?_⟩
  intro n hn
  obtain ⟨p, hp, hpn, _⟩ := path n hn
  refine ⟨p, sub p hp, (ds_restrict_iff_l I hpn gfn.1).mpr ?_⟩
  intro r hr
  obtain ⟨i, x, hir⟩ := hpn.1.1 r hr
  have hip : Rd_entry_d i x p := ⟨r, hir, hr⟩
  have hiω := hω.transitive hZF n hn i (hpn.input_mem_of_pairMember hip)
  obtain ⟨y, _, hiy⟩ := hg.2.1 i hiω
  obtain ⟨m, _, t, _, hmt, hty⟩ := (value i y).mp (val i y hiy)
  obtain ⟨_, l, _, s, _, hls, hps⟩ := (read p).mp hp
  have eq := unique i l m s t x y hls hmt ⟨r, hir, hps r hr⟩ hty
  obtain ⟨v, hv, hvg⟩ := eq.symm ▸ hiy
  exact (kpair_unique_l M hZF.1 hv hir) ▸ hvg

end YesMetaZFC.SetTheory.LargeCardinal
