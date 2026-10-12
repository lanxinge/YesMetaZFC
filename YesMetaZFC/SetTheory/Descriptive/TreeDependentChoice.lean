import YesMetaZFC.SetTheory.Descriptive.TreeBounded
import YesMetaZFC.Model.SetTheory.DependentChoice

/-! # 任意集合字母表上的无枝树与良基性

依赖选择只用于无死节点树上的逐项延长链；链的并与良基秩均在 ZF 中构造。
内部长度遍历原模型的整个 ω，不要求字母表可数或 ω 外部标准。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable (hZF : M.Models ZF)
include hZF

theorem tree_pruned_dc_l {ω X F T : M.Domain} (hω : M.IsOmega ω) (dc : Dc_d I ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T) (ne : ∃ s, M.mem s T)
    (next : ∀ s, M.mem s T → ∃ t, M.mem t T ∧ Step_d I ω s t) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ Branch_d F T f := by
  let φ : BinarySchema 1 := { body := step_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  obtain ⟨R, _, read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ⟨fun _ => ω, fun _ => ω⟩ T
  have edges s t : M.PairMember I s t R ↔ M.mem s T ∧ M.mem t T ∧ Step_d I ω s t :=
    (read s t).trans (and_congr_right fun _ => and_congr_right fun _ => step_sat_l I hZF.1 ..)
  obtain ⟨e, he, heω⟩ := hω.1.1
  have root := ne.elim fun s hs => tree.2 s hs e ((space e).mpr ⟨e, heω, ds_empty_fun_l I he⟩)
    (fun x hx => (he x hx).elim)
  obtain ⟨H, fn, zero, chain⟩ := dc T R e root
    (fun s hs => (next s hs).imp fun t ht => ⟨ht.1, (edges s t).mpr ⟨hs, ht⟩⟩)
  obtain ⟨f, ff, path⟩ := ds_path_run_l I hZF hω (fun s hs => (space s).mp (tree.1 s hs)) fn he zero
    (fun i j s t hj hs ht => ((edges s t).mp (chain i j s t hj hs ht)).2.2)
  exact ⟨f, ff, (tree_branch_l I hZF hω space ff).mpr (fun n hn =>
    (path n hn).imp fun s hs => ⟨hs.1, (ds_restrict_iff_l I hs.2.1 ff.1).mpr hs.2.2⟩)⟩

theorem tree_wf_dc_l {ω X F T R : M.Domain} (hω : M.IsOmega ω) (dc : Dc_d I ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T) (edges : Edge_d I ω T R)
    (no : ∀ f, M.IsSetFunctionFromTo I f ω X → ¬ Branch_d F T f) : Wf_rel_d T R := by
  classical
  intro Q sub ne
  apply Classical.byContradiction
  intro bad
  have next q (hq : M.mem q Q) : ∃ v, M.mem v Q ∧ Step_d I ω q v := by
    apply Classical.byContradiction
    intro no
    exact bad ⟨q, hq, fun v hv edge => no ⟨v, hv, ((edges.2 q v).mp edge).2.2⟩⟩
  obtain ⟨P, read⟩ := ktree_exists_l (ZF.modelsKP hZF) F Q
  have contained s (hs : M.mem s P) : M.mem s T :=
    ((read s).mp hs).2.elim fun q hq => tree.2 q (sub q hq.1) s ((read s).mp hs).1 hq.2
  have pruned s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Step_d I ω s t := by
    obtain ⟨hsF, q, hq, sq⟩ := (read s).mp hs
    obtain ⟨v, hv, qv⟩ := next q hq
    obtain ⟨n, hn, fs⟩ := (space s).mp hsF
    obtain ⟨l, hl, fq⟩ := (space q).mp (tree.1 q (sub q hq))
    obtain ⟨m, hm, fv⟩ := (space v).mp (tree.1 v (sub v hv))
    obtain ⟨succ, qv⟩ := (tree_step_iff_l I hZF hω hl hm fq fv).mp qv
    have nl : M.MemberSubset n l := fun i hi => by
      obtain ⟨a, _, value⟩ := fs.2.2 i hi
      exact fq.input_mem_of_pairMember (value.elim fun p hp => ⟨p, hp.1, sq p hp.2⟩)
    have nm : M.mem n m := by
      rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn l hl with eq | lt | gt
      · exact (hZF.1.eq_of_same_members n l eq).symm ▸ succ.predecessor_mem
      · exact (succ n).mpr (Or.inl lt)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (nl l gt)).elim
    obtain ⟨u, su, hu⟩ := hω.1.2 n hn
    have um : M.MemberSubset u m := fun i hi => ((su i).mp hi).elim
      (fun hi => (succ i).mpr (Or.inl (nl i hi))) (fun eq => (hZF.1.eq_of_same_members i n eq).symm ▸ nm)
    obtain ⟨t, rt⟩ := ZF.exists_restriction hZF I v u
    have ft := rt.isSetFunctionFromTo fv um
    have st := ds_prefix_mono_l I fs ft.1 ((ds_restrict_iff_l I fs fv.1).mpr
      (fun p hp => qv p (sq p hp))) rt (fun i hi => (su i).mpr (Or.inl hi))
    exact ⟨t, (read t).mpr ⟨(space t).mpr ⟨u, hu, ft⟩, v, hv, (ds_restrict_iff_l I ft fv.1).mp rt⟩,
      (tree_step_iff_l I hZF hω hn hu fs ft).mpr ⟨su, st⟩⟩
  have treeP : Tree_d F P := ⟨fun s hs => ((read s).mp hs).1, fun s hs t ht ts => by
    obtain ⟨_, q, hq, sq⟩ := (read s).mp hs
    exact (read t).mpr ⟨ht, q, hq, fun x hx => sq x (ts x hx)⟩⟩
  have neP := ne.imp fun q hq => (read q).mpr ⟨tree.1 q (sub q hq), q, hq, fun _ hx => hx⟩
  obtain ⟨f, ff, branch⟩ := tree_pruned_dc_l I hZF hω dc space treeP neP pruned
  exact no f ff (fun s hs sf => contained s (branch s hs sf))

end YesMetaZFC.SetTheory.Descriptive
