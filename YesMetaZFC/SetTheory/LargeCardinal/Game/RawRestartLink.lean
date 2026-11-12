import YesMetaZFC.SetTheory.LargeCardinal.Game.RestartLinkSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.Restart
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalStep
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor

/-! # 原继续中的三图严格衔接

恢复节点的完整函数域经共同图逆向读回，同一历史的事件唯一性给出
旧短图包含于当前短图。低层方块再把旧图的原边像识别为共同图像。
完整前驱方程搬运两个包含关系，恢复图则保留精确的单点追加方程。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一恢复记录实际生成下一保存轮所需的长度、短图、标签图及恢复图方程。 -/
theorem Ic_common_d.raw_restart_link_l
    {c N R d P S w η C wp ηp Cp L l U V Γ g k j : M.Domain}
    (common : Ic_common_d I N R P S L l U V Γ g)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (context : Tg_context_d I w N R η C) (target : Tg_context_d I wp P S ηp Cp)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) mp.2.1).Domain //
      (smdl_structure_l I (R := S) mp.2.1).mem x ⟨Cp,target.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46)
    (ψ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 12)
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨Cp,target.member⟩ nd) 54)
    (ε ζ π : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨Cp,target.member⟩ nd) 12)
    (r : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨Cp,target.member⟩ nd) 29)
    (v : (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨Cp,target.member⟩ nd).Domain)
    (a : Fin 16 → (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨Cp,target.member⟩ nd).Domain)
    (s t n : (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc).Domain)
    (issued : Formula.satisfies ι tg_issued0_m) (old : Formula.satisfies ρ tg_round0_m)
    (recovered : Formula.satisfies r tc_recovered0_m)
    (play : Tg_play_d I N R C (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val s.val.val)
    (queryPlay : Tg_play_d I N R C (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val (ψ.bound 5).val.val)
    (graph : Tg_graph_d (kp_pair_l hN) n.val s.val)
    (size : (smdl_structure_l I (R := R) mn.2.1).MemberSubset n.val (ι.bound 26).val)
    (labels : (smdl_structure_l I (R := R) mn.2.1).MemberSubset t.val (ι.bound 23).val)
    (coords : ∀ i : Fin 6, ψ.bound ([0,1,2,3,4,6].get i) = ι.bound ([0,1,27,28,26,23].get i))
    (images : ∀ i, Rd_entry_d (ψ.bound i).val.val (ζ.bound i).val.val g)
    (domainEq : (ζ.bound 4).val = (r.bound 10).val)
    (shortEq : (r.bound 15).val = (ζ.bound 5).val)
    (labelEq : (r.bound 16).val = (ζ.bound 6).val)
    (indexEq : (r.bound 9).val = (ρ.bound 22).val)
    (graphEq : (r.bound 26).val = (ρ.bound 42).val)
    (γ Vγ κ K : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (rankγ : V_d (kp_pair_l hN) γ Vγ) (rankκ : V_d (kp_pair_l hN) κ K)
    (below : (smdl_structure_l I (R := R) mn.2.1).MemberSubset γ κ)
    (lowS : (smdl_structure_l I (R := R) mn.2.1).mem (ψ.bound 5).val Vγ)
    (lowT : (smdl_structure_l I (R := R) mn.2.1).mem (ψ.bound 6).val Vγ)
    (oldImages : ∀ i : Fin 2, ∃ x,
      Rd_entry_d ([s,t].get i).val.val x k ∧ Rd_entry_d x (ρ.bound ([40,41].get i)).val.val j)
    (square : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain, ∀ y Z,
      (smdl_structure_l I (R := R) mn.2.1).mem x K → Rd_entry_d x.val y k →
        (Rd_entry_d x.val Z g ↔ Rd_entry_d y Z j)) :
    let ρ' := tg_round_env_d (tg_restart_env_d ρ ε r π v) a
    Rd_entry_d s.val.val (ρ.bound 40).val.val g ∧ Rd_entry_d t.val.val (ρ.bound 41).val.val g ∧
    Tg_restart_link_d I P S (fun i => (ρ.bound ([19,22,40,41,42].get i)).val.val)
      (fun i => (ρ'.bound i).val.val) := by
  intro ρ'
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let Pn := smdl_structure_l I (R := S) mp.2.1
  have fs := context.finite_l mn.2.1 hN.1
  have ft := target.finite_l mp.2.1 hP.1
  let Un : Nn.Domain := ⟨U,common.left_rank.2.1⟩
  let Vn : Pn.Domain := ⟨V,common.right_rank.2.1⟩
  have rankU := (rr_rank_native_l I mn.2.1 hN ⟨L,common.left_rank.1⟩ Un).mp common.left_rank
  have rankV := (rr_rank_native_l I mp.2.1 hP ⟨l,common.right_rank.1⟩ Vn).mp common.right_rank
  obtain ⟨Δ,b,carrier,injection,image,pred,inverse⟩ := common.reverse_native_l hZF mn hN
  have node := recovered
  simp only [tc_recovered0_m,tc_recovered_m,Formula.satisfies_conj_iff] at node
  obtain ⟨_,_,_,_,_,_,_,_,_,node,_⟩ := node
  have node := (tg_node_source_l ft.transitive nd hP.1 (KP.exists_pair hP) r
    (.bound 10) (.bound 24) (.bound 15) (.bound 16) (.bound 2)).mp node
  have targetGraph : Tg_graph_d (kp_pair_l hP) (ζ.bound 4).val (ζ.bound 5).val :=
    Eq.mp (congrArg (Tg_graph_d (kp_pair_l hP) (ζ.bound 4).val) shortEq)
      (Eq.mpr (congrArg (fun n => Tg_graph_d (kp_pair_l hP) n (r.bound 15).val) domainEq) node.1)
  have sourceGraph := rr_native_graph_l I hZF.1 mp.2.1 mn.2.1 hP.1 (KP.exists_pair hP)
    hN.1 (KP.exists_pair hN) Vn Un (v_transitive_l (kp_pair_l hP) rankV)
    (v_transitive_l (kp_pair_l hN) rankU) carrier injection image pred
    (ζ.bound 4).val (ζ.bound 5).val (ψ.bound 4).val (ψ.bound 5).val
    ((inverse _ _).mpr (images 4)) ((inverse _ _).mpr (images 5)) targetGraph
  have sourceGraph : Tg_graph_d (kp_pair_l hN) (ι.bound 26).val (ψ.bound 5).val :=
    Eq.mp (congrArg (fun n => Tg_graph_d (kp_pair_l hN) n (ψ.bound 5).val)
      (congrArg Subtype.val (coords 4))) sourceGraph
  have shortSub := play.native_subset_l I mn.2.1 hN.1 (KP.exists_pair hN)
    ⟨C,context.member⟩ fs.transitive nc (rt_pair_l fs.transitive nc hN.1 fs.pair)
    ι issued n.val (ι.bound 26).val s (ψ.bound 5) queryPlay graph sourceGraph size
  have labelSub : Nn.MemberSubset t.val (ψ.bound 6).val :=
    Eq.mpr (congrArg (fun x => Nn.MemberSubset t.val x) (congrArg Subtype.val (coords 5))) labels
  have low := (KP.v_compare_l hN rankγ rankκ below).1
  obtain ⟨xs,sx,xs'⟩ := oldImages 0
  obtain ⟨xt,tx,xt'⟩ := oldImages 1
  have pointS := (square s.val xs (ρ.bound 40).val.val
    (low _ (v_subset_mem_l (kp_pair_l hN) rankγ lowS shortSub)) sx).mpr xs'
  have pointT := (square t.val xt (ρ.bound 41).val.val
    (low _ (v_subset_mem_l (kp_pair_l hN) rankγ lowT labelSub)) tx).mpr xt'
  -- 完整前驱方程直接搬运包含关系，无需重新构造图或选择成员。
  have carry (u v : Nn.Domain) (u' v' : Pn.Domain)
      (iu : Rd_entry_d u.val u'.val g) (iv : Rd_entry_d v.val v'.val g)
      (sub : Nn.MemberSubset u v) : Pn.MemberSubset u' v' := by
    intro z hz
    obtain ⟨x,hx,xz⟩ := (common.pred u.val u'.val iu z.val).mp hz
    have xn := ((common.carrier x).mp (common.injection.1.input_mem_of_pairMember xz)).1
    exact (common.pred v.val v'.val iv z.val).mpr ⟨x,sub ⟨x,xn⟩ hx,xz⟩
  have shortNew : Pn.MemberSubset (ρ.bound 40).val (ρ'.bound 40).val :=
    Eq.mpr (congrArg (fun x => Pn.MemberSubset (ρ.bound 40).val x) shortEq)
      (carry s.val (ψ.bound 5).val (ρ.bound 40).val (ζ.bound 5).val pointS (images 5) shortSub)
  have labelNew : Pn.MemberSubset (ρ.bound 41).val (ρ'.bound 41).val :=
    Eq.mpr (congrArg (fun x => Pn.MemberSubset (ρ.bound 41).val x) labelEq)
      (carry t.val (ψ.bound 6).val (ρ.bound 41).val (ζ.bound 6).val pointT (images 6) labelSub)
  obtain ⟨entry,ends⟩ := tg_recovered_graph_l hP.1 ft.transitive nd r recovered
  have entry := Eq.mp (congrArg (fun x => Rd_entry_d x (r.bound 1).val (r.bound 2).val) indexEq) entry
  have both : ((r.bound 9).val,(r.bound 26).val) = ((ρ.bound 22).val,(ρ.bound 42).val) :=
    Prod.ext indexEq graphEq
  have ends (p : Pn.Domain) : Pn.mem p (ρ'.bound 42).val ↔
      Pn.mem p (ρ.bound 42).val ∨ KPair_d Pn p (ρ.bound 22).val (r.bound 1).val :=
    Eq.mp (congrArg (fun x : Pn.Domain × Pn.Domain => Pn.mem p (r.bound 2).val ↔
      Pn.mem p x.2 ∨ KPair_d Pn p x.1 (r.bound 1).val) both) (ends p)
  have seed := ((Formula.satisfies_conj_iff ..).mp old).1
  simp only [tg_seed0_m,Formula.satisfies_rename,tg_seed_m,Formula.satisfies_conj_iff] at seed
  have succ := (rt_successor_l ft.transitive nd hP.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp seed.2.2.2.2.2.2.2.1)
  exact ⟨pointS,pointT,Tg_restart_link_d.of_native_l I mp.2.1 hP.1
    (fun i => (ρ.bound ([19,22,40,41,42].get i)).val) (fun i => (ρ'.bound i).val)
    (r.bound 1).val rfl succ shortNew labelNew entry ends⟩

end YesMetaZFC.SetTheory.LargeCardinal
