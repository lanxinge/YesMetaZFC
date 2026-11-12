import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchOdd
import YesMetaZFC.SetTheory.LargeCardinal.Game.GeneralProjection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchDepth
import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchProjection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyTree

/-! # 良基 demanding 极限固定原字母

档案共同图把任一旧像的前驱送入当前完整根切片；根方块及共同图的
单射性再将它识别为原根前驱的像。共尾奇行因此满足极限固定性所需的
完整前驱条件，无需给档案附加新的切片字段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_state_d.archive_predecessors_l {v : Fin 66 → M.Domain} {m p wr B A : M.Domain}
    (state : Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)))
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (cut : Tg_root_cut_d I (g 1) (g 3) (g 4) wr (g 5) B (g 8) (g 6) A)
    (source : Smem_d I (g 1) (g 3) (g 4)) (trans : M.TransitiveSet (g 3))
    (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (v 11)) (code : Rt_tuple_d row.values_d p) :
    ∀ x y, M.mem x (g 6) → Rd_entry_d x y row.p → ∀ z,
      Rd_entry_d z y row.R ↔ ∃ a, M.mem a x ∧ Rd_entry_d a z row.p := by
  obtain ⟨saved,l,V,Γ,t,common,_,square,_⟩ := (state.archive m p entry).read_l I code
  have hRoot := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF state.tree.omega))
  have hA := ZF.modelsKP (ZFC.models_zf_l
    ((root.map_l hZF state.tree.omega saved.model saved.origin).native_l I hZF state.tree.omega))
  let N := smdl_structure_l I (R := row.R) saved.model.2.1
  have rank := (rr_rank_native_l I saved.model.2.1 hA
    (⟨row.L,common.left_rank.1⟩ : N.Domain) ⟨row.U,common.left_rank.2.1⟩).mp common.left_rank
  intro x y hx xy z
  constructor
  · intro zy
    obtain ⟨x',_,xx⟩ := state.slice.injection.1.2.2 x hx
    have yx := (square x hx y xy x').mpr (state.slice.root x x' xx)
    have hy := (common.carrier y).mp (common.injection.1.input_mem_of_pairMember yx)
    have hz := (saved.model.2.2.2 z y zy).1
    have hzΓ := (common.carrier z).mpr ⟨hz,(v_transitive_l (kp_pair_l hA) rank)
      ⟨y,hy.1⟩ hy.2 ⟨z,hz⟩ zy⟩
    obtain ⟨z',_,zz⟩ := common.injection.1.2.2 z hzΓ
    have zx := (common.pred y x' yx z').mpr ⟨z,zy,zz⟩
    obtain ⟨a,ax,az⟩ := (state.slice.predecessors x x' xx z').mp zx
    have ha := cut.down_l hZF hRoot x a hx ax
    obtain ⟨a',_,aa⟩ := saved.origin.1.1.2.2 a ((cut.carrier a).mp ha).1
    have eq := common.injection.2 a' z z'
      ((square a ha a' aa z').mpr (state.slice.root a z' az)) zz
    exact ⟨a,((source.2 a x).mp ax).2.2,eq ▸ aa⟩
  · rintro ⟨a,ax,az⟩
    exact (saved.origin.relation_l I hZF state.tree.omega root.model saved.model az xy).mp
      ((source.2 a x).mpr ⟨trans x ((cut.carrier x).mp hx).1 a ax,((cut.carrier x).mp hx).1,ax⟩)

theorem Td_run_d.root_fixed_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) {wr B A b d N W P : M.Domain}
    (cut : Tg_root_cut_d I (g 1) (g 3) (g 4) wr (g 5) B (g 8) (g 6) A)
    (source : Smem_d I (g 1) (g 3) (g 4)) (trans : M.TransitiveSet (g 3))
    (wf : It_wf_branch_d hZF (g 0) (g 0) (U 0) (U 1) (U 2) b)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P) :
    ∀ j, Rd_entry_d (g 2) j P → ∀ x, M.mem x (g 6) → Rd_entry_d x x j := by
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 e he
  obtain ⟨v,cv,state⟩ := (run.rows e s hs).1
  have rootNode := u.entry_l hZF hs cv 1 state.root_node
  have hRoot := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF u.tree.omega))
  apply cone.fixed_l hZF u.tree.omega u.tree.diagram wf.1 rootNode root.model target nt
  intro i hi
  obtain ⟨m,p,row,entry,code,member,later⟩ := run.wf_rows_l hZF u wf i (wf.1.subset i hi)
  have saved := run.archive_source_l hZF u row entry code
  obtain ⟨node,edge,_⟩ := u.links m p row entry code
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨w,n,t,ht,cw,hq⟩ := (u.columns 5 q).mp hq
  have current := run.read_l hZF ht cw
  have dt := (current.slice.mem_carrier_l hZF cut source trans hRoot).transitive
  exact ⟨row.i,row.p,row.c,row.X,row.R,member,wf.1.forward_l u.tree.diagram.order hi member later,
    edge,node,saved.model,
    dt,(fun x hx => (saved.origin.1.1.2.2 x ((cut.carrier x).mp hx).1).imp fun _ h => h.2),
    current.archive_predecessors_l hZF root cut source trans row ⟨q,pair,hq⟩ code⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一 demanding 并树的全部活动临界点

操作先在某个有限阶段出现；该阶段保留的实际所属模型、根切片及下界
随原列进入并树。没有为无限树重新选择扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_run_d.critical_l {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}
    (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U) :
    Tg_raw_critical_d I (g 3) (g 4) (g 5) (g 6) (g 7) (g 2) (U 1) (U 2) (U 3) := by
  intro i p κ L F entry payload
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨v,n,s,hs,cv,hq⟩ := (u.columns 3 q).mp hq
  obtain ⟨c,Y,R,C,j,γ,V,t,node,model,edge,slice,lower⟩ :=
    (run.read_l hZF hs cv).critical i p κ L F ⟨q,pair,hq⟩ payload
  obtain ⟨q,pair,eq⟩ := edge
  exact ⟨c,Y,R,C,j,γ,V,t,u.entry_l hZF hs cv 1 node,model,
    ⟨q,pair,u.entry_l hZF hs cv 2 eq⟩,slice,lower⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.8 的广义 demanding 投影

同一普通迭代树的全部活动临界点越过原字母集的秩；每条良基共尾枝
都在自身极限中给出原对局的三坐标分支，第一辅助坐标满射。
完整源与活动边的原生强度证书随树保留；尚不把原关系支撑解释成背景序数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_mem_shifted_d (Ω o c γ S₀ f : M.Domain) : Prop :=
  ∃ T Q G E, It_tree_d hZF Ω c Ω T Q G E ∧ It_owned_d I Ω Q E ∧
    It_copyable_d hZF Ω c T Q G E ∧ It_critical_bound_d I γ Q E ∧
    ∀ b, It_wf_branch_d hZF Ω Ω T Q G b →
      ∃ d N W P j S Y F A B, Smem_d I d N W ∧ M.TransitiveSet N ∧
        It_cone_d (kp_pair_l (ZF.modelsKP hZF)) Ω b Q G d N W P ∧ Rd_entry_d o j P ∧ Rd_entry_d S₀ S j ∧
        Fseq_space_d I Ω Y F ∧ Tree_d F S ∧ Td_alphabet_d S A B ∧ Td_projection_d hZF Ω A B Y F S f

def Td_gp_d (Ω o c A S f : M.Domain) : Prop :=
  ∃ ρ γ, Rk_d I A ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧ Td_mem_shifted_d hZF Ω o c γ S f

/-- 实际运行保留根腿、字母固定性及整个原低秩切片的逐点固定性。 -/
def Td_fixed_shifted_d (Ω o c X γ A S₀ f : M.Domain) : Prop :=
  ∃ T Q G E, It_tree_d hZF Ω c Ω T Q G E ∧ It_owned_d I Ω Q E ∧
    It_copyable_d hZF Ω c T Q G E ∧ It_critical_bound_d I γ Q E ∧
    ∀ b, It_wf_branch_d hZF Ω Ω T Q G b →
      ∃ d N W P j S Y F U V, Smem_d I d N W ∧ M.TransitiveSet N ∧
        It_cone_d (kp_pair_l (ZF.modelsKP hZF)) Ω b Q G d N W P ∧ Rd_entry_d o j P ∧ Rd_entry_d S₀ S j ∧
        Fseq_space_d I Ω Y F ∧ Tree_d F S ∧ Td_alphabet_d S U V ∧ Td_projection_d hZF Ω U V Y F S f ∧
        Smap_d I Ω c d X N j ∧ Rd_entry_d A A j ∧ (∀ x, M.mem x A → Rd_entry_d x x j) ∧
        ∃ K, M.mem γ X ∧ M.mem K X ∧ Vr_d X γ K ∧ M.mem A K ∧
          ∀ x, M.mem x K → Rd_entry_d x x j

def Td_fixed_gp_d (Ω o c X A S f : M.Domain) : Prop :=
  ∃ ρ γ, Rk_d I A ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧ Td_fixed_shifted_d hZF Ω o c X γ A S f

theorem Td_fixed_gp_d.projection_l {Ω o c X A S f : M.Domain}
    (fixed : Td_fixed_gp_d hZF Ω o c X A S f) : Td_gp_d hZF Ω o c A S f := by
  obtain ⟨ρ,γ,rank,lower,ordinal,T,Q,G,E,tree,owned,copy,bound,branches⟩ := fixed
  refine ⟨ρ,γ,rank,lower,ordinal,T,Q,G,E,tree,owned,copy,bound,?_⟩
  intro b wf
  obtain ⟨d,N,W,P,j,S',Y,F,U,V,target,trans,cone,leg,image,space,closed,alphabet,projection,_⟩ := branches b wf
  exact ⟨d,N,W,P,j,S',Y,F,U,V,target,trans,cone,leg,image,space,closed,alphabet,projection⟩

theorem Td_run_d.fixed_shifted_l {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}
    (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    (copy : It_copyable_d hZF (g 0) (g 1) (U 0) (U 1) (U 2) (U 3))
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) {wr B A : M.Domain}
    (cut : Tg_root_cut_d I (g 1) (g 3) (g 4) wr (g 5) B (g 8) (g 6) A)
    (source : Smem_d I (g 1) (g 3) (g 4)) (trans : M.TransitiveSet (g 3))
    (played : Td_run_play_d I (g 0) A H f) :
    Td_fixed_shifted_d hZF (g 0) (g 2) (g 1) (g 3) (g 5) (g 8) (g 9) f := by
  have hRoot := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF u.tree.omega))
  refine ⟨U 0,U 1,U 2,U 3,u.tree,u.owned,copy,
    (run.critical_l hZF u).mem_l hZF source trans hRoot cut.rank cut.carrier,?_⟩
  intro b wf
  obtain ⟨d,N,W,P,j,S,Y,F,x,A',B',target,nt,cone,leg,image,comp,space,tree,alphabet,projection⟩ :=
    run.wf_projection_l hZF u root (fun x hx => ((cut.letters x).mp hx).1) played wf
  have fixed := run.root_fixed_l hZF u root cut source trans wf target nt cone j leg
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 e he
  obtain ⟨v,cv,state⟩ := (run.rows e s hs).1
  have map := cone.elementary (g 2) j (g 1) (g 3) (g 4) leg
    (u.entry_l hZF hs cv 1 state.root_node) root.model
  have inside y (hy : M.mem y A) : M.mem y (g 6) := cut.down_l hZF hRoot (g 8) y
    ((cut.carrier (g 8)).mpr ⟨(root.model.2.2.2 _ _ cut.alphabet).1,cut.alphabet⟩) ((cut.letters y).mp hy).2
  have ff := fn0_function_l (ZF.modelsKP hZF) played.1
  have relation : M.IsSetRelation I x := comp.1
  have eq : x = f := relation.eq_of_pairMember_iff hZF.1 ff.1.1 (by
    intro n z
    apply (comp.2 n z).trans
    constructor
    · rintro ⟨y,ny,yz⟩
      have yy := fixed y (inside y (played.1.bound_l ny).2)
      exact map.1.1.1.2 y y z yy yz ▸ ny
    · intro nz
      exact ⟨z,nz,fixed z (inside z (played.1.bound_l nz).2)⟩)
  have letters := cut.letters_eq_l (ZF.modelsKP hZF) source trans
  have carrier y : M.mem y (g 6) ↔ M.mem y B := (cut.carrier y).trans
    ⟨fun h => ((source.2 y B).mp h.2).2.2,fun h =>
      ⟨trans B cut.rank.2.1 y h,(source.2 y B).mpr ⟨trans B cut.rank.2.1 y h,cut.rank.2.1,h⟩⟩⟩
  exact ⟨d,N,W,P,j,S,Y,F,A',B',target,nt,cone,leg,image,space,tree,alphabet,eq ▸ projection,map,
    fixed (g 8) ((cut.carrier (g 8)).mpr ⟨(root.model.2.2.2 _ _ cut.alphabet).1,cut.alphabet⟩),
    (fun y hy => fixed y (inside y (letters.symm ▸ hy))),B,cut.rank.1,cut.rank.2.1,
    (rr_rank_mem_l I (ZF.modelsKP hZF) source trans cut.rank.1 cut.rank.2.1).mp cut.rank,
    ((source.2 (g 8) B).mp cut.alphabet).2.2,fun y hy => fixed y ((carrier y).mpr hy)⟩

end YesMetaZFC.SetTheory.LargeCardinal
