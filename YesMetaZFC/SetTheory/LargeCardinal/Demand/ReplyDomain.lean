import YesMetaZFC.SetTheory.LargeCardinal.Demand.Parameters
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.FiniteArithmeticSource
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ControlRecord
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead
import YesMetaZFC.SetTheory.CumulativeRelativeRead

/-! # 有限读写层中的 demanding 元数

同一加倍历史和三个后继直接读到所属模型，有限性由实际 ω 闭包产生。
该读取同时用于 issued 负载及固定 Q 行，不要求反射层满足集合论理论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_arity_source_l {ω C : M.Domain} (hw : M.IsOmega ω)
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (k d q n m : (rt_model_l C nc).Domain) (hk : M.mem k.val ω)
    (arity : Td_arity_d (rt_pair_l fs.transitive nc hZF.1 fs.pair) k d q n m) :
    Td_arity_d I k.val d.val q.val n.val m.val ∧
      M.mem d.val ω ∧ M.mem q.val ω ∧ M.mem n.val ω ∧ M.mem m.val ω := by
  have add := (fs_add_l hZF hw fs nc k k d hk hk).mp arity.1
  have sq := (rt_successor_l fs.transitive nc hZF.1 q d).mp arity.2.1
  have sn := (rt_successor_l fs.transitive nc hZF.1 n q).mp arity.2.2.1
  have sm := (rt_successor_l fs.transitive nc hZF.1 m n).mp arity.2.2.2
  have hd := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
  have successor {a b : M.Domain} (ha : M.mem a ω) (step : M.SuccessorOf b a) : M.mem b ω := by
    obtain ⟨b',sb,hb⟩ := hw.1.2 a ha
    exact sb.eq hZF.1 step ▸ hb
  have hq := successor hd sq
  have hn := successor hq sn
  exact ⟨⟨add,sq,sn,sm⟩,hd,hq,hn,successor hn sm⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原固定查询行的双池在原生反射层中的读取

查询码只从同一 Q 表读取。有限加倍、后继、秩和完整有限池分别由实际
反射层的闭包读回；反射层本身不需满足 ZF。源节点池与回答池按其各自
元数分别返回，五条查询保留同一表行中的原码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 五个证书仍是当前原结构中的完整原公式，保留固定表选定的代码。 -/
structure Td_query_formulas_d (ω e k q n m s A U Du Dw pn pm pp pb ph : M.Domain) : Prop where
  node : Formula.satisfies
    (⟨fun i => [ω,e,n,q,U,Du,s,k,pn].get i,fun _ => ω⟩ : Env M 9)
    td_node_query0_m
  largest : Formula.satisfies
    (⟨fun i => [ω,q,n,U,Du,pm].get i,fun _ => ω⟩ : Env M 6)
    tg_max_query0_m
  pending : Formula.satisfies
    (⟨fun i => [ω,A,e,m,q,U,Dw,k,pp].get i,fun _ => ω⟩ : Env M 9)
    td_pending_query0_m
  bound : Formula.satisfies
    (⟨fun i => [ω,e,n,m,U,Dw,pb].get i,fun _ => ω⟩ : Env M 7)
    tg_bound_query0_m
  height : Formula.satisfies
    (⟨fun i => [ω,n,m,U,Dw,ph].get i,fun _ => ω⟩ : Env M 6)
    tg_height_query0_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 读取同一合法键的原 Q 行，实际生成 q/n/m 的有限性及两个不同元数的池。 -/
theorem td_control_query_read_l {ω η C : M.Domain} (hω : M.IsOmega ω)
    (rank : V_d I η C) (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (control : Env (rt_model_l C nc) 19) (key : Env (rt_model_l C nc) 5)
    (valid : Formula.satisfies control td_control0_m)
    (hw : (control.bound 0).val = ω) (sameω : key.bound 0 = control.bound 0)
    (sameA : key.bound 4 = control.bound 6)
    (below : M.mem (key.bound 1).val (control.bound 5).val)
    (request : Formula.satisfies key tg_query_request0_m) :
    ∃ d q n m B U Du Dw pn pm pp pb ph : (rt_model_l C nc).Domain,
      Td_query_data_d (control.bound 11) (key.bound 1) (key.bound 2) (key.bound 3) (control.bound 6)
        B U Du Dw pn pm pp pb ph ∧
      Td_arity_d I (key.bound 2).val d.val q.val n.val m.val ∧
      M.mem d.val ω ∧ M.mem q.val ω ∧ M.mem n.val ω ∧ M.mem m.val ω ∧
      M.IsLimitOrdinal (key.bound 1).val ∧ V_d I (key.bound 1).val B.val ∧
      (∀ x, M.mem x U.val ↔ M.mem x B.val ∨ x = (key.bound 1).val) ∧
      Tt_pool_d I ω n.val U.val Du.val ∧ Tt_pool_d I ω m.val U.val Dw.val ∧
      Td_query_formulas_d (control.bound 0) (control.bound 1) (key.bound 2) q n m
        (key.bound 3) (control.bound 6) U Du Dw pn pm pp pb ph := by
  let N := rt_model_l C nc
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have total := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp valid).1).2
  have total := (Formula.satisfies_conj_iff ..).mp total |>.1
  simp only [td_query_total_m,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,tg_query_request_m,Formula.satisfies_bind] at total
  have packet := total (key.bound 1) below (key.bound 2) (key.bound 3) (by
    apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := key) (η := _) ?_).mp request
    funext i
    exact Fin.cases sameω (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases sameA (fun j => Fin.elim0 j))))) i)
  simp only [Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,td_query_packet_m,
    td_arity_sat_l J ext,rd_quad_sat_l ext,rd_entry0_sat_l ext,rd_triple0_sat_l ext,
    Definitional.Term.eval_weaken] at packet
  obtain ⟨x,c,keyCode,entry,d,q,n,m,B,U,Du,Dw,pn,pm,pp,pb,ph,t,v,
    arity,row,codes,tail,base,constants,poolu,poolw,node,largest,pending,bound,height,_⟩ := packet
  let ρ : Env N 39 := control.push (key.bound 1) |>.push (key.bound 2) |>.push (key.bound 3)
    |>.push x |>.push c |>.push d |>.push q |>.push n |>.push m |>.push B |>.push U
    |>.push Du |>.push Dw |>.push pn |>.push pm |>.push pp |>.push pb |>.push ph |>.push t |>.push v
  have req := request
  simp only [tg_query_request0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at req
  have hk : M.mem (key.bound 2).val ω := hw ▸ congrArg Subtype.val sameω ▸ req.2.1
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (key.bound 1)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp req.1)
  obtain ⟨actualArity,hd,hq,hn,hm⟩ := td_arity_source_l hZF hω fs nc (key.bound 2) d q n m hk arity
  have relative : Vr_d C (key.bound 1).val B.val :=
    (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp base
  have actualRank := relative.absolute_l (ZF.modelsKP hZF) fs.transitive B.property
    (fun A D hA sub => v_subset_mem_l I rank hA sub)
  have actualConstants := (tt_constants0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l _ _ _) _).mp constants)
  obtain ⟨Au,Eu,_,_,nu,su,pu⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ (.bound 20) (.bound 12) (.bound 9) (.bound 8) hw).mp poolu
  obtain ⟨Aw,Ew,_,_,nw,sw,pw⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ (.bound 20) (.bound 11) (.bound 9) (.bound 7) hw).mp poolw
  have read {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
      (η : Env N n) (u : Fin n → N.Domain)
      (same : η.bound = u) (truth : Formula.satisfies η φ) :
      Formula.satisfies (⟨u,fun _ => control.bound 0⟩ : Env N n) φ :=
    (Formula.closed_env_l φ closed same).mp truth
  simp only [td_node_query_m,Formula.satisfies_bind] at node
  simp only [tg_max_query_m,Formula.satisfies_bind] at largest
  simp only [td_pending_query_m,Formula.satisfies_bind] at pending
  simp only [tg_bound_query_m,Formula.satisfies_bind] at bound
  simp only [tg_height_query_m,Formula.satisfies_bind] at height
  have formulas : Td_query_formulas_d (control.bound 0) (control.bound 1) (key.bound 2) q n m
      (key.bound 3) (control.bound 6) U Du Dw pn pm pp pb ph := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · refine read _ td_node_query0_closed_l _ _ ?_ node
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))) i
    · refine read _ tg_max_query0_closed_l _ _ ?_ largest
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))) i
    · refine read _ td_pending_query0_closed_l _ _ ?_ pending
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))) i
    · refine read _ tg_bound_query0_closed_l _ _ ?_ bound
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    · refine read _ tg_height_query0_closed_l _ _ ?_ height
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))) i
  exact ⟨d,q,n,m,B,U,Du,Dw,pn,pm,pp,pb,ph,⟨x,c,t,v,keyCode,entry,row,codes,tail⟩,
    actualArity,hd,hq,hn,hm,limit,actualRank,actualConstants,
    ⟨Au,Eu,nu,su,pu⟩,⟨Aw,Ew,nw,sw,pw⟩,formulas⟩

end YesMetaZFC.SetTheory.LargeCardinal
