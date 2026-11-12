import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchDepth
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Padding
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail

/-! # Claim 7.9：demanding 偶数枝的实际直接极限不良基

若极限良基，则坍塌后的控制树像恒定，历史像逐轮严格增长。
将原请求中的秩证书沿锥腿运输，再以 Δ₀ 绝对性读取，便得到
背景内部全 ω 的序数下降链。这里只用背景 ZF 及运行已有的证据。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem td_issued_position_l {X R : M.Domain} {v : Fin 47 → M.Domain}
    (h : Rr_truth_d I X R td_issued0_m v) : Rd_entry_d (v 20) (v 18) R := by
  obtain ⟨bounds,valid⟩ := h
  simp only [td_issued0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at valid
  exact valid.2.1.2.2.2.1

/-- 只对秩证书使用绝对性；控制和策略公式仍在真实目标模型中解释。 -/
private theorem td_issued_mem_rank_l {c X R : M.Domain} (model : Smem_d I c X R)
    (trans : M.TransitiveSet X) {v : Fin 47 → M.Domain} (h : Rr_truth_d I X R td_issued0_m v) :
    ∃ α F, Cg_rank_d (v 0) (v 12) (v 18) α F := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let ρ : Env N 47 := ⟨fun i => ⟨v i,h.1 i⟩,fun _ => ⟨v 0,h.1 0⟩⟩
  have valid : Formula.satisfies ρ td_issued0_m :=
    (rr_truth_native_l I model.1.2.1 td_issued0_m td_issued0_closed_l ρ.bound).mp h
  have control := (Formula.satisfies_conj_iff ..).mp valid |>.1
  simp only [Formula.satisfies_rename,td_control0_m,Formula.satisfies_conj_iff] at control
  have rank := control.2.2.2.2.2.2.2.1
  simp only [cg_rank_m,Formula.satisfies_exists_iff] at rank
  obtain ⟨α,F,rank⟩ := rank
  let ν : Env N 21 := ((ρ.reindex (fun i : Fin 19 => i.castAdd 28)).push α).push F
  let φ : Formula 1 21 := cg_rank0_m (.bound 2) (.bound 14) (.bound 20) (.bound 1) .newest
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ]
  have rank : Formula.satisfies ν φ := rank
  have raw := (rr_truth_native_l I model.1.2.1 φ closed ν.bound).mpr
    ((Formula.closed_env_l φ closed (ρ := ν) (η := ⟨ν.bound,fun _ => ν.bound 0⟩) rfl).mp rank)
  let η : Env M 21 := ⟨fun i => (ν.bound i).val,fun _ => (ν.bound 0).val⟩
  have read : Formula.satisfies η φ :=
    ((rr_truth_mem_l I trans model φ (cg_rank0_delta_l ..) (fun i => (ν.bound i).val)).mp raw).2
  exact ⟨α.val,F.val,(cg_rank0_sat_l (ZF.modelsKP hZF) η (.bound 2) (.bound 14) (.bound 20) (.bound 1) .newest).mp read⟩

variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.even_illfounded_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {B : M.Domain} (branch : ∀ x, M.mem x B ↔ Tg_even_d (5 : Fin 66) H (U 0) x) :
    ¬ It_wf_branch_d hZF (g 0) (g 0) (U 0) (U 1) (U 2) B := by
  intro wf
  have hw := u.tree.omega
  obtain ⟨β,T',Q',G',ext⟩ := it_wf_branch_extend_l hZF u.tree (hw.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_,_,_,_,_,_,d,N,W,P,_,_,_,target,nt,cone,_⟩ := ext.limit
  have elem {i s j} {v : Fin 66 → M.Domain} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s)
      (hj : Rd_entry_d (v 5) j P) := cone.elementary (v 5) j (v 2) (v 0) (v 1) hj
        (run.node_l hZF u hs code) (run.read_l hZF hs code).model
  obtain ⟨R,_,same⟩ := run.control_const_l hZF u branch cone.toIt_embedding_d 18
  obtain ⟨F,ff,fs⟩ := run.limit_values_l hZF u branch cone.toIt_embedding_d 20
  -- 全部历史像都在同一控制树中。
  have position i x (hx : Tg_limit_value_d (5 : Fin 66) (39 : Fin 66) H P i x) : M.mem x R := by
    obtain ⟨v,s,j,hs,code,hj,hx⟩ := hx
    have state := run.read_l hZF hs code
    have old := td_issued_position_l hZF state.issued
    obtain ⟨z,_,hz⟩ := (elem hs code hj).1.1.2.2 (v 37) (state.issued.1 18)
    have eq : z = R := same i z ⟨v,s,j,hs,code,hj,hz⟩
    have image := ((elem hs code hj).relation_l I hZF hw state.model target.1 hx hz).mp old
    exact eq ▸ ((target.2 x z).mp image).2.2
  have fn : Fn0_d (g 0) R F := by
    have ft := fn0_function_l (ZF.modelsKP hZF) ff
    exact fn0_of_function_l (ZF.modelsKP hZF) ⟨ft.1,ft.2.1,fun i hi => by
      obtain ⟨x,_,hx⟩ := ft.2.2 i hi
      exact ⟨x,position i x ((fs i x).mp hx),hx⟩⟩
  -- 从首个真实请求运输秩；不在各轮重新选秩函数。
  obtain ⟨e,_,heω⟩ := hw.1.1
  obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 e heω
  obtain ⟨v,code,state⟩ := (run.rows e s hs).1
  obtain ⟨j,hj⟩ := (cone.domain (v 5)).mp ((branch _).mpr
    ⟨v,e,s,hs,code,u.tree.diagram.order.refl _ state.finite⟩)
  have map := elem hs code hj
  have images (i : Fin 47) : ∃ y, Rd_entry_d (v (Fin.natAdd 19 i)) y j := by
    obtain ⟨y,_,hy⟩ := map.1.1.2.2 _ (state.issued.1 i)
    exact ⟨y,hy⟩
  obtain ⟨w,images⟩ := Classical.axiomOfChoice images
  have moved : Rr_truth_d I N W td_issued0_m w :=
    state.issued.map_l I hZF hw state.model target.1 map td_issued0_closed_l images
  obtain ⟨α,J,rank⟩ := td_issued_mem_rank_l hZF target nt moved
  have eq : w 18 = R := same e _ ⟨v,s,j,hs,code,hj,images 18⟩
  have rank : Cg_rank_d (w 0) (w 12) R α J := eq ▸ rank
  -- 原边上的严格包含沿交换锥运输为同一传递模型中的严格包含。
  have proper i k x y (succ : M.SuccessorOf k i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d k y F) :
      M.MemberSubset x y ∧ x ≠ y := by
    obtain ⟨v,s,r,hs,ps,hr,hx⟩ := (fs i x).mp hx
    obtain ⟨w,t,l,ht,pt,hl,hy⟩ := (fs k y).mp hy
    have vr := run.read_l hZF hs ps
    have wr := run.read_l hZF ht pt
    obtain ⟨_,_,v',w',ps',pt',next⟩ := run.steps i k s t succ hs ht
    have eq := rt_tuple_inj_l ps' ps
    subst v'
    have eq := rt_tuple_inj_l pt' pt
    subst w'
    obtain ⟨b,z,edge,hz,ne,sub⟩ := next.history_l hZF wr
    have edge : It_map_d (U 2) (v 5) (w 5) b := by
      obtain ⟨q,pair,entry⟩ := edge
      exact ⟨q,pair,u.entry_l hZF ht pt 2 entry⟩
    have between := u.tree.diagram.elementary (v 5) (w 5) b (v 2) (v 0) (v 1) (w 2) (w 0) (w 1)
      edge (run.node_l hZF u hs ps) (run.node_l hZF u ht pt) vr.model wr.model
    have leg := elem ht pt hl
    obtain ⟨x',_,hz'⟩ := leg.1.1.2.2 z (between.1.1.output_mem_of_pairMember hz)
    have eq := (elem hs ps hr).1.1.1.2 _ x' x (cone.commute (v 5) (w 5) b r l edge hr hl _ z x' hz hz') hx
    have image : Rd_entry_d z x l := eq ▸ hz'
    have moved : Rr_truth_d I N W (Formula.subset (.bound 1) .newest) (Fin.cases y (fun _ : Fin 1 => x)) :=
      sub.map_l I hZF hw wr.model target.1 leg (by simp -implicitDefEqProofs) (Fin.cases hy (fun _ => image))
    let η : Env M 2 := ⟨Fin.cases y (fun _ : Fin 1 => x),fun _ => y⟩
    have read : Formula.satisfies η (Formula.subset (.bound 1) .newest) :=
      ((rr_truth_mem_l I nt target (Formula.subset (.bound 1) .newest) (.atom ..)
        (Fin.cases y (fun _ : Fin 1 => x))).mp moved).2
    have subset : M.MemberSubset x y := (Formula.satisfies_subset_iff η (.bound 1) .newest).mp read
    exact ⟨subset,fun eq => ne (leg.1.2 z (w 39) y (eq ▸ image) hy)⟩
  -- 复合固定秩得到内部无限下降链，与背景基础公理矛盾。
  obtain ⟨D,df,ds⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) fn) (fn0_function_l (ZF.modelsKP hZF) rank.function)
  obtain ⟨E,wf,edges⟩ := wf_membership_l hZF α
  apply wf_no_desc_l hZF hw wf (fn0_of_function_l (ZF.modelsKP hZF) df)
  intro i k a b succ ha hb
  obtain ⟨_,x,hx,xa⟩ := (ds i a).mp ha
  obtain ⟨_,y,hy,yb⟩ := (ds k b).mp hb
  have step := proper i k x y succ hx hy
  exact (edges b a).mpr ⟨df.output_mem_of_pairMember hb,df.output_mem_of_pairMember ha,
    rank.proper x y a b xa yb step.1 step.2⟩

/-- Claim 7.9：同时构造实际偶数枝与商直接极限，并证明其关系不良基。 -/
theorem Td_run_d.even_limit_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U) :
    ∃ B, It_ill_branch_d hZF (g 0) (g 0) (U 0) (U 1) (U 2) B ∧
      ∀ x, M.mem x B ↔ Tg_even_d (5 : Fin 66) H (U 0) x := by
  obtain ⟨B,branch,values⟩ := run.even_branch_l hZF u
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨i,hi,_⟩ := branch.cofinal e he
  obtain ⟨L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model⟩ :=
    it_branch_data_l hZF u.tree.omega u.tree.diagram branch ⟨i,hi⟩
  exact ⟨B,⟨branch,L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model,
    fun wf => run.even_illfounded_l hZF u values
      ⟨branch,L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model,wf⟩⟩,values⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 良基枝中的实际奇档案共尾

7.9 排除偶数枝，首次出现阶段则把每个足够晚的枝节点识别为真实奇档案。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.wf_rows_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b : M.Domain} (wf : It_wf_branch_d hZF (g 0) (g 0) (U 0) (U 1) (U 2) b) :
    ∀ i, M.mem i (g 0) → ∃ m p, ∃ row : Td_archive_row_d M.Domain,
      Rd_entry_d m p (U 5) ∧ Rt_tuple_d row.values_d p ∧ M.mem row.i b ∧ (i = row.i ∨ M.mem i row.i) := by
  obtain ⟨B,evenBranch,even⟩ := run.even_branch_l hZF u
  have ne : b ≠ B := fun eq => run.even_illfounded_l hZF u even (eq ▸ wf)
  obtain ⟨e,empty,he⟩ := u.tree.omega.1.1
  obtain ⟨s,_,first⟩ := run.recursion.1.2.1 e he
  obtain ⟨v,code,_⟩ := (run.rows e s first).1
  have finite := ((run.frames_l hZF).read_l hZF v first code).finite
  intro i hi
  obtain ⟨y,hy,iy,notEven,outside⟩ := wf.1.separate_l hZF.1 u.tree.diagram.order evenBranch ne finite i hi
  obtain ⟨_,_,w,_,_,_,_,row,p,index,entry,tuple,_⟩ :=
    run.birth_l hZF u even empty first code (wf.1.subset y hy) outside notEven
  exact ⟨w 12,p,row,entry,tuple,index.symm ▸ hy,index.symm ▸ iy⟩

end YesMetaZFC.SetTheory.LargeCardinal
