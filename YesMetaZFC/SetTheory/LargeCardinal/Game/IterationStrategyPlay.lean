import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationCopy
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveGrowth
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Padding
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameStage
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveImageSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationArchivePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveGraph
import YesMetaZFC.SetTheory.LargeCardinal.Game.ImageValue
import YesMetaZFC.SetTheory.LargeCardinal.Game.TreeImage

/-! # 同一指定分支中的唯一档案像及实际增长

原档案的严格节点次序消去不同档案索引；五坐标像随后由同一锥腿唯一确定。
原继续边的增长直接使用实际模型列和锥交换方块，不另要求调用者提供中间像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

/-- 同一树节点的两个原档案像必相同，即使其展示索引尚未识别。 -/
theorem Tg_iteration_run_d.archive_image_unique_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {b d N W P m n i : M.Domain} {v w : Fin 5 → M.Domain}
    (branch : It_branch_d ω (U 0) b) (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (hv : Tg_archive_image_d (U 5) P m i v) (hw : Tg_archive_image_d (U 5) P n i w) : v = w := by
  have hv₀ := hv
  have hw₀ := hw
  obtain ⟨p,left,hp,cp,left_i,_⟩ := hv
  obtain ⟨q,right,hq,cq,right_i,_⟩ := hw
  obtain ⟨eq,_⟩ := h.archive_unique_l hZF u left right hp hq cp cq (left_i.trans right_i.symm)
  subst n
  have legs (i j) (hj : Rd_entry_d i j P) :
      ∀ x y z, Rd_entry_d x y j → Rd_entry_d x z j → y = z := by
    have hi := branch.subset i ((cone.domain i).mpr ⟨j,hj⟩)
    obtain ⟨c,X,R,node,model⟩ := u.tree.diagram.model_l hZF hi
    exact (cone.elementary i j c X R hj node model).1.1.1.2
  exact (Tg_archive_image_d.unique_l I hZF.1 u.archive.2.1.2 cone.function.2 legs hv₀ hw₀).2

/-- 实际两端档案及同一原继续边自动给出目标中的完整增长方程。 -/
theorem Tg_iteration_run_d.archive_growth_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {b d N W P m n p q j : M.Domain} {v w : Fin 5 → M.Domain}
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (old row : Tg_archive_row_d M.Domain)
    (old_entry : Rd_entry_d m p (U 5)) (new_entry : Rd_entry_d n q (U 5))
    (old_tuple : Rt_tuple_d old.values_d p) (new_tuple : Rt_tuple_d row.values_d q)
    (edge : It_map_d (U 2) old.i row.i j) (step : Tg_archive_step_d I old row j)
    (hv : Tg_archive_image_d (U 5) P m old.i v) (hw : Tg_archive_image_d (U 5) P n row.i w) :
    v 1 = w 1 ∧ M.SuccessorOf (w 0) (v 0) ∧
    (∀ i : Fin 3, M.MemberSubset (v ([2,3,4].get i)) (w ([2,3,4].get i))) ∧
    ∃ x, Rd_entry_d (v 0) x (w 4) ∧ ∀ s, M.mem s (w 4) ↔ M.mem s (v 4) ∨ KPair_d M s (v 0) x := by
  obtain ⟨old_node,old_model,_⟩ := h.archive_read_l hZF u old old_entry old_tuple
  obtain ⟨new_node,new_model,_⟩ := h.archive_read_l hZF u row new_entry new_tuple
  have step₀ := step
  obtain ⟨a,b,ca,cb,_⟩ := step
  obtain ⟨_,l,hl,iv⟩ := hv.read_l I hZF.1 u.archive.2.1.2 old_entry old_tuple ca
  obtain ⟨_,k,hk,iw⟩ := hw.read_l I hZF.1 u.archive.2.1.2 new_entry new_tuple cb
  have between := u.tree.diagram.elementary old.i row.i j old.c old.X old.R row.c row.X row.R
    edge old_node new_node old_model new_model
  have left := cone.elementary old.i l old.c old.X old.R hl old_node old_model
  have right := cone.elementary row.i k row.c row.X row.R hk new_node new_model
  exact step₀.image_l hZF u.tree.omega new_model target nt between.1.1 left.1.1.1 right
    (cone.commute old.i row.i j l k edge hl hk) ca cb v w iv iw

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系运行的偶数枝及同一锥中的控制像

当前节点的前驱并给出实际共尾枝。记录坐标沿原模型的真实锥腿读取，
十九项控制沿相邻边保持，因此在任一共同锥中有相同的像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

theorem Tg_iteration_run_d.even_branch_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U) :
    ∃ B, It_branch_d ω (U 0) B ∧ ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x :=
  (h.frames_l hZF).even_branch_l hZF u.tree u.columns
    (fun _ _ v hs code => (h.read_l hZF v hs code).successor)

theorem Tg_iteration_run_d.node_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {i s} (v : Fin 75 → M.Domain) (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
    Rd_entry_d (v 7) (v 15) (U 1) := by
  obtain ⟨p,pair,hp⟩ := (h.read_l hZF v hs code).node
  exact ⟨p,pair,(u.columns 1 p).mpr ⟨v,i,s,hs,code,hp⟩⟩

theorem Tg_iteration_run_d.limit_values_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {B d N W P : M.Domain} (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B (U 1) (U 2) d N W P) (b : Fin 46) :
    ∃ F, Fn0_d ω N F ∧ ∀ i x, Rd_entry_d i x F ↔ Tg_limit_value_d (7 : Fin 75) (Fin.natAdd 29 b) H P i x := by
  apply cone.record_values_l hZF (7 : Fin 75) (Fin.natAdd 29 b) h.recursion.1
  · intro i s hs
    obtain ⟨v,code,_⟩ := (h.rows i s hs).1
    exact ⟨v,code⟩
  · intro i s v hs code
    have state := h.read_l hZF v hs code
    exact ⟨v 15,v 0,v 1,h.node_l hZF u v hs code,state.model,
      state.request.values.elim (fun bounds _ => bounds b.succ),
      (branch _).mpr ⟨v,i,s,hs,code,u.tree.diagram.order.refl _ state.finite⟩⟩

theorem Tg_iteration_run_d.control_const_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {B d N W P : M.Domain} (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B (U 1) (U 2) d N W P) (b : Fin 19) :
    ∃ z, M.mem z N ∧ ∀ i x, Tg_limit_value_d (7 : Fin 75) (Fin.natAdd 29 (b.castAdd 27)) H P i x → x = z := by
  obtain ⟨F,ff,fs⟩ := h.limit_values_l hZF u branch cone (b.castAdd 27)
  have step i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) : x = y := by
    obtain ⟨v,s,r,hs,ps,hr,hx⟩ := (fs i x).mp hx
    obtain ⟨w,t,l,ht,pt,hl,hy⟩ := (fs j y).mp hy
    obtain ⟨_,_,v',w',ps',pt',next⟩ := h.steps i j s t succ hs ht
    have eq := rt_tuple_inj_l ps' ps
    subst v'
    have eq := rt_tuple_inj_l pt' pt
    subst w'
    obtain ⟨_,_,_,_,_,k,_,_,_,edge,control,_⟩ := next
    have edge : It_map_d (U 2) (v 7) (w 7) k := by
      obtain ⟨b,bp,q,qp,hq⟩ := edge
      exact ⟨b,bp,q,qp,(u.columns 2 q).mpr ⟨w,j,t,ht,pt,hq⟩⟩
    have elem := cone.elementary (v 7) r (v 15) (v 0) (v 1) hr
      (h.node_l hZF u v hs ps) (h.read_l hZF v hs ps).model
    exact elem.1.1.1.2 _ x y hx (cone.commute (v 7) (w 7) k r l edge hr hl _ _ y (control b) hy)
  let η : Env M 0 := ⟨Fin.elim0,fun _ => F⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  have eqv x y : φ.denote η x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  have all := ZF.rel_chain_l I hZF φ η u.tree.omega (fn0_function_l (ZF.modelsKP hZF) ff)
    (fun _ _ _ _ _ _ hx hy => (eqv _ _).mpr (((eqv _ _).mp hx).trans ((eqv _ _).mp hy)))
    (fun i j x y succ hx hy => (eqv _ _).mpr (step i j x y succ hx hy))
  obtain ⟨e,he,heω⟩ := u.tree.omega.1.1
  obtain ⟨z,hz,first⟩ := ff.2.1 e heω
  refine ⟨z,hz,fun i x hx => ?_⟩
  have hx := (fs i x).mpr hx
  rcases (u.tree.omega.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare e heω i (ff.bound_l hx).1 with eq | ei | ie
  · have eq := hZF.1.eq_of_same_members e i eq
    exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 i x z hx (eq ▸ first)
  · exact ((eqv z x).mp (all e i z x ei first hx)).symm
  · exact (he i ie).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际原关系偶数枝的极限不良基

若该枝良基，实际坍塌给出传递目标。原请求的控制树像恒定，历史像严格包含，
目标反射层中的原控制秩于是产生内部无限下降链。原节点始终使用自身的关系和数字图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

theorem Tg_iteration_run_d.even_illfounded_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U) {B : M.Domain}
    (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x) :
    ¬ It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) B := by
  intro wf
  have hw := u.tree.omega
  obtain ⟨β,T',Q',G',ext⟩ := it_wf_branch_extend_l hZF u.tree (hw.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_,_,_,_,_,_,d,N,W,P,_,_,_,target,nt,cone,nodes,_⟩ := ext.limit
  obtain ⟨N',W',K,target',source⟩ :=
    (ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl,rfl⟩))).mem_l hZF ⟨N,W,target,nt⟩
  obtain ⟨eqN,eqW⟩ := smdl_unique_l I target'.1 target.1
  subst N' W'
  have elem {i s j} {v : Fin 75 → M.Domain} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s)
      (hj : Rd_entry_d (v 7) j P) := cone.elementary (v 7) j (v 15) (v 0) (v 1) hj
        (h.node_l hZF u v hs code) (h.read_l hZF v hs code).model
  have raw_ext {i s} (v : Fin 75 → M.Domain) (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
      Rf_ext_d I (v 0) (v 1) := by
    obtain ⟨Y,S,_,_,_,model,source,_⟩ := (u.tree.sources (v 7) (v 15) (h.node_l hZF u v hs code)).objects
    obtain ⟨eqY,eqS⟩ := smdl_unique_l I model (h.read_l hZF v hs code).model
    subst Y S
    exact source.ext
  obtain ⟨R,_,same⟩ := h.control_const_l hZF u branch cone.toIt_embedding_d 18
  obtain ⟨F,ff,fs⟩ := h.limit_values_l hZF u branch cone.toIt_embedding_d 20
  have position i x (hx : Tg_limit_value_d (7 : Fin 75) (49 : Fin 75) H P i x) : M.mem x R := by
    obtain ⟨v,s,j,hs,code,hj,hx⟩ := hx
    have state := h.read_l hZF v hs code
    have rext := (raw_ext v hs code).native_l I ⟨v 2,state.request.context.omega_mem⟩
    have finite := state.request.context.finite_l ⟨v 2,state.request.context.omega_mem⟩ rext
    obtain ⟨nc,ρ,points,valid,_⟩ := state.request.read_l I (ZF.modelsKP hZF) rext
    have issued := (tg_issued_sat_l (rt_pair_l finite.transitive nc rext finite.pair)
      (rt_model_ext_l rext finite.transitive nc) ρ).mp valid
    have old : Rd_entry_d (v 49) (v 47) (v 1) := by
      have pos := issued.position
      change Rd_entry_d (ρ.bound 20).val.val (ρ.bound 18).val.val (v 1) at pos
      exact points 20 ▸ points 18 ▸ pos
    obtain ⟨r,_,hr⟩ := (elem hs code hj).1.1.2.2 (v 47)
      (state.request.values.elim fun bounds _ => bounds 19)
    have eq : r = R := same i r ⟨v,s,j,hs,code,hj,hr⟩
    have image := ((elem hs code hj).relation_l I hZF hw state.model target.1 hx hr).mp old
    exact eq ▸ ((target.2 x r).mp image).2.2
  have fn : Fn0_d ω R F := by
    have ft := fn0_function_l (ZF.modelsKP hZF) ff
    exact fn0_of_function_l (ZF.modelsKP hZF) ⟨ft.1,ft.2.1,fun i hi => by
      obtain ⟨x,_,hx⟩ := ft.2.2 i hi
      exact ⟨x,position i x ((fs i x).mp hx),hx⟩⟩
  -- 只在实际良基坍塌目标中读取完整控制记录及其真序数秩。
  obtain ⟨e,_,heω⟩ := hw.1.1
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 e heω
  obtain ⟨v,code,state⟩ := (h.rows e s hs).1
  obtain ⟨j,hj⟩ := (cone.domain (v 7)).mp ((branch _).mpr
    ⟨v,e,s,hs,code,u.tree.diagram.order.refl _ state.finite⟩)
  have map := elem hs code hj
  have number := state.request.numbers.omega_image_mem_l I hZF hw (raw_ext v hs code) state.model target nt map
  obtain ⟨η',C',_,imageC,context⟩ := state.request.context.map_l hZF hw state.model target.1 map number.1
  let nc' : Nonempty {x // M.mem x C'} := ⟨⟨ω,context.omega_l source.code⟩⟩
  have newFs := (context.read_l hZF source).1
  let N₀ := smdl_structure_l I (R := W) target.1.2.1
  let Cn : N₀.Domain := ⟨C',context.member⟩
  let nd : Nonempty {x : N₀.Domain // N₀.mem x Cn} :=
    ⟨⟨⟨ω,source.omega_mem⟩,(target.2 ω C').mpr ⟨source.omega_mem,context.member,context.omega_l source.code⟩⟩⟩
  obtain ⟨_,ρ,_,images,_,_,valid⟩ := map.record_image_l I hZF hw state.model target.1
    (smem_ext_l I target.1 target.2 nt hZF.1) Cn imageC (target.slice_transitive_l I Cn newFs.transitive)
      nd tg_issued0_m tg_issued0_closed_l state.request.record state.request.values
  let θ := target.slice_env_d I Cn nd nc' ρ
  have valid : Formula.satisfies θ tg_issued0_m :=
    (target.slice_formula_l I Cn (nt C' context.member) nd nc' tg_issued0_m ρ).mp valid
  have issued := (tg_issued_sat_l (rt_pair_l newFs.transitive nc' hZF.1 newFs.pair)
    (rt_model_ext_l hZF.1 newFs.transitive nc') θ).mp valid
  obtain ⟨α,J,_,_,rank⟩ := tg_control_rank_l (ZF.modelsKP hZF) newFs.transitive nc' _ issued.control
  have eq : (θ.bound 18).val = R := same e _ ⟨v,s,j,hs,code,hj,images 18⟩
  have rank : Cg_rank_d (θ.bound 0).val (θ.bound 12).val R α J := eq ▸ rank
  have proper i k x y (succ : M.SuccessorOf k i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d k y F) :
      M.MemberSubset x y ∧ x ≠ y := by
    obtain ⟨v,s,r,hs,ps,hr,hx⟩ := (fs i x).mp hx
    obtain ⟨w,t,l,ht,pt,hl,hy⟩ := (fs k y).mp hy
    have vr := h.read_l hZF v hs ps
    have wr := h.read_l hZF w ht pt
    obtain ⟨_,_,v',w',ps',pt',next⟩ := h.steps i k s t succ hs ht
    have eq := rt_tuple_inj_l ps' ps
    subst v'
    have eq := rt_tuple_inj_l pt' pt
    subst w'
    obtain ⟨_,_,_,_,_,b,_,_,_,edge,_,strict,_⟩ := next
    obtain ⟨z,hz,ne,sub⟩ := strict
    have edge : It_map_d (U 2) (v 7) (w 7) b := by
      obtain ⟨q,pair,p,pp,hp⟩ := edge
      exact ⟨q,pair,p,pp,(u.columns 2 p).mpr ⟨w,k,t,ht,pt,hp⟩⟩
    have between := u.tree.diagram.elementary (v 7) (w 7) b (v 15) (v 0) (v 1) (w 15) (w 0) (w 1)
      edge (h.node_l hZF u v hs ps) (h.node_l hZF u w ht pt) vr.model wr.model
    have leg := elem ht pt hl
    obtain ⟨x',_,hz'⟩ := leg.1.1.2.2 z (between.1.1.output_mem_of_pairMember hz)
    have eq := (elem hs ps hr).1.1.1.2 _ x' x (cone.commute (v 7) (w 7) b r l edge hr hl _ z x' hz hz') hx
    have image : Rd_entry_d z x l := eq ▸ hz'
    -- 子集断言先沿原关系初等图搬运，只在传递目标中读为背景包含。
    have subset : M.MemberSubset x y := by
      let V := smdl_structure_l I (R := w 1) wr.model.2.1
      let ξ : Env V 2 := ⟨fun i => Fin.cases ⟨w 49,leg.1.1.input_mem_of_pairMember hy⟩
        (fun _ => ⟨z,leg.1.1.input_mem_of_pairMember image⟩) i,fun _ => ⟨z,leg.1.1.input_mem_of_pairMember image⟩⟩
      let ψ : Formula 1 2 := Formula.subset (.bound 1) .newest
      have valid : Formula.satisfies ξ ψ := (Formula.satisfies_subset_iff ..).mpr
        (fun v hv => sub v.val v.property hv)
      have raw := (rr_truth_native_l I wr.model.2.1 ψ (by simp -implicitDefEqProofs [ψ]) ξ.bound).mpr valid
      have moved : Rr_truth_d I N W ψ (Fin.cases y (fun _ : Fin 1 => x)) :=
        raw.map_l I hZF hw wr.model target.1 leg (by simp -implicitDefEqProofs [ψ])
        (Fin.cases hy (fun _ => image))
      exact (Formula.satisfies_subset_iff (⟨Fin.cases y (fun _ => x),fun _ => x⟩ : Env M 2) (.bound 1) .newest).mp
        ((rr_truth_mem_l I nt target ψ (.atom ..) (Fin.cases y (fun _ => x))).mp moved).2
    exact ⟨subset,fun eq => ne (leg.1.2 z (w 49) y (eq ▸ image) hy)⟩
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

/-- 原偶数枝及其实际直接极限同时构造；该极限的商关系不良基。 -/
theorem Tg_iteration_run_d.even_limit_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U) : ∃ B,
    It_ill_branch_d hZF ω ω (U 0) (U 1) (U 2) B ∧
      ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x := by
  obtain ⟨B,branch,values⟩ := h.even_branch_l hZF u
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨i,hi,_⟩ := branch.cofinal e he
  obtain ⟨L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model⟩ :=
    it_branch_data_l hZF u.tree.omega u.tree.diagram branch ⟨i,hi⟩
  exact ⟨B,⟨branch,L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model,
    fun wf => h.even_illfounded_l hZF u values
      ⟨branch,L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model,wf⟩⟩,values⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系运行的实际极限固定根低层

共尾档案行各自保留完整低层图及同一原根图。原根仅需一般关系模型；
低层图和根图的相合由真实基底给出，再由极限锥的内部成员归纳得出固定性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_iteration_run_d.branch_fixed_l
    {ω c o C₀ S₀ γ Bγ A X K r a f H b d N W P : M.Domain}
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    (branch : It_branch_d ω (U 0) b) (odd : Tg_odd_cofinal_d ω b (U 5))
    (mn : Smem_d I d N W) (nt : M.TransitiveSet N)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P) :
    ∀ j, Rd_entry_d o j P → ∀ x, M.mem x Bγ → Rd_entry_d x x j := by
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 e he
  obtain ⟨v,code,state⟩ := (h.rows e s hs).1
  have root : Rd_entry_d o c (U 1) := by
    obtain ⟨p,pair,hp⟩ := state.root_node
    exact ⟨p,pair,(u.columns 1 p).mpr ⟨v,e,s,hs,code,hp⟩⟩
  obtain ⟨X₀,R₀,mx⟩ := u.tree.diagram.models o c root
  apply cone.fixed_l hZF u.tree.omega u.tree.diagram branch root mx mn nt
  intro i hi
  obtain ⟨k,hk,ik,m,r,t,entry,pair⟩ := odd i (branch.subset i hi)
  obtain ⟨p,pp,hp⟩ := entry
  obtain ⟨v,l,s,hs,pack,hp⟩ := (u.columns 5 p).mp hp
  have state := h.read_l hZF v hs pack
  have entry : Rd_entry_d m r (v 13) := ⟨p,pp,hp⟩
  obtain ⟨row,code,my,_,_,basis,_⟩ := state.request.views m r entry
  have index : row.i = k := by
    obtain ⟨t',pair',_⟩ := code
    exact (kpair_injective_l M pair' pair).1
  subst k
  have links := state.request.links m r row entry code
  have node : Rd_entry_d row.i row.c (U 1) := by
    obtain ⟨q,qp,hq⟩ := links.2.1
    exact ⟨q,qp,(u.columns 1 q).mpr ⟨v,l,s,hs,pack,hq⟩⟩
  have edge : It_map_d (U 2) o row.i row.p := by
    obtain ⟨q,qp,p,pp,hp⟩ := links.2.2.1
    exact ⟨q,qp,p,pp,(u.columns 2 p).mpr ⟨v,l,s,hs,pack,hp⟩⟩
  have map := u.tree.diagram.elementary o row.i row.p c X₀ R₀ row.c row.X row.R
    edge root node mx my
  obtain ⟨_,V,_,t,_,layer,_,fixed⟩ := basis.anchor_l I
  refine ⟨row.i,row.p,row.c,row.X,row.R,hk,
    branch.forward_l u.tree.diagram.order hi hk ik,edge,node,my,layer.transitive,?_,?_⟩
  · intro x hx
    obtain ⟨y,_,xy⟩ := layer.injection.1.2.2 x hx
    exact ⟨y,fixed x y xy⟩
  · intro x y hx xy z
    obtain ⟨y',_,xy'⟩ := layer.injection.1.2.2 x hx
    have same := map.1.1.1.2 x y' y (fixed x y' xy') xy
    apply (layer.predecessors x y (same ▸ xy') z).trans
    apply exists_congr
    intro a
    apply and_congr_right
    intro ax
    refine ⟨fixed a z,fun az => ?_⟩
    obtain ⟨z',_,az'⟩ := layer.injection.1.2.2 a (layer.transitive x hx a ax)
    exact map.1.1.1.2 a z' z (fixed a z' az') az ▸ az'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系运行中的实际奇数尾段

非偶数节点的首次出现只能是同一次两步延伸新增的档案行。其父边和完整存档方程
一起进入原并树；与偶数枝分离后，尾段中的每条父边都来自真实继续步骤。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_iteration_odd_d (H D T G B y : M.Domain) : Prop :=
  ∃ n s, ∃ v : Fin 75 → M.Domain, Rd_entry_d n s H ∧ Rt_tuple_d v s ∧ y = v 6 ∧
    ∃ k, ∃ row : Tg_archive_row_d M.Domain, ∃ r, row.i = y ∧ Rd_entry_d (v 27) r D ∧
      Rt_tuple_d row.values_d r ∧
      Tg_iteration_parent_d hZF (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 29 i)) k G row ∧
      It_pred_d T k y ∧ M.mem (v 7) B

/-- 尾段保留完整两端原档案、严格较早的索引及同一继续边上的三图方程。 -/
def Tg_archive_tail_d (J : kpair_convention_l.Interpretation M) (D T G B b : M.Domain) : Prop := ∃ z,
  M.mem z b ∧ ¬ M.mem z B ∧ Tg_odd_node_d D z ∧ ∀ y, M.mem y b → M.mem z y →
    ∃ m r, ∃ row : Tg_archive_row_d M.Domain, Rd_entry_d m r D ∧ Rt_tuple_d row.values_d r ∧ row.i = y ∧
      ∃ l t, ∃ old : Tg_archive_row_d M.Domain, ∃ j, M.mem l m ∧ Rd_entry_d l t D ∧ Rt_tuple_d old.values_d t ∧
        It_pred_d T old.i y ∧ M.mem old.i b ∧ ¬ M.mem old.i B ∧ (z = old.i ∨ M.mem z old.i) ∧
        It_map_d G old.i y j ∧ Tg_archive_step_d J old row j

variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

theorem Tg_iteration_run_d.late_odd_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {B e s₀ y : M.Domain} {v₀ : Fin 75 → M.Domain}
    (even : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x) (empty : ∀ x, ¬ M.mem x e)
    (first : Rd_entry_d e s₀ H) (code₀ : Rt_tuple_d v₀ s₀) (hy : M.mem y ω)
    (outside : ¬ M.mem y (v₀ 6)) (not_even : ¬ M.mem y B) :
    Tg_odd_node_d (U 5) y ∧ Tg_iteration_odd_d hZF H (U 5) (U 0) (U 2) B y := by
  obtain ⟨l,k,t,s,w,v,succ,ht,ct,hs,code,old,hyv⟩ :=
    (h.frames_l hZF).first_l hZF v₀ empty first code₀ hy outside
  obtain ⟨_,_,w',v',ct',code',next⟩ := h.steps l k t s succ ht hs
  have eq := rt_tuple_inj_l ct' ct
  subst w'
  have eq := rt_tuple_inj_l code' code
  subst v'
  obtain ⟨a,T,Q,G,E,j,mid,e₁,e₂,_,_,_,_,_,_,_,_,_,_,row,r,index,rc,parent,entries⟩ := next
  have index : row.i = w 6 := index
  rcases (e₂.1 y).mp hyv with hym | eq
  · rcases (e₁.1 y).mp hym with hyo | eq
    · exact (old hyo).elim
    · have eq := hZF.1.eq_of_same_members y (w 6) eq
      subst y
      have state := h.read_l hZF w ht ct
      have inside (b : Fin 6) {i j} (entry : Rd_entry_d i j (v ⟨8+b.val,by omega⟩)) : Rd_entry_d i j (U b) := by
        obtain ⟨p,pair,hp⟩ := entry
        exact ⟨p,pair,(u.columns b p).mpr ⟨v,k,s,hs,code,hp⟩⟩
      have ha : M.mem a (w 6) := by
        obtain ⟨_,_,choice⟩ := parent
        rcases choice with ⟨_,eq,_⟩ | ⟨_,l,r,old,_,_,entry,pack,eq,_⟩
        · exact eq.symm ▸ state.successor.predecessor_mem
        · have links := state.request.links l r old entry pack
          exact eq ▸ (state.tree.diagram.model_domain old.i).mpr ⟨old.c,links.2.1⟩
      have keep₁ := state.tree.extension_keep_l hZF e₁
      have keep₂ := mid.extension_keep_l hZF e₂
      have hw := e₁.1.predecessor_mem
      have hyv := (e₂.1 _).mpr (Or.inl hw)
      have hav := (e₂.1 _).mpr (Or.inl ((e₁.1 _).mpr (Or.inl ha)))
      have tip i : Rd_entry_d i (w 6) T ↔ i = w 6 ∨ Rd_entry_d i a (w 8) :=
        (e₁.2.1 i (w 6)).trans ⟨fun h => h.elim
          (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) _ (state.tree.diagram.order.bound _ _ h).2).elim)
          And.right,fun h => Or.inr ⟨rfl,h⟩⟩
      have pred : It_pred_d (U 0) a (w 6) := ⟨ha,fun i =>
        (u.restriction k s v hs code i _ hyv).trans ((keep₂.1 i _ hw).trans
          ((tip i).trans (or_congr Iff.rfl ((keep₁.1 i a ha).symm.trans
            ((keep₂.1 i a ((e₁.1 a).mpr (Or.inl ha))).symm.trans (u.restriction k s v hs code i a hav).symm)))))⟩
      have lift {i j} (edge : It_map_d G i (w 6) j) : It_map_d (U 2) i (w 6) j := by
        obtain ⟨p,pair,entry⟩ := (e₂.2.2.2.1 i (w 6) j hw).mpr edge
        exact ⟨p,pair,inside 2 entry⟩
      have parent : Tg_iteration_parent_d hZF (fun i => w (i.castAdd 46))
          (fun i => w (Fin.natAdd 29 i)) a (U 2) row := by
        obtain ⟨j,edge,choice⟩ := parent
        exact ⟨j,lift edge,choice⟩
      have entry := inside 5 ((entries (w 27) r).mpr (Or.inr ⟨rfl,rfl⟩))
      have node : Tg_odd_node_d (U 5) (w 6) := by
        obtain ⟨tail,pair,_⟩ := rc
        have pair : KPair_d M r row.i tail := pair
        exact ⟨w 27,r,tail,entry,index ▸ pair⟩
      exact ⟨node,l,t,w,ht,ct,rfl,a,row,r,index,entry,rc,parent,pred,
        (even _).mpr ⟨w,l,t,ht,ct,u.tree.diagram.order.refl _ state.finite⟩⟩
  · have eq := hZF.1.eq_of_same_members y (v 7) eq
    exact (not_even ((even y).mpr ⟨v,k,s,hs,code,
      eq.symm ▸ u.tree.diagram.order.refl _ (h.read_l hZF v hs code).finite⟩)).elim

/-- 与偶数枝分离后，实际树前驱仍在同一尾段；重置被排除，留下完整继续边。 -/
theorem Tg_iteration_run_d.odd_tail_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U) {B b : M.Domain}
    (even_branch : It_branch_d ω (U 0) B)
    (even : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x)
    (branch : It_branch_d ω (U 0) b) (ne : b ≠ B) :
    Tg_odd_cofinal_d ω b (U 5) ∧ Tg_archive_tail_d I (U 5) (U 0) (U 2) B b := by
  have hw := u.tree.omega
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨e,empty,he⟩ := hw.1.1
  obtain ⟨s₀,_,first⟩ := h.recursion.1.2.1 e he
  obtain ⟨v₀,code₀,_⟩ := (h.rows e s₀ first).1
  have finite := ((h.frames_l hZF).read_l hZF v₀ first code₀).finite
  have late := branch.separate_l hZF.1 u.tree.diagram.order even_branch ne finite
  refine ⟨fun i hi => ?_,?_⟩
  · obtain ⟨y,hy,iy,yn,outside⟩ := late i hi
    exact ⟨y,hy,iy,(h.late_odd_l hZF u even empty first code₀ (branch.subset y hy) outside yn).1⟩
  · obtain ⟨z,hz,_,zn,outside⟩ := late e he
    refine ⟨z,hz,zn,(h.late_odd_l hZF u even empty first code₀ (branch.subset z hz) outside zn).1,?_⟩
    intro y hy zy
    have order := branch.forward_l u.tree.diagram.order hz hy (Or.inr zy)
    have yn : ¬ M.mem y B := fun h => zn (even_branch.down z y order h)
    have yo : ¬ M.mem y (v₀ 6) := fun h => outside
      ((hw.members_areOrdinals (ZF.modelsKP hZF) _ finite).transitive y h z zy)
    obtain ⟨_,n,s,v,hs,code,yv,k,row,r,index,entry,rc,parent,pred,ev⟩ :=
      h.late_odd_l hZF u even empty first code₀ (branch.subset y hy) yo yn
    have zk : Rd_entry_d z k (U 0) := ((pred.2 z).mp order).elim
      (fun eq => (ir y (eq ▸ zy)).elim) id
    have ky := (pred.2 k).mpr (Or.inr (u.tree.diagram.order.refl k
      (hw.transitive (ZF.modelsKP hZF) y (branch.subset y hy) k pred.1)))
    have kb := branch.down k y ky hy
    have kn : ¬ M.mem k B := fun h => zn (even_branch.down z k zk h)
    have ze := u.tree.diagram.order.forward z k zk
    obtain ⟨j,edge,choice⟩ := parent
    have edge : It_map_d (U 2) k y j := by
      have edge : It_map_d (U 2) k (v 6) j := edge
      exact yv.symm ▸ edge
    rcases choice with ⟨_,eq,_⟩ | ⟨_,l,t,old,lt,_,old_entry,pack,eq,step⟩
    · have eq : k = v 7 := eq
      exact (kn (eq.symm ▸ ev)).elim
    · have old_entry : Rd_entry_d l t (U 5) := by
        obtain ⟨p,pair,hp⟩ := old_entry
        exact ⟨p,pair,(u.columns 5 p).mpr ⟨v,n,s,hs,code,hp⟩⟩
      exact ⟨v 27,r,row,entry,rc,index,l,t,old,j,lt,old_entry,pack,
        eq.symm ▸ pred,eq.symm ▸ kb,eq.symm ▸ kn,eq.symm ▸ ze,eq.symm ▸ edge,step⟩

/-- 枝上的完整档案尾段自动共尾；有限初段由尾段起点本身覆盖。 -/
theorem Tg_archive_tail_d.cofinal_l (hE : Extensional M)
    {J : kpair_convention_l.Interpretation M} {ω D T G B b : M.Domain}
    (tail : Tg_archive_tail_d J D T G B b) (ordinal : M.IsOrdinal ω)
    (branch : It_branch_d ω T b) : Tg_odd_cofinal_d ω b D := by
  obtain ⟨z,hz,_,node,later⟩ := tail
  intro i hi
  obtain ⟨y,hy,iy⟩ := branch.cofinal i hi
  rcases ordinal.wellOrder.linear.compare z (branch.subset z hz) y (branch.subset y hy) with eq | zy | yz
  · have eq := hE.eq_of_same_members z y eq
    subst y
    exact ⟨z,hz,iy,node⟩
  · obtain ⟨m,r,row,entry,pack,index,_⟩ := later y hy zy
    obtain ⟨t,pair,_⟩ := pack
    have pair : KPair_d M r row.i t := pair
    exact ⟨y,hy,iy,m,r,t,entry,index ▸ pair⟩
  · exact ⟨z,hz,Or.inr (iy.elim (fun eq => eq.symm ▸ yz)
      (fun lt => (ordinal.mem (branch.subset z hz)).transitive y yz i lt)),node⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定原奇数尾段的唯一目标节点列

实际相邻树节点列确定档案，档案与同一锥确定全部五个像。背景替换一次收集整列，
其每个相邻步骤保留同一树、长度后继、三图包含及恢复图精确追加。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_archive_sequence_d (I : kpair_convention_l.Interpretation M)
    (ω N D P b L J F : M.Domain) : Prop extends Tg_node_sequence_d I ω N L F where
  indices : Fn0_d ω b J
  images : ∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    ∃ k m, Rd_entry_d i k J ∧ Tg_archive_image_d D P m k v
  equations : ∀ i j r s (v w : Fin 5 → M.Domain), M.SuccessorOf j i →
    Rd_entry_d i r F → Rd_entry_d j s F → Rt_tuple_d v r → Rt_tuple_d w s →
      v 1 = w 1 ∧ ∃ x, Rd_entry_d (v 0) x (w 4) ∧
        ∀ p, M.mem p (w 4) ↔ M.mem p (v 4) ∨ KPair_d M p (v 0) x

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

theorem Tg_iteration_run_d.archive_sequence_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {B b d N W P : M.Domain} (branch : It_branch_d ω (U 0) b)
    (tail : Tg_archive_tail_d I (U 5) (U 0) (U 2) B b)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N) :
    ∃ L J F, Tg_archive_sequence_d I ω N (U 5) P b L J F := by
  have hw := u.tree.omega
  have unique {m n i} {v w : Fin 5 → M.Domain}
      (hv : Tg_archive_image_d (U 5) P m i v) (hw : Tg_archive_image_d (U 5) P n i w) : v = w :=
    h.archive_image_unique_l hZF u branch cone hv hw
  have decoded m p (hp : Rd_entry_d m p (U 5)) : ∃ row : Tg_archive_row_d M.Domain, Rt_tuple_d row.values_d p := by
    obtain ⟨q,pair,hq⟩ := hp
    obtain ⟨v,i,s,hs,code,hq⟩ := (u.columns 5 q).mp hq
    obtain ⟨row,pack,_⟩ := (h.read_l hZF v hs code).request.views m p ⟨q,pair,hq⟩
    exact ⟨row,pack⟩
  have data {m i} {v : Fin 5 → M.Domain} (trace : Tg_archive_image_d (U 5) P m i v) :
      M.mem (v 0) ω ∧ (∀ a, M.mem (v a) N) ∧ Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4) := by
    have copy := trace
    obtain ⟨p,row,entry,tuple,index,_,_,j,leg,_⟩ := copy
    have hi := index.symm ▸ (cone.domain i).mpr ⟨j,leg⟩
    obtain ⟨w,finite,members,node,image⟩ := h.archive_images_l hZF u cone target nt row entry tuple hi
    have image : Tg_archive_image_d (U 5) P m i w := index ▸ image
    exact (unique trace image).symm ▸ ⟨finite,members,node⟩
  obtain ⟨z,hz,_,hzOdd,late⟩ := tail
  obtain ⟨J,jf,_,adjacent,above⟩ := branch.successor_sequence_l hZF hw u.tree.diagram.order hz
  let ρ : Env M 3 := ⟨fun i => [U 5,P,J].get i,fun _ => ω⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ k,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,k,⌜(.bound 4 : Term 5)⌝ₛ) ∧
    ⌜tg_archive_row_image_m⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ,⌜(.bound 3 : Term 5)⌝ₛ,k,⌜(.newest : Term 5)⌝ₛ)⟫ }
  have sat i r : φ.denote ρ i r ↔ ∃ k, Rd_entry_d i k J ∧ Tg_archive_row_image_d (U 5) P k r := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,tg_archive_row_image_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  have total i (hi : M.mem i ω) : ∃ r, φ.denote ρ i r := by
    obtain ⟨k,hk,hik⟩ := jf.2.1 i hi
    have odd : Tg_odd_node_d (U 5) k := by
      rcases above i k hik with eq | zk
      · exact eq ▸ hzOdd
      · obtain ⟨m,p,row,entry,tuple,index,_⟩ := late k hk zk
        obtain ⟨t,pair,_⟩ := tuple
        have pair : KPair_d M p row.i t := pair
        exact ⟨m,p,t,entry,index ▸ pair⟩
    obtain ⟨m,p,t,entry,pair⟩ := odd
    obtain ⟨row,tuple⟩ := decoded m p entry
    have index : row.i = k := by
      obtain ⟨t',pair',_⟩ := tuple
      exact (kpair_injective_l M pair' pair).1
    obtain ⟨v,_,_,_,trace⟩ := h.archive_images_l hZF u cone target nt row entry tuple (index.symm ▸ hk)
    obtain ⟨r,code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) v
    exact ⟨r,(sat i r).mpr ⟨k,hik,m,v,index ▸ trace,code⟩⟩
  have one i r s (hr : φ.denote ρ i r) (hs : φ.denote ρ i s) : r = s := by
    obtain ⟨k,hk,m,v,trace,code⟩ := (sat i r).mp hr
    obtain ⟨l,hl,n,w,trace',code'⟩ := (sat i s).mp hs
    have eq := (fn0_function_l (ZF.modelsKP hZF) jf).1.2 i l k hl hk
    subst l
    exact rt_tuple_unique_l hZF.1 code ((unique trace trace').symm ▸ code')
  obtain ⟨L,ls⟩ := ZF.exists_functionalImage hZF φ ρ ω total one
  obtain ⟨F,ff,fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun i _ => one i)
    (fun i r hi hr => (ls r).mpr ⟨i,hi,hr⟩)
  have read i r (v : Fin 5 → M.Domain) (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) :
      ∃ k m, Rd_entry_d i k J ∧ Tg_archive_image_d (U 5) P m k v := by
    obtain ⟨k,hk,m,w,trace,pack⟩ := (sat i r).mp ((fs i r).mp hr).2
    exact ⟨k,m,hk,rt_tuple_inj_l pack code ▸ trace⟩
  have coded i r (hr : Rd_entry_d i r F) : ∃ v : Fin 5 → M.Domain, Rt_tuple_d v r := by
    obtain ⟨_,_,_,v,_,code⟩ := (sat i r).mp ((fs i r).mp hr).2
    exact ⟨v,code⟩
  have growth i j r s (v w : Fin 5 → M.Domain) (succ : M.SuccessorOf j i)
      (hr : Rd_entry_d i r F) (hs : Rd_entry_d j s F) (code : Rt_tuple_d v r) (pack : Rt_tuple_d w s) :
      v 1 = w 1 ∧ M.SuccessorOf (w 0) (v 0) ∧
      (∀ a : Fin 3, M.MemberSubset (v ([2,3,4].get a)) (w ([2,3,4].get a))) ∧
      ∃ x, Rd_entry_d (v 0) x (w 4) ∧ ∀ p, M.mem p (w 4) ↔ M.mem p (v 4) ∨ KPair_d M p (v 0) x := by
    obtain ⟨x,m,hx,tr⟩ := read i r v hr code
    obtain ⟨y,n,hy,tr'⟩ := read j s w hs pack
    have pred := adjacent i j x y succ hx hy
    have zy : M.mem z y := (above i x hx).elim (fun eq => eq.symm ▸ pred.1)
      (fun zx => (hw.members_areOrdinals (ZF.modelsKP hZF) y (branch.subset y (jf.bound_l hy).2)).transitive x pred.1 z zx)
    obtain ⟨n',q,row,entry,tuple,index,m',p,old,edge,_,prior,tuple',pk,kb,_,_,map,step⟩ := late y (jf.bound_l hy).2 zy
    have pk : It_pred_d (U 0) old.i y := pk
    have eq := pk.unique_l hZF u.tree.diagram.order pred (branch.subset y (jf.bound_l hy).2)
    obtain ⟨v',_,_,_,left⟩ := h.archive_images_l hZF u cone target nt old prior tuple' kb
    obtain ⟨w',_,_,_,right⟩ := h.archive_images_l hZF u cone target nt row entry tuple (index.symm ▸ (jf.bound_l hy).2)
    have ev : v = v' := unique tr (eq ▸ left)
    have ew : w = w' := unique tr' (index ▸ right)
    have edge' : It_map_d (U 2) old.i row.i edge := index.symm ▸ map
    exact ev.symm ▸ ew.symm ▸ h.archive_growth_l hZF u cone target nt old row prior entry tuple' tuple edge' step left right
  refine ⟨L,J,F,{
    omega := hw
    transitive := nt
    function := fn0_of_function_l (ZF.modelsKP hZF) ff
    codes := coded
    rows := ?_
    steps := ?_
    indices := jf
    images := read
    equations := ?_ }⟩
  · intro i r v hr code
    obtain ⟨_,_,_,trace⟩ := read i r v hr code
    exact data trace
  · intro i j r s v w succ hr hs code pack
    have grow := growth i j r s v w succ hr hs code pack
    exact ⟨grow.2.1,grow.2.2.1⟩
  · intro i j r s v w succ hr hs code pack
    have grow := growth i j r s v w succ hr hs code pack
    exact ⟨grow.1,grow.2.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真实原档案在指定极限中的共同根树像

每行的树名及根图都从同一次实际请求读回；锥交换把其树坐标识别为原根对象的像。
实际节点列的一行已足以取得根腿，故无需另给树名条件、根模型呈示或根对象所属。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

/-- 同一全局档案行保留实际请求中的根图及原根树名。 -/
theorem Tg_iteration_run_d.archive_names_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {m r : M.Domain} (row : Tg_archive_row_d M.Domain)
    (entry : Rd_entry_d m r (U 5)) (tuple : Rt_tuple_d row.values_d r) :
    It_map_d (U 2) o row.i row.p ∧ Tg_saved_name_d I S₀ row.X row.R row.w row.U row.q row.p := by
  obtain ⟨p,pair,hp⟩ := entry
  obtain ⟨v,k,s,hs,pack,hp⟩ := (u.columns 5 p).mp hp
  have state := h.read_l hZF v hs pack
  have entry : Rd_entry_d m r (v 13) := ⟨p,pair,hp⟩
  have links := state.request.links m r row entry tuple
  obtain ⟨q,pair',p,pp,hp⟩ := links.2.2.1
  exact ⟨⟨q,pair',p,pp,(u.columns 2 p).mpr ⟨v,k,s,hs,pack,hp⟩⟩,
    state.request.names m r row entry tuple⟩

/-- 每个实际五坐标像的树坐标都沿同一根腿解释原根树对象。 -/
theorem Tg_iteration_run_d.archive_tree_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {b d N W P j₀ m i : M.Domain} {v : Fin 5 → M.Domain}
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (root : Rd_entry_d o j₀ P) (trace : Tg_archive_image_d (U 5) P m i v) :
    Rd_entry_d S₀ (v 1) j₀ := by
  obtain ⟨r,row,entry,tuple,index,w,code,j,leg,images⟩ := trace
  obtain ⟨map,name⟩ := h.archive_names_l hZF u row entry tuple
  have leg : Rd_entry_d row.i j P := index.symm ▸ leg
  exact cone.commute o row.i row.p j₀ j map root leg S₀ (w 19) (v 1) (name w code) (images 1)

/-- 实际节点列自动提供根腿；同一树对象识别该锥中的全部原档案像。 -/
theorem Tg_iteration_run_d.archive_sequence_tree_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {b d N W P L J F : M.Domain} (branch : It_branch_d ω (U 0) b)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (seq : Tg_archive_sequence_d I ω N (U 5) P b L J F) :
    ∃ j₀ S, Rd_entry_d o j₀ P ∧ M.mem S N ∧ Rd_entry_d S₀ S j₀ ∧
      ∀ m i (v : Fin 5 → M.Domain), Tg_archive_image_d (U 5) P m i v → v 1 = S := by
  obtain ⟨e,_,he⟩ := seq.omega.1.1
  obtain ⟨s,_,hs⟩ := seq.function.2.1 e he
  obtain ⟨v,code⟩ := seq.codes e s hs
  obtain ⟨i,m,_,trace⟩ := seq.images e s v hs code
  have trace₀ := trace
  obtain ⟨r,row,entry,tuple,index,w,pack,j,leg,images⟩ := trace
  have map := (h.archive_names_l hZF u row entry tuple).1
  have hi : M.mem row.i b := index.symm ▸ (cone.domain i).mpr ⟨j,leg⟩
  have ho := branch.down o row.i (u.tree.diagram.map_bound_l hZF map) hi
  obtain ⟨j₀,root⟩ := (cone.domain o).mp ho
  obtain ⟨c',X',R',node,model⟩ := u.tree.diagram.model_l hZF (branch.subset o ho)
  have image := h.archive_tree_l hZF u cone root trace₀
  have elementary := cone.elementary o j₀ c' X' R' root node model
  refine ⟨j₀,v 1,root,(seq.rows e s v hs code).2.1 1,image,?_⟩
  intro m i w trace
  exact elementary.1.1.1.2 S₀ (w 1) (v 1) (h.archive_tree_l hZF u cone root trace) image

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定极限中的每份实数档案像仍是原对局的有限部分

目标取值先沿同一锥腿回拉到原档案，再沿真实共同图进入足够晚的实际历史。
事件唯一性识别当前根字母，完整低层交换把它读回原档案；锥交换与根低层固定性最后识别目标值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_iteration_run_d.archive_real_l
    {ω c o C₀ S₀ γ Bγ A X K r a f H X₀ R₀ b d N W P j₀ m k : M.Domain}
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    (root : Zc_model_d I ω c X₀ R₀) (letters : M.mem A Bγ) (input : Fn0_d ω A f)
    (played : Tg_archive_play_native_d I ω (U 5) H f)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (rootLeg : Rd_entry_d o j₀ P) (fixed : ∀ x, M.mem x Bγ → Rd_entry_d x x j₀)
    {v : Fin 5 → M.Domain} (trace : Tg_archive_image_d (U 5) P m k v)
    (finite : M.mem (v 0) ω) (graph : Tg_graph_d I (v 0) (v 2)) : M.MemberSubset (v 2) f := by
  obtain ⟨r,row,entry,tuple,index,w,code,j,leg,images⟩ := trace
  have leg : Rd_entry_d row.i j P := index.symm ▸ leg
  obtain ⟨node,model,saved,z,numbers⟩ := h.archive_read_l hZF u row entry tuple
  have map := cone.elementary row.i j row.c row.X row.R leg node model
  have natural := numbers.omega_image_mem_l I hZF u.tree.omega saved.ext model target nt map
  have edge := (h.archive_names_l hZF u row entry tuple).1
  intro p hp
  obtain ⟨i,y,pair⟩ := graph.1.1 p hp
  have value : Rd_entry_d i y (v 2) := ⟨p,pair,hp⟩
  have hi := u.tree.omega.transitive (ZF.modelsKP hZF) _ finite i ((graph.2 i).mpr ⟨y,value⟩)
  obtain ⟨n,_,point⟩ := numbers.injection.1.2.2 i hi
  obtain ⟨x,raw,image⟩ := Smap_d.value_preimage_l hZF u.tree.omega model target nt map saved.ext
    (natural.2 i n point) (images 2) graph.1 value
  obtain ⟨l,t,ρ,l',φ,V,Γ,g,s,ht,pack,_,old,common,short,_,values⟩ := played m r row entry tuple w code i hi
  have state := h.read_l hZF ρ ht pack
  obtain ⟨n',x',point',_,ix',value'⟩ := state.archive_transport_l hZF root row old tuple common short numbers point raw
  obtain ⟨z,hz,iz⟩ := input.2.1 i hi
  have current : Rd_entry_d z x' (ρ 16) := values n' x' z point' value' iz
  obtain ⟨_,_,_,_,_,layer,_,_⟩ := state.basis.anchor_l I
  have low := layer.transitive A letters z hz
  have source := (state.archive_low_l hZF root row old tuple common).2.2.2 z x x' low ix' current
  have rootNode : Rd_entry_d o c (U 1) := by
    obtain ⟨q,qp,hq⟩ := state.root_node
    exact ⟨q,qp,(u.columns 1 q).mpr ⟨ρ,l,t,ht,pack,hq⟩⟩
  have rootMap := cone.elementary o j₀ c X₀ R₀ rootLeg rootNode root.model
  have eq := rootMap.1.1.1.2 z y z
    (cone.commute o row.i row.p j₀ j edge rootLeg leg z x y source image) (fixed z low)
  obtain ⟨q,qp,hq⟩ := iz
  exact kpair_unique_l M hZF.1 qp (eq ▸ pair) ▸ hq

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定良基枝中的实际档案像与三图并

给定分支自身的良基极限供应传递目标和真实锥。档案像列的共同树就是原根树名的像，
同一根腿固定完整低层。三张图的并定义于整个内部ω，并合成为该树中的共尾分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_archive_union_d (ω o S₀ Bγ D T Q G b : M.Domain) : Prop :=
  ∃ d N W P L J F S j, ∃ g : Fin 3 → M.Domain,
    Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧ It_branch_d ω T b ∧
    It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Tg_archive_sequence_d I ω N D P b L J F ∧
    Rd_entry_d o j P ∧ Rd_entry_d S₀ S j ∧
    (∀ x, M.mem x Bγ → Rd_entry_d x x j) ∧ M.mem S N ∧
    (∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → v 1 = S) ∧
    (∀ a, Tg_return_union_d hZF ω N F a (g a)) ∧
    ∃ Y q, Tg_cofinal_branch_d hZF ω Y S q ∧ Tg_join_d I ω (g 0) (g 1) (g 2) q

/-- 同一次指定良基极限保留真实根树名、低层固定性与完整合成分支。 -/
theorem Tg_iteration_run_d.branch_union_l {ω c o C₀ S₀ γ Bγ A X K r a f H B b : M.Domain}
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    (tail : Tg_archive_tail_d I (U 5) (U 0) (U 2) B b)
    (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b) :
    Tg_archive_union_d hZF ω o S₀ Bγ (U 5) (U 0) (U 1) (U 2) b := by
  obtain ⟨β,T',Q',G',ext⟩ := it_wf_branch_extend_l hZF u.tree
    (u.tree.omega.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_,_,_,_,_,_,d,N,W,P,_,_,_,model,nt,cone,nodes,_⟩ := ext.limit
  have source := ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl,rfl⟩))
  obtain ⟨L,J,F,seq⟩ := h.archive_sequence_l hZF u wf.1 tail cone.toIt_embedding_d model nt
  obtain ⟨j,S,root,hS,image,names⟩ := h.archive_sequence_tree_l hZF u wf.1 cone.toIt_embedding_d seq
  have name i r (v : Fin 5 → M.Domain) (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) : v 1 = S := by
    obtain ⟨k,m,_,trace⟩ := seq.images i r v hr code
    exact names m k v trace
  have odd := tail.cofinal_l hZF.1 u.tree.diagram.order.ordinal wf.1
  have fixed := h.branch_fixed_l hZF u wf.1 odd model nt cone j root
  obtain ⟨g₀,union₀⟩ := seq.toTg_node_sequence_d.union_l hZF 0
  obtain ⟨g₁,union₁⟩ := seq.toTg_node_sequence_d.union_l hZF 1
  obtain ⟨g₂,union₂⟩ := seq.toTg_node_sequence_d.union_l hZF 2
  let g : Fin 3 → M.Domain := fun i => [g₀,g₁,g₂].get i
  have unions : ∀ a, Tg_return_union_d hZF ω N F a (g a) :=
    Fin.cases union₀ (Fin.cases union₁ (Fin.cases union₂ (fun i => Fin.elim0 i)))
  obtain ⟨Y,q,cofinal,join⟩ := seq.toTg_node_sequence_d.branch_join_l hZF name unions
  exact ⟨d,N,W,P,L,J,F,S,j,g,model,nt,source,wf.1,cone,seq,root,image,fixed,hS,name,unions,Y,q,cofinal,join⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一档案并图在实际根树像中的完整分支

保留指定极限及同一节点列、三张并图和合成图。原根的完整数字图把其自然数对象
送到背景ω，原有限空间及树随后沿同一根腿搬运；共尾前缀由树封闭性成为完整分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原档案并的全部实际证据，以及同一合成图在根树像中的完整分支。 -/
def Tg_archive_full_tree_d (ω o S₀ Bγ D T Q G b Y₀ F₀ : M.Domain) : Prop :=
  ∃ d N W P L J F S j, ∃ g : Fin 3 → M.Domain,
    Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧ It_branch_d ω T b ∧
    It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Tg_archive_sequence_d I ω N D P b L J F ∧
    Rd_entry_d o j P ∧ Rd_entry_d S₀ S j ∧
    (∀ x, M.mem x Bγ → Rd_entry_d x x j) ∧ M.mem S N ∧
    (∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → v 1 = S) ∧
    (∀ a, Tg_return_union_d hZF ω N F a (g a)) ∧
    ∃ Y q Y' F', Tg_cofinal_branch_d hZF ω Y S q ∧ Tg_join_d I ω (g 0) (g 1) (g 2) q ∧
      Rd_entry_d Y₀ Y' j ∧ Rd_entry_d F₀ F' j ∧ Fseq_space_d I ω Y' F' ∧ Tree_d F' S ∧
      Fn0_d ω Y' q ∧ Branch_d F' S q

theorem Tg_archive_union_d.tree_l
    {ω c o C₀ S₀ γ Bγ A X K r a f H b X₀ R₀ w z Y₀ F₀ : M.Domain} {U : Fin 6 → M.Domain}
    (bundle : Tg_archive_union_d hZF ω o S₀ Bγ (U 5) (U 0) (U 1) (U 2) b)
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    (u : Tg_iteration_union_d hZF ω c γ H U) (model : Smdl_d I c X₀ R₀)
    (numbers : Rr_layer_d I ω X₀ R₀ w z) (space : Sc_fseq_d I w Y₀ F₀ X₀ R₀)
    (closed : Rr_truth_d I X₀ R₀ (tree_m (.bound 1) .newest) (Fin.cases S₀ (fun _ : Fin 1 => F₀))) :
    Tg_archive_full_tree_d hZF ω o S₀ Bγ (U 5) (U 0) (U 1) (U 2) b Y₀ F₀ := by
  have hw := u.tree.omega
  obtain ⟨e,_,he⟩ := hw.1.1
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 e he
  obtain ⟨v,code,state⟩ := (h.rows e s hs).1
  have root : Rd_entry_d o c (U 1) := by
    obtain ⟨p,pair,hp⟩ := state.root_node
    exact ⟨p,pair,(u.columns 1 p).mpr ⟨v,e,s,hs,code,hp⟩⟩
  have ext : Rf_ext_d I X₀ R₀ := by
    obtain ⟨X',R',_,_,_,model',source,_⟩ := (u.tree.sources o c root).objects
    obtain ⟨eqX,eqR⟩ := smdl_unique_l I model' model
    subst X' R'
    exact source.ext
  obtain ⟨d,N,W,P,L,J,F,S,j,g,target,nt,ready,branch,cone,seq,
    leg,image,fixed,member,names,unions,Y,q,cofinal,join⟩ := bundle
  have map := cone.elementary o j c X₀ R₀ leg root model
  have iw := (numbers.omega_image_mem_l I hZF hw ext model target nt map).1
  obtain ⟨Y',_,iY⟩ := map.1.1.2.2 Y₀ (space.bounds_l I).2.1
  obtain ⟨F',_,iF⟩ := map.1.1.2.2 F₀ (space.bounds_l I).2.2
  obtain ⟨N',W',K',model',source⟩ := ready.mem_l hZF ⟨N,W,target,nt⟩
  obtain ⟨eqN,eqW⟩ := smdl_unique_l I model'.1 target.1
  subst N' W'
  have algebra := source.algebra_l (ZF.modelsKP hZF)
  obtain ⟨targetSpace,targetTree⟩ := Smap_d.tree_space_l hZF hw model target nt map
    algebra.pair algebra.union iw iY iF image space closed
  have full := cofinal.branch_l hZF hw targetSpace targetTree
  exact ⟨d,N,W,P,L,J,F,S,j,g,target,nt,ready,branch,cone,seq,leg,image,fixed,member,names,unions,
    Y,q,Y',F',cofinal,join,iY,iF,targetSpace,targetTree,full.1,full.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系运行在指定良基枝上的实际原局投影

每个有限实数像都属于原对局，因此其并图也包含于原对局。两者定义域同为内部ω，
函数性将包含升级为相等；另两张并图和原来的完整合成分支即为投影见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_archive_full_tree_d.projection_l
    {ω c o C₀ S₀ γ Bγ A X K r a f H X₀ R₀ b Y₀ F₀ : M.Domain} {U : Fin 6 → M.Domain}
    (full : Tg_archive_full_tree_d hZF ω o S₀ Bγ (U 5) (U 0) (U 1) (U 2) b Y₀ F₀)
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    (u : Tg_iteration_union_d hZF ω c γ H U)
    (root : Zc_model_d I ω c X₀ R₀) (letters : M.mem A Bγ) (input : Fn0_d ω A f)
    (played : Tg_archive_play_native_d I ω (U 5) H f) :
    ∃ d N W P j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P ∧ Rd_entry_d o j P ∧
      Rd_entry_d Y₀ Y' j ∧ Rd_entry_d F₀ F' j ∧ Rd_entry_d S₀ S' j ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' f := by
  obtain ⟨d,N,W,P,L,J,F,S,j,g,target,nt,ready,branch,cone,seq,leg,image,fixed,_,_,unions,
    _,q,Y',F',_,join,iY,iF,space,tree,fq,bq⟩ := full
  have sub : M.MemberSubset (g 0) f := by
    intro p hp
    obtain ⟨i,s,v,hs,code,hp⟩ := ((unions 0).2.1 p).mp hp
    obtain ⟨k,m,_,trace⟩ := seq.images i s v hs code
    have row := seq.rows i s v hs code
    exact h.archive_real_l hZF u root letters input played cone.toIt_embedding_d target nt leg fixed
      trace row.1 row.2.2.1 p hp
  have fg := fn0_function_l (ZF.modelsKP hZF) (unions 0).1
  have ff := fn0_function_l (ZF.modelsKP hZF) input
  have front i x (ix : Rd_entry_d i x (g 0)) : Rd_entry_d i x f :=
    ix.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  have eq : g 0 = f := fg.1.1.eq_of_pairMember_iff hZF.1 ff.1.1 (fun i x =>
    ⟨front i x,fun ix => by
      obtain ⟨y,_,iy⟩ := (unions 0).1.2.1 i (input.bound_l ix).1
      exact ff.1.2 i y x (front i y iy) ix ▸ iy⟩)
  have graph a : Tg_graph_d I ω (g a) :=
    ⟨(fn0_function_l (ZF.modelsKP hZF) (unions a).1).1,(fn0_function_l (ZF.modelsKP hZF) (unions a).1).2.1⟩
  exact ⟨d,N,W,P,j,Y',F',S,target,ready,cone,leg,iY,iF,image,space,tree,
    q,g 1,g 2,fq,bq,graph 1,graph 2,eq ▸ join⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 服从实际策略的原对局与内部状态逐轮一致

偶数位置读取给定输入，奇数位置通过同一响应表和有限前缀因果性读取策略。
内部归纳证明每个状态中的背景原局就是给定对局的精确限制；同一次运行随后给出ω长原并树、
完整工作复制历史、nice工作树和偶数枝的实际不良基极限。任意指定良基枝都有实际原档案组成的继续尾段，
并在该枝自身的极限中识别原根树名、固定根低层。有限空间和树真值沿根腿搬运后，
三张完整并图给出同一个原对局的实际投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_iteration_choice_d.play_l {ω c o C₀ S₀ γ Bγ A r X D K a F σ f H : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (sf : Fn0_d F A σ)
    (values : ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_iteration_response_d hZF ω X K r a s y)
    (ff : Fn0_d ω A f) (follows : Gm_follows_d I false ω σ f)
    (run : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H) :
    ∀ n u q, Rd_entry_d n u H → Rt_coord_d (28 : Fin 75) u q → M.IsRestrictionOf I q f n := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  have fn := fn0_function_l (ZF.modelsKP hZF) ff
  have read {n u q} (nu : Rd_entry_d n u H) (play : Rt_coord_d (28 : Fin 75) u q) : Fn0_d n A q := by
    obtain ⟨k,num,fn⟩ := (run.rows n u nu).1.play_l hZF play
    exact num.unique_l (run.rows n u nu).2 ▸ fn
  let ρ : Env M 2 := ⟨fun i => [H,f].get i,fun _ => H⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ u q,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,u,⌜(.bound 1 : Term 3)⌝ₛ) →
    ⌜(rt_coord_m (28 : Fin 75))⌝ₚ(u,q) →
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(q,⌜(.bound 2 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ u q, Rd_entry_d n u H → Rt_coord_d (28 : Fin 75) u q →
      M.IsRestrictionOf I q f n := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Formula.satisfies_isRestriction_iff I,
      Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ u q, Rd_entry_d n u H → Rt_coord_d (28 : Fin 75) u q →
      M.IsRestrictionOf I q f n := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz u q nu play
      have fq := read nu play
      exact ⟨(fn0_function_l (ZF.modelsKP hZF) fq).1.1,fun i y =>
        ⟨fun hi => (hz i (fq.bound_l hi).1).elim,fun hi => (hz i hi.1).elim⟩⟩
    · intro n hn ih m succ t q mt play
      obtain ⟨u,_,nu⟩ := run.recursion.1.2.1 n hn
      have state := run.rows n u nu
      obtain ⟨x,p,input,pair,pt⟩ := run.recursion.2.2 n m u t succ nu mt
      have edge := (h.step u x t p state.1 pair pt).2
      obtain ⟨_,s,q',y,_,old,new,_,ends,last,even⟩ := edge.last_l hZF state.1 state.2
      have qq := new.unique_l play
      subst q'
      have cut := ih u s nu old
      have fs := fn0_function_l (ZF.modelsKP hZF) (read nu old)
      obtain ⟨z,_,nz⟩ := ff.2.1 n hn
      have yz : y = z := by
        rcases Classical.em (Gm_even_d I ω n) with he | he
        · exact (even he).trans (input.elim (fun hx => fn.1.2 n x z hx.2 nz)
            (fun hx => (hx.1 ⟨he,z,nz⟩).elim))
        · have xa : x = a := input.elim (fun hx => (he hx.1).elim) And.right
          obtain ⟨G,grun⟩ := h.run_l hZF zero empty ha fs.1 (fun _ _ hi => fs.output_mem_of_pairMember hi)
          obtain ⟨u',_,nu'⟩ := grun.recursion.1.2.1 n hn
          have uu := run.recursion.prefix_l hZF hw (fn0_function_l (ZF.modelsKP hZF) h.function).1
            fn.1 grun.recursion hn cut u u' nu nu'
          have response : Tg_iteration_response_d hZF ω X K r a s y :=
            ⟨n,G,u,p,t,q,fs.2.1,grun.recursion,uu.symm ▸ nu',xa ▸ pair,pt,play,last⟩
          have sy := (values s y).mpr ⟨(space s).mpr ⟨n,hn,fs⟩,response⟩
          exact (fn0_function_l (ZF.modelsKP hZF) sf).1.2 s y z sy (follows n hn he s cut z nz)
      have fq := fn0_function_l (ZF.modelsKP hZF) (read mt play)
      apply (ds_restrict_iff_l I fq fn.1).mpr
      intro p hp
      obtain ⟨i,v,pair⟩ := fq.1.1 p hp
      have iv : Rd_entry_d i v q := ⟨p,pair,hp⟩
      have entry : Rd_entry_d i v f := by
        rcases (succ i).mp (fq.input_mem_of_pairMember iv) with hi | eq
        · obtain ⟨l,k,d⟩ := ends
          have kn := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
          exact ((cut.2 i v).mp ((d.prefix_restriction.2 i v).mpr ⟨kn.symm ▸ hi,iv⟩)).2
        · have eq := hZF.1.eq_of_same_members i n eq
          subst i
          exact (fq.1.2 n v y iv last).symm ▸ yz.symm ▸ nz
      obtain ⟨p',pair',hp'⟩ := entry
      exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  exact fun n u q nu play => all n (run.recursion.1.bound_l nu).1 u q nu play

theorem Tg_iteration_choice_d.strategy_run_l {ω c o C₀ S₀ γ Bγ A r X D K a F : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) : ∃ σ, Fn0_d F A σ ∧
      (∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_iteration_response_d hZF ω X K r a s y) ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d I false ω σ f → ∃ H U W B,
        Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H ∧
        Tg_iteration_union_d hZF ω c γ H U ∧
        Tg_iteration_copy_d hZF ω c o H U W ∧
        It_ill_branch_d hZF ω ω (U 0) (U 1) (U 2) B ∧
        (∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x) ∧
        (∀ b, It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b →
          Tg_odd_cofinal_d ω b (U 5) ∧ Tg_archive_tail_d I (U 5) (U 0) (U 2) B b ∧
          Tg_archive_union_d hZF ω o S₀ Bγ (U 5) (U 0) (U 1) (U 2) b) ∧
        Tg_archive_play_native_d I ω (U 5) H f ∧
        ∀ n u q, Rd_entry_d n u H → Rt_coord_d (28 : Fin 75) u q → M.IsRestrictionOf I q f n := by
  obtain ⟨σ,sf,values⟩ := h.strategy_l hZF zero empty ha space
  refine ⟨σ,sf,values,fun f ff follows => ?_⟩
  obtain ⟨H,run⟩ := h.run_l hZF zero empty ha (fn0_function_l (ZF.modelsKP hZF) ff).1 (fun _ _ hi => (ff.bound_l hi).2)
  obtain ⟨U,tree⟩ := run.union_l hZF
  obtain ⟨W,copy⟩ := run.copy_l hZF tree empty
  obtain ⟨B,ill,valuesB⟩ := run.even_limit_l hZF tree
  have play := h.play_l hZF zero empty ha space sf values ff follows run
  refine ⟨H,U,W,B,run,tree,copy,ill,valuesB,?_,run.archive_play_l hZF tree play,play⟩
  intro b wf
  have odd := run.odd_tail_l hZF tree ill.1 valuesB wf.1
    (fun eq => run.even_illfounded_l hZF tree valuesB (eq ▸ wf))
  exact ⟨odd.1,odd.2,run.branch_union_l hZF tree odd.2 wf⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 原策略在每条指定良基枝自己的极限中给出同一原对局的实际根树像投影。 -/
theorem Tg_iteration_d.strategy_l {ω c X₀ R₀ w₀ z₀ o C₀ S₀ γ Bγ A a F : M.Domain}
    {v : Fin 29 → M.Domain} {u : Fin 46 → M.Domain}
    (root : Zc_model_d J ω c X₀ R₀) (numbers : Rr_layer_d J ω X₀ R₀ w₀ z₀)
    (initial : Tg_iteration_d hZ ω c o C₀ S₀ γ Bγ A v u) (zero : v 27 = o)
    (empty : ∀ z, ¬ M.mem z o) (letters : M.mem A Bγ) (ha : M.mem a A)
    (space : Fseq_space_d J ω A F) : ∃ r X D K σ,
      Tg_iteration_choice_d hZ ω c o C₀ S₀ γ Bγ A r X D K ∧
      Rt_tuple_d (Fin.addCases (m := 29) (n := 46) (motive := fun _ => M.Domain) v u) r ∧ Fn0_d F A σ ∧
      (∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_iteration_response_d hZ ω X K r a s y) ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d J false ω σ f → ∃ H U W B,
        Tg_iteration_run_d hZ ω c o C₀ S₀ γ Bγ A X K r a f H ∧
        Tg_iteration_union_d hZ ω c γ H U ∧
        Tg_iteration_copy_d hZ ω c o H U W ∧
        It_ill_branch_d hZ ω ω (U 0) (U 1) (U 2) B ∧
        (∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 75) H (U 0) x) ∧
        (∀ b, It_wf_branch_d hZ ω ω (U 0) (U 1) (U 2) b →
          Tg_odd_cofinal_d ω b (U 5) ∧ Tg_archive_tail_d J (U 5) (U 0) (U 2) B b ∧
          Tg_archive_union_d hZ ω o S₀ Bγ (U 5) (U 0) (U 1) (U 2) b ∧
          ∀ Y₀ F₀, Sc_fseq_d J w₀ Y₀ F₀ X₀ R₀ →
            Rr_truth_d J X₀ R₀ (tree_m (.bound 1) .newest) (Fin.cases S₀ (fun _ : Fin 1 => F₀)) →
            ∃ d N W P j Y' F' S', Smem_d J d N W ∧ It_source_d hZ ω d ∧
              It_cone_d (kp_pair_l (ZF.modelsKP hZ)) ω b (U 1) (U 2) d N W P ∧ Rd_entry_d o j P ∧
              Rd_entry_d Y₀ Y' j ∧ Rd_entry_d F₀ F' j ∧ Rd_entry_d S₀ S' j ∧
              Fseq_space_d J ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZ ω Y' F' S' f) ∧
        Tg_archive_play_native_d J ω (U 5) H f ∧
        ∀ n u q, Rd_entry_d n u H → Rt_coord_d (28 : Fin 75) u q → M.IsRestrictionOf J q f n := by
  obtain ⟨r,X,D,K,code,choice⟩ := initial.choice_l hZFC root numbers letters
  have index : Rt_coord_d (27 : Fin 75) r o := ⟨_,code,
    (Fin.addCases_left (m := 29) (n := 46) (motive := fun _ => M.Domain) (left := v) (right := u) 27).trans zero⟩
  obtain ⟨σ,sf,values,runs⟩ := choice.strategy_run_l hZ index empty ha space
  refine ⟨r,X,D,K,σ,choice,code,sf,values,?_⟩
  intro f ff follows
  obtain ⟨H,U,W,B,run,union,copy,ill,even,branches,archive,play⟩ := runs f ff follows
  refine ⟨H,U,W,B,run,union,copy,ill,even,?_,archive,play⟩
  intro b wf
  obtain ⟨odd,tail,bundle⟩ := branches b wf
  exact ⟨odd,tail,bundle,fun _ _ finite closed =>
    (bundle.tree_l hZ run union root.model numbers finite closed).projection_l hZ run union root letters ff archive⟩

end YesMetaZFC.SetTheory.LargeCardinal
