import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveEdge
import YesMetaZFC.SetTheory.LargeCardinal.Game.RestartLinkSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Padding
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameStage
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection

/-! # 同一锥目标中的原继续边

五个原边像沿新锥腿进入目标，再由交换律和旧锥腿的函数性识别为旧节点坐标。
完整继续方程因此给出相同的树、长度后继、三图包含和恢复图的精确单点追加。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两端目标向量均按长度、树、实数图、标签图、恢复图排列。 -/
theorem Tg_raw_archive_step_d.image_l {ω d N W j p q : M.Domain}
    {s t : Tg_raw_archive_row_d M.Domain} {v w : Fin 54 → M.Domain}
    (step : Tg_raw_archive_step_d I s t j) (hw : M.IsOmega ω)
    (model : Smdl_d I t.c t.X t.R) (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (edge : M.IsSetFunctionFromTo I j s.X t.X) (left : M.IsSetFunction I p)
    (right : Smap_d I ω t.c d t.X N q)
    (square : ∀ x y z, Rd_entry_d x y j → Rd_entry_d y z q → Rd_entry_d x z p)
    (cv : Tg_saved_code_d s.X s.R s.w s.U s.q v)
    (cw : Tg_saved_code_d t.X t.R t.w t.U t.q w)
    (a b : Fin 5 → M.Domain)
    (ia : ∀ i, Rd_entry_d (v ([22,19,40,41,42].get i)) (a i) p)
    (ib : ∀ i, Rd_entry_d (w ([22,19,40,41,42].get i)) (b i) q) :
    a 1 = b 1 ∧ M.SuccessorOf (b 0) (a 0) ∧
    (∀ i : Fin 3, M.MemberSubset (a ([2,3,4].get i)) (b ([2,3,4].get i))) ∧
    ∃ x, Rd_entry_d (a 0) x (b 4) ∧ ∀ r, M.mem r (b 4) ↔ M.mem r (a 4) ∨ KPair_d M r (a 0) x := by
  obtain ⟨v',w',cv',cw',u,images,link⟩ := step
  have ev : v' = v := funext fun i => congrFun (cv'.inj_l I hZF.1 cv) i.succ.succ
  subst v'
  have ew : w' = w := funext fun i => congrFun (cw'.inj_l I hZF.1 cw) i.succ.succ
  subst w'
  let a' : Fin 5 → M.Domain := fun i => [a 1,a 0,a 2,a 3,a 4].get i
  have old : ∀ i, Rd_entry_d (v ([19,22,40,41,42].get i)) (a' i) p :=
    Fin.cases (ia 1) (Fin.cases (ia 0) (Fin.cases (ia 2) (Fin.cases (ia 3)
      (Fin.cases (ia 4) (fun i => Fin.elim0 i)))))
  have moved i : Rd_entry_d (u i) (a' i) q := by
    obtain ⟨y,_,hy⟩ := right.1.1.2.2 (u i) (edge.output_mem_of_pairMember (images i))
    have eq := left.2 _ y (a' i) (square _ _ _ (images i) hy) (old i)
    exact eq ▸ hy
  obtain ⟨name,succ,real,labels,x,entry,graph⟩ :=
    link.image_l hZF hw model target nt right a' b moved ib
  have recovery : M.MemberSubset (a 4) (b 4) := fun r hr => (graph r).mpr (Or.inl hr)
  exact ⟨name,succ,Fin.cases real (Fin.cases labels (Fin.cases recovery (fun i => Fin.elim0 i))),x,entry,graph⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原档案索引与真实新增节点的严格次序

第m份档案的节点就是第m轮开始时的原树长。较早档案已经进入较晚轮的实际有限档案，
故其节点严格较小；同一树节点因此只能对应同一档案索引及同一行码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

theorem Tg_raw_iteration_run_d.archive_stage_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {m p s : M.Domain} (row : Tg_raw_archive_row_d M.Domain) (v : Fin 66 → M.Domain)
    (entry : Rd_entry_d m p (U 5)) (tuple : Rt_tuple_d row.values_d p)
    (hs : Rd_entry_d m s H) (code : Rt_tuple_d v s) : row.i = v 6 := by
  have hm := (u.archive.2.2 m).mpr ⟨p,entry⟩
  obtain ⟨j,succ,hj⟩ := u.tree.omega.1.2 m hm
  obtain ⟨t,_,ht⟩ := h.recursion.1.2.1 j hj
  obtain ⟨_,_,v',w,ps,pt,next⟩ := h.steps m j s t succ hs ht
  have eq := rt_tuple_inj_l ps code
  subst v'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,new,q,index,pack,_,entries⟩ := next
  have added : Rd_entry_d (v 18) q (w 13) := (entries (v 18) q).mpr (Or.inr ⟨rfl,rfl⟩)
  have number : v 18 = m := (h.rows m s hs).2.read_l v code
  have global : Rd_entry_d m q (U 5) := by
    obtain ⟨b,pair,hb⟩ := added
    exact number ▸ (show Rd_entry_d (v 18) q (U 5) from ⟨b,pair,(u.columns 5 b).mpr ⟨w,j,t,ht,pt,hb⟩⟩)
  have eq := u.archive.2.1.2 m q p global entry
  subst q
  have eq := Tg_raw_archive_row_d.eq_l (rt_tuple_inj_l pack tuple)
  subst new
  exact index

theorem Tg_raw_iteration_run_d.archive_order_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {m n p q : M.Domain} (left right : Tg_raw_archive_row_d M.Domain)
    (hp : Rd_entry_d m p (U 5)) (hq : Rd_entry_d n q (U 5))
    (cp : Rt_tuple_d left.values_d p) (cq : Rt_tuple_d right.values_d q) (mn : M.mem m n) : M.mem left.i right.i := by
  have hn := (u.archive.2.2 n).mpr ⟨q,hq⟩
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 n hn
  obtain ⟨v,code,state⟩ := (h.rows n s hs).1
  have number : v 18 = n := (h.rows n s hs).2.read_l v code
  obtain ⟨p',entry⟩ := (state.request.sequence.2.2 m).mp (number.symm ▸ mn)
  have global : Rd_entry_d m p' (U 5) := by
    obtain ⟨b,pair,hb⟩ := entry
    exact ⟨b,pair,(u.columns 5 b).mpr ⟨v,n,s,hs,code,hb⟩⟩
  have eq := u.archive.2.1.2 m p' p global hp
  subst p'
  have links := state.request.links m p left entry cp
  have bound : M.mem left.i (v 6) := (state.successor left.i).mpr (Or.inl links.1)
  exact (h.archive_stage_l hZF u right v hq cq hs code).symm ▸ bound

/-- 同一原节点唯一确定原档案索引和完整外部行码。 -/
theorem Tg_raw_iteration_run_d.archive_unique_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {m n p q : M.Domain} (left right : Tg_raw_archive_row_d M.Domain)
    (hp : Rd_entry_d m p (U 5)) (hq : Rd_entry_d n q (U 5))
    (cp : Rt_tuple_d left.values_d p) (cq : Rt_tuple_d right.values_d q) (eq : left.i = right.i) : m = n ∧ p = q := by
  have hm := (u.archive.2.2 m).mpr ⟨p,hp⟩
  have hn := (u.archive.2.2 n).mpr ⟨q,hq⟩
  rcases (u.tree.omega.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm n hn with same | mn | nm
  · have same := hZF.1.eq_of_same_members m n same
    subst n
    exact ⟨rfl,u.archive.2.1.2 m p q hp hq⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) right.i (eq ▸ h.archive_order_l hZF u left right hp hq cp cq mn)).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) left.i (eq.symm ▸ h.archive_order_l hZF u right left hq hp cq cp nm)).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原档案五坐标像的完整一阶公式

一次量化十一项原行、五十四项原存档、行码及锥腿。公式保留原档案索引、
节点、完整存档与五个实际像，供背景替换收集指定分支中的真实节点列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_raw_archive_image_m {d} (D P m i : Term d) (v : Fin 5 → Term d) : Formula 1 d :=
  let e : Term d → Term (67+d) := fun t => t.rename (Fin.natAdd 67)
  let s : Fin 11 → Term (67+d) := fun k => .bound ((k.castAdd 56).castAdd d)
  let w : Fin 54 → Term (67+d) := fun k => .bound ((Fin.natAdd 11 (k.castAdd 2)).castAdd d)
  let r : Term (67+d) := .bound ((65 : Fin 67).castAdd d)
  let j : Term (67+d) := .bound ((66 : Fin 67).castAdd d)
  rb_exists_m (n := 67) (.conj (rd_entry0_m (e m) r (e D))
    (.conj (rt_tuple_m s r) (.conj (Formula.extensionalEq (s 0) (e i))
      (.conj (tg_saved_code_m (s 2) (s 3) (s 4) (s 8) (s 9) w)
        (.conj (rd_entry0_m (e i) j (e P))
          (rb_conj_m (fun a : Fin 5 => rd_entry0_m (w ([22,19,40,41,42].get a)) (e (v a)) j)))))))

@[simp] theorem tg_raw_archive_image_closed_l {d} (D P m i : Term d) (v : Fin 5 → Term d)
    (hD : D.freeSupport = []) (hP : P.freeSupport = []) (hm : m.freeSupport = [])
    (hi : i.freeSupport = []) (hv : ∀ a, (v a).freeSupport = []) : (tg_raw_archive_image_m D P m i v).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_archive_image_m,Definitional.Formula.FreeClosed,hD,hP,hm,hi,hv]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_raw_archive_image_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (D P m i : Term d) (v : Fin 5 → Term d) :
    Formula.satisfies ρ (tg_raw_archive_image_m D P m i v) ↔
      Tg_raw_archive_image_d (D.eval ρ) (P.eval ρ) (m.eval ρ) (i.eval ρ) (fun a => (v a).eval ρ) := by
  simp only [tg_raw_archive_image_m,rb_exists_sat_l,Formula.satisfies_conj_iff,rd_entry0_sat_l hE,
    rt_tuple_sat_l hE,Formula.satisfies_extensionalEq_iff_eq hE,tg_saved_code_sat_l,rb_conj_sat_l,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨u,entry,pack,index,code,leg,images⟩
    refine ⟨u 65,Tg_raw_archive_row_d.from_values_d (fun k => u (k.castAdd 56)),entry,?_,index,
      (fun k => u (Fin.natAdd 11 (k.castAdd 2))),code,u 66,leg,images⟩
    simpa only [Tg_raw_archive_row_d.values_from_l] using pack
  · rintro ⟨r,row,entry,pack,index,w,code,j,leg,images⟩
    let tail : Fin 56 → M.Domain := Fin.addCases (m := 54) (n := 2) (motive := fun _ => M.Domain)
      w (fun k : Fin 2 => [r,j].get k)
    let u : Fin 67 → M.Domain := Fin.addCases (m := 11) (n := 56) (motive := fun _ => M.Domain) row.values_d tail
    have rs : (fun k : Fin 11 => u (k.castAdd 56)) = row.values_d :=
      funext (fun k => Fin.addCases_left (m := 11) (n := 56) (motive := fun _ => M.Domain)
        (left := row.values_d) (right := tail) k)
    have ws : (fun k : Fin 54 => u (Fin.natAdd 11 (k.castAdd 2))) = w := by
      funext k
      simp only [u,tail,Fin.addCases_right,Fin.addCases_left]
    refine ⟨u,entry,?_,index,?_,leg,?_⟩
    · exact Eq.mpr (congrArg (fun v => Rt_tuple_d v r) rs) pack
    · rw [ws]
      exact code
    · exact Eq.mpr (congrArg (fun w => ∀ a : Fin 5,
        Rd_entry_d (w ([22,19,40,41,42].get a)) ((v a).eval ρ) j) ws) images

def Tg_raw_archive_row_image_d (D P i r : M.Domain) : Prop := ∃ m, ∃ v : Fin 5 → M.Domain,
  Tg_raw_archive_image_d D P m i v ∧ Rt_tuple_d v r

def tg_raw_archive_row_image_m {d} (D P i r : Term d) : Formula 1 d := .existsE (
  let e : Term (d+1) → Term (5+(d+1)) := fun t => t.rename (Fin.natAdd 5)
  let v : Fin 5 → Term (5+(d+1)) := fun k => .bound (k.castAdd (d+1))
  rb_exists_m (n := 5) (.conj (tg_raw_archive_image_m (e D.weaken) (e P.weaken) (e .newest) (e i.weaken) v)
    (rt_tuple_m v (e r.weaken))))

@[simp] theorem tg_raw_archive_row_image_closed_l {d} (D P i r : Term d)
    (hD : D.freeSupport = []) (hP : P.freeSupport = []) (hi : i.freeSupport = []) (hr : r.freeSupport = []) :
    (tg_raw_archive_row_image_m D P i r).FreeClosed := by
  simp -implicitDefEqProofs [tg_raw_archive_row_image_m,Definitional.Formula.FreeClosed,hD,hP,hi]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr)

theorem tg_raw_archive_row_image_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D P i r : Term d) :
    Formula.satisfies ρ (tg_raw_archive_row_image_m D P i r) ↔
      Tg_raw_archive_row_image_d (D.eval ρ) (P.eval ρ) (i.eval ρ) (r.eval ρ) := by
  simp only [tg_raw_archive_row_image_m,Tg_raw_archive_row_image_d,Formula.satisfies_exists_iff,
    rb_exists_sat_l,Formula.satisfies_conj_iff,tg_raw_archive_image_sat_l hE,rt_tuple_sat_l hE,
    rb_old_eval_l,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound,Fin.addCases_left]

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一指定分支中的唯一档案像及实际增长

原档案的严格节点次序消去不同档案索引；五坐标像随后由同一锥腿唯一确定。
原继续边的增长直接使用实际模型列和锥交换方块，不另要求调用者提供中间像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

/-- 同一树节点的两个原档案像必相同，即使其展示索引尚未识别。 -/
theorem Tg_raw_iteration_run_d.archive_image_unique_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {b d N W P m n i : M.Domain} {v w : Fin 5 → M.Domain}
    (branch : It_branch_d ω (U 0) b) (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (hv : Tg_raw_archive_image_d (U 5) P m i v) (hw : Tg_raw_archive_image_d (U 5) P n i w) : v = w := by
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
  exact (Tg_raw_archive_image_d.unique_l I hZF.1 u.archive.2.1.2 cone.function.2 legs hv₀ hw₀).2

/-- 实际两端档案及同一原继续边自动给出目标中的完整增长方程。 -/
theorem Tg_raw_iteration_run_d.archive_growth_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {b d N W P m n p q j : M.Domain} {v w : Fin 5 → M.Domain}
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (old row : Tg_raw_archive_row_d M.Domain)
    (old_entry : Rd_entry_d m p (U 5)) (new_entry : Rd_entry_d n q (U 5))
    (old_tuple : Rt_tuple_d old.values_d p) (new_tuple : Rt_tuple_d row.values_d q)
    (edge : It_map_d (U 2) old.i row.i j) (step : Tg_raw_archive_step_d I old row j)
    (hv : Tg_raw_archive_image_d (U 5) P m old.i v) (hw : Tg_raw_archive_image_d (U 5) P n row.i w) :
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
variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

theorem Tg_raw_iteration_run_d.even_branch_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U) :
    ∃ B, It_branch_d ω (U 0) B ∧ ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 66) H (U 0) x :=
  (h.frames_l hZF).even_branch_l hZF u.tree u.columns
    (fun _ _ v hs code => (h.read_l hZF v hs code).successor)

theorem Tg_raw_iteration_run_d.node_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {i s} (v : Fin 66 → M.Domain) (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
    Rd_entry_d (v 7) (v 15) (U 1) := by
  obtain ⟨p,pair,hp⟩ := (h.read_l hZF v hs code).node
  exact ⟨p,pair,(u.columns 1 p).mpr ⟨v,i,s,hs,code,hp⟩⟩

theorem Tg_raw_iteration_run_d.limit_values_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {B d N W P : M.Domain} (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 66) H (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B (U 1) (U 2) d N W P) (b : Fin 46) :
    ∃ F, Fn0_d ω N F ∧ ∀ i x, Rd_entry_d i x F ↔ Tg_limit_value_d (7 : Fin 66) (Fin.natAdd 20 b) H P i x := by
  apply cone.record_values_l hZF (7 : Fin 66) (Fin.natAdd 20 b) h.recursion.1
  · intro i s hs
    obtain ⟨v,code,_⟩ := (h.rows i s hs).1
    exact ⟨v,code⟩
  · intro i s v hs code
    have state := h.read_l hZF v hs code
    exact ⟨v 15,v 0,v 1,h.node_l hZF u v hs code,state.model,
      state.request.values.elim (fun bounds _ => bounds b.succ),
      (branch _).mpr ⟨v,i,s,hs,code,u.tree.diagram.order.refl _ state.finite⟩⟩

theorem Tg_raw_iteration_run_d.control_const_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {B d N W P : M.Domain} (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 66) H (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B (U 1) (U 2) d N W P) (b : Fin 19) :
    ∃ z, M.mem z N ∧ ∀ i x, Tg_limit_value_d (7 : Fin 66) (Fin.natAdd 20 (b.castAdd 27)) H P i x → x = z := by
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
variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

theorem Tg_raw_iteration_run_d.even_illfounded_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U) {B : M.Domain}
    (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 66) H (U 0) x) :
    ¬ It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) B := by
  intro wf
  have hw := u.tree.omega
  obtain ⟨β,T',Q',G',ext⟩ := it_wf_branch_extend_l hZF u.tree (hw.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_,_,_,_,_,_,d,N,W,P,_,_,_,target,nt,cone,nodes,_⟩ := ext.limit
  obtain ⟨N',W',K,target',source⟩ :=
    (ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl,rfl⟩))).mem_l hZF ⟨N,W,target,nt⟩
  obtain ⟨eqN,eqW⟩ := smdl_unique_l I target'.1 target.1
  subst N' W'
  have elem {i s j} {v : Fin 66 → M.Domain} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s)
      (hj : Rd_entry_d (v 7) j P) := cone.elementary (v 7) j (v 15) (v 0) (v 1) hj
        (h.node_l hZF u v hs code) (h.read_l hZF v hs code).model
  have raw_ext {i s} (v : Fin 66 → M.Domain) (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
      Rf_ext_d I (v 0) (v 1) := by
    obtain ⟨Y,S,_,_,_,model,source,_⟩ := (u.tree.sources (v 7) (v 15) (h.node_l hZF u v hs code)).objects
    obtain ⟨eqY,eqS⟩ := smdl_unique_l I model (h.read_l hZF v hs code).model
    subst Y S
    exact source.ext
  obtain ⟨R,_,same⟩ := h.control_const_l hZF u branch cone.toIt_embedding_d 18
  obtain ⟨F,ff,fs⟩ := h.limit_values_l hZF u branch cone.toIt_embedding_d 20
  have position i x (hx : Tg_limit_value_d (7 : Fin 66) (40 : Fin 66) H P i x) : M.mem x R := by
    obtain ⟨v,s,j,hs,code,hj,hx⟩ := hx
    have state := h.read_l hZF v hs code
    have rext := (raw_ext v hs code).native_l I ⟨v 2,state.request.context.omega_mem⟩
    have finite := state.request.context.finite_l ⟨v 2,state.request.context.omega_mem⟩ rext
    obtain ⟨nc,ρ,points,valid,_⟩ := state.request.read_l I (ZF.modelsKP hZF) rext
    have issued := (tg_issued_sat_l (rt_pair_l finite.transitive nc rext finite.pair)
      (rt_model_ext_l rext finite.transitive nc) ρ).mp valid
    have old : Rd_entry_d (v 40) (v 38) (v 1) := by
      have pos := issued.position
      change Rd_entry_d (ρ.bound 20).val.val (ρ.bound 18).val.val (v 1) at pos
      exact points 20 ▸ points 18 ▸ pos
    obtain ⟨r,_,hr⟩ := (elem hs code hj).1.1.2.2 (v 38)
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
      let ξ : Env V 2 := ⟨fun i => Fin.cases ⟨w 40,leg.1.1.input_mem_of_pairMember hy⟩
        (fun _ => ⟨z,leg.1.1.input_mem_of_pairMember image⟩) i,fun _ => ⟨z,leg.1.1.input_mem_of_pairMember image⟩⟩
      let ψ : Formula 1 2 := Formula.subset (.bound 1) .newest
      have valid : Formula.satisfies ξ ψ := (Formula.satisfies_subset_iff ..).mpr
        (fun v hv => sub v.val hv)
      have raw := (rr_truth_native_l I wr.model.2.1 ψ (by simp -implicitDefEqProofs [ψ]) ξ.bound).mpr valid
      have moved : Rr_truth_d I N W ψ (Fin.cases y (fun _ : Fin 1 => x)) :=
        raw.map_l I hZF hw wr.model target.1 leg (by simp -implicitDefEqProofs [ψ])
        (Fin.cases hy (fun _ => image))
      exact (Formula.satisfies_subset_iff (⟨Fin.cases y (fun _ => x),fun _ => x⟩ : Env M 2) (.bound 1) .newest).mp
        ((rr_truth_mem_l I nt target ψ (.atom ..) (Fin.cases y (fun _ => x))).mp moved).2
    exact ⟨subset,fun eq => ne (leg.1.2 z (w 40) y (eq ▸ image) hy)⟩
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
theorem Tg_raw_iteration_run_d.even_limit_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U) : ∃ B,
    It_ill_branch_d hZF ω ω (U 0) (U 1) (U 2) B ∧
      ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 66) H (U 0) x := by
  obtain ⟨B,branch,values⟩ := h.even_branch_l hZF u
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨i,hi,_⟩ := branch.cofinal e he
  obtain ⟨L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model⟩ :=
    it_branch_data_l hZF u.tree.omega u.tree.diagram branch ⟨i,hi⟩
  exact ⟨B,⟨branch,L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model,
    fun wf => h.even_illfounded_l hZF u values
      ⟨branch,L,V,p,G,R,q,d,N,W,order,system,elementary,limit,model,wf⟩⟩,values⟩

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

def Tg_raw_iteration_odd_d (H D T G B y : M.Domain) : Prop :=
  ∃ n s, ∃ v : Fin 66 → M.Domain, Rd_entry_d n s H ∧ Rt_tuple_d v s ∧ y = v 6 ∧
    ∃ k, ∃ row : Tg_raw_archive_row_d M.Domain, ∃ r, row.i = y ∧ Rd_entry_d (v 18) r D ∧
      Rt_tuple_d row.values_d r ∧
      Tg_raw_iteration_parent_d hZF (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 20 i)) k G row ∧
      It_pred_d T k y ∧ M.mem (v 7) B

/-- 尾段保留完整两端原档案、严格较早的索引及同一继续边上的三图方程。 -/
def Tg_raw_archive_tail_d (J : kpair_convention_l.Interpretation M) (D T G B b : M.Domain) : Prop := ∃ z,
  M.mem z b ∧ ¬ M.mem z B ∧ Tg_odd_node_d D z ∧ ∀ y, M.mem y b → M.mem z y →
    ∃ m r, ∃ row : Tg_raw_archive_row_d M.Domain, Rd_entry_d m r D ∧ Rt_tuple_d row.values_d r ∧ row.i = y ∧
      ∃ l t, ∃ old : Tg_raw_archive_row_d M.Domain, ∃ j, M.mem l m ∧ Rd_entry_d l t D ∧ Rt_tuple_d old.values_d t ∧
        It_pred_d T old.i y ∧ M.mem old.i b ∧ ¬ M.mem old.i B ∧ (z = old.i ∨ M.mem z old.i) ∧
        It_map_d G old.i y j ∧ Tg_raw_archive_step_d J old row j

variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

theorem Tg_raw_iteration_run_d.late_odd_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {B e s₀ y : M.Domain} {v₀ : Fin 66 → M.Domain}
    (even : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 66) H (U 0) x) (empty : ∀ x, ¬ M.mem x e)
    (first : Rd_entry_d e s₀ H) (code₀ : Rt_tuple_d v₀ s₀) (hy : M.mem y ω)
    (outside : ¬ M.mem y (v₀ 6)) (not_even : ¬ M.mem y B) :
    Tg_odd_node_d (U 5) y ∧ Tg_raw_iteration_odd_d hZF H (U 5) (U 0) (U 2) B y := by
  obtain ⟨l,k,t,s,w,v,succ,ht,ct,hs,code,old,hyv⟩ :=
    (h.frames_l hZF).first_l hZF v₀ empty first code₀ hy outside
  obtain ⟨_,_,w',v',ct',code',next⟩ := h.steps l k t s succ ht hs
  have eq := rt_tuple_inj_l ct' ct
  subst w'
  have eq := rt_tuple_inj_l code' code
  subst v'
  obtain ⟨a,T,Q,G,E,j,mid,e₁,e₂,_,_,_,_,_,_,_,_,row,r,index,rc,parent,entries⟩ := next
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
      have parent : Tg_raw_iteration_parent_d hZF (fun i => w (i.castAdd 46))
          (fun i => w (Fin.natAdd 20 i)) a (U 2) row := by
        obtain ⟨j,edge,choice⟩ := parent
        exact ⟨j,lift edge,choice⟩
      have entry := inside 5 ((entries (w 18) r).mpr (Or.inr ⟨rfl,rfl⟩))
      have node : Tg_odd_node_d (U 5) (w 6) := by
        obtain ⟨tail,pair,_⟩ := rc
        have pair : KPair_d M r row.i tail := pair
        exact ⟨w 18,r,tail,entry,index ▸ pair⟩
      exact ⟨node,l,t,w,ht,ct,rfl,a,row,r,index,entry,rc,parent,pred,
        (even _).mpr ⟨w,l,t,ht,ct,u.tree.diagram.order.refl _ state.finite⟩⟩
  · have eq := hZF.1.eq_of_same_members y (v 7) eq
    exact (not_even ((even y).mpr ⟨v,k,s,hs,code,
      eq.symm ▸ u.tree.diagram.order.refl _ (h.read_l hZF v hs code).finite⟩)).elim

/-- 与偶数枝分离后，实际树前驱仍在同一尾段；重置被排除，留下完整继续边。 -/
theorem Tg_raw_iteration_run_d.odd_tail_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U) {B b : M.Domain}
    (even_branch : It_branch_d ω (U 0) B)
    (even : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 66) H (U 0) x)
    (branch : It_branch_d ω (U 0) b) (ne : b ≠ B) :
    Tg_odd_cofinal_d ω b (U 5) ∧ Tg_raw_archive_tail_d I (U 5) (U 0) (U 2) B b := by
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
      exact ⟨v 18,r,row,entry,rc,index,l,t,old,j,lt,old_entry,pack,
        eq.symm ▸ pred,eq.symm ▸ kb,eq.symm ▸ kn,eq.symm ▸ ze,eq.symm ▸ edge,step⟩

/-- 枝上的完整档案尾段自动共尾；有限初段由尾段起点本身覆盖。 -/
theorem Tg_raw_archive_tail_d.cofinal_l (hE : Extensional M)
    {J : kpair_convention_l.Interpretation M} {ω D T G B b : M.Domain}
    (tail : Tg_raw_archive_tail_d J D T G B b) (ordinal : M.IsOrdinal ω)
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

/-- 任意指定良基枝自动避开偶数枝，故拥有真实十一项档案及原三图的完整继续尾段。 -/
theorem Tg_raw_iteration_run_d.wf_tail_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {b : M.Domain} (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b) :
    ∃ B, It_ill_branch_d hZF ω ω (U 0) (U 1) (U 2) B ∧
      Tg_odd_cofinal_d ω b (U 5) ∧ Tg_raw_archive_tail_d I (U 5) (U 0) (U 2) B b := by
  obtain ⟨B,ill,even⟩ := h.even_limit_l hZF u
  have ne : b ≠ B := fun eq => h.even_illfounded_l hZF u even (eq ▸ wf)
  exact ⟨B,ill,h.odd_tail_l hZF u ill.1 even wf.1 ne⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定原奇数尾段的唯一目标节点列

实际相邻树节点列确定档案，档案与同一锥确定全部五个像。背景替换一次收集整列，
其每个相邻步骤保留同一树、长度后继、三图包含及恢复图精确追加。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_raw_archive_sequence_d (I : kpair_convention_l.Interpretation M)
    (ω N D P b L J F : M.Domain) : Prop extends Tg_node_sequence_d I ω N L F where
  indices : Fn0_d ω b J
  images : ∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    ∃ k m, Rd_entry_d i k J ∧ Tg_raw_archive_image_d D P m k v
  equations : ∀ i j r s (v w : Fin 5 → M.Domain), M.SuccessorOf j i →
    Rd_entry_d i r F → Rd_entry_d j s F → Rt_tuple_d v r → Rt_tuple_d w s →
      v 1 = w 1 ∧ ∃ x, Rd_entry_d (v 0) x (w 4) ∧
        ∀ p, M.mem p (w 4) ↔ M.mem p (v 4) ∨ KPair_d M p (v 0) x

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

theorem Tg_raw_iteration_run_d.archive_sequence_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {B b d N W P : M.Domain} (branch : It_branch_d ω (U 0) b)
    (tail : Tg_raw_archive_tail_d I (U 5) (U 0) (U 2) B b)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N) :
    ∃ L J F, Tg_raw_archive_sequence_d I ω N (U 5) P b L J F := by
  have hw := u.tree.omega
  have unique {m n i} {v w : Fin 5 → M.Domain}
      (hv : Tg_raw_archive_image_d (U 5) P m i v) (hw : Tg_raw_archive_image_d (U 5) P n i w) : v = w :=
    h.archive_image_unique_l hZF u branch cone hv hw
  have decoded m p (hp : Rd_entry_d m p (U 5)) : ∃ row : Tg_raw_archive_row_d M.Domain, Rt_tuple_d row.values_d p := by
    obtain ⟨q,pair,hq⟩ := hp
    obtain ⟨v,i,s,hs,code,hq⟩ := (u.columns 5 q).mp hq
    obtain ⟨row,pack,_⟩ := (h.read_l hZF v hs code).request.views m p ⟨q,pair,hq⟩
    exact ⟨row,pack⟩
  have data {m i} {v : Fin 5 → M.Domain} (trace : Tg_raw_archive_image_d (U 5) P m i v) :
      M.mem (v 0) ω ∧ (∀ a, M.mem (v a) N) ∧ Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4) := by
    have copy := trace
    obtain ⟨p,row,entry,tuple,index,_,_,j,leg,_⟩ := copy
    have hi := index.symm ▸ (cone.domain i).mpr ⟨j,leg⟩
    obtain ⟨w,finite,members,node,image⟩ := h.archive_images_l hZF u cone target nt row entry tuple hi
    have image : Tg_raw_archive_image_d (U 5) P m i w := index ▸ image
    exact (unique trace image).symm ▸ ⟨finite,members,node⟩
  obtain ⟨z,hz,_,hzOdd,late⟩ := tail
  obtain ⟨J,jf,_,adjacent,above⟩ := branch.successor_sequence_l hZF hw u.tree.diagram.order hz
  let ρ : Env M 3 := ⟨fun i => [U 5,P,J].get i,fun _ => ω⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ k,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,k,⌜(.bound 4 : Term 5)⌝ₛ) ∧
    ⌜tg_raw_archive_row_image_m⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ,⌜(.bound 3 : Term 5)⌝ₛ,k,⌜(.newest : Term 5)⌝ₛ)⟫ }
  have sat i r : φ.denote ρ i r ↔ ∃ k, Rd_entry_d i k J ∧ Tg_raw_archive_row_image_d (U 5) P k r := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,tg_raw_archive_row_image_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
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
      ∃ k m, Rd_entry_d i k J ∧ Tg_raw_archive_image_d (U 5) P m k v := by
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
