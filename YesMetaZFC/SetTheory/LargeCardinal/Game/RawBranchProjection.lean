import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeEntry
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.ImageValue
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveSequence
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.TreeImage

/-! # 每份原档案在同一晚阶段读回原对局字母

每次比较先合并档案所在阶段与给定指标的后继阶段。档案中的共同图和
根交换方块成对读回；实际控制事件把短图的值识别为当前根图的字母像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 同一原请求的两份短图通过实际历史事件识别字母。 -/
theorem Tg_raw_request_d.play_value_l (hKP : M.Models KP)
    {Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ X R w η C χ z k D r q A f s i n x y : M.Domain}
    {frame : Tg_raw_archive_frame_d M.Domain} {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ X R w η C χ z k D r q frame v)
    (ext : Rf_ext_d I X R)
    (prior : Tg_prefix_d I k A X R C (v 4) (v 3) (v 20) z q f)
    (play : Tg_play_d I X R C (v 4) (v 3) (v 20) s)
    (point : M.PairMember I i n z) (value : Rf_val_d I X R n x s)
    (actual : Rd_entry_d i y f) : M.PairMember I y x q := by
  let nx : ∃ a, M.mem a X := ⟨w,request.context.omega_mem⟩
  have en := ext.native_l I nx
  obtain ⟨nc,ρ,eq,issued,_⟩ := request.read_l I hKP en
  obtain ⟨fn,t,played,graph⟩ := prior
  obtain ⟨n',x',point',image,val⟩ := (graph i y (fn.bound_l actual).1 (fn.bound_l actual).2).mp actual
  have same : n' = n := request.numbers.injection.1.1.2 i n' n point' point
  subst n'
  have fs := request.context.finite_l nx en
  let J := rt_pair_l fs.transitive nc en fs.pair
  have same : x = x' := Tg_play_d.native_entry_eq_l I nx en ⟨C,request.context.member⟩ fs.transitive nc J ρ issued
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ play)
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ played) value val
  exact same.symm ▸ image

def Tg_raw_archive_play_d (ω D₀ D H f : M.Domain) : Prop :=
  ∀ m r, ∀ row : Tg_raw_archive_row_d M.Domain, Rd_entry_d m r D → Rt_tuple_d row.values_d r →
    ∀ w : Fin 54 → M.Domain, Tg_saved_code_d row.X row.R row.w row.U row.q w →
    ∀ i, M.mem i ω → ∃ k t, ∃ v : Fin 66 → M.Domain, ∃ l V Γ g s,
      Rd_entry_d k t H ∧ Rt_tuple_d v t ∧ M.mem i k ∧ Rd_entry_d m r (v 13) ∧
      Ic_common_d I row.X row.R (v 0) (v 1) row.L l row.U V Γ g ∧
      Tg_root_square_d D₀ row.p (v 16) g ∧
      Rd_entry_d (w 40) s g ∧ Tg_play_d I (v 0) (v 1) (v 5) (v 24) (v 23) (v 40) s ∧
      ∀ n x y, Rd_entry_d i n (v 3) → Rf_val_d I (v 0) (v 1) n x s →
        Rd_entry_d i y f → Rd_entry_d y x (v 16)

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 原档案视图和根方块从同一完整条目读取，不重新选择共同图。 -/
theorem Tg_raw_iteration_d.archive_value_l
    {Ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A m r : M.Domain}
    {v : Fin 20 → M.Domain} {a : Fin 46 → M.Domain}
    (state : Tg_raw_iteration_d hZF Ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A v a)
    (row : Tg_raw_archive_row_d M.Domain) (entry : Rd_entry_d m r (v 13))
    (tuple : Rt_tuple_d row.values_d r) {w : Fin 54 → M.Domain}
    (code : Tg_saved_code_d row.X row.R row.w row.U row.q w) :
    ∃ l V Γ g s,
      Ic_common_d Kp row.X row.R (v 0) (v 1) row.L l row.U V Γ g ∧
      Tg_root_square_d D₀ row.p (v 16) g ∧
      Rd_entry_d (w 40) s g ∧ Tg_play_d Kp (v 0) (v 1) (v 5) (a 4) (a 3) (a 20) s ∧
      ∀ i n x y, Rd_entry_d i n (v 3) → Rf_val_d Kp (v 0) (v 1) n x s →
        Rd_entry_d i y (v 19) → Rd_entry_d y x (v 16) := by
  obtain ⟨X',R',_,_,_,model,source,_⟩ := (state.tree.sources (v 7) (v 15) state.node).objects
  obtain ⟨eqX,eqR⟩ := smdl_unique_l Kp model state.model
  subst X' R'
  obtain ⟨_,_,_,_,_,_,l,V,Γ,g,common,_,roots,view⟩ := (state.request.views m r entry).read_l Kp tuple
  obtain ⟨w',pack,_,_,_,_,_,_,_,_,_,s,image,play⟩ := view
  have eq : w' 40 = w 40 := congrFun (pack.inj_l Kp hZF.1 code) 42
  exact ⟨l,V,Γ,g,s,common,roots,eq ▸ image,play,
    fun _ _ _ _ point value actual => state.request.play_value_l Kp (ZF.modelsKP hZF)
      source.ext state.play play point value actual⟩

/-- 指标的后继阶段与档案阶段实际合并，保证所选短图可比较该原字母。 -/
theorem Tg_raw_iteration_run_d.archive_play_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (played : ∀ n t q, Rd_entry_d n t H → Rt_coord_d (19 : Fin 66) t q → M.IsRestrictionOf Kp q f n) :
    Tg_raw_archive_play_d Kp ω D₀ (U 5) H f := by
  intro m r row entry tuple w code i hi
  obtain ⟨p,pair,hp⟩ := entry
  obtain ⟨v,k,t,ht,pack,hp⟩ := (u.columns 5 p).mp hp
  obtain ⟨j,succ,hj⟩ := u.tree.omega.1.2 i hi
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 j hj
  obtain ⟨v',pack',_⟩ := (h.rows j s hs).1
  obtain ⟨k',t',v'',ht',pack'',keep,keep'⟩ := (h.frames_l hZF).merge k j t s v v' ht hs pack pack'
  have current := h.read_l hZF v'' ht' pack''
  have prior := h.read_l hZF v' hs pack'
  have index : v' 18 = j := (h.rows j s hs).2.read_l v' pack'
  have index' : v'' 18 = k' := (h.rows k' t' ht').2.read_l v'' pack''
  obtain ⟨q,z,zp,hz⟩ := (prior.request.sequence.2.2 i).mp (index.symm ▸ succ.predecessor_mem)
  have ik : M.mem i k' := index' ▸ (current.request.sequence.2.2 i).mpr
    ⟨q,z,zp,keep'.2.2.1 5 z hz⟩
  have old : Rd_entry_d m r (v'' 13) := ⟨p,pair,keep.2.2.1 5 p hp⟩
  obtain ⟨l,V,Γ,g,s',common,roots,image,play,values⟩ := current.archive_value_l hZF row old tuple code
  have cut := played k' t' (v'' 19) ht' ⟨v'',pack'',rfl⟩
  exact ⟨k',t',v'',l,V,Γ,g,s',ht',pack'',ik,old,common,roots,image,play,
    fun n x y point value iy => values i n x y point value ((cut.2 i y).mpr ⟨ik,iy⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原档案第一图是原对局沿根腿逐字母搬运所得的有限图

目标求值先回拉到同一原档案，再沿已选共同图进入足够晚的真实历史。
根切片只保证实际字母处的交换，单射性把字母读回原档案；最后由同锥
交换得到根腿的字母像，不把原对局对象或原字母假定为字面固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定所选共同图上的实际原生求值，在当前请求中保留同一背景数字。 -/
theorem Tg_raw_iteration_d.archive_transport_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A m r l V Γ g q s z i n x : M.Domain}
    {v : Fin 20 → M.Domain} {a : Fin 46 → M.Domain}
    (state : Tg_raw_iteration_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A v a)
    (root : Zc_model_d I ω c X₀ R₀) (row : Tg_raw_archive_row_d M.Domain)
    (entry : Rd_entry_d m r (v 13)) (tuple : Rt_tuple_d row.values_d r)
    (common : Ic_common_d I row.X row.R (v 0) (v 1) row.L l row.U V Γ g)
    (short : Rd_entry_d q s g) (numbers : Rr_layer_d I ω row.X row.R row.w z)
    (point : Rd_entry_d i n z) (value : Rf_val_d I row.X row.R n x q) :
    ∃ n' x', Rd_entry_d i n' (v 3) ∧ Rd_entry_d n n' g ∧ Rd_entry_d x x' g ∧
      Rf_val_d I (v 0) (v 1) n' x' s := by
  obtain ⟨model,saved,_⟩ := (state.request.views m r entry).read_l I tuple
  have links := state.request.links m r row entry tuple
  have left := state.tree.diagram.elementary o row.i row.p c X₀ R₀ row.c row.X row.R
    links.2.2.1 state.root_node links.2.1 root.model model
  have right := state.tree.diagram.elementary o (v 7) (v 16) c X₀ R₀ (v 15) (v 0) (v 1)
    state.request.origin state.root_node state.node root.model state.model
  have source := root.map_l hZF state.tree.omega model left
  have target := root.map_l hZF state.tree.omega state.model right
  have hX := ZF.modelsKP (ZFC.models_zf_l (source.native_l I hZF state.tree.omega))
  let N := smdl_structure_l I (R := row.R) model.2.1
  let P := smdl_structure_l I (R := v 1) state.model.2.1
  let U : N.Domain := ⟨row.U,common.left_rank.2.1⟩
  let L : N.Domain := ⟨row.L,common.left_rank.1⟩
  have trans := v_transitive_l (kp_pair_l hX) ((rr_rank_native_l I model.2.1 hX L U).mp common.left_rank)
  -- 原语言把 ω 放在已保存的常量池中，该池属于共同层；无需比较任意根秩层。
  obtain ⟨nc,ρ,_,round,hw,_,pool,_,_⟩ := saved.read_l I hZF.1
  have fs := saved.context.finite_l model.2.1 hX.1
  have parts := tg_round_parts_l hX fs nc ρ round
  have domain := ((Formula.satisfies_conj_iff ..).mp parts.language).1
  simp only [ee_domain_pack_m,Formula.satisfies_bind,ee_domain_pack0_m,Formula.satisfies_conj_iff] at domain
  have omegaPool : N.mem (ρ.bound 16).val (ρ.bound 13).val :=
    (Formula.satisfies_mem_iff ..).mp domain.1
  have omegaU : Rd_entry_d row.w row.U row.R :=
    hw ▸ trans (ρ.bound 13).val pool (ρ.bound 16).val omegaPool
  let sn : N.Domain := ⟨q,(value.bounds_l I).2.2⟩
  let ni : N.Domain := ⟨n,(value.bounds_l I).1⟩
  let xi : N.Domain := ⟨x,(value.bounds_l I).2.1⟩
  have old := (rf_val_native_l I model.2.1 hX.1 ni xi sn).mp value
  have member : N.mem sn U := ((common.carrier q).mp (common.injection.1.input_mem_of_pairMember short)).2
  have bounds := rd_entry_transitive_l trans member old
  have pick (a : N.Domain) (ha : N.mem a U) : ∃ b : P.Domain, Rd_entry_d a.val b.val g := by
    obtain ⟨b,hb,image⟩ := common.injection.1.2.2 a.val ((common.carrier a.val).mpr ⟨a.property,ha⟩)
    exact ⟨⟨b,hb⟩,image⟩
  obtain ⟨ni',in'⟩ := pick ni bounds.1
  obtain ⟨xi',ix'⟩ := pick xi bounds.2
  let sn' : P.Domain := ⟨s,common.injection.1.output_mem_of_pairMember short⟩
  have move := rr_graph_delta_l I model.2.1 state.model.2.1
    ⟨q,common.injection.1.input_mem_of_pairMember short⟩
    (fun y hy => ((common.carrier y).mp hy).1)
    (fun y t hy ht ty => (common.carrier t).mpr ⟨ht,
      trans ⟨y,((common.carrier y).mp hy).1⟩ ((common.carrier y).mp hy).2 ⟨t,ht⟩ ty⟩)
    common.injection common.pred
    (rd_entry0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    (⟨fun k => [ni,xi,sn].get k,fun _ => sn⟩ : Env N 3)
    (⟨fun k => [ni',xi',sn'].get k,fun _ => sn'⟩ : Env P 3)
    (Fin.cases in' (Fin.cases ix' (Fin.cases short (fun k => Fin.elim0 k))))
  have ey := target.ext.native_l I state.model.2.1
  have moved : Rd_entry_d ni' xi' sn' := (rd_entry0_sat_l ey ..).mp (move.mp ((rd_entry0_sat_l hX.1 ..).mpr old))
  -- 此处仅对背景内部 ω 的完整数字图使用层搬运，不识别任意原根切片。
  have graph := (common.layer_image_l (ZF.modelsKP hZF) model.2.1 target.ext
    numbers state.request.numbers trans omegaU).2
  exact ⟨ni'.val,xi'.val,(graph i ni'.val).mpr ⟨n,point,in'⟩,in',ix',
    (rf_val_native_l I state.model.2.1 ey ni' xi' sn').mpr moved⟩

/-- 任一真实有限档案像的取值，都来自原对局同指标字母在同一根腿下的像。 -/
theorem Tg_raw_iteration_run_d.archive_real_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A X K r a f H b d N W P j₀ m k : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (root : Zc_model_d I ω c X₀ R₀) (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (input : Fn0_d ω A f)
    (played : ∀ n t q, Rd_entry_d n t H → Rt_coord_d (19 : Fin 66) t q → M.IsRestrictionOf I q f n)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N) (rootLeg : Rd_entry_d o j₀ P)
    {v : Fin 5 → M.Domain} (trace : Tg_raw_archive_image_d (U 5) P m k v)
    (finite : M.mem (v 0) ω) (graph : Tg_graph_d I (v 0) (v 2)) :
    ∀ i y, Rd_entry_d i y (v 2) → ∃ x, Rd_entry_d i x f ∧ Rd_entry_d x y j₀ := by
  obtain ⟨r,row,entry,tuple,index,w,code,j,leg,images⟩ := trace
  have leg : Rd_entry_d row.i j P := index.symm ▸ leg
  obtain ⟨node,model,saved,⟨z,numbers⟩,_,_,_,edge,_⟩ := h.archive_read_l hZF u row entry tuple
  have map := cone.elementary row.i j row.c row.X row.R leg node model
  have natural := numbers.omega_image_mem_l I hZF u.tree.omega saved.ext model target nt map
  have late := h.archive_play_l hZF u played
  have hRoot := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF u.tree.omega))
  have alphabetD : M.mem A₀ D₀ := (cut.carrier A₀).mpr ⟨(cut.model.2.2.2 A₀ B₀ cut.alphabet).1,cut.alphabet⟩
  intro i y value
  have hi := u.tree.omega.transitive (ZF.modelsKP hZF) _ finite i ((graph.2 i).mpr ⟨y,value⟩)
  obtain ⟨n,_,point⟩ := numbers.injection.1.2.2 i hi
  obtain ⟨x,raw,image⟩ := Smap_d.value_preimage_l hZF u.tree.omega model target nt map saved.ext
    (natural.2 i n point) (images 2) graph.1 value
  obtain ⟨l,t,ρ,l',V,Γ,g,s,ht,pack,_,old,common,roots,short,_,values⟩ := late m r row entry tuple w code i hi
  have state := h.read_l hZF ρ ht pack
  obtain ⟨n',x',point',_,ix',value'⟩ := state.archive_transport_l hZF root row old tuple common short numbers point raw
  obtain ⟨a,ha,ia⟩ := input.2.1 i hi
  have current : Rd_entry_d a x' (ρ 16) := values n' x' a point' value' ia
  have low : M.mem a D₀ := cut.down_l hZF hRoot A₀ a alphabetD ((cut.letters a).mp ha).2
  have links := state.request.links m r row old tuple
  have left := state.tree.diagram.elementary o row.i row.p c X₀ R₀ row.c row.X row.R
    links.2.2.1 state.root_node links.2.1 root.model model
  obtain ⟨a',_,source⟩ := left.1.1.2.2 a ((cut.letters a).mp ha).1
  have same : a' = x := common.injection.2 a' x x' ((roots a low a' source x').mpr current) ix'
  have source : Rd_entry_d a x row.p := same ▸ source
  exact ⟨a,ia,cone.commute o row.i row.p j₀ j edge rootLeg leg a x y source image⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一良基锥中的原根树名

每份十一项档案保存原根边及树名。锥交换把全部五坐标像的树坐标
识别为同一个根腿的像；实际节点列的一行已经供应该根腿。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

theorem Tg_raw_iteration_run_d.archive_tree_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {b d N W P j₀ m i : M.Domain} {v : Fin 5 → M.Domain}
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (root : Rd_entry_d o j₀ P) (trace : Tg_raw_archive_image_d (U 5) P m i v) :
    Rd_entry_d S₀ (v 1) j₀ := by
  obtain ⟨r,row,entry,tuple,index,w,code,j,leg,images⟩ := trace
  obtain ⟨_,_,_,_,name,_,_,edge,_⟩ := h.archive_read_l hZF u row entry tuple
  have leg : Rd_entry_d row.i j P := index.symm ▸ leg
  exact cone.commute o row.i row.p j₀ j edge root leg S₀ (w 19) (v 1) (name w code) (images 1)

/-- 由真实列的一行取得根腿，继而识别同锥全部档案的树名。 -/
theorem Tg_raw_iteration_run_d.archive_sequence_tree_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {b d N W P L J F : M.Domain} (branch : It_branch_d ω (U 0) b)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (seq : Tg_raw_archive_sequence_d I ω N (U 5) P b L J F) :
    ∃ j₀ S, Rd_entry_d o j₀ P ∧ M.mem S N ∧ Rd_entry_d S₀ S j₀ ∧
      ∀ m i (v : Fin 5 → M.Domain), Tg_raw_archive_image_d (U 5) P m i v → v 1 = S := by
  obtain ⟨e,_,he⟩ := seq.omega.1.1
  obtain ⟨s,_,hs⟩ := seq.function.2.1 e he
  obtain ⟨v,code⟩ := seq.codes e s hs
  obtain ⟨i,m,_,trace⟩ := seq.images e s v hs code
  have trace₀ := trace
  obtain ⟨r,row,entry,tuple,index,w,pack,j,leg,images⟩ := trace
  obtain ⟨_,_,_,_,_,_,_,edge,_⟩ := h.archive_read_l hZF u row entry tuple
  have hi : M.mem row.i b := index.symm ▸ (cone.domain i).mpr ⟨j,leg⟩
  have ho := branch.down o row.i (u.tree.diagram.map_bound_l hZF edge) hi
  obtain ⟨j₀,root⟩ := (cone.domain o).mp ho
  obtain ⟨c',X',R',node,model⟩ := u.tree.diagram.model_l hZF (branch.subset o ho)
  have image := h.archive_tree_l hZF u cone root trace₀
  have elementary := cone.elementary o j₀ c' X' R' root node model
  refine ⟨j₀,v 1,root,(seq.rows e s v hs code).2.1 1,image,?_⟩
  intro m i w trace
  exact elementary.1.1.1.2 S₀ (w 1) (v 1) (h.archive_tree_l hZF u cone root trace) image

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意良基原枝中的同次三图并

指定分支自身的良基极限供应目标及锥。原档案尾段在同一锥中成为实际
有限节点列，三图的并合成为原根树像的共尾分支；第一坐标先保留其原像身份。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_raw_archive_union_d (ω o S₀ D T Q G b : M.Domain) : Prop :=
  ∃ d N W P L J F S j, ∃ g : Fin 3 → M.Domain,
    Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧ It_branch_d ω T b ∧
    It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Tg_raw_archive_sequence_d I ω N D P b L J F ∧
    Rd_entry_d o j P ∧ Rd_entry_d S₀ S j ∧ M.mem S N ∧
    (∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → v 1 = S) ∧
    (∀ a, Tg_return_union_d hZF ω N F a (g a)) ∧
    ∃ Y q, Tg_cofinal_branch_d hZF ω Y S q ∧ Tg_join_d I ω (g 0) (g 1) (g 2) q

/-- 不预设奇数尾段；任意原良基枝直接生产同一个根树像中的三图合成。 -/
theorem Tg_raw_iteration_run_d.branch_union_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H b : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b) :
    Tg_raw_archive_union_d hZF ω o S₀ (U 5) (U 0) (U 1) (U 2) b := by
  obtain ⟨B,_,_,tail⟩ := h.wf_tail_l hZF u wf
  obtain ⟨β,T',Q',G',ext⟩ := it_wf_branch_extend_l hZF u.tree
    (u.tree.omega.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_,_,_,_,_,_,d,N,W,P,_,_,_,model,nt,cone,nodes,_⟩ := ext.limit
  have source := ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl,rfl⟩))
  obtain ⟨L,J,F,seq⟩ := h.archive_sequence_l hZF u wf.1 tail cone.toIt_embedding_d model nt
  obtain ⟨j,S,root,hS,image,names⟩ := h.archive_sequence_tree_l hZF u wf.1 cone.toIt_embedding_d seq
  have name i r (v : Fin 5 → M.Domain) (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) : v 1 = S := by
    obtain ⟨k,m,_,trace⟩ := seq.images i r v hr code
    exact names m k v trace
  obtain ⟨g₀,union₀⟩ := seq.toTg_node_sequence_d.union_l hZF 0
  obtain ⟨g₁,union₁⟩ := seq.toTg_node_sequence_d.union_l hZF 1
  obtain ⟨g₂,union₂⟩ := seq.toTg_node_sequence_d.union_l hZF 2
  let g : Fin 3 → M.Domain := fun i => [g₀,g₁,g₂].get i
  have unions : ∀ a, Tg_return_union_d hZF ω N F a (g a) :=
    Fin.cases union₀ (Fin.cases union₁ (Fin.cases union₂ (fun i => Fin.elim0 i)))
  obtain ⟨Y,q,cofinal,join⟩ := seq.toTg_node_sequence_d.branch_join_l hZF name unions
  exact ⟨d,N,W,P,L,J,F,S,j,g,model,nt,source,wf.1,cone,seq,root,image,hS,name,unions,Y,q,cofinal,join⟩

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
def Tg_raw_archive_full_tree_d (ω o S₀ D T Q G b Y₀ F₀ : M.Domain) : Prop :=
  ∃ d N W P L J F S j, ∃ g : Fin 3 → M.Domain,
    Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧ It_branch_d ω T b ∧
    It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Tg_raw_archive_sequence_d I ω N D P b L J F ∧
    Rd_entry_d o j P ∧ Rd_entry_d S₀ S j ∧
    M.mem S N ∧
    (∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → v 1 = S) ∧
    (∀ a, Tg_return_union_d hZF ω N F a (g a)) ∧
    ∃ Y q Y' F', Tg_cofinal_branch_d hZF ω Y S q ∧ Tg_join_d I ω (g 0) (g 1) (g 2) q ∧
      Rd_entry_d Y₀ Y' j ∧ Rd_entry_d F₀ F' j ∧ Fseq_space_d I ω Y' F' ∧ Tree_d F' S ∧
      Fn0_d ω Y' q ∧ Branch_d F' S q

theorem Tg_raw_archive_union_d.tree_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H b w z Y₀ F₀ : M.Domain} {U : Fin 6 → M.Domain}
    (bundle : Tg_raw_archive_union_d hZF ω o S₀ (U 5) (U 0) (U 1) (U 2) b)
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U) (model : Smdl_d I c X₀ R₀)
    (numbers : Rr_layer_d I ω X₀ R₀ w z) (space : Sc_fseq_d I w Y₀ F₀ X₀ R₀)
    (closed : Rr_truth_d I X₀ R₀ (tree_m (.bound 1) .newest) (Fin.cases S₀ (fun _ : Fin 1 => F₀))) :
    Tg_raw_archive_full_tree_d hZF ω o S₀ (U 5) (U 0) (U 1) (U 2) b Y₀ F₀ := by
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
    leg,image,member,names,unions,Y,q,cofinal,join⟩ := bundle
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
  exact ⟨d,N,W,P,L,J,F,S,j,g,target,nt,ready,branch,cone,seq,leg,image,member,names,unions,
    Y,q,Y',F',cofinal,join,iY,iF,targetSpace,targetTree,full.1,full.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意原良基枝中的字母推送投影

同一档案并图的第一坐标逐点等于原对局经过根腿后的字母像。完整内部
ω 定义域和两张实际函数图将这一方向升级为精确复合；另外两张并图及
合成分支保持不变。一般原模型不要求根腿字面固定字母。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_archive_full_tree_d.projection_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A X K r a f H b Y₀ F₀ : M.Domain}
    {U : Fin 6 → M.Domain}
    (full : Tg_raw_archive_full_tree_d hZF ω o S₀ (U 5) (U 0) (U 1) (U 2) b Y₀ F₀)
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (root : Zc_model_d I ω c X₀ R₀)
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A) (input : Fn0_d ω A f)
    (played : ∀ n s q, Rd_entry_d n s H → Rt_coord_d (19 : Fin 66) s q → M.IsRestrictionOf I q f n) :
    ∃ d N W P j Y' F' S' f', Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P ∧ Rd_entry_d o j P ∧
      Smap_d I ω c d X₀ N j ∧ Rd_entry_d Y₀ Y' j ∧ Rd_entry_d F₀ F' j ∧ Rd_entry_d S₀ S' j ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ It_comp_d f j f' ∧ Tg_projection_d hZF ω Y' F' S' f' := by
  obtain ⟨d,N,W,P,L,J,F,S,j,g,target,nt,ready,branch,cone,seq,leg,image,member,names,unions,
    Y,q,Y',F',cofinal,join,iY,iF,space,tree,fq,bq⟩ := full
  obtain ⟨e,_,he⟩ := u.tree.omega.1.1
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 e he
  obtain ⟨v,code,state⟩ := (h.rows e s hs).1
  have node : Rd_entry_d o c (U 1) := by
    obtain ⟨p,pair,hp⟩ := state.root_node
    exact ⟨p,pair,(u.columns 1 p).mpr ⟨v,e,s,hs,code,hp⟩⟩
  have map := cone.elementary o j c X₀ R₀ leg node root.model
  have front i y (value : Rd_entry_d i y (g 0)) : ∃ x, Rd_entry_d i x f ∧ Rd_entry_d x y j := by
    obtain ⟨p,pair,hp⟩ := value
    obtain ⟨n,s,v,hs,code,hp⟩ := ((unions 0).2.1 p).mp hp
    obtain ⟨k,m,_,trace⟩ := seq.images n s v hs code
    have row := seq.rows n s v hs code
    exact h.archive_real_l hZF u root cut input played cone.toIt_embedding_d target nt leg
      trace row.1 row.2.2.1 i y ⟨p,pair,hp⟩
  have fg := fn0_function_l (ZF.modelsKP hZF) (unions 0).1
  have ff := fn0_function_l (ZF.modelsKP hZF) input
  have composition : It_comp_d f j (g 0) := by
    refine ⟨fg.1.1,fun i y => ⟨front i y,?_⟩⟩
    rintro ⟨x,ix,xy⟩
    obtain ⟨z,_,iz⟩ := (unions 0).1.2.1 i (input.bound_l ix).1
    obtain ⟨x',ix',xz⟩ := front i z iz
    have same := ff.1.2 i x' x ix' ix
    have eq := map.1.1.1.2 x z y (same ▸ xz) xy
    exact eq ▸ iz
  have graph a : Tg_graph_d I ω (g a) :=
    ⟨(fn0_function_l (ZF.modelsKP hZF) (unions a).1).1,
      (fn0_function_l (ZF.modelsKP hZF) (unions a).1).2.1⟩
  exact ⟨d,N,W,P,j,Y',F',S,g 0,target,nt,ready,cone,leg,map,iY,iF,image,space,tree,composition,
    q,g 1,g 2,fq,bq,graph 1,graph 2,join⟩

/-- 指定任意良基枝后才构造该枝自己的目标；输入对局已由同表策略逐轮实现。 -/
theorem Tg_raw_iteration_run_d.wf_projection_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A X K r a f H b z Y₀ F₀ : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (root : Zc_model_d I ω c X₀ R₀)
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (numbers : Rr_layer_d I ω X₀ R₀ w₀ z) (space : Sc_fseq_d I w₀ Y₀ F₀ X₀ R₀)
    (closed : Rr_truth_d I X₀ R₀ (tree_m (.bound 1) .newest) (Fin.cases S₀ (fun _ : Fin 1 => F₀)))
    (input : Fn0_d ω A f)
    (played : ∀ n s q, Rd_entry_d n s H → Rt_coord_d (19 : Fin 66) s q → M.IsRestrictionOf I q f n)
    (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b) :
    ∃ d N W P j Y' F' S' f', Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P ∧ Rd_entry_d o j P ∧
      Smap_d I ω c d X₀ N j ∧ Rd_entry_d Y₀ Y' j ∧ Rd_entry_d F₀ F' j ∧ Rd_entry_d S₀ S' j ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ It_comp_d f j f' ∧ Tg_projection_d hZF ω Y' F' S' f' := by
  have bundle := h.branch_union_l hZF u wf
  have full := bundle.tree_l hZF h u root.model numbers space closed
  exact full.projection_l hZF h u root cut input played

end YesMetaZFC.SetTheory.LargeCardinal
