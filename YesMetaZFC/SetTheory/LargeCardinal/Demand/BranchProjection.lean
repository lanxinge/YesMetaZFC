import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchDepth
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Game.TreeImage
import YesMetaZFC.Model.SetTheory.Game.GraphUnion
import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchOdd
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RunPlay
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundReal
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.SetTheory.LargeCardinal.Game.ImageValue
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ProjectionSpace

/-! # 任意源行的枚举行沿实际奇枝永久保留

首个后继把源枚举行加入祖先表；以后每条原边运输旧表。直接嵌入与逐边运输
由同一原树的复合律和函数唯一性识别，覆盖目标模型中的实际值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_run_d.branch_table_l {g : Fin 10 → M.Domain} {X K r a f H : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {U : Fin 6 → M.Domain} (u : Td_union_d hZF g H U)
    {b r₀ A J F e p y : M.Domain} (branch : It_branch_d (g 0) (U 0) b)
    (base : Td_archive_row_d M.Domain) (tuple : Rt_tuple_d base.values_d r₀)
    (rows : Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b base.i r₀ A J F)
    (pair : KPair_d M p base.depth e) (enumerated : Rd_entry_d e y base.enumeration)
    {i s j z : M.Domain} (row : Td_archive_row_d M.Domain) (is : Rd_entry_d i s F) (pack : Rt_tuple_d row.values_d s)
    (map : It_map_d (U 2) base.i row.i j) (image : Rd_entry_d y z j) (strict : M.mem base.depth row.depth) :
    Rd_entry_d p z row.ancestors := by
  have hw := u.tree.omega
  obtain ⟨o,empty,ho⟩ := hw.1.1
  obtain ⟨_,_,_,baseMember,_,nodeBase,sourceBase⟩ := run.branch_read_l hZF u rows base (rows.first o empty) tuple
  have he := (sourceBase.enumeration.function.bound_l enumerated).1
  have hy := (sourceBase.enumeration.function.bound_l enumerated).2
  have decode i r (ir : Rd_entry_d i r F) : ∃ row : Td_archive_row_d M.Domain, Rt_tuple_d row.values_d r := by
    obtain ⟨_,_,m,entry,_⟩ := rows.records i r ir
    exact run.archive_decode_l hZF u entry
  let property (i : M.Domain) : Prop := ∀ r n d T,
    Rd_entry_d i r F → Rt_coord_d (62 : Fin 73) r n → Rt_coord_d (70 : Fin 73) r d → Rt_coord_d (71 : Fin 73) r T →
      (base.depth = d ∨ M.mem base.depth d) ∧ (d = base.depth → r = r₀) ∧
      ∀ j z, It_map_d (U 2) base.i n j → Rd_entry_d y z j → M.mem base.depth d → Rd_entry_d p z T
  let ρ : Env M 7 := ⟨fun i => [F,U 2,base.i,base.depth,p,y,r₀].get i,fun _ => F⟩
  let φ : UnarySchema 7 := { body := set[8] ⟪∀ r n d T,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 8)⌝ₛ,r,⌜(.bound 1 : Term 8)⌝ₛ) →
    ⌜(rt_coord_m (62 : Fin 73))⌝ₚ(r,n) → ⌜(rt_coord_m (70 : Fin 73))⌝ₚ(r,d) → ⌜(rt_coord_m (71 : Fin 73))⌝ₚ(r,T) →
    (⌜(.bound 4 : Term 8)⌝ₛ = d ∨ ⌜(.bound 4 : Term 8)⌝ₛ ∈ d) ∧
    (d = ⌜(.bound 4 : Term 8)⌝ₛ → r = ⌜(.bound 7 : Term 8)⌝ₛ) ∧
    (∀ j z, ⌜it_map_m⌝ₚ(⌜(.bound 2 : Term 8)⌝ₛ,⌜(.bound 3 : Term 8)⌝ₛ,n,j) →
      ⌜rd_entry0_m⌝ₚ(⌜(.bound 6 : Term 8)⌝ₛ,z,j) → ⌜(.bound 4 : Term 8)⌝ₛ ∈ d →
        ⌜rd_entry0_m⌝ₚ(⌜(.bound 5 : Term 8)⌝ₛ,z,T))⟫ }
  have sat i : φ.denote ρ i ↔ property i := by
    simp only [φ,UnarySchema.denote,property,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Formula.satisfies_conj_iff,Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_mem_iff,it_map_sat_l hZF.1,
      Definitional.Term.eval_weaken]
    rfl
  have all : ∀ i, M.mem i (g 0) → property i := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ (g 0)
      exact ⟨B,fun i => (bs i).trans (and_congr_right fun _ => sat i)⟩
    · intro e empty r n d T er cn cd ct
      have eq := (fn0_function_l (ZF.modelsKP hZF) rows.sequence).1.2 e r r₀ er (rows.first e empty)
      have depth : base.depth = d := cd.read_l base.values_d (eq.symm ▸ tuple)
      exact ⟨Or.inl depth,fun _ => eq,fun _ _ _ _ low =>
        (KP.mem_irrefl_d (ZF.modelsKP hZF) base.depth (depth.symm ▸ low)).elim⟩
    · intro i hi ih k succ r n d T kr cn cd ct
      obtain ⟨leftCode,_,il⟩ := rows.sequence.2.1 i hi
      obtain ⟨left,cl⟩ := decode i leftCode il
      obtain ⟨right,cr⟩ := decode k r kr
      have en : right.i = n := cn.read_l right.values_d cr
      have ed : right.depth = d := cd.read_l right.values_d cr
      have et : right.ancestors = T := ct.read_l right.values_d cr
      rw [← en,← ed,← et]
      have prior := ih leftCode left.i left.depth left.ancestors il
        ⟨left.values_d,cl,rfl⟩ ⟨left.values_d,cl,rfl⟩ ⟨left.values_d,cl,rfl⟩
      obtain ⟨step,edge,depth,table,_⟩ := rows.equations i k leftCode r left right succ il kr cl cr
      have lower : M.mem base.depth right.depth := (depth base.depth).mpr
        (prior.1.elim (fun eq => Or.inr (eq ▸ fun _ => Iff.rfl)) Or.inl)
      refine ⟨Or.inr lower,fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) base.depth (eq ▸ lower)).elim,?_⟩
      intro map z mapLeg yz _
      rcases prior.1 with eq | before
      · have same := prior.2.1 eq.symm
        have sameRow := Td_archive_row_d.eq_l (rt_tuple_inj_l cl (same.symm ▸ tuple))
        subst left
        have sameMap := u.tree.diagram.map_unique_l hZF edge mapLeg
        exact (table p z).mpr ⟨base.depth,e,y,pair,he,Or.inr ⟨rfl,enumerated⟩,sameMap.symm ▸ yz⟩
      · obtain ⟨_,_,leftIndex,leftMember,leftAbove,nodeLeft,sourceLeft⟩ := run.branch_read_l hZF u rows left il cl
        obtain ⟨_,_,_,_,_,nodeRight,sourceRight⟩ := run.branch_read_l hZF u rows right kr cr
        obtain ⟨oldMap,oldLeg⟩ := u.tree.diagram.map_l hZF
          (branch.forward_l u.tree.diagram.order baseMember leftMember leftAbove)
        have oldEmbed := u.tree.diagram.elementary base.i left.i oldMap base.c base.X base.R left.c left.X left.R
          oldLeg nodeBase nodeLeft sourceBase.model sourceLeft.model
        obtain ⟨x,hx,yx⟩ := oldEmbed.1.1.2.2 y hy
        have px := prior.2.2 oldMap x oldLeg yx before
        have stepEmbed := u.tree.diagram.elementary left.i right.i step left.c left.X left.R right.c right.X right.R
          edge nodeLeft nodeRight sourceLeft.model sourceRight.model
        obtain ⟨z',_,xz⟩ := stepEmbed.1.1.2.2 x hx
        have yz' := u.tree.diagram.comp base.i left.i right.i oldMap step map oldLeg edge mapLeg y x z' yx xz
        have embed := u.tree.diagram.elementary base.i right.i map base.c base.X base.R right.c right.X right.R
          mapLeg nodeBase nodeRight sourceBase.model sourceRight.model
        have eq := embed.1.1.1.2 y z' z yz' yz
        exact eq ▸ (table p z').mpr ⟨base.depth,e,x,pair,he,Or.inl ⟨before,px⟩,xz⟩
  exact (all i (rows.sequence.bound_l is).1 s row.i row.depth row.ancestors is
    ⟨row.values_d,pack,rfl⟩ ⟨row.values_d,pack,rfl⟩ ⟨row.values_d,pack,rfl⟩).2.2 j z map image strict

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## Neeman 7.8 (iii)：实际奇枝的内部深度覆盖

给定源深度 d 和枚举编号 e，实际奇枝到达 ⟨d,e⟩+1；该节点的祖先表
含有源字母的原树嵌入像，调度选择因此恰等于这个像。全部量词遍历模型
内部的 ω、完整字母域及实际原树枝，不使用额外的分支命中前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_depth_cover_d (Ω D T G : M.Domain) : Prop := ∀ b, It_branch_d Ω T b →
  ∀ m r, ∀ row : Td_archive_row_d M.Domain, Rd_entry_d m r D → Rt_tuple_d row.values_d r → M.mem row.i b →
    ∀ y, M.mem y row.X → Rd_entry_d y (row.v 47) row.R →
      ∃ n s, ∃ next : Td_archive_row_d M.Domain, ∃ j,
        Rd_entry_d n s D ∧ Rt_tuple_d next.values_d s ∧ M.mem m n ∧
        M.mem next.i b ∧ M.mem row.i next.i ∧ It_map_d G row.i next.i j ∧ Rd_entry_d y (next.v 49) j

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_run_d.cover_l {g : Fin 10 → M.Domain} {X K r a f H : M.Domain}
    (run : Td_run_d hZF g X K r a f H) {U : Fin 6 → M.Domain} (u : Td_union_d hZF g H U) :
    Td_depth_cover_d (g 0) (U 5) (U 0) (U 2) := by
  intro b branch m r₀ base entry tuple member y hy letter
  have hw := u.tree.omega
  have source := run.archive_source_l hZF u base entry tuple
  obtain ⟨e,he,enumerated⟩ := source.enumeration.onto y hy letter
  obtain ⟨A,J,F,rows⟩ := run.branch_rows_l hZF u branch base entry tuple member
  -- 任务由源深度与枚举编号确定；实际奇枝必到达其代码的下一深度。
  have hd := source.depth.natural
  obtain ⟨n,code⟩ := oc_pair_exists_l I hZF
    (hw.members_areOrdinals (ZF.modelsKP hZF) base.depth hd) (hw.members_areOrdinals (ZF.modelsKP hZF) e he)
  have hn := oc_pair_natural_l I hZF hw hd he code
  obtain ⟨d,succ,hd'⟩ := hw.1.2 n hn
  have lower : M.mem base.depth d := ordinal_down_l (ZF.modelsKP hZF)
    (hw.members_areOrdinals (ZF.modelsKP hZF) base.depth hd) (hw.members_areOrdinals (ZF.modelsKP hZF) d hd')
      (oc_pair_left_bound_l I hZF hw hd he code) succ.predecessor_mem
  obtain ⟨i,s,next,is,pack,depth⟩ := run.branch_depth_l hZF u base tuple rows hd' (Or.inr lower)
  obtain ⟨m',entry',index,member',above,nodeNext,sourceNext⟩ := run.branch_read_l hZF u rows next is pack
  have strict : M.mem base.depth next.depth := depth.symm ▸ lower
  have later : M.mem base.i next.i := by
    rcases above with eq | lt
    · have ep := (run.archive_unique_l hZF u base next entry entry' tuple pack eq).2
      have erow := Td_archive_row_d.eq_l (rt_tuple_inj_l tuple (ep.symm ▸ pack))
      have eqd := congrArg Td_archive_row_d.depth erow
      have impossible := strict
      rw [← eqd] at impossible
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) base.depth impossible).elim
    · exact lt
  -- 源字母沿同一原树嵌入运输，其像已由祖先表保持定理记录。
  obtain ⟨j,map⟩ := u.tree.diagram.map_l hZF
    (branch.forward_l u.tree.diagram.order member member' (Or.inr later))
  have embed := u.tree.diagram.elementary base.i next.i j base.c base.X base.R next.c next.X next.R
    map (run.archive_node_l hZF u base entry tuple) nodeNext source.model sourceNext.model
  obtain ⟨z,_,yz⟩ := embed.1.1.2.2 y hy
  obtain ⟨p,pair⟩ := (I).total base.depth e
  have value := run.branch_table_l hZF u branch base tuple rows pair enumerated next is pack map yz strict
  obtain ⟨D,_,table⟩ := sourceNext.depth.table
  -- 当前调度与已运输表项具有同一索引，函数唯一性给出精确命中。
  have chosen := sourceNext.chosen.hit_l hZF (fn0_function_l (ZF.modelsKP hZF) table).1
    hd he code (depth.symm ▸ succ) pair value
  exact ⟨m',s,next,j,entry',pack,run.archive_index_l hZF u base next entry entry' tuple pack later,
    member',later,map,chosen.symm ▸ yz⟩

theorem Td_run_d.bookkeeping_l {g : Fin 10 → M.Domain} {X K r a f H : M.Domain}
    (run : Td_run_d hZF g X K r a f H) :
    ∃ U : Fin 6 → M.Domain, Td_union_d hZF g H U ∧ Td_depth_cover_d (g 0) (U 5) (U 0) (U 2) := by
  obtain ⟨U,tree⟩ := run.union_l hZF
  exact ⟨U,tree,run.cover_l hZF tree⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一极限锥中的辅助图延长

原奇父边与两条锥腿交换，故父边搬来的旧坐标正是极限中的旧坐标。
延长及字母入图都是 Δ₀ 断言，可在传递极限中读为实际函数图的关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

/-- 同一实际档案行沿指定锥腿产生全部坐标像。 -/
theorem Td_run_d.archive_images_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P m p : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5))
    (code : Rt_tuple_d row.values_d p) (member : M.mem row.i b) :
    ∃ j, ∃ v : Fin 62 → M.Domain, Rd_entry_d row.i j P ∧ ∀ i, Rd_entry_d (row.v i) (v i) j := by
  have source := run.archive_source_l hZF u row entry code
  obtain ⟨j,leg⟩ := (cone.domain row.i).mp member
  have map := cone.elementary row.i j row.c row.X row.R leg (run.archive_node_l hZF u row entry code) source.model
  have total i : ∃ x, Rd_entry_d (row.v i) x j := by
    obtain ⟨x,_,hx⟩ := map.1.1.2.2 _ (source.round.1 i)
    exact ⟨x,hx⟩
  obtain ⟨v,points⟩ := Classical.axiomOfChoice total
  exact ⟨j,v,leg,points⟩

theorem Td_run_d.aux_growth_image_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P m n p q j l k : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (old row : Td_archive_row_d M.Domain)
    (oldEntry : Rd_entry_d m p (U 5)) (newEntry : Rd_entry_d n q (U 5))
    (oldCode : Rt_tuple_d old.values_d p) (newCode : Rt_tuple_d row.values_d q)
    (edge : It_map_d (U 2) old.i row.i j) (growth : Td_aux_growth_d I row.X row.R j old.v row.v)
    (left : Rd_entry_d old.i l P) (right : Rd_entry_d row.i k P)
    (v w : Fin 62 → M.Domain) (iv : ∀ i, Rd_entry_d (old.v i) (v i) l)
    (iw : ∀ i, Rd_entry_d (row.v i) (w i) k) :
    M.SuccessorOf (w 25) (v 25) ∧ M.MemberSubset (v 45) (w 45) ∧
      M.MemberSubset (v 46) (w 46) ∧ Rd_entry_d (v 25) (v 49) (w 45) := by
  have mo := (run.archive_source_l hZF u old oldEntry oldCode).model
  have mr := (run.archive_source_l hZF u row newEntry newCode).model
  have no := run.archive_node_l hZF u old oldEntry oldCode
  have nr := run.archive_node_l hZF u row newEntry newCode
  have between := u.tree.diagram.elementary old.i row.i j old.c old.X old.R row.c row.X row.R edge no nr mo mr
  have ml := cone.elementary old.i l old.c old.X old.R left no mo
  have mk := cone.elementary row.i k row.c row.X row.R right nr mr
  obtain ⟨q,points,raw⟩ := growth
  have image (i : Fin 4) : Rd_entry_d (q i) (v ([25,45,46,49].get i)) k := by
    obtain ⟨y,_,hy⟩ := mk.1.1.2.2 _ (between.1.1.output_mem_of_pairMember (points i))
    have eq := ml.1.1.1.2 _ _ _ (cone.commute old.i row.i j l k edge left right _ _ y (points i) hy)
      (iv ([25,45,46,49].get i))
    exact eq ▸ hy
  let t : Fin 7 → M.Domain := td_aux_growth_values_d (fun i => v ([25,45,46,49].get i)) w
  have images : ∀ i, Rd_entry_d (td_aux_growth_values_d q row.v i) (t i) k :=
    Fin.cases (image 0) (Fin.cases (image 1) (Fin.cases (image 2) (Fin.cases (image 3)
      (Fin.cases (iw 25) (Fin.cases (iw 45) (Fin.cases (iw 46) (fun i => Fin.elim0 i)))))))
  have moved := raw.map_l I hZF u.tree.omega mr target.1 mk td_aux_growth0_closed_l images
  have valid := ((rr_truth_mem_l I nt target td_aux_growth0_m td_aux_growth0_delta_l t).mp moved).2
  simp only [td_aux_growth0_m,Formula.satisfies_conj_iff,KP.succ0_sat_l hZF.1,
    Formula.satisfies_subset_iff,rd_entry0_sat_l hZF.1] at valid
  exact valid

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一奇枝锥中的最小辅助字母域

每行的树来自同一原根。初等运输保留最小字母域的全称定义，因此各行
字母域的极限像相等，包括不属于任一较早字母域像的新成员。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem td_round_alphabet_l (ext : Extensional M) (ρ : Env M 62)
    (valid : Formula.satisfies ρ td_round0_m) : Td_alphabet_d (ρ.bound 22) (ρ.bound 47) (ρ.bound 48) := by
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp valid).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,alphabet,_⟩ := seed
  exact (td_alphabet_sat_l ext (ρ.reindex (fun i => ⟨19+i.val,by omega⟩)) (.bound 3) (.bound 28) (.bound 29)).mp alphabet

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

/-- 最小字母域在传递目标中绝对；出现见证全部来自树中的实际有序对。 -/
theorem Td_run_d.archive_alphabet_mem_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P m p j : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5)) (code : Rt_tuple_d row.values_d p)
    (leg : Rd_entry_d row.i j P) (v : Fin 62 → M.Domain) (points : ∀ i, Rd_entry_d (row.v i) (v i) j) :
    Td_alphabet_d (v 22) (v 47) (v 48) := by
  have source := run.archive_source_l hZF u row entry code
  have map := cone.elementary row.i j row.c row.X row.R leg (run.archive_node_l hZF u row entry code) source.model
  have raw := source.round.map_l I hZF u.tree.omega source.model target.1 map td_round0_closed_l points
  let nc : Nonempty {x // M.mem x N} := ⟨⟨v 0,raw.1 0⟩⟩
  let V := rt_model_l N nc
  let ρ : Env V 62 := ⟨fun i => ⟨v i,raw.1 i⟩,fun _ => ⟨v 0,raw.1 0⟩⟩
  have ext := rt_model_ext_l hZF.1 nt nc
  have valid : Formula.satisfies ρ td_round0_m :=
    (smem_formula_l I target nc td_round0_m ρ).mpr
      ((rr_truth_native_l I target.1.2.1 td_round0_m td_round0_closed_l (fun i => ⟨v i,raw.1 i⟩)).mp raw)
  have alphabet := td_round_alphabet_l ext ρ valid
  have read (side : Bool) (z : V.Domain) : Td_letter_d side (ρ.bound 22) z ↔ Td_letter_d side (v 22) z.val := by
    let η : Env V 2 := ⟨Fin.cases z (fun _ => ρ.bound 22),fun _ => z⟩
    exact (td_letter_sat_l ext η side (.bound 1) .newest).symm.trans (td_letter_source_l nt nc hZF.1 η side (.bound 1) .newest)
  have all (side : Bool) (A : M.Domain) (hA : M.mem A N)
      (spec : ∀ z : V.Domain, M.mem z.val A ↔ Td_letter_d side (ρ.bound 22) z) :
      ∀ z, M.mem z A ↔ Td_letter_d side (v 22) z := by
    intro z
    constructor
    · intro hz
      let zn : V.Domain := ⟨z,nt A hA z hz⟩
      exact (read side zn).mp ((spec zn).mp hz)
    · intro letter
      let zn : V.Domain := ⟨z,letter.mem_l nt (raw.1 22)⟩
      exact (spec zn).mpr ((read side zn).mpr letter)
  exact ⟨all false (v 47) (raw.1 47) alphabet.1,all true (v 48) (raw.1 48) alphabet.2⟩

theorem Td_run_d.archive_root_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {m p : M.Domain} (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5))
    (code : Rt_tuple_d row.values_d p) : It_map_d (U 2) (g 2) row.i row.p := by
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨v,i,s,hs,pack,hq⟩ := (u.columns 5 q).mp hq
  obtain ⟨_,edge,_⟩ := (run.read_l hZF hs pack).links m p row ⟨q,pair,hq⟩ code
  obtain ⟨z,pair,entry⟩ := edge
  exact ⟨z,pair,u.entry_l hZF hs pack 2 entry⟩

theorem Td_run_d.alphabet_same_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P m n p q l k : M.Domain} (branch : It_branch_d (g 0) (U 0) b)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (old row : Td_archive_row_d M.Domain)
    (oldEntry : Rd_entry_d m p (U 5)) (newEntry : Rd_entry_d n q (U 5))
    (oldCode : Rt_tuple_d old.values_d p) (newCode : Rt_tuple_d row.values_d q)
    (left : Rd_entry_d old.i l P) (right : Rd_entry_d row.i k P)
    (v w : Fin 62 → M.Domain) (iv : ∀ i, Rd_entry_d (old.v i) (v i) l)
    (iw : ∀ i, Rd_entry_d (row.v i) (w i) k) : v 47 = w 47 ∧ v 48 = w 48 := by
  have so := run.archive_source_l hZF u old oldEntry oldCode
  have sr := run.archive_source_l hZF u row newEntry newCode
  have no := run.archive_node_l hZF u old oldEntry oldCode
  have nr := run.archive_node_l hZF u row newEntry newCode
  have ml := cone.elementary old.i l old.c old.X old.R left no so.model
  have mk := cone.elementary row.i k row.c row.X row.R right nr sr.model
  have eo := run.archive_root_l hZF u old oldEntry oldCode
  have er := run.archive_root_l hZF u row newEntry newCode
  have order := u.tree.diagram.map_bound_l hZF eo
  have rootMember := branch.down _ _ order ((cone.domain old.i).mpr ⟨l,left⟩)
  obtain ⟨j,root⟩ := (cone.domain (g 2)).mp rootMember
  obtain ⟨c,Y,R,node,model⟩ := u.tree.diagram.model_l hZF (branch.subset _ rootMember)
  have map := cone.elementary (g 2) j c Y R root node model
  have sameTree : v 22 = w 22 := map.1.1.1.2 _ _ _
    (cone.commute _ _ _ _ _ eo root left _ _ _ so.tree_root (iv 22))
    (cone.commute _ _ _ _ _ er root right _ _ _ sr.tree_root (iw 22))
  let V := smdl_structure_l I (R := W) target.1.2.1
  have ext := smem_ext_l I target.1 target.2 nt hZF.1
  let ρ : Env V 62 := ⟨fun i => ⟨v i,ml.1.1.output_mem_of_pairMember (iv i)⟩,
    fun _ => ⟨v 0,ml.1.1.output_mem_of_pairMember (iv 0)⟩⟩
  let η : Env V 62 := ⟨fun i => ⟨w i,mk.1.1.output_mem_of_pairMember (iw i)⟩,
    fun _ => ⟨w 0,mk.1.1.output_mem_of_pairMember (iw 0)⟩⟩
  have av := td_round_alphabet_l ext ρ
    ((rr_truth_native_l I target.1.2.1 td_round0_m td_round0_closed_l ρ.bound).mp
      (so.round.map_l I hZF u.tree.omega so.model target.1 ml td_round0_closed_l iv))
  have aw := td_round_alphabet_l ext η
    ((rr_truth_native_l I target.1.2.1 td_round0_m td_round0_closed_l η.bound).mp
      (sr.round.map_l I hZF u.tree.omega sr.model target.1 mk td_round0_closed_l iw))
  have eq : ρ.bound 22 = η.bound 22 := Subtype.ext sameTree
  obtain ⟨ea,eb⟩ := (eq ▸ av).ext_l ext aw
  exact ⟨congrArg Subtype.val ea,congrArg Subtype.val eb⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 深度覆盖的字母在实际极限第一图中出现

给定任一奇节点的字母，深度调度在后续真实行选中它的像；紧接的奇父边
将该待填字母放入第一图。两次交换方块将其识别为原字母在同一极限中的像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.letter_capture_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P m p l y z : M.Domain} (branch : It_branch_d (g 0) (U 0) b)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (base : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5)) (code : Rt_tuple_d base.values_d p)
    (member : M.mem base.i b) (hy : M.mem y base.X) (letter : Rd_entry_d y (base.v 47) base.R)
    (leg : Rd_entry_d base.i l P) (image : Rd_entry_d y z l) :
    ∃ n s, ∃ row : Td_archive_row_d M.Domain, ∃ k, ∃ v : Fin 62 → M.Domain,
      Rd_entry_d n s (U 5) ∧ Rt_tuple_d row.values_d s ∧ M.mem m n ∧ M.mem row.i b ∧
      Rd_entry_d row.i k P ∧ (∀ i, Rd_entry_d (row.v i) (v i) k) ∧ ∃ t, Rd_entry_d t z (v 45) := by
  have hw := u.tree.omega
  obtain ⟨m₁,p₁,chosen,j,entry₁,code₁,later,member₁,_,edge,hit⟩ :=
    run.cover_l hZF u b branch m p base entry code member y hy letter
  obtain ⟨l₁,v,leg₁,iv⟩ := run.archive_images_l hZF u cone chosen entry₁ code₁ member₁
  have source := run.archive_source_l hZF u base entry code
  have map := cone.elementary base.i l base.c base.X base.R leg (run.archive_node_l hZF u base entry code) source.model
  have eq : v 49 = z := map.1.1.1.2 y _ z
    (cone.commute base.i chosen.i j l l₁ edge leg leg₁ y (chosen.v 49) (v 49) hit (iv 49)) image
  -- 被选中字母在下一次奇父延长中进入第一图，而非停留在 pending 槽。
  obtain ⟨A,J,F,rows⟩ := run.branch_rows_l hZF u branch chosen entry₁ code₁ member₁
  obtain ⟨e,empty,he⟩ := hw.1.1
  obtain ⟨e',succ,he'⟩ := hw.1.2 e he
  obtain ⟨s,_,es⟩ := rows.sequence.2.1 e' he'
  obtain ⟨_,_,n,entry₂,_⟩ := rows.records e' s es
  obtain ⟨row,code₂⟩ := run.archive_decode_l hZF u entry₂
  obtain ⟨n',entry₂',_,member₂,_,_,_⟩ := run.branch_read_l hZF u rows row es code₂
  have en := (run.archive_unique_l hZF u row row entry₂ entry₂' code₂ code₂ rfl).1
  subst n'
  obtain ⟨k,w,leg₂,iw⟩ := run.archive_images_l hZF u cone row entry₂ code₂ member₂
  obtain ⟨j',edge',depth,_,growth⟩ := rows.equations e e' p₁ s chosen row succ (rows.first e empty) es code₁ code₂
  have finite := run.aux_growth_image_l hZF u cone target nt chosen row entry₁ entry₂ code₁ code₂
    edge' growth leg₁ leg₂ v w iv iw
  have different : chosen.i ≠ row.i := by
    intro same
    have codes := (run.archive_unique_l hZF u chosen row entry₁ entry₂ code₁ code₂ same).2
    have same := Td_archive_row_d.eq_l (rt_tuple_inj_l code₁ (codes.symm ▸ code₂))
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) row.depth
      (congrArg Td_archive_row_d.depth same ▸ depth.predecessor_mem)
  have next : M.mem chosen.i row.i :=
    (u.tree.diagram.order.forward _ _ (u.tree.diagram.map_bound_l hZF edge')).elim
      (fun same => (different same).elim) id
  have mn := run.archive_index_l hZF u chosen row entry₁ entry₂ code₁ code₂ next
  have bound := (u.archive.2.2 n).mpr ⟨s,entry₂⟩
  exact ⟨n,s,row,k,w,entry₂,code₂,(hw.members_areOrdinals (ZF.modelsKP hZF) n bound).transitive m₁ mn m later,
    member₂,leg₂,iw,v 25,eq ▸ finite.2.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际奇档案在传递极限中的完整有限节点

原轮中的节点和树条件一起沿锥腿运输。自然数对象由该行的完整数字图
识别为背景 ω；节点见证从树成员中回收，故不要求目标另满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem td_round_mem_node_l {Ω d N W : M.Domain} (target : Smem_d I d N W)
    (nt : M.TransitiveSet N) (v : Fin 62 → M.Domain) (raw : Rr_truth_d I N W td_round0_m v)
    (omega : v 19 = Ω) : M.mem (v 25) Ω ∧ Tg_node_d I (v 25) (v 22) (v 44) (v 45) (v 46) := by
  let nc : Nonempty {x // M.mem x N} := ⟨⟨v 0,raw.1 0⟩⟩
  let ρ : Env (rt_model_l N nc) 62 := ⟨fun i => ⟨v i,raw.1 i⟩,fun _ => ⟨v 0,raw.1 0⟩⟩
  have valid : Formula.satisfies ρ td_round0_m :=
    (smem_formula_l I target nc td_round0_m ρ).mpr
      ((rr_truth_native_l I target.1.2.1 td_round0_m td_round0_closed_l
        (fun i => ⟨v i,raw.1 i⟩)).mp raw)
  let η := ρ.reindex (fun i : Fin 43 => ⟨19+i.val,by omega⟩)
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp valid).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,node,tree,_⟩ := seed
  have node : Tg_node_d I (v 25) (v 22) (v 44) (v 45) (v 46) :=
    (tg_node_source_l nt nc hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) η
      (.bound 6) (.bound 3) (.bound 25) (.bound 26) (.bound 27)).mp node
  have data := node
  obtain ⟨_,_,_,q,hq,graph,_⟩ := data
  have hqN := nt (v 22) (raw.1 22) q hq
  simp only [td_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff] at tree
  obtain ⟨n,hn,gn,_⟩ := tree.1 ⟨q,hqN⟩ hq
  have gn := (tg_graph_source_l nt nc hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    ((η.push ⟨q,hqN⟩).push n) .newest (.bound 1)).mp gn
  have eq : n.val = v 25 := gn.2.eq hZF.1 graph.2
  exact ⟨omega ▸ eq ▸ hn,node⟩

variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.archive_node_image_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P m p j : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5)) (code : Rt_tuple_d row.values_d p)
    (leg : Rd_entry_d row.i j P) (v : Fin 62 → M.Domain) (points : ∀ i, Rd_entry_d (row.v i) (v i) j) :
    M.mem (v 25) (g 0) ∧ Tg_node_d I (v 25) (v 22) (v 44) (v 45) (v 46) := by
  have source := run.archive_source_l hZF u row entry code
  have node := run.archive_node_l hZF u row entry code
  have map := cone.elementary row.i j row.c row.X row.R leg node source.model
  obtain ⟨Y,R,_,_,_,model,ready,_⟩ := (u.tree.sources row.i row.c node).objects
  obtain ⟨ey,er⟩ := smdl_unique_l I model source.model
  subst Y R
  have number := source.numbers.omega_image_mem_l I hZF u.tree.omega ready.ext source.model target nt map
  have omega := map.1.1.1.2 _ _ _ (points 19) number.1
  exact td_round_mem_node_l hZF target nt v
    (source.round.map_l I hZF u.tree.omega source.model target.1 map td_round0_closed_l points) omega

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一极限树的完整有限列空间

从原档案模型中的内在树构造有限空间，再沿其真实锥腿运输。
目标源的配对、并集闭性回收全部背景内部有限列，不限制为标准长度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.archive_tree_space_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) {b d N W P m p j : M.Domain}
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5)) (code : Rt_tuple_d row.values_d p)
    (leg : Rd_entry_d row.i j P) (v : Fin 62 → M.Domain) (points : ∀ i, Rd_entry_d (row.v i) (v i) j) :
    ∃ Y F, Fseq_space_d I (g 0) Y F ∧ Tree_d F (v 22) := by
  have saved := run.archive_source_l hZF u row entry code
  have node := run.archive_node_l hZF u row entry code
  have map := cone.elementary row.i j row.c row.X row.R leg node saved.model
  have certificate := root.map_l hZF u.tree.omega saved.model saved.origin
  have native := ZFC.models_zf_l (certificate.native_l I hZF u.tree.omega)
  have hA := ZF.modelsKP native
  let A := smdl_structure_l I (R := row.R) saved.model.2.1
  let ρ : Env A 62 := ⟨fun i => ⟨row.v i,saved.round.1 i⟩,fun _ => ⟨row.v 0,saved.round.1 0⟩⟩
  have round : Formula.satisfies ρ td_round0_m :=
    (rr_truth_native_l I saved.model.2.1 td_round0_m td_round0_closed_l ρ.bound).mp saved.round
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨hw,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,tree,_⟩ := seed
  have omega := (Formula.satisfies_isOmega_iff ..).mp hw
  have tree := (td_tree_sat_l (kp_pair_l hA) hA.1 ..).mp tree
  obtain ⟨_,_,_,Y,F,_,_,_,space,closed⟩ := tree.space_l native omega
  have finite : Sc_fseq_d I (row.v 19) Y.val F.val row.X row.R :=
    (sc_fseq_native_l I saved.model.2.1 hA.1 (ρ.bound 19) Y F).mpr (fun s => (space s).trans
      ⟨fun ⟨n,hn,fn⟩ => ⟨n,hn,fn0_of_function_l hA fn⟩,fun ⟨n,hn,fn⟩ => ⟨n,hn,fn0_function_l hA fn⟩⟩)
  let η : Env A 2 := ⟨Fin.cases (ρ.bound 22) (fun _ => F),fun _ => ρ.bound 22⟩
  have raw : Rr_truth_d I row.X row.R (tree_m (.bound 1) .newest)
      (Fin.cases (row.v 22) (fun _ : Fin 1 => F.val)) := by
    have values : (fun i => (η.bound i).val) = Fin.cases (row.v 22) (fun _ : Fin 1 => F.val) :=
      funext (Fin.cases rfl (fun _ => rfl))
    have truth := (rr_truth_native_l I saved.model.2.1 (tree_m (.bound 1) .newest)
      (by simp -implicitDefEqProofs) η.bound).mpr ((tree_sat_l _ (.bound 1) .newest).mpr closed)
    exact Eq.mp (congrArg (Rr_truth_d I row.X row.R (tree_m (.bound 1) .newest)) values) truth
  have natural := (saved.numbers.omega_image_mem_l I hZF u.tree.omega certificate.ext saved.model target nt map).1
  obtain ⟨Y',_,iY⟩ := map.1.1.2.2 Y.val Y.property
  obtain ⟨F',_,iF⟩ := map.1.1.2.2 F.val F.property
  obtain ⟨_,source⟩ := (u.tree.sources row.i row.c node).image_mem_l hZF saved.model target nt map
  have algebra := source.algebra_l (ZF.modelsKP hZF)
  exact ⟨Y',F',Smap_d.tree_space_l hZF u.tree.omega saved.model target nt map algebra.pair algebra.union
    natural iY iF (points 22) finite raw⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真实奇行列的逐坐标极限图

每个内部阶段的全部坐标像由该行的唯一锥腿确定。背景替换收集坐标列，
读取任一坐标时仍回到同一实际行，供有限图取并使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.branch_values_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P start r₀ A J F : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (rows : Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b start r₀ A J F) (a : Fin 62) :
    ∃ G, Fn0_d (g 0) N G ∧ ∀ i x, Rd_entry_d i x G ↔ Tg_limit_value_d (62 : Fin 73) (a.castAdd 11) F P i x := by
  apply cone.record_values_l hZF (62 : Fin 73) (a.castAdd 11) rows.sequence
  · intro i s hs
    obtain ⟨_,_,m,entry,_⟩ := rows.records i s hs
    obtain ⟨row,code⟩ := run.archive_decode_l hZF u entry
    exact ⟨row.values_d,code⟩
  · intro i s v hs code
    obtain ⟨_,_,m,entry,_⟩ := rows.records i s hs
    obtain ⟨row,pack⟩ := run.archive_decode_l hZF u entry
    have eq := rt_tuple_inj_l code pack
    subst v
    obtain ⟨_,_,_,member,_,node,source⟩ := run.branch_read_l hZF u rows row hs pack
    exact ⟨row.c,row.X,row.R,node,source.model,
      by simpa only [Td_archive_row_d.values_d,Fin.addCases_left] using source.round.1 a,member⟩

theorem Td_run_d.branch_value_read_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P start r₀ A J F i s j x : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (rows : Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b start r₀ A J F)
    (row : Td_archive_row_d M.Domain) (hs : Rd_entry_d i s F) (code : Rt_tuple_d row.values_d s)
    (leg : Rd_entry_d row.i j P) (v : Fin 62 → M.Domain) (points : ∀ a, Rd_entry_d (row.v a) (v a) j)
    (a : Fin 62) (hx : Tg_limit_value_d (62 : Fin 73) (a.castAdd 11) F P i x) : x = v a := by
  obtain ⟨w,t,k,ht,pack,hk,hx⟩ := hx
  have eq := (fn0_function_l (ZF.modelsKP hZF) rows.sequence).1.2 i t s ht hs
  subst t
  have eq := rt_tuple_inj_l pack code
  subst w
  have eq := cone.function.2 row.i k j hk leg
  subst k
  obtain ⟨_,_,_,_,_,node,source⟩ := run.branch_read_l hZF u rows row hs code
  simp only [Td_archive_row_d.values_d,Fin.addCases_left] at hx
  exact (cone.elementary row.i j row.c row.X row.R leg node source.model).1.1.1.2 _ x (v a) hx (points a)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一实际奇尾段上两张辅助图的内部无限并

长度每步恰增一，有限图沿父边包含。已有内部有限图取并定理遂给出
定义域为整个背景 ω 的两张函数图，并保留每个有限阶段的全部条目。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_aux_union_d (Ω N F P : M.Domain) (a : Fin 2) (f : M.Domain) : Prop :=
  Fn0_d Ω N f ∧ ∀ p, M.mem p f ↔ ∃ i h,
    Tg_limit_value_d (62 : Fin 73) (([45,46].get a : Fin 62).castAdd 11) F P i h ∧ M.mem p h

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.aux_union_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b d N W P start r₀ A J F : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (rows : Td_branch_rows_d I (g 0) (U 5) (U 0) (U 2) b start r₀ A J F) (a : Fin 2) :
    ∃ f, Td_aux_union_d (g 0) N F P a f := by
  let c : Fin 62 := [45,46].get a
  obtain ⟨L,lf,ls⟩ := run.branch_values_l hZF u cone rows 25
  obtain ⟨G,gf,gs⟩ := run.branch_values_l hZF u cone rows c
  have data i (hi : M.mem i (g 0)) : ∃ m s, ∃ row : Td_archive_row_d M.Domain, ∃ j, ∃ v : Fin 62 → M.Domain,
      Rd_entry_d m s (U 5) ∧ Rd_entry_d i s F ∧ Rt_tuple_d row.values_d s ∧ Rd_entry_d row.i j P ∧
      (∀ t, Rd_entry_d (row.v t) (v t) j) ∧ M.mem (v 25) (g 0) ∧
      Tg_node_d I (v 25) (v 22) (v 44) (v 45) (v 46) := by
    obtain ⟨s,_,hs⟩ := rows.sequence.2.1 i hi
    obtain ⟨_,_,m,entry,_⟩ := rows.records i s hs
    obtain ⟨row,code⟩ := run.archive_decode_l hZF u entry
    obtain ⟨_,_,_,member,_⟩ := run.branch_read_l hZF u rows row hs code
    obtain ⟨j,v,leg,points⟩ := run.archive_images_l hZF u cone row entry code member
    exact ⟨m,s,row,j,v,entry,hs,code,leg,points,
      run.archive_node_image_l hZF u cone target nt row entry code leg v points⟩
  have length : Fn0_d (g 0) (g 0) L := by
    have fn := fn0_function_l (ZF.modelsKP hZF) lf
    apply fn0_of_function_l (ZF.modelsKP hZF)
    refine ⟨fn.1,fn.2.1,?_⟩
    intro i hi
    obtain ⟨n,_,hn⟩ := fn.2.2 i hi
    obtain ⟨_,s,row,j,v,_,hs,code,leg,points,finite,_⟩ := data i hi
    have eq := run.branch_value_read_l hZF u cone rows row hs code leg v points 25 ((ls i n).mp hn)
    exact ⟨n,eq.symm ▸ finite,hn⟩
  have finite i n h (hn : Rd_entry_d i n L) (hh : Rd_entry_d i h G) : Tg_graph_d I n h := by
    obtain ⟨_,s,row,j,v,_,hs,code,leg,points,_,node⟩ := data i (lf.bound_l hn).1
    have en := run.branch_value_read_l hZF u cone rows row hs code leg v points 25 ((ls i n).mp hn)
    have eh := run.branch_value_read_l hZF u cone rows row hs code leg v points c ((gs i h).mp hh)
    have graphs : ∀ a : Fin 2, Tg_graph_d I (v 25) (v ([45,46].get a)) :=
      Fin.cases node.2.1 (Fin.cases node.2.2.1 (fun i => Fin.elim0 i))
    have graph := graphs a
    exact en.symm ▸ eh.symm ▸ graph
  have next i k n m h t (succ : M.SuccessorOf k i)
      (hn : Rd_entry_d i n L) (hm : Rd_entry_d k m L) (hh : Rd_entry_d i h G) (ht : Rd_entry_d k t G) :
      M.SuccessorOf m n ∧ M.MemberSubset h t := by
    obtain ⟨m₀,s,old,l,v,entry,hs,code,leg,points,_,_⟩ := data i (lf.bound_l hn).1
    obtain ⟨m₁,s',row,l',w,entry',hs',code',leg',points',_,_⟩ := data k (lf.bound_l hm).1
    have en := run.branch_value_read_l hZF u cone rows old hs code leg v points 25 ((ls i n).mp hn)
    have em := run.branch_value_read_l hZF u cone rows row hs' code' leg' w points' 25 ((ls k m).mp hm)
    have eh := run.branch_value_read_l hZF u cone rows old hs code leg v points c ((gs i h).mp hh)
    have et := run.branch_value_read_l hZF u cone rows row hs' code' leg' w points' c ((gs k t).mp ht)
    obtain ⟨j,edge,_,_,growth⟩ := rows.equations i k s s' old row succ hs hs' code code'
    have result := run.aux_growth_image_l hZF u cone target nt old row entry entry' code code'
      edge growth leg leg' v w points points'
    have subs : ∀ a : Fin 2, M.MemberSubset (v ([45,46].get a)) (w ([45,46].get a)) :=
      Fin.cases result.2.1 (Fin.cases result.2.2.1 (fun i => Fin.elim0 i))
    have sub := subs a
    exact ⟨em.symm ▸ en.symm ▸ result.1,eh.symm ▸ et.symm ▸ sub⟩
  obtain ⟨f,ff,union,_⟩ := tg_graph_union_l hZF u.tree.omega nt length gf finite (by
    intro i k n m succ hn hm
    obtain ⟨h,_,hh⟩ := gf.2.1 i (lf.bound_l hn).1
    obtain ⟨t,_,ht⟩ := gf.2.1 k (lf.bound_l hm).1
    exact (next i k n m h t succ hn hm hh ht).1) (by
    intro i k h t succ hh ht
    obtain ⟨n,_,hn⟩ := lf.2.1 i (gf.bound_l hh).1
    obtain ⟨m,_,hm⟩ := lf.2.1 k (gf.bound_l ht).1
    exact (next i k n m h t succ hn hm hh ht).2)
  exact ⟨f,ff,fun p => (union p).trans ⟨fun ⟨i,h,ih,hp⟩ => ⟨i,h,(gs i h).mp ih,hp⟩,
    fun ⟨i,h,ih,hp⟩ => ⟨i,h,(gs i h).mpr ih,hp⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## Claim 7.10 的两张无限辅助图及第一坐标满射

在同一实际良基奇枝锥中取相邻行列的并。每个极限字母的代表可推到
任意较晚奇节点；随后深度调度及恢复把它加入同一列的第一图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_aux_limit_d (Ω D T Q G b : M.Domain) : Prop :=
  ∃ d N W P S A B a b', Smem_d I d N W ∧ M.TransitiveSet N ∧
    It_cone_d (kp_pair_l (ZF.modelsKP hZF)) Ω b Q G d N W P ∧ Td_alphabet_d S A B ∧
    Fn0_d Ω A a ∧ M.IsSetSurjectiveOnto I a Ω A ∧ Fn0_d Ω B b' ∧
    ∃ m p, ∃ row : Td_archive_row_d M.Domain, ∃ l,
      Rd_entry_d m p D ∧ Rt_tuple_d row.values_d p ∧ Rd_entry_d row.i l P ∧
      Rd_entry_d (row.v 22) S l ∧ Rd_entry_d (row.v 47) A l ∧ Rd_entry_d (row.v 48) B l ∧
      ∃ L J F, Td_branch_rows_d I Ω D T G b row.i p L J F ∧
        Td_aux_union_d Ω N F P 0 a ∧ Td_aux_union_d Ω N F P 1 b'

variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.wf_aux_limit_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {b : M.Domain} (wf : It_wf_branch_d hZF (g 0) (g 0) (U 0) (U 1) (U 2) b) :
    Td_aux_limit_d hZF (g 0) (U 5) (U 0) (U 1) (U 2) b := by
  have hw := u.tree.omega
  obtain ⟨_,_,_,_,ext⟩ := it_wf_branch_extend_l hZF u.tree (hw.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_,_,_,_,_,_,d,N,W,P,_,_,_,target,nt,cone,_⟩ := ext.limit
  obtain ⟨e,_,he⟩ := hw.1.1
  obtain ⟨m,p,base,entry,code,member,_⟩ := run.wf_rows_l hZF u wf e he
  obtain ⟨l,v,leg,iv⟩ := run.archive_images_l hZF u cone.toIt_embedding_d base entry code member
  obtain ⟨D,J,F,rows⟩ := run.branch_rows_l hZF u wf.1 base entry code member
  have unions (c : Fin 2) := run.aux_union_l hZF u cone.toIt_embedding_d target nt rows c
  obtain ⟨aux,unions⟩ := Classical.axiomOfChoice unions
  have alphabet := run.archive_alphabet_mem_l hZF u cone.toIt_embedding_d target nt base entry code leg v iv
  have source := run.archive_source_l hZF u base entry code
  have map := cone.elementary base.i l base.c base.X base.R leg (run.archive_node_l hZF u base entry code) source.model
  -- 任一并图条目回到产生它的有限节点，最小字母域的像恒定给出精确值域。
  have typed (c : Fin 2) : Fn0_d (g 0) (v ([47,48].get c)) (aux c) := by
    have fn := fn0_function_l (ZF.modelsKP hZF) (unions c).1
    apply fn0_of_function_l (ZF.modelsKP hZF)
    refine ⟨fn.1,fn.2.1,?_⟩
    intro i hi
    obtain ⟨y,_,iy⟩ := fn.2.2 i hi
    obtain ⟨q,pair,hq⟩ := iy
    obtain ⟨j,h,trace,qh⟩ := (unions c).2 q |>.mp hq
    obtain ⟨w₀,s,k,js,pack,jk,image⟩ := trace
    obtain ⟨_,_,n,entry',_⟩ := rows.records j s js
    obtain ⟨row,code'⟩ := run.archive_decode_l hZF u entry'
    have eq := rt_tuple_inj_l pack code'
    subst w₀
    obtain ⟨_,_,_,member',_,_,_⟩ := run.branch_read_l hZF u rows row js code'
    obtain ⟨k',w,leg',iw⟩ := run.archive_images_l hZF u cone.toIt_embedding_d row entry' code' member'
    have eq := cone.function.2 row.i k k' jk leg'
    subst k
    have eq := run.branch_value_read_l hZF u cone.toIt_embedding_d rows row js code' leg' w iw
      ([45,46].get c) ⟨row.values_d,s,k',js,code',leg',image⟩
    have hit : Rd_entry_d i y (w ([45,46].get c)) := eq ▸ ⟨q,pair,qh⟩
    have node := (run.archive_node_image_l hZF u cone.toIt_embedding_d target nt row entry' code' leg' w iw).2
    have alph := run.archive_alphabet_mem_l hZF u cone.toIt_embedding_d target nt row entry' code' leg' w iw
    have bounds := alph.node_l I hZF.1 node
    have bound : ∀ c : Fin 2, Rd_entry_d i y (w ([45,46].get c)) → M.mem y (w ([47,48].get c)) :=
      Fin.cases (bounds.1 i y) (Fin.cases (bounds.2 i y) (fun i => Fin.elim0 i))
    have same := run.alphabet_same_l hZF u wf.1 cone.toIt_embedding_d target nt base row
      entry entry' code code' leg leg' v w iv iw
    have same : ∀ c : Fin 2, v ([47,48].get c) = w ([47,48].get c) :=
      Fin.cases same.1 (Fin.cases same.2 (fun i => Fin.elim0 i))
    exact ⟨y,(same c).symm ▸ bound c hit,q,pair,hq⟩
  have onto : M.IsSetSurjectiveOnto I (aux 0) (g 0) (v 47) := by
    intro z hz
    have hA := map.1.1.output_mem_of_pairMember (iv 47)
    obtain ⟨i,l₀,y,leg₀,yz⟩ := cone.cover z (nt (v 47) hA z hz)
    have hi := (cone.domain i).mpr ⟨l₀,leg₀⟩
    -- 同时越过代表阶段和固定尾段起点，确保命中属于已经构造的同一并图。
    obtain ⟨t,front,baseFront⟩ := wf.1.front_directed_l hZF u.tree.diagram.order i base.i
      (wf.1.subset i hi) (wf.1.subset base.i member)
    obtain ⟨n,q,row,entry',code',member',later⟩ := run.wf_rows_l hZF u wf t (wf.1.subset t front.2.1)
    have tr := wf.1.forward_l u.tree.diagram.order front.2.1 member' later
    have ir := u.tree.diagram.order.trans i t row.i
      (wf.1.forward_l u.tree.diagram.order hi front.2.1 front.2.2) tr
    have br := u.tree.diagram.order.trans base.i t row.i
      (wf.1.forward_l u.tree.diagram.order member baseFront.2.1 baseFront.2.2) tr
    obtain ⟨k,w,leg',iw⟩ := run.archive_images_l hZF u cone.toIt_embedding_d row entry' code' member'
    have same := (run.alphabet_same_l hZF u wf.1 cone.toIt_embedding_d target nt base row
      entry entry' code code' leg leg' v w iv iw).1
    obtain ⟨c,Y,R,node,model⟩ := u.tree.diagram.model_l hZF (wf.1.subset i hi)
    have oldMap := cone.elementary i l₀ c Y R leg₀ node model
    have rowSource := run.archive_source_l hZF u row entry' code'
    have rowNode := run.archive_node_l hZF u row entry' code'
    have newMap := cone.elementary row.i k row.c row.X row.R leg' rowNode rowSource.model
    obtain ⟨j,edge⟩ := u.tree.diagram.map_l hZF ir
    have between := u.tree.diagram.elementary i row.i j c Y R row.c row.X row.R edge node rowNode model rowSource.model
    obtain ⟨y',hy',yy⟩ := between.1.1.2.2 y (oldMap.1.1.input_mem_of_pairMember yz)
    obtain ⟨z',_,image'⟩ := newMap.1.1.2.2 y' hy'
    have eq := oldMap.1.1.1.2 y z' z (cone.commute i row.i j l₀ k edge leg₀ leg' y y' z' yy image') yz
    have image : Rd_entry_d y' z k := eq ▸ image'
    have letter : Rd_entry_d y' (row.v 47) row.R :=
      (newMap.relation_l I hZF hw rowSource.model target.1 image (iw 47)).mpr
        ((target.2 z (w 47)).mpr ⟨nt (v 47) hA z hz,same ▸ hA,same ▸ hz⟩)
    obtain ⟨n',s,row',k',v',entry'',code'',nn',member'',leg'',points,j',hit⟩ :=
      run.letter_capture_l hZF u wf.1 cone.toIt_embedding_d target nt row entry' code' member' hy' letter leg' image
    have next := run.archive_order_l hZF u row row' entry' entry'' code' code'' nn'
    have baseNext := u.tree.diagram.order.forward _ _ (u.tree.diagram.order.trans _ _ _ br
      (wf.1.forward_l u.tree.diagram.order member' member'' (Or.inr next)))
    obtain ⟨i',is⟩ := run.branch_range_l hZF u wf.1 member rows row' entry'' code'' member'' baseNext
    obtain ⟨q',pair,hq'⟩ := hit
    have hit : Rd_entry_d j' z (aux 0) := ⟨q',pair,(unions 0).2 q' |>.mpr
      ⟨i',v' 45,⟨row'.values_d,s,k',is,code'',leg'',points 45⟩,hq'⟩⟩
    exact ⟨j',((unions 0).1.bound_l hit).1,hit⟩
  exact ⟨d,N,W,P,v 22,v 47,v 48,aux 0,aux 1,target,nt,cone,alphabet,typed 0,onto,typed 1,
    m,p,base,l,entry,code,leg,iv 22,iv 47,iv 48,D,J,F,rows,unions 0,unions 1⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限实数图的值通过同一档案共同层进入当前历史

数字与字母都由图的实际前驱回收。完整数字图保证背景指标不变，
短图的全部取值沿同一共同图运输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_state_d.archive_transport_l {g : Fin 10 → M.Domain} {v : Fin 66 → M.Domain}
    {m p l V Γ t s i n x : M.Domain}
    (state : Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)))
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) (row : Td_archive_row_d M.Domain)
    (entry : Rd_entry_d m p (v 11)) (code : Rt_tuple_d row.values_d p)
    (common : Ic_common_d I row.X row.R (v 0) (v 1) row.L l row.U V Γ t)
    (short : Rd_entry_d (row.v 44) s t) (point : Rd_entry_d i n row.z)
    (value : Rf_val_d I row.X row.R n x (row.v 44)) :
    ∃ n' x', Rd_entry_d i n' (v 4) ∧ Rd_entry_d n n' t ∧ Rd_entry_d x x' t ∧
      Rf_val_d I (v 0) (v 1) n' x' s := by
  have saved := ((state.archive m p entry).read_l I code).1
  have current := state.tree.diagram.elementary (g 2) (v 5) (v 3) (g 1) (g 3) (g 4)
    (v 2) (v 0) (v 1) state.origin state.root_node state.node root.model state.model
  have source := root.map_l hZF state.tree.omega saved.model saved.origin
  have target := root.map_l hZF state.tree.omega state.model current
  have native := ZFC.models_zf_l (source.native_l I hZF state.tree.omega)
  have hA := ZF.modelsKP native
  let A := smdl_structure_l I (R := row.R) saved.model.2.1
  let N := smdl_structure_l I (R := v 1) state.model.2.1
  let U : A.Domain := ⟨row.U,common.left_rank.2.1⟩
  have rank := (rr_rank_native_l I saved.model.2.1 hA (⟨row.L,common.left_rank.1⟩ : A.Domain) U).mp common.left_rank
  have trans := v_transitive_l (kp_pair_l hA) rank
  let ρ : Env A 62 := ⟨fun i => ⟨row.v i,saved.round.1 i⟩,fun _ => ⟨row.v 0,saved.round.1 0⟩⟩
  have round : Formula.satisfies ρ td_round0_m :=
    (rr_truth_native_l I saved.model.2.1 td_round0_m td_round0_closed_l ρ.bound).mp saved.round
  have omegaU : Rd_entry_d (row.v 19) row.U row.R := trans (ρ.bound 1)
    (ZF.v_mem_l (kp_pair_l hA) native (td_round_letters_l native ρ round).1 rank saved.below)
    (ρ.bound 19) (td_round_omega_low_l native ρ round)
  let sn : A.Domain := ⟨row.v 44,(value.bounds_l I).2.2⟩
  let ni : A.Domain := ⟨n,(value.bounds_l I).1⟩
  let xi : A.Domain := ⟨x,(value.bounds_l I).2.1⟩
  have old := (rf_val_native_l I saved.model.2.1 hA.1 ni xi sn).mp value
  have member : A.mem sn U := ((common.carrier _).mp (common.injection.1.input_mem_of_pairMember short)).2
  have bounds := rd_entry_transitive_l trans member old
  have pick (a : A.Domain) (ha : A.mem a U) : ∃ b : N.Domain, Rd_entry_d a.val b.val t := by
    obtain ⟨b,hb,ab⟩ := common.injection.1.2.2 a.val ((common.carrier a.val).mpr ⟨a.property,ha⟩)
    exact ⟨⟨b,hb⟩,ab⟩
  obtain ⟨ni',in'⟩ := pick ni bounds.1
  obtain ⟨xi',ix'⟩ := pick xi bounds.2
  let sn' : N.Domain := ⟨s,common.injection.1.output_mem_of_pairMember short⟩
  have move := rr_graph_delta_l I saved.model.2.1 state.model.2.1
    ⟨row.v 44,common.injection.1.input_mem_of_pairMember short⟩
    (fun y hy => ((common.carrier y).mp hy).1)
    (fun y z hy hz zy => (common.carrier z).mpr ⟨hz,
      trans ⟨y,((common.carrier y).mp hy).1⟩ ((common.carrier y).mp hy).2 ⟨z,hz⟩ zy⟩)
    common.injection common.pred
    (rd_entry0_m (.bound 0) (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    (⟨fun k => [ni,xi,sn].get k,fun _ => sn⟩ : Env A 3)
    (⟨fun k => [ni',xi',sn'].get k,fun _ => sn'⟩ : Env N 3)
    (Fin.cases in' (Fin.cases ix' (Fin.cases short (fun k => Fin.elim0 k))))
  have ext := target.ext.native_l I state.model.2.1
  have moved : Rd_entry_d ni' xi' sn' := (rd_entry0_sat_l ext ..).mp (move.mp ((rd_entry0_sat_l hA.1 ..).mpr old))
  have graph := (common.layer_image_l (ZF.modelsKP hZF) saved.model.2.1 target.ext saved.numbers state.numbers trans omegaU).2
  exact ⟨ni'.val,xi'.val,(graph i ni'.val).mpr ⟨n,point,in'⟩,in',ix',
    (rf_val_native_l I state.model.2.1 ext ni' xi' sn').mpr moved⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 每份有限实数图逐点来自同一原对局

先在同一晚阶段的真实历史中读回档案条目，再经根切片回收原字母。
原对局的图由内部运行统一构造，故不依赖所选奇枝或极限模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_state_d.archive_real_l {g : Fin 10 → M.Domain} {v : Fin 66 → M.Domain}
    {m p i n x : M.Domain}
    (state : Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)))
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) (row : Td_archive_row_d M.Domain)
    (entry : Rd_entry_d m p (v 11)) (code : Rt_tuple_d row.values_d p)
    (point : Rd_entry_d i n row.z) (value : Rf_val_d I row.X row.R n x (row.v 44)) :
    ∃ a, Td_real_d I v i a ∧ Rd_entry_d a x row.p := by
  obtain ⟨saved,l,V,Γ,t,common,_,roots,_,_,_,_,_,_,_,_,_,s,short,play⟩ := (state.archive m p entry).read_l I code
  obtain ⟨n',x',idx,in',ix',val⟩ := state.archive_transport_l hZF root row entry code common short point value
  have map := state.tree.diagram.elementary (g 2) (v 5) (v 3) (g 1) (g 3) (g 4)
    (v 2) (v 0) (v 1) state.origin state.root_node state.node root.model state.model
  have native := ZFC.models_zf_l ((root.map_l hZF state.tree.omega state.model map).native_l I hZF state.tree.omega)
  have source := ZFC.models_zf_l ((root.map_l hZF state.tree.omega saved.model saved.origin).native_l I hZF state.tree.omega)
  have hN := ZF.modelsKP native
  have hA := ZF.modelsKP source
  let N := smdl_structure_l I (R := v 1) state.model.2.1
  let A := smdl_structure_l I (R := row.R) saved.model.2.1
  let ρ : Env N 47 := ⟨fun i => ⟨v (Fin.natAdd 19 i),state.issued.1 i⟩,fun _ => ⟨v 19,state.issued.1 0⟩⟩
  let η : Env A 62 := ⟨fun i => ⟨row.v i,saved.round.1 i⟩,fun _ => ⟨row.v 0,saved.round.1 0⟩⟩
  have issued : Formula.satisfies ρ td_issued0_m :=
    (rr_truth_native_l I state.model.2.1 td_issued0_m td_issued0_closed_l ρ.bound).mp state.issued
  have round : Formula.satisfies η td_round0_m :=
    (rr_truth_native_l I saved.model.2.1 td_round0_m td_round0_closed_l η.bound).mp saved.round
  have xv : A.mem ⟨x,(value.bounds_l I).2.1⟩ (η.bound 50) :=
    (td_round_real_l hA η round).2.2.2.bound_l
      ((rf_val_native_l I saved.model.2.1 hA.1 ⟨n,(value.bounds_l I).1⟩ ⟨x,(value.bounds_l I).2.1⟩ (η.bound 44)).mp value) |>.2
  -- 根字母域自身位于根切片；根方块因此识别共同图中的同一字母域。
  obtain ⟨Ar,hAr,ArImage⟩ := (state.slice.image (v 25)).mp state.letters_low
  have eq : Ar = g 8 := map.1.2 _ _ _ (state.slice.root _ _ ArImage) state.letters_root
  have hAr : M.mem (g 8) (g 6) := eq ▸ hAr
  have letterImage := (roots (g 8) hAr (row.v 50) saved.letters_root (v 25)).mpr state.letters_root
  have hx' : Rd_entry_d x' (v 25) (v 1) := (common.pred _ _ letterImage x').mpr ⟨x,xv,ix'⟩
  have rank := (rr_rank_native_l I state.model.2.1 hN
    (⟨v 15,state.slice.rank.1⟩ : N.Domain) ⟨v 16,state.slice.rank.2.1⟩).mp state.slice.rank
  have low : Rd_entry_d x' (v 16) (v 1) := (v_transitive_l (kp_pair_l hN) rank)
    (ρ.bound 6) state.letters_low ⟨x',(val.bounds_l I).2.1⟩ hx'
  obtain ⟨a,ha,ax⟩ := (state.slice.image x').mp low
  have actual := state.slice.root a x' ax
  obtain ⟨a',_,aa⟩ := saved.origin.1.1.2.2 a (map.1.1.input_mem_of_pairMember actual)
  have eq : a' = x := common.injection.2 _ _ x' ((roots a ha a' aa x').mpr actual) ix'
  have sourceImage : Rd_entry_d a x row.p := eq ▸ aa
  -- 档案 play 与当前原历史使用相同的实数余数，历史中的实际值因此进入原对局图。
  let sn : N.Domain := ⟨s,(val.bounds_l I).2.2⟩
  let ni : N.Domain := ⟨n',(val.bounds_l I).1⟩
  let xi : N.Domain := ⟨x',(val.bounds_l I).2.1⟩
  let ξ : Env N 4 := ⟨fun i => [ρ.bound 4,ρ.bound 2,ρ.bound 20,sn].get i,ρ.free⟩
  obtain ⟨b,succ,events⟩ := (td_play_native_l I state.model.2.1 hN ξ).mp play
  have control := (td_issued_sat_l (kp_pair_l hN) hN.1 ρ).mp issued |>.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have rules := (td_rules_sat_l native ..).mp control.2.2.1
  have eq : b = ρ.bound 3 := succ.eq hN.1 rules.two
  have event : Tg_event_d (kp_pair_l hN) (ρ.bound 4) ni (ρ.bound 3) (ρ.bound 20) xi :=
    eq ▸ events ni xi ((rf_val_native_l I state.model.2.1 hN.1 ni xi sn).mp val)
  refine ⟨a,⟨n',x',idx,actual,Fin.cases (ρ.bound 4).property (Fin.cases ni.property
    (Fin.cases (ρ.bound 3).property (Fin.cases (ρ.bound 20).property (Fin.cases xi.property (fun i => Fin.elim0 i))))),?_⟩,sourceImage⟩
  exact (tg_event_sat_l (kp_pair_l hN) hN.1 _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr event

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限中的有限实数图是同一原对局的前缀

极限取值回拉到原档案，再由实际历史回收到唯一原根字母。
锥交换律把这个字母的原根像识别为最初给定的极限取值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.archive_real_image_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) {A play b d N W P j₀ m p j : M.Domain}
    (played : Td_run_play_d I (g 0) A H play)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (g 0) b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N) (rootLeg : Rd_entry_d (g 2) j₀ P)
    (row : Td_archive_row_d M.Domain) (entry : Rd_entry_d m p (U 5)) (code : Rt_tuple_d row.values_d p)
    (leg : Rd_entry_d row.i j P) (v : Fin 62 → M.Domain) (points : ∀ i, Rd_entry_d (row.v i) (v i) j) :
    ∀ i y, Rd_entry_d i y (v 44) → ∃ x, Rd_entry_d i x play ∧ Rd_entry_d x y j₀ := by
  have source := run.archive_source_l hZF u row entry code
  have node := run.archive_node_l hZF u row entry code
  have map := cone.elementary row.i j row.c row.X row.R leg node source.model
  have ext := (root.map_l hZF u.tree.omega source.model source.origin).ext
  have natural := source.numbers.omega_image_mem_l I hZF u.tree.omega ext source.model target nt map
  obtain ⟨finite,graphs⟩ := run.archive_node_image_l hZF u cone target nt row entry code leg v points
  have edge := run.archive_root_l hZF u row entry code
  intro i y value
  have hi := u.tree.omega.transitive (ZF.modelsKP hZF) _ finite i ((graphs.1.2 i).mpr ⟨y,value⟩)
  obtain ⟨n,_,point⟩ := source.numbers.injection.1.2.2 i hi
  obtain ⟨x,raw,image⟩ := Smap_d.value_preimage_l hZF u.tree.omega source.model target nt map ext
    (natural.2 i n point) (points 44) graphs.1.1 value
  obtain ⟨q,pair,hq⟩ := entry
  obtain ⟨w,k,t,ht,pack,hq⟩ := (u.columns 5 q).mp hq
  have state := run.read_l hZF ht pack
  obtain ⟨z,actual,rootImage⟩ := state.archive_real_l hZF root row ⟨q,pair,hq⟩ code point raw
  exact ⟨z,(played.2 i z).mpr ⟨hi,k,t,ht,w,pack,actual⟩,
    cone.commute (g 2) row.i row.p j₀ j edge rootLeg leg z x y rootImage image⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## Claim 7.10：同一原对局与两张辅助图合成完整分支

先固定由内部运行构造的原实数对局，再任取良基奇枝。有限实数图逐点
等于该原对局沿根腿的像，辅助图则是同一相邻行列的并；共尾有限节点
因此拼成原树像中的完整分支，第一辅助坐标保持满射。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_branch_projection_d (Ω o S₀ Q G b play : M.Domain) : Prop :=
  ∃ d N W P j S Y F x A B, Smem_d I d N W ∧ M.TransitiveSet N ∧
    It_cone_d (kp_pair_l (ZF.modelsKP hZF)) Ω b Q G d N W P ∧ Rd_entry_d o j P ∧ Rd_entry_d S₀ S j ∧
    It_comp_d play j x ∧ Fseq_space_d I Ω Y F ∧ Tree_d F S ∧ Td_alphabet_d S A B ∧
    Td_projection_d hZF Ω A B Y F S x

private theorem td_graph_cut_l {n s f : M.Domain} (graph : Tg_graph_d I n s)
    (function : M.IsSetFunction I f) (values : ∀ i x, Rd_entry_d i x s → Rd_entry_d i x f) :
    M.IsRestrictionOf I s f n := by
  refine ⟨graph.1.1,fun i x => ⟨fun h => ⟨(graph.2 i).mpr ⟨x,h⟩,values i x h⟩,?_⟩⟩
  rintro ⟨hi,hx⟩
  obtain ⟨y,hy⟩ := (graph.2 i).mp hi
  exact function.2 i y x (values i y hy) hx ▸ hy

variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.wf_projection_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) {A₀ play b : M.Domain}
    (inside : M.MemberSubset A₀ (g 3)) (played : Td_run_play_d I (g 0) A₀ H play)
    (wf : It_wf_branch_d hZF (g 0) (g 0) (U 0) (U 1) (U 2) b) :
    Td_branch_projection_d hZF (g 0) (g 2) (g 9) (U 1) (U 2) b play := by
  obtain ⟨d,N,W,P,S,A,B,a,b',target,nt,cone,alphabet,fa,onto,fb,
    m,p,base,l,entry,code,leg,iS,iA,iB,L,J,F,rows,ua,ub⟩ := run.wf_aux_limit_l hZF u wf
  have hw := u.tree.omega
  have source := run.archive_source_l hZF u base entry code
  have edge := run.archive_root_l hZF u base entry code
  have member := (cone.domain base.i).mpr ⟨l,leg⟩
  have rootMember := wf.1.down _ _ (u.tree.diagram.map_bound_l hZF edge) member
  obtain ⟨j,rootLeg⟩ := (cone.domain (g 2)).mp rootMember
  obtain ⟨e,_,he⟩ := hw.1.1
  obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 e he
  obtain ⟨v₀,cv,state⟩ := (run.rows e s hs).1
  have rootNode := u.entry_l hZF hs cv 1 state.root_node
  have map := cone.elementary (g 2) j (g 1) (g 3) (g 4) rootLeg rootNode root.model
  have treeImage := cone.commute (g 2) base.i base.p j l edge rootLeg leg (g 9) (base.v 22) S source.tree_root iS
  -- 原对局先固定；极限实数图是其与同一根腿的实际复合。
  obtain ⟨x,fx,composition⟩ := ZF.exists_compositionFunction hZF I
    (Structure.IsSetFunctionFromTo.mono_target_l I (fn0_function_l (ZF.modelsKP hZF) played.1) inside) map.1.1
  have comp : It_comp_d play j x := ⟨fx.1.1,fun i z => (composition i z).trans
    ⟨And.right,fun ⟨y,iy,yz⟩ => ⟨(played.1.bound_l iy).1,y,iy,yz⟩⟩⟩
  obtain ⟨l',v,leg',points⟩ := run.archive_images_l hZF u cone.toIt_embedding_d base entry code member
  have eq := cone.function.2 base.i l' l leg' leg
  subst l'
  have baseMap := cone.elementary base.i l base.c base.X base.R leg (run.archive_node_l hZF u base entry code) source.model
  have eqS : v 22 = S := baseMap.1.1.1.2 _ _ _ (points 22) iS
  obtain ⟨Y,E,space,tree⟩ := run.archive_tree_space_l hZF u root cone.toIt_embedding_d target nt base entry code leg v points
  have tree : Tree_d E S := eqS ▸ tree
  have nodes n (hn : M.mem n (g 0)) : ∃ k s t v, M.mem n k ∧ M.mem k (g 0) ∧
      M.IsRestrictionOf I s x k ∧ M.IsRestrictionOf I t a k ∧ M.IsRestrictionOf I v b' k ∧ Tg_node_d I k S s t v := by
    -- 第一并图已有全 ω 定义域，故其中任一 n 条目来自长度严格超过 n 的实际有限节点。
    obtain ⟨z,_,nz⟩ := fa.2.1 n hn
    obtain ⟨q,pair,hq⟩ := nz
    obtain ⟨i,t,trace,qt⟩ := (ua.2 q).mp hq
    obtain ⟨v₁,s,l₁,is,cs,leg₁,image⟩ := trace
    obtain ⟨_,_,m₁,entry₁,_⟩ := rows.records i s is
    obtain ⟨row,code₁⟩ := run.archive_decode_l hZF u entry₁
    have eq := rt_tuple_inj_l cs code₁
    subst v₁
    obtain ⟨_,_,_,member₁,_,_,_⟩ := run.branch_read_l hZF u rows row is code₁
    obtain ⟨l₂,w,leg₂,iw⟩ := run.archive_images_l hZF u cone.toIt_embedding_d row entry₁ code₁ member₁
    have eq := cone.function.2 row.i l₁ l₂ leg₁ leg₂
    subst l₁
    have et := run.branch_value_read_l hZF u cone.toIt_embedding_d rows row is code₁ leg₂ w iw 45
      ⟨row.values_d,s,l₂,is,code₁,leg₂,image⟩
    have nz : Rd_entry_d n z (w 45) := et ▸ ⟨q,pair,qt⟩
    obtain ⟨finite,node⟩ := run.archive_node_image_l hZF u cone.toIt_embedding_d target nt row entry₁ code₁ leg₂ w iw
    have rowSource := run.archive_source_l hZF u row entry₁ code₁
    have rowEdge := run.archive_root_l hZF u row entry₁ code₁
    have sameTree : w 22 = S := map.1.1.1.2 _ _ _
      (cone.commute (g 2) row.i row.p j l₂ rowEdge rootLeg leg₂ _ _ _ rowSource.tree_root (iw 22)) treeImage
    have realCut : M.IsRestrictionOf I (w 44) x (w 25) := td_graph_cut_l hZF node.1 fx.1 (by
      intro i z iz
      obtain ⟨y,iy,yz⟩ := run.archive_real_image_l hZF u root played cone.toIt_embedding_d target nt rootLeg
        row entry₁ code₁ leg₂ w iw i z iz
      exact (comp.2 i z).mpr ⟨y,iy,yz⟩)
    have keep (c : Fin 2) (t : M.Domain) (union : Td_aux_union_d (g 0) N F P c t) :
        ∀ i z, Rd_entry_d i z (w ([45,46].get c)) → Rd_entry_d i z t := by
      rintro i' z ⟨q,pair,hq⟩
      refine ⟨q,pair,(union.2 q).mpr ⟨i,w ([45,46].get c),⟨row.values_d,s,l₂,is,code₁,leg₂,?_⟩,hq⟩⟩
      simpa only [Td_archive_row_d.values_d,Fin.addCases_left] using iw ([45,46].get c)
    have leftCut := td_graph_cut_l hZF node.2.1 (fn0_function_l (ZF.modelsKP hZF) fa).1 (keep 0 a ua)
    have rightCut := td_graph_cut_l hZF node.2.2.1 (fn0_function_l (ZF.modelsKP hZF) fb).1 (keep 1 b' ub)
    exact ⟨w 25,w 44,w 45,w 46,(node.2.1.2 n).mpr ⟨z,nz⟩,finite,realCut,leftCut,rightCut,sameTree ▸ node⟩
  exact ⟨d,N,W,P,j,S,Y,E,x,A,B,target,nt,cone,rootLeg,treeImage,comp,space,tree,alphabet,
    td_projection_of_nodes_l hZF hw (fn0_of_function_l (ZF.modelsKP hZF) fx) fa onto fb space tree nodes⟩

end YesMetaZFC.SetTheory.LargeCardinal
