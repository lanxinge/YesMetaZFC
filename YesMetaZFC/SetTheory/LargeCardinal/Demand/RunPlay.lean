import YesMetaZFC.SetTheory.LargeCardinal.Demand.StateReal
import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchDepth

/-! # 每个实际后继保留原对局的已落实数字母

数字、根字母与历史沿同一原偶数边运输。历史包含来自实际三次追加，
故搬运后的旧事件仍是新请求历史中的事件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.real_step_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {i k s t n x : M.Domain} {v w : Fin 66 → M.Domain}
    (succ : M.SuccessorOf k i) (hs : Rd_entry_d i s H) (ht : Rd_entry_d k t H)
    (cv : Rt_tuple_d v s) (cw : Rt_tuple_d w t) (real : Td_real_d I v n x) : Td_real_d I w n x := by
  have vr := run.read_l hZF hs cv
  have wr := run.read_l hZF ht cw
  obtain ⟨_,_,v',w',cv',cw',next⟩ := run.steps i k s t succ hs ht
  have eq := rt_tuple_inj_l cv' cv
  subst v'
  have eq := rt_tuple_inj_l cw' cw
  subst w'
  obtain ⟨j',z,edge',hz,_,sub⟩ := next.history_l hZF wr
  obtain ⟨_,_,_,_,_,j,_,_,_,edge,_,images,_⟩ := next.2
  obtain ⟨q,points,head,_⟩ := images
  have eq := wr.tree.diagram.map_unique_l hZF edge' edge
  subst j'
  have lift {v : Fin 66 → M.Domain} {i s x y j : M.Domain}
      (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) (edge : It_map_d (v 9) x y j) : It_map_d (U 2) x y j := by
    obtain ⟨p,pair,entry⟩ := edge
    exact ⟨p,pair,u.entry_l hZF hs code 2 entry⟩
  have edge := lift ht cw edge
  have map := u.tree.diagram.elementary (v 5) (w 5) j (v 2) (v 0) (v 1) (w 2) (w 0) (w 1)
    edge (run.node_l hZF u hs cv) (run.node_l hZF u ht cw) vr.model wr.model
  obtain ⟨ev,pv⟩ := vr.native_base_l hZF
  obtain ⟨ew,pw⟩ := wr.native_base_l hZF
  have extV : Rf_ext_d I (v 0) (v 1) := fun a ha b hb same => congrArg Subtype.val
    (ev.eq_of_same_members ⟨a,ha⟩ ⟨b,hb⟩ (fun z => same z.val z.property))
  have extW : Rf_ext_d I (w 0) (w 1) := fun a ha b hb same => congrArg Subtype.val
    (ew.eq_of_same_members ⟨a,ha⟩ ⟨b,hb⟩ (fun z => same z.val z.property))
  obtain ⟨n₀,y,index,xy,event⟩ := real
  obtain ⟨n₁,_,index'⟩ := wr.numbers.injection.1.2.2 n (vr.numbers.injection.1.input_mem_of_pairMember index)
  have nn := (vr.numbers.omega_map_l I hZF u.tree.omega vr.model wr.model map extV extW wr.numbers).2 n n₀ n₁ index index'
  obtain ⟨y',_,yy⟩ := map.1.1.2.2 y (event.1 4)
  have rootImage := u.tree.diagram.comp (g 2) (v 5) (w 5) (v 3) j (w 3)
    (lift hs cv vr.origin) edge (lift ht cw wr.origin) x y y' xy yy
  have pc : Rd_entry_d (v 23) (w 23) j := by
    have eq : w 23 = q 4 := head 4
    exact eq.symm ▸ points 4
  have pb : Rd_entry_d (v 22) (w 22) j := by
    have eq : w 22 = q 3 := head 3
    exact eq.symm ▸ points 3
  have copied : Rr_truth_d I (w 0) (w 1) td_real_event0_m (fun i => [w 23,n₁,w 22,z,y'].get i) :=
    event.map_l I hZF u.tree.omega vr.model wr.model map td_real_event0_closed_l
      (Fin.cases pc (Fin.cases nn (Fin.cases pb (Fin.cases hz (Fin.cases yy (fun i => Fin.elim0 i))))))
  let P := smdl_structure_l I (R := w 1) wr.model.2.1
  let J := kpair_interpretation_l P ew pw
  obtain ⟨bounds,valid⟩ := copied
  obtain ⟨subBounds,subset⟩ := sub
  let ρ : Env P 5 := ⟨fun i => ⟨[w 23,n₁,w 22,z,y'].get i,bounds i⟩,fun _ => ⟨w 23,bounds 0⟩⟩
  let h : P.Domain := ⟨w 39,subBounds 0⟩
  have old : Tg_event_d J (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) :=
    (tg_event_sat_l J ew ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mp valid
  have inside : P.MemberSubset (ρ.bound 3) h := (Formula.satisfies_subset_iff _ (.bound 1) .newest).mp subset
  have new := old.mono_l J inside
  refine ⟨n₁,y',index',rootImage,Fin.cases (bounds 0) (Fin.cases (bounds 1) (Fin.cases (bounds 2)
    (Fin.cases (subBounds 0) (Fin.cases (bounds 4) (fun i => Fin.elim0 i))))),?_⟩
  exact (tg_event_sat_l J ew _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr new

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原对局条目沿内部全部阶段保持

归纳对象是实际行码上的纯公式；源模型的任意额外谓词不参与分离。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.real_mono_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    {i k s t n x : M.Domain} (ik : M.mem i k) (hs : Rd_entry_d i s H) (ht : Rd_entry_d k t H)
    (real : Td_real_record_d I s n x) : Td_real_record_d I t n x := by
  let ρ : Env M 0 := ⟨Fin.elim0,fun _ => H⟩
  let φ : BinarySchema 0 := { body := .forallE (.forallE
    (.imp (td_real_record_m (.bound 3) (.bound 1) .newest) (td_real_record_m (.bound 2) (.bound 1) .newest))) }
  have sat s t : φ.denote ρ s t ↔ ∀ n x, Td_real_record_d I s n x → Td_real_record_d I t n x := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,td_real_record_sat_l I hZF.1]
    rfl
  have chain := ZF.rel_chain_l I hZF φ ρ u.tree.omega (fn0_function_l (ZF.modelsKP hZF) run.recursion.1)
    (fun _ _ _ _ _ _ a b => (sat _ _).mpr fun n x hx => (sat _ _).mp b n x ((sat _ _).mp a n x hx)) (by
      intro i k s t succ hs ht
      apply (sat s t).mpr
      rintro n x ⟨v,cv,real⟩
      obtain ⟨w,cw,_⟩ := (run.rows k t ht).1
      exact ⟨w,cw,run.real_step_l hZF u succ hs ht cv cw real⟩)
  exact (sat s t).mp (chain i k s t ik hs ht) n x real

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从真实内部历史唯一构造完整原实数对局

任一已落字母在所有更晚阶段保持；任何两阶段可在同一后继比较。
替换据此构造一张背景 ω 函数图，定义不依赖选择哪条迭代树枝。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_run_play_d (I : kpair_convention_l.Interpretation M) (Ω A H F : M.Domain) : Prop :=
  Fn0_d Ω A F ∧ ∀ i x, Rd_entry_d i x F ↔ M.mem i Ω ∧
    ∃ n s, Rd_entry_d n s H ∧ Td_real_record_d I s i x

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {g : Fin 10 → M.Domain} {X K r a f H : M.Domain} {U : Fin 6 → M.Domain}

theorem Td_run_d.play_l (run : Td_run_d hZF g X K r a f H) (u : Td_union_d hZF g H U)
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4)) {A : M.Domain}
    (letters : ∀ x, M.mem x A ↔ M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4)) :
    ∃ F, Td_run_play_d I (g 0) A H F := by
  have hw := u.tree.omega
  have total i (hi : M.mem i (g 0)) : ∃ x, M.mem x A ∧ ∃ n s, Rd_entry_d n s H ∧ Td_real_record_d I s i x := by
    obtain ⟨n,succ,hn⟩ := hw.1.2 i hi
    obtain ⟨s,_,hs⟩ := run.recursion.1.2.1 n hn
    obtain ⟨v,code,state⟩ := (run.rows n s hs).1
    have index := (run.rows n s hs).2.read_l v code
    obtain ⟨x,hx,real⟩ := state.real_total_l hZF root letters (index.symm ▸ succ.predecessor_mem)
    exact ⟨x,hx,n,s,hs,v,code,real⟩
  have same {n s i x y} (hs : Rd_entry_d n s H)
      (hx : Td_real_record_d I s i x) (hy : Td_real_record_d I s i y) : x = y := by
    obtain ⟨v,cv,rx⟩ := hx
    obtain ⟨w,cw,ry⟩ := hy
    have eq := rt_tuple_inj_l cw cv
    subst w
    exact (run.read_l hZF hs cv).real_unique_l hZF root.model rx ry
  have unique i x y (hx : ∃ n s, Rd_entry_d n s H ∧ Td_real_record_d I s i x)
      (hy : ∃ n s, Rd_entry_d n s H ∧ Td_real_record_d I s i y) : x = y := by
    obtain ⟨n,s,hs,rx⟩ := hx
    obtain ⟨m,t,ht,ry⟩ := hy
    rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n (run.recursion.1.bound_l hs).1
      m (run.recursion.1.bound_l ht).1 with eq | nm | mn
    · have eq := hZF.1.eq_of_same_members n m eq
      subst m
      have eq := (fn0_function_l (ZF.modelsKP hZF) run.recursion.1).1.2 n t s ht hs
      exact same hs rx (eq ▸ ry)
    · exact same ht (run.real_mono_l hZF u nm hs ht rx) ry
    · exact same hs rx (run.real_mono_l hZF u mn ht hs ry)
  let ρ : Env M 1 := ⟨fun _ => H,fun _ => H⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ n s,
    ⌜rd_entry0_m⌝ₚ(n,s,⌜(.bound 2 : Term 3)⌝ₛ) ∧
      ⌜td_real_record_m⌝ₚ(s,⌜(.bound 1 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have sat i x : φ.denote ρ i x ↔ ∃ n s, Rd_entry_d n s H ∧ Td_real_record_d I s i x := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,td_real_record_sat_l I hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨F,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun i hi => (total i hi).imp fun x hx => (sat i x).mpr hx.2)
    (fun i _ x y hx hy => unique i x y ((sat i x).mp hx) ((sat i y).mp hy)) (by
      intro i x hi hx
      obtain ⟨y,hy,trace⟩ := total i hi
      exact (unique i y x trace ((sat i x).mp hx)) ▸ hy)
  exact ⟨F,fn0_of_function_l (ZF.modelsKP hZF) fn,
    fun i x => (graph i x).trans (and_congr_right fun _ => sat i x)⟩

end YesMetaZFC.SetTheory.LargeCardinal
