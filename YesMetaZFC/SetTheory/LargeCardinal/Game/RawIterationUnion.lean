import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationCodeStep
import YesMetaZFC.Model.SetTheory.ClassResponse
import YesMetaZFC.SetTheory.Descriptive.Demand.InputIteration
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # 原迭代全部输入共用的响应表

完整原状态及两次实际原边已编码。反射闭包与集合选择固定同一张表；
每次查询直接执行已证明的实际后继，不随未来原对局重选树或共同图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_raw_iteration_choice_d (hZF : M.Models ZF)
    (ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K : M.Domain) : Prop where
  initial : Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r
  member : M.mem r X
  product : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) D X A
  function : Fn0_d D X K
  step : ∀ s x t p, Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s →
    (kp_pair_l (ZF.modelsKP hZF)).Codes p s x → Rd_entry_d p t K →
    Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A t ∧
      Tg_raw_iteration_edge_d hZF ω c₀ A x s t

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_iteration_code_d.choice_l
    {ω c₀ o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A r : M.Domain}
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (initial : Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r) :
    ∃ X D K, Tg_raw_iteration_choice_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K := by
  have hw : M.IsOmega ω := initial.elim fun _ h => h.2.tree.omega
  let ρ : Env M 11 := ⟨fun i => [ω,c₀,o,X₀,R₀,γ₀,D₀,C₀,S₀,A₀,A].get i,fun _ => ω⟩
  let V : UnarySchema 11 := { body := tg_raw_iteration_code_m (fun i => .bound i.succ) .newest }
  let φ : UnarySchema 13 := { body := tg_raw_iteration_edge_m (.bound 3) (.bound 4) (.bound 13) (.bound 1) (.bound 2) .newest }
  have valid s : V.denote ρ s ↔ Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s :=
    tg_raw_iteration_code_sat_l hZF ..
  have action s x t : φ.denote ((ρ.push s).push x) t ↔ Tg_raw_iteration_edge_d hZF ω c₀ A x s t :=
    tg_raw_iteration_edge_sat_l hZF ..
  obtain ⟨X,D,K,member,product,function,steps⟩ := ZFC.class_response_l I hZFC V φ ρ (a := r) hw (by
    intro s x hs hx
    obtain ⟨t,next,edge⟩ := ((valid s).mp hs).advance_l hZFC root cut hx
    exact ⟨t,(valid t).mpr next,(action s x t).mpr edge⟩)
  refine ⟨X,D,K,⟨initial,member,product,fn0_of_function_l (ZF.modelsKP hZF) function,?_⟩⟩
  intro s x t p state pair entry
  obtain ⟨next,edge⟩ := steps s x t p pair entry ((valid s).mpr state)
  exact ⟨(valid t).mp next,(action s x t).mp edge⟩

/-- 实际有限原状态直接构造统一表，不假设存在额外的工作嵌入。 -/
theorem Tg_raw_iteration_d.choice_l
    {ω c₀ o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A : M.Domain}
    {v : Fin 20 → M.Domain} {a : Fin 46 → M.Domain}
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (h : Tg_raw_iteration_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A v a) :
    ∃ r X D K, Rt_tuple_d (Fin.addCases (m := 20) (n := 46) (motive := fun _ => M.Domain) v a) r ∧
      Tg_raw_iteration_choice_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K := by
  obtain ⟨r,code,initial⟩ := h.pack_l hZF
  obtain ⟨X,D,K,choice⟩ := initial.choice_l hZFC root cut
  exact ⟨r,X,D,K,code,choice⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原响应表上的内部全 ω 运行

模型自己的 ω 归纳保持完整六十六项状态及准确外部轮号。每一步保存
实际输入和两条原边的全部几何；所有对局均使用预先固定的同一张表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_raw_iteration_run_d (ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain) : Prop where
  recursion : Gi_d hZF true ω X K r a f H
  rows : ∀ n s, Rd_entry_d n s H →
    Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s ∧ Rt_coord_d (18 : Fin 66) s n
  steps : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H →
    ∃ x, Gi_input_d hZF true ω a f i x ∧ Tg_raw_iteration_edge_d hZF ω c₀ A x s t

/-- 实际后继中的轮号后继与元组唯一性保证递归索引不发生漂移。 -/
private theorem tg_raw_iteration_edge_index_l {ω c₀ A x s t i j : M.Domain}
    (edge : Tg_raw_iteration_edge_d hZF ω c₀ A x s t) (old : Rt_coord_d (18 : Fin 66) s i)
    (succ : M.SuccessorOf j i) : Rt_coord_d (18 : Fin 66) t j := by
  obtain ⟨v,w,ps,pt,next⟩ := edge
  have index : v 18 = i := old.read_l v ps
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,step,_⟩ := next
  have step : M.SuccessorOf (w 18) i := index ▸ step
  exact ⟨w,pt,step.eq hZF.1 succ⟩

theorem Tg_raw_iteration_choice_d.validate_l
    {ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a f H : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (run : Gi_d hZF true ω X K r a f H) :
    Tg_raw_iteration_run_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  let ρ : Env M 12 := ⟨fun i => [ω,c₀,o,X₀,R₀,γ₀,D₀,C₀,S₀,A₀,A,H].get i,fun _ => ω⟩
  let e : Fin 11 → Term 14 := fun i => .bound (i.castAdd 1).succ.succ
  let φ : UnarySchema 12 := {
    body := .forallE (.imp (rd_entry0_m (.bound 1) .newest (.bound 13))
      (.conj (tg_raw_iteration_code_m e .newest) (rt_coord_m (18 : Fin 66) .newest (.bound 1))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,e] }
  have sat n : φ.denote ρ n ↔ ∀ s, Rd_entry_d n s H →
      Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s ∧ Rt_coord_d (18 : Fin 66) s n := by
    simp only [φ,e,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,Formula.satisfies_conj_iff,tg_raw_iteration_code_sat_l hZF,
      rt_coord_sat_l hZF.1]
    rfl
  have all : ∀ n, M.mem n ω → ∀ s, Rd_entry_d n s H →
      Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s ∧ Rt_coord_d (18 : Fin 66) s n := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz s hs
      have zo := hZF.1.eq_of_same_members z o (fun x => iff_of_false (hz x) (empty x))
      have sr := (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 z s r hs (run.2.1 z hz)
      exact ⟨sr.symm ▸ h.initial,sr.symm ▸ zo.symm ▸ zero⟩
    · intro i hi ih j succ t ht
      obtain ⟨s,_,hs⟩ := run.1.2.1 i hi
      obtain ⟨x,p,_,pair,entry⟩ := run.2.2 i j s t succ hs ht
      obtain ⟨next,edge⟩ := h.step s x t p (ih s hs).1 pair entry
      exact ⟨next,tg_raw_iteration_edge_index_l hZF edge (ih s hs).2 succ⟩
  have rows n s (hs : Rd_entry_d n s H) := all n (run.1.bound_l hs).1 s hs
  refine ⟨run,rows,?_⟩
  intro i j s t succ hs ht
  obtain ⟨x,p,input,pair,entry⟩ := run.2.2 i j s t succ hs ht
  exact ⟨x,input,(h.step s x t p (rows i s hs).1 pair entry).2⟩

theorem Tg_raw_iteration_choice_d.run_l
    {ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a f : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (ff : M.IsSetFunction I f) (range : ∀ i x, Rd_entry_d i x f → M.mem x A) :
    ∃ H, Tg_raw_iteration_run_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  obtain ⟨H,run⟩ := gi_exists_l hZF (b := true) hw h.product h.function h.member ha ff range
  exact ⟨H,h.validate_l hZF zero empty run⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 先由实际零轮固定响应表，再对任意完整原输入构造内部全 ω 运行。 -/
theorem Tg_raw_iteration_d.recursion_l
    {ω c₀ o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A a : M.Domain}
    {v : Fin 20 → M.Domain} {u : Fin 46 → M.Domain}
    (root : Zc_model_d J ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d J c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (initial : Tg_raw_iteration_d hZ ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A v u)
    (zero : v 18 = o) (empty : ∀ z, ¬ M.mem z o) (ha : M.mem a A) :
    ∃ r X D K, Tg_raw_iteration_choice_d hZ ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K ∧
      Rt_tuple_d (Fin.addCases (m := 20) (n := 46) (motive := fun _ => M.Domain) v u) r ∧
      ∀ f, Fn0_d ω A f → ∃ H,
        Tg_raw_iteration_run_d hZ ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H := by
  obtain ⟨r,X,D,K,code,choice⟩ := initial.choice_l hZFC root cut
  have index : Rt_coord_d (18 : Fin 66) r o := ⟨_,code,
    (Fin.addCases_left (m := 20) (n := 46) (motive := fun _ => M.Domain) (left := v) (right := u) 18).trans zero⟩
  refine ⟨r,X,D,K,choice,code,fun f ff => ?_⟩
  exact choice.run_l hZ index empty ha (fn0_function_l (ZF.modelsKP hZ) ff).1
    (fun _ _ h => (ff.bound_l h).2)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生六十六项运行的内部并树

每轮实际两条原边保持六列及旧终点的全部前驱。内部自然数归纳证明
树长共尾，再由公共有限框架取并。每个扩展器仍使用它原来所属节点的
完整根切片；根对象 γ₀ 始终由根关系解释，不转为背景序数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一原运行的六张并列：树序、模型、嵌入、操作、支撑及档案。 -/
structure Tg_raw_iteration_union_d (ω c o X₀ R₀ γ₀ D₀ C₀ H : M.Domain)
    (U : Fin 6 → M.Domain) : Prop where
  tree : It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3)
  critical : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o (U 1) (U 2) (U 3)
  levels_function : M.IsSetFunction I (U 4)
  levels : ∀ i L, Rd_entry_d i L (U 4) ↔ ∃ p κ F, Rd_entry_d i p (U 3) ∧ It_payload_d p κ L F
  archive : M.IsSequenceOfLength I (U 5) ω
  columns : ∀ b x, M.mem x (U b) ↔ Tg_run_value_d (n := 65) ⟨8+b.val,by omega⟩ H x
  restriction : ∀ i s (v : Fin 66 → M.Domain), Rd_entry_d i s H → Rt_tuple_d v s →
    ∀ x y, M.mem y (v 6) → (Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v 8))

/-- 支撑包含只用同一操作的 payload，档案包含只用实际追加方程。 -/
theorem Tg_raw_iteration_next_d.keep_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A x : M.Domain} {v w : Fin 66 → M.Domain}
    (h : Tg_raw_iteration_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A
      (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 20 i)))
    (g : Tg_raw_iteration_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A
      (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 20 i)))
    (step : Tg_raw_iteration_next_d hZF ω c A x
      (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
      (fun i => v (Fin.natAdd 20 i)) (fun i => w (Fin.natAdd 20 i))) :
    Tg_tree_keep_d (fun i => v (i.castAdd 52)) (fun i => w (i.castAdd 52)) := by
  obtain ⟨k,T,Q,G,E,j,mid,e,e',even,_,_,_,y,_,_,_,row,r,_,_,_,past⟩ := step
  obtain ⟨order,t,q,gmap,move⟩ := h.tree.extension_keep_l hZF e
  obtain ⟨order',t',q',gmap',move'⟩ := mid.extension_keep_l hZF e'
  have sub {a b : M.Domain} (s : M.SuccessorOf b a) : M.MemberSubset a b := fun x hx => (s x).mpr (Or.inl hx)
  have moves : M.MemberSubset (v 11) (w 11) := fun x hx => move' x (move x hx)
  have levels := it_levels_subset_l hZF.1 h.levels_function.1
    (fun i l => (h.levels i l).mp) (fun i l => (g.levels i l).mpr) moves
  have archive : M.MemberSubset (v 13) (w 13) := by
    intro p hp
    obtain ⟨i,s,pair⟩ := h.request.sequence.2.1.1 p hp
    obtain ⟨p',pair',hp'⟩ := (past i s).mpr (Or.inl ⟨p,pair,hp⟩)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  have keep (a : Fin 6) : M.MemberSubset (v ⟨8+a.val,by omega⟩) (w ⟨8+a.val,by omega⟩) := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))))) a
    · exact fun x hx => t' x (t x hx)
    · exact fun x hx => q' x (q x hx)
    · exact fun x hx => gmap' x (gmap x hx)
    · exact moves
    · exact levels
    · exact archive
  refine ⟨fun x hx => sub e'.1 x (sub e.1 x hx),
    fun i j hj => (order' i j (sub e.1 j hj)).trans (order i j hj),keep,?_⟩
  intro i hi
  have old := (e'.2.1 i (v 7)).mpr (Or.inl ((e.2.1 i (v 7)).mpr (Or.inl hi)))
  exact g.tree.diagram.order.trans i (v 7) (w 7) old (g.tree.diagram.map_bound_l hZF even)

variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

theorem Tg_raw_iteration_run_d.read_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    (v : Fin 66 → M.Domain) {i s} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
    Tg_raw_iteration_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A
      (fun j => v (j.castAdd 46)) (fun j => v (Fin.natAdd 20 j)) :=
  (h.rows i s hs).1.read_l hZF code

/-- 树长覆盖模型内部的全部轮号，不要求背景 ω 标准。 -/
theorem Tg_raw_iteration_run_d.span_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {i s m} (hs : Rd_entry_d i s H) (coord : Rt_coord_d (6 : Fin 66) s m) : M.mem i m := by
  have hw : M.IsOmega ω := by
    obtain ⟨v,code,_⟩ := coord
    exact (h.read_l hZF v hs code).tree.omega
  let ρ : Env M 1 := ⟨fun _ => H,fun _ => H⟩
  let φ : UnarySchema 1 := { body := set[2] ⟪∀ s m,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 2)⌝ₛ,s,⌜(.bound 1 : Term 2)⌝ₛ) →
    ⌜(rt_coord_m (6 : Fin 66))⌝ₚ(s,m) → ⌜(.newest : Term 2)⌝ₛ ∈ m⟫ }
  have sat n : φ.denote ρ n ↔ ∀ s m, Rd_entry_d n s H → Rt_coord_d (6 : Fin 66) s m → M.mem n m := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ s m, Rd_entry_d n s H → Rt_coord_d (6 : Fin 66) s m → M.mem n m := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz s m hs coord
      obtain ⟨v,code,eq⟩ := coord
      have state := h.read_l hZF v hs code
      exact eq ▸ state.tree.diagram.order.ordinal.empty_mem_of_nonempty (ZF.modelsKP hZF)
        ⟨v 7,state.successor.predecessor_mem⟩ hz
    · intro n hn ih j succ t m ht coord
      obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 n hn
      obtain ⟨x,_,v,w,ps,pt,step⟩ := h.steps n j s t succ hs ht
      have old := h.read_l hZF v hs ps
      have bound := ih s (v 6) hs ⟨v,ps,rfl⟩
      have eq := coord.read_l w pt
      obtain ⟨_,_,_,_,_,_,mid,e,e',_⟩ := step
      have sub : M.MemberSubset j (v 6) := by
        intro z hz
        rcases (succ z).mp hz with hz | eq
        · exact old.tree.diagram.order.ordinal.transitive n bound z hz
        · exact (hZF.1.eq_of_same_members z n eq).symm ▸ bound
      have jm : M.mem j (w 7) := Structure.IsOrdinal.mem_of_properSubset hZF.1
        (KP.successor_isOrdinal (ZF.modelsKP hZF) (hw.members_areOrdinals (ZF.modelsKP hZF) n hn) succ)
        mid.diagram.order.ordinal
        ⟨fun z hz => (e.1 z).mpr (Or.inl (sub z hz)),fun eq =>
          KP.mem_irrefl_d (ZF.modelsKP hZF) (v 6) (sub (v 6) ((eq (v 6)).mpr e.1.predecessor_mem))⟩
        (KP.difference_exists_d (ZF.modelsKP hZF) j (w 7))
      exact eq ▸ (e'.1 j).mpr (Or.inl jm)
  exact all i (h.recursion.1.bound_l hs).1 s m hs coord

/-- 两轮的合并及所有有限框架均由同一实际运行生产。 -/
theorem Tg_raw_iteration_run_d.frames_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H) :
    It_frames_d hZF (fun i : Fin 14 => i.castAdd 52) ω c X H := by
  have read {i s} {v : Fin 66 → M.Domain} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) := h.read_l hZF v hs code
  have hw : M.IsOmega ω := by
    obtain ⟨z,hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
    obtain ⟨_,_,state⟩ := (h.rows z r (h.recursion.2.1 z hz)).1
    exact state.tree.omega
  refine ⟨h.recursion.1,?_,?_⟩
  · intro i s hs
    obtain ⟨v,code,state⟩ := (h.rows i s hs).1
    obtain ⟨m,succ,hm⟩ := hw.1.2 (v 7) state.finite
    have finite : M.mem (v 6) ω := succ.eq hZF.1 state.successor ▸ hm
    exact ⟨v,code,state.tree,finite,h.span_l hZF hs ⟨v,code,rfl⟩,
      state.levels_function,state.levels,state.request.sequence.2.1⟩
  · have next (i j s t) (succ : M.SuccessorOf j i) (hs : Rd_entry_d i s H) (ht : Rd_entry_d j t H) :
        Tg_run_keep_d (fun i : Fin 14 => i.castAdd 52) s t := by
      obtain ⟨x,_,v,w,ps,pt,step⟩ := h.steps i j s t succ hs ht
      exact ⟨v,w,ps,pt,step.keep_l (v := v) (w := w) hZF (read hs ps) (read ht pt)⟩
    exact fun _ _ _ _ _ _ hs ht ps pt => Tg_run_keep_d.merge_l hZF hw h.recursion.1 next hs ht ps pt

/-- 完整所属模型、根边及根切片从操作所在的同一阶段进入并树。 -/
theorem Tg_raw_iteration_run_d.critical_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {Q G E : M.Domain}
    (models : ∀ x, M.mem x Q ↔ Tg_run_value_d (9 : Fin 66) H x)
    (maps : ∀ x, M.mem x G ↔ Tg_run_value_d (10 : Fin 66) H x)
    (moves : ∀ x, M.mem x E ↔ Tg_run_value_d (11 : Fin 66) H x) :
    Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E := by
  rintro i p κ L F ⟨b,pair,hb⟩ payload
  obtain ⟨v,n,s,hs,code,hb⟩ := (moves b).mp hb
  obtain ⟨c,Y,S,C,q,γ,V,t,⟨r,rp,hr⟩,model,⟨e,ep,z,zp,hz⟩,slice,lower⟩ :=
    (h.read_l hZF v hs code).critical i p κ L F ⟨b,pair,hb⟩ payload
  exact ⟨c,Y,S,C,q,γ,V,t,⟨r,rp,(models r).mpr ⟨v,n,s,hs,code,hr⟩⟩,model,
    ⟨e,ep,z,zp,(maps z).mpr ⟨v,n,s,hs,code,hz⟩⟩,slice,lower⟩

/-- 直接消费真实运行，构造完整 ω 原树、支撑列和全域档案列。 -/
theorem Tg_raw_iteration_run_d.union_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H) :
    ∃ U : Fin 6 → M.Domain, Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U := by
  have frames := h.frames_l hZF
  obtain ⟨z,hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨v,code,state⟩ := (h.rows z r (h.recursion.2.1 z hz)).1
  have hw := state.tree.omega
  obtain ⟨U,tree,lf,levels,archive,columns⟩ := frames.union_l hZF hw
  refine ⟨U,⟨tree,h.critical_l hZF (columns 1) (columns 2) (columns 3),lf,levels,
    ⟨hw.isOrdinal (ZF.modelsKP hZF),archive,?_⟩,columns,?_⟩⟩
  · intro i
    constructor
    · intro hi
      obtain ⟨j,succ,hj⟩ := hw.1.2 i hi
      obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 j hj
      obtain ⟨v,code,state⟩ := (h.rows j s hs).1
      have index := (h.rows j s hs).2.read_l v code
      obtain ⟨t,p,pair,hp⟩ := (state.request.sequence.2.2 i).mp (index.symm ▸ succ.predecessor_mem)
      exact ⟨t,p,pair,(columns 5 p).mpr ⟨v,j,s,hs,code,hp⟩⟩
    · rintro ⟨t,p,pair,hp⟩
      obtain ⟨v,j,s,hs,code,hp⟩ := (columns 5 p).mp hp
      have state := h.read_l hZF v hs code
      exact (hw.isOrdinal (ZF.modelsKP hZF)).transitive (v 18) state.request.finite i
        ((state.request.sequence.2.2 i).mpr ⟨t,p,pair,hp⟩)
  · exact fun _ _ _ hs code _ _ hy => frames.order_l hZF columns hs code hy

end YesMetaZFC.SetTheory.LargeCardinal
