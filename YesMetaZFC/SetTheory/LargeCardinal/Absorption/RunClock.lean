import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Links

/-! # 有限终点队列的内部终止与公平性

K、L 是真实自然数域上的游标列与终点列。未完成时两列保持，完成后游标
恰好递增一。对这些集合图的原公式归纳，证明每个任务在原终点的前一行完成，
再证明所有内部编号均被完成；不使用宿主自然数或外部任意谓词归纳。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Ab_clock_d (ω K L : M.Domain) : Prop where
  cursor : Fn0_d ω ω K
  endpoint : Fn0_d ω ω L
  bound : ∀ i k, Rd_entry_d i k K → M.MemberSubset k i
  future : ∀ i m, Rd_entry_d i m L → M.mem i m
  step : ∀ i j k m k' m', M.SuccessorOf j i →
    Rd_entry_d i k K → Rd_entry_d i m L → Rd_entry_d j k' K → Rd_entry_d j m' L →
      (M.mem j m ∧ k' = k ∧ m' = m) ∨ (j = m ∧ M.SuccessorOf k' k)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 在原终点之前，仍服务同一编号和同一终点。 -/
theorem Ab_clock_d.pending_l {ω K L i k m : M.Domain} (hw : M.IsOmega ω)
    (h : Ab_clock_d ω K L) (ik : Rd_entry_d i k K) (im : Rd_entry_d i m L) :
    ∀ j k' m', (i = j ∨ M.mem i j) → M.mem j m →
      Rd_entry_d j k' K → Rd_entry_d j m' L → k' = k ∧ m' = m := by
  let ρ : Env M 6 := ⟨fun a => [ω,i,k,m,K,L].get a,fun _ => i⟩
  let φ : UnarySchema 6 := { body := set[7] ⟪
    (⌜(.bound 2 : Term 7)⌝ₛ = ⌜(.bound 0 : Term 7)⌝ₛ ∨ ⌜(.bound 2 : Term 7)⌝ₛ ∈ ⌜(.bound 0 : Term 7)⌝ₛ) →
    ⌜(.bound 0 : Term 7)⌝ₛ ∈ ⌜(.bound 4 : Term 7)⌝ₛ → ∀ k' m',
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term 7)⌝ₛ,k',⌜(.bound 5 : Term 7)⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term 7)⌝ₛ,m',⌜(.bound 6 : Term 7)⌝ₛ) →
      k' = ⌜(.bound 3 : Term 7)⌝ₛ ∧ m' = ⌜(.bound 4 : Term 7)⌝ₛ⟫ }
  have read j : φ.denote ρ j ↔ (i = j ∨ M.mem i j) → M.mem j m →
      ∀ k' m', Rd_entry_d j k' K → Rd_entry_d j m' L → k' = k ∧ m' = m := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_forall_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all j : φ.denote ρ j := ZF.mem_ind_l M hZF I φ ρ (by
    intro j ih
    apply (read j).mpr
    intro above jm k' m' jk jl
    rcases above with rfl | ij
    · exact ⟨(fn0_function_l (ZF.modelsKP hZF) h.cursor).1.2 i k' k jk ik,
        (fn0_function_l (ZF.modelsKP hZF) h.endpoint).1.2 i m' m jl im⟩
    · obtain ⟨p,hp,succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF (h.cursor.bound_l jk).1 ⟨i,ij⟩
      obtain ⟨a,_,pa⟩ := h.cursor.2.1 p hp
      obtain ⟨b,_,pb⟩ := h.endpoint.2.1 p hp
      have ip : i = p ∨ M.mem i p := ((succ i).mp ij).elim Or.inr
        (fun eq => Or.inl (hZF.1.eq_of_same_members i p eq))
      have pm := (hw.members_areOrdinals (ZF.modelsKP hZF) m (h.endpoint.bound_l im).2).transitive j jm p succ.predecessor_mem
      obtain ⟨ea,eb⟩ := (read p).mp (ih p succ.predecessor_mem) ip pm a b pa pb
      subst a b
      exact (h.step p j k m k' m' succ pa pb jk jl).elim And.right
        (fun hm => (KP.mem_irrefl_d (ZF.modelsKP hZF) m (hm.1 ▸ jm)).elim)) j
  exact fun j k' m' above jm jk jl => (read j).mp (all j) above jm k' m' jk jl

/-- 每项有限任务在其原终点的前一行实际完成。 -/
theorem Ab_clock_d.finish_l {ω K L i k m : M.Domain} (hw : M.IsOmega ω)
    (h : Ab_clock_d ω K L) (ik : Rd_entry_d i k K) (im : Rd_entry_d i m L) :
    ∃ j, M.mem j ω ∧ (i = j ∨ M.mem i j) ∧ M.SuccessorOf m j ∧
      Rd_entry_d j k K ∧ Rd_entry_d j m L := by
  obtain ⟨j,hj,succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF (h.endpoint.bound_l im).2 ⟨i,h.future i m im⟩
  have ij : i = j ∨ M.mem i j := ((succ i).mp (h.future i m im)).elim Or.inr
    (fun eq => Or.inl (hZF.1.eq_of_same_members i j eq))
  obtain ⟨k',_,jk⟩ := h.cursor.2.1 j hj
  obtain ⟨m',_,jm⟩ := h.endpoint.2.1 j hj
  obtain ⟨rfl,rfl⟩ := h.pending_l hZF hw ik im j k' m' ij succ.predecessor_mem jk jm
  exact ⟨j,hj,ij,succ,jk,jm⟩

/-- 全部内部编号最终被服务并完成；配对像外的空号同样不会阻塞后续任务。 -/
theorem Ab_clock_d.fair_l {ω K L : M.Domain} (hw : M.IsOmega ω) (h : Ab_clock_d ω K L) :
    ∀ k, M.mem k ω → ∃ i m, M.mem i ω ∧ M.SuccessorOf m i ∧ Rd_entry_d i k K ∧ Rd_entry_d i m L := by
  let ρ : Env M 3 := ⟨fun a => [ω,K,L].get a,fun _ => K⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪∃ i m, i ∈ ⌜(.bound 1 : Term 4)⌝ₛ ∧
    ⌜Formula.isSuccessor⌝ₚ(m,i) ∧ ⌜rd_entry0_m⌝ₚ(i,⌜(.bound 0 : Term 4)⌝ₛ,⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(i,m,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have read k : φ.denote ρ k ↔ ∃ i m, M.mem i ω ∧ M.SuccessorOf m i ∧ Rd_entry_d i k K ∧ Rd_entry_d i m L := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_isSuccessor_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all := hw.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) (by
    intro o empty
    obtain ⟨z,empty',hz⟩ := hw.1.1
    have eq := hZF.1.eq_of_same_members z o (fun x => iff_of_false (empty' x) (empty x))
    subst z
    obtain ⟨k,_,ok⟩ := h.cursor.2.1 o hz
    obtain ⟨m,_,om⟩ := h.endpoint.2.1 o hz
    have eq := hZF.1.eq_of_same_members k o (fun x => iff_of_false (fun hx => empty x (h.bound o k ok x hx)) (empty x))
    subst k
    obtain ⟨i,hi,_,succ,ik,im⟩ := h.finish_l hZF hw ok om
    exact (read o).mpr ⟨i,m,hi,succ,ik,im⟩) (by
    intro k hk ih l succ
    obtain ⟨i,m,_,done,ik,im⟩ := (read k).mp ih
    have hm := (h.endpoint.bound_l im).2
    obtain ⟨k',_,mk⟩ := h.cursor.2.1 m hm
    obtain ⟨m',_,mm⟩ := h.endpoint.2.1 m hm
    have next : M.SuccessorOf k' k := (h.step i m k m k' m' done ik im mk mm).elim
      (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) m h.1).elim) And.right
    have eq := next.eq hZF.1 succ
    subst k'
    obtain ⟨j,hj,_,done',jl,jm⟩ := h.finish_l hZF hw mk mm
    exact (read l).mpr ⟨j,m',hj,done',jl,jm⟩)
  exact fun k hk => (read k).mp (all k hk)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真实吸收运行生产终止时钟与全部编号的实际命中

游标和终点由原记录的第 18、20 坐标唯一投影。它们的转移律直接来自
两种实际工作回合；完成行的同一条件属于原稠密集，也属于该行前缀泛型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

theorem Ab_run_d.clock_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F : M.Domain}
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) : ∃ K L, Ab_clock_d ω.val K L ∧
      (∀ i k, Rd_entry_d i k K ↔ ∃ r, Rd_entry_d i r F ∧ Rt_coord_d (18 : Fin 26) r k) ∧
      ∀ i m, Rd_entry_d i m L ↔ ∃ r, Rd_entry_d i r F ∧ Rt_coord_d (20 : Fin 26) r m := by
  have tuples i r (ir : Rd_entry_d i r F) : ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r :=
    (run.timing_l hZF.1 model trans ir).elim fun v h => ⟨v,h.1⟩
  have read {i r : M.Domain} {v : Fin 26 → M.Domain} (ir : Rd_entry_d i r F)
      (vr : Rt_tuple_d v r) : Ab_timing_d ω.val i v := by
    obtain ⟨w,wr,timing⟩ := run.timing_l hZF.1 model trans ir
    exact rt_tuple_inj_l wr vr ▸ timing
  have bound (a : Fin 26) (ha : a = 18 ∨ a = 20) i r (v : Fin 26 → M.Domain)
      (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r) : M.mem (v a) ω.val :=
    ha.elim (fun eq => eq.symm ▸ (read ir vr).cursor) (fun eq => eq.symm ▸ (read ir vr).endpoint)
  obtain ⟨K,kf,ks⟩ := rt_coordinate_l hZF (18 : Fin 26) run.function tuples (bound 18 (Or.inl rfl))
  obtain ⟨L,lf,ls⟩ := rt_coordinate_l hZF (20 : Fin 26) run.function tuples (bound 20 (Or.inr rfl))
  have coords {i r k m : M.Domain} {v : Fin 26 → M.Domain} (ir : Rd_entry_d i r F)
      (vr : Rt_tuple_d v r) (ik : Rd_entry_d i k K) (im : Rd_entry_d i m L) : v 18 = k ∧ v 20 = m := by
    have hk := (ks i (v 18)).mpr ⟨r,ir,v,vr,rfl⟩
    have hm := (ls i (v 20)).mpr ⟨r,ir,v,vr,rfl⟩
    exact ⟨(fn0_function_l (ZF.modelsKP hZF) kf).1.2 _ _ _ hk ik,
      (fn0_function_l (ZF.modelsKP hZF) lf).1.2 _ _ _ hm im⟩
  refine ⟨K,L,⟨kf,lf,?_,?_,?_⟩,ks,ls⟩
  · intro i k ik
    obtain ⟨r,ir,v,vr,eq⟩ := (ks i k).mp ik
    exact eq ▸ (read ir vr).bound
  · intro i m im
    obtain ⟨r,ir,v,vr,eq⟩ := (ls i m).mp im
    exact eq ▸ (read ir vr).future
  · intro i j k m k' m' succ ik im jk jm
    obtain ⟨r,_,ir⟩ := run.function.2.1 i (kf.bound_l ik).1
    obtain ⟨s,_,js⟩ := run.function.2.1 j (kf.bound_l jk).1
    obtain ⟨v,vr,timing⟩ := run.timing_l hZF.1 model trans ir
    obtain ⟨w,ws,_⟩ := run.timing_l hZF.1 model trans js
    obtain ⟨ek,em⟩ := coords ir vr ik im
    obtain ⟨ek',em'⟩ := coords js ws jk jm
    have ej := timing.stage.eq hZF.1 succ
    rcases run.clock_step_l hZF.1 model trans succ ir js vr ws with ⟨active,same,endEq⟩ | ⟨done,next⟩
    · exact Or.inl ⟨ej ▸ em ▸ active,ek'.symm.trans (same.trans ek),em'.symm.trans (endEq.trans em)⟩
    · exact Or.inr ⟨ej.symm.trans (done.trans em),ek' ▸ ek ▸ next⟩

/-- 每个编号都有真实完成行，所选条件在该行同时命中稠密集与前缀泛型。 -/
theorem Ab_run_d.fair_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F : M.Domain}
    (hΩ : M.IsOmega ω.val) (run : Ab_run_d I P ω.val cY.val Y.val S.val F) :
    ∀ k, M.mem k ω.val → ∃ i r, ∃ v : Fin 26 → M.Domain,
      Rd_entry_d i r F ∧ Rt_tuple_d v r ∧ v 18 = k ∧ v 7 = v 20 ∧ M.mem (v 21) (v 19) ∧ M.mem (v 21) (v 11) := by
  obtain ⟨K,L,clock,ks,ls⟩ := run.clock_l hZF model trans
  intro k hk
  obtain ⟨i,m,_,done,ik,im⟩ := clock.fair_l hZF hΩ k hk
  obtain ⟨r,ir,v,vr,ek⟩ := (ks i k).mp ik
  obtain ⟨w,wr,timing⟩ := run.timing_l hZF.1 model trans ir
  have ev := rt_tuple_inj_l vr wr
  subst v
  have eqm : w 20 = m := (fn0_function_l (ZF.modelsKP hZF) clock.endpoint).1.2 _ _ _
    ((ls i (w 20)).mpr ⟨r,ir,w,wr,rfl⟩) im
  have endEq : w 7 = w 20 := (timing.stage.eq hZF.1 done).trans eqm.symm
  exact ⟨i,r,w,ir,wr,ek,endEq,timing.hit,timing.done endEq⟩

end YesMetaZFC.SetTheory.LargeCardinal
