import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Links
import YesMetaZFC.Model.Forcing.Ground.ProductCoordinates
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Target
import YesMetaZFC.Model.Forcing.Ground.RealGround
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.SetTheory.ClassChoice
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.KeepTransfer
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedRankReals
import YesMetaZFC.SetTheory.Card.EnumerationPrefix
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding

/-! # 原泛型有限启动段的实际不变量

完整机器共用原 G 及其唯一坐标列 F；当前前缀是 F 的限制，当前任务仍属于 G。
各字段均由原零轮实际构造，原公式供内部有限递归直接使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Ab_original_d (Ω cY Y S G F : M.Domain) (v : Fin 26 → M.Domain) : Prop where
  machine : Ab_machine_d hZF Ω cY Y S v
  generic : Gset_d (v 5) (v 6) (v 5) (v 1) G
  sequence : M.IsSequenceOfLength I F Ω
  coordinates : ∀ i K, Rd_entry_d i K F ↔ M.mem i Ω ∧ Fp_coord_d (v 1) (v 5) G i K
  real_inside : M.mem (v 13) (v 1)
  cut : M.IsRestrictionOf I (v 10) F (v 7)
  projection : Fp_filter_project_d (v 8) (v 6) G (v 11)
  task : M.mem (v 21) G
  frozen : ∀ d, M.mem d G → Fp_ready_d I (v 7) (v 10) d

def ab_original_m {n} (Ω cY Y S G F : Term n) (v : Fin 26 → Term n) : Formula 1 n :=
  .conj (ab_machine_m Ω cY Y S v) (set[n] ⟪
    ⌜gset_m⌝ₚ(⌜v 5⌝ₛ,⌜v 6⌝ₛ,⌜v 5⌝ₛ,⌜v 1⌝ₛ,⌜G⌝ₛ) ∧
    ⌜Formula.isSequenceOfLength kpair_convention_l⌝ₚ(⌜F⌝ₛ,⌜Ω⌝ₛ) ∧
    (∀ i K, ⌜rd_entry0_m⌝ₚ(i,K,⌜F⌝ₛ) ↔ i ∈ ⌜Ω⌝ₛ ∧ ⌜fp_coord_m⌝ₚ(⌜v 1⌝ₛ,⌜v 5⌝ₛ,⌜G⌝ₛ,i,K)) ∧
    ⌜v 13⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜Formula.isRestriction kpair_convention_l⌝ₚ(⌜v 10⌝ₛ,⌜F⌝ₛ,⌜v 7⌝ₛ) ∧
    ⌜fp_filter_project_m⌝ₚ(⌜v 8⌝ₛ,⌜v 6⌝ₛ,⌜G⌝ₛ,⌜v 11⌝ₛ) ∧ ⌜v 21⌝ₛ ∈ ⌜G⌝ₛ ∧
    (∀ d, d ∈ ⌜G⌝ₛ → ⌜fp_ready_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 7⌝ₛ,⌜v 10⌝ₛ,d))⟫)

@[simp] theorem ab_original_closed_l {n} (Ω cY Y S G F : Term n) (v : Fin 26 → Term n)
    (hΩ : Ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = [])
    (hS : S.freeSupport = []) (hG : G.freeSupport = []) (hF : F.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) : (ab_original_m Ω cY Y S G F v).FreeClosed := by
  simp -implicitDefEqProofs [ab_original_m,Definitional.Formula.FreeClosed,hΩ,hcY,hY,hS,hG,hF,hv]

theorem ab_original_sat_l {n} (ρ : Env M n) (Ω cY Y S G F : Term n) (v : Fin 26 → Term n) :
    Formula.satisfies ρ (ab_original_m Ω cY Y S G F v) ↔
      Ab_original_d hZF (Ω.eval ρ) (cY.eval ρ) (Y.eval ρ) (S.eval ρ) (G.eval ρ) (F.eval ρ)
        (fun i => (v i).eval ρ) := by
  simp only [ab_original_m,Formula.satisfies_conj_iff,ab_machine_sat_l hZF,gset_sat_l hZF.1,
    Formula.satisfies_isSequenceOfLength_iff I hZF.1,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,rd_entry0_sat_l hZF.1,Formula.satisfies_mem_iff,fp_coord_sat_l hZF.1,
    Formula.satisfies_isRestriction_iff I,fp_filter_project_sat_l hZF.1,
    Formula.satisfies_imp_iff,fp_ready_sat_l I,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i⟩ => ⟨a,b,c,d,e,f,g,h,i⟩,
    fun h => ⟨h.machine,h.generic,h.sequence,h.coordinates,h.real_inside,h.cut,h.projection,h.task,h.frozen⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原泛型上的实际零轮机器

原 G 的长度一前缀成为首帧，初始稠密任务仍在 G 中选择。出生枚举、
空出生表、游标及单节点返回历史全部实际构造，统一地实数提供首行名字。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_original_zero_l {Ω c X R cY Y S π G : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω) (target : Smem_d I cY Y S) (embed : Smap_d I Ω c cY X Y π)
    {ω A P T : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A P T)
    (generic : Gset_d P.val T.val P.val X G) :
    ∃ o F r, ∃ w : Fin 26 → M.Domain,
      (∀ a, ¬ M.mem a o) ∧ Rt_tuple_d w r ∧
      Ab_original_d hZF Ω cY Y S G F w ∧ w 14 = o ∧ w 18 = o ∧
      ∀ k : Fin 7, w (k.castAdd 19) = ([c,X,R,π,A.val,P.val,T.val] : List M.Domain).get k := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  obtain ⟨x,_,F,seq,rows,prefixes⟩ := ab_frame_prefix_l hZF hΩ certificate source xt count embed hw sequence product generic
  obtain ⟨o,empty,ho⟩ := hw.1.1
  obtain ⟨n,succ,hn⟩ := hw.1.2 o ho
  obtain ⟨C,U,stage⟩ := product.prefix_l native hn
  obtain ⟨f,H,_,_,cut,projection,_,frame,frozen,tasks⟩ := prefixes n C U hn stage
  let v : Fin 14 → M.Domain := fun k =>
    [c,X,R,π,A.val,P.val,T.val,n.val,C.val,U.val,f,H,ω.val,x.val].get k
  change Ab_frame_d I Ω cY Y v at frame
  have full := smem_full_l I source xt
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have empty₀ a : ¬ M.mem a o.val := fun ha => (full o a).mp ha |>.elim fun b hb => empty b hb.1
  have successor := image_successor_l (hEN := hZF.1) Subtype.val inj full native.1 succ
  obtain ⟨z,E,e,B,emptyZ,birth⟩ := frame.birth_zero_l hZF hΩ
  have ez := hZF.1.eq_of_same_members z o.val (fun a => iff_of_false (emptyZ a) (empty₀ a))
  subst z
  obtain ⟨D,hD,letter,pick⟩ := birth.pick_l hZF hΩ (k := o.val) (fun _ h => h)
  let D₀ : N.Domain := ⟨D,hD⟩
  have dense := ((birth.family.members D).mp ((source.2 D E).mp letter).2.2).2
  obtain ⟨m,d,task,active,gd⟩ := tasks D₀
    ((source.dense_code_l I hZF.1 xt (ZF.modelsKP native) P T P D₀).mp dense)
  have queue : Ab_queue_d I Ω cY Y v o.val E e B o.val D m d :=
    ⟨frame,birth,successor,birth.history.natural,fun _ h => h,pick,task,
      fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) m (eq ▸ active)).elim⟩
  obtain ⟨L,Q,J,U₀,hist,code,returns⟩ := frame.history_zero_l hZF hΩ target empty₀ successor
  let w : Fin 26 → M.Domain := Fin.addCases (m := 14) (n := 12) v
    (fun k => [o.val,E,e,B,o.val,D,m,d,L,Q,J,U₀].get k)
  have head : ab_head_v w = v := by
    funext k
    simp only [ab_head_v,w,Fin.addCases_left]
  have machine : Ab_machine_d hZF Ω cY Y S w := ⟨head.symm ▸ queue,hist,code,returns⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) w
  refine ⟨o.val,F,r,w,empty₀,tuple,⟨machine,generic,seq,rows,x.property,cut,projection,gd,frozen⟩,rfl,rfl,?_⟩
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 G 内的实际任务选择及游标推进

沿用未完成的原条件，或在原块完成后从指定出生稠密集中选择新的 G 条件。
新任务严格超过当前前缀；游标递增只使用原队列已证明的完成余量。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ab_original_d.select_l {Ω cY Y S G F D : M.Domain} {v : Fin 26 → M.Domain}
    (h : Ab_original_d hZF Ω cY Y S G F v) (hΩ : M.IsOmega Ω)
    (hD : M.mem D (v 1)) (dense : Dense_set_d M (v 5) (v 6) (v 5) D) :
    ∃ m d, Ab_task_d I Ω (ab_head_v v) D m d ∧ M.mem (v 7) m ∧ M.mem d G := by
  have a := h.machine.queue.frame
  let N := smdl_structure_l I (R := v 2) a.model.1.2.1
  have native := ZFC.models_zf_l (a.theory.native_l I hZF hΩ)
  obtain ⟨hω,hA,hP,hT,hn,hC,hU,_⟩ := a.inside
  let ω : N.Domain := ⟨Ω,hω⟩
  let A : N.Domain := ⟨v 4,hA⟩
  let P : N.Domain := ⟨v 5,hP⟩
  let T : N.Domain := ⟨v 6,hT⟩
  let n : N.Domain := ⟨v 7,hn⟩
  let C : N.Domain := ⟨v 8,hC⟩
  let U : N.Domain := ⟨v 9,hU⟩
  let D₀ : N.Domain := ⟨D,hD⟩
  obtain ⟨hw,sequence,product,_⟩ := (ab_kernel_read_l I a.model a.transitive native ω A P T n C U).mp a.kernel
  have member {b c : N.Domain} : N.mem b c ↔ M.mem b.val c.val :=
    smem_member_l I a.model.1 a.model.2 b c
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction native (kp_pair_l (ZF.modelsKP native))
    sequence.function sequence.domain
  have fa : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω W :=
    ⟨sequence.function,sequence.domain,fun i hi => ((sequence.domain i).mp hi).elim fun δ edge =>
      ⟨δ,(range δ).mpr ⟨i,edge⟩,edge⟩⟩
  have g := ((a.model.generic_code_l I hZF.1 a.transitive (ZF.modelsKP native) P T P G).mp h.generic).2
  obtain ⟨m,d,hm,nm,gd,dD,fd⟩ := product.task_in_generic_l native hw ((member (b := n) (c := ω)).mpr a.index) fa g
    ((a.model.dense_code_l I hZF.1 a.transitive (ZF.modelsKP native) P T P D₀).mp dense)
  have bound := (hΩ.members_areOrdinals (ZF.modelsKP hZF) m.val (member.mp hm)).transitive n.val (member.mp nm)
  exact ⟨m.val,d.val,⟨hD,d.property,member.mp hm,bound,dense,member.mp dD,
    (ab_block_read_l I a.model a.transitive (ZF.modelsKP native) ω A m d).mpr fd,h.frozen d.val gd⟩,member.mp nm,gd⟩

theorem Ab_original_d.work_l {Ω cY Y S G F : M.Domain} {v : Fin 26 → M.Domain}
    (h : Ab_original_d hZF Ω cY Y S G F v) (hΩ : M.IsOmega Ω) :
    ∃ k D m d, Ab_work_d I Ω (ab_head_v v) (v 14) (v 17) (v 16)
      (v 18) (v 19) (v 20) (v 21) k D m d ∧ M.mem d G := by
  have q := h.machine.queue
  classical
  by_cases done : v 7 = v 20
  · obtain ⟨k,succ,hk⟩ := hΩ.1.2 (v 18) q.cursor
    have kt := (q.done done).1
    have bound : M.MemberSubset k (v 14) := by
      intro i hi
      rcases (succ i).mp hi with ik | eq
      · exact (hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 14) q.birth.history.natural).transitive (v 18) kt i ik
      · exact (hZF.1.eq_of_same_members i (v 18) eq).symm ▸ kt
    obtain ⟨D,hD,letter,pick⟩ := q.birth.pick_l hZF hΩ bound
    have dense := ((q.birth.family.members D).mp ((q.frame.model.2 D (v 15)).mp letter).2.2).2
    obtain ⟨m,d,task,active,gd⟩ := h.select_l hZF hΩ hD dense
    exact ⟨k,D,m,d,⟨hk,bound,pick,task,active,Or.inr ⟨done,succ⟩⟩,gd⟩
  · have active : M.mem (v 7) (v 20) := by
      have on := hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 7) q.frame.index
      have om := hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 20) q.task.finite
      rcases on.trichotomy hZF.1 om (KP.difference_exists_d (ZF.modelsKP hZF))
          (KP.intersection_exists_d (ZF.modelsKP hZF) (v 7) (v 20)) with eq | nm | mn
      · exact (done (hZF.1.eq_of_same_members (v 7) (v 20) eq)).elim
      · exact nm
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) (v 20) (q.task.remaining (v 20) mn)).elim
    exact ⟨v 18,v 19,v 20,v 21,⟨q.cursor,q.bound,q.pick,q.task,active,Or.inl ⟨active,rfl,rfl,rfl,rfl⟩⟩,h.task⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 G 下有限机器的真实后继

同一原坐标列追加一个滤子，模型和返回图保持原值。恒等根图运输出生表，
当前 G 条件继续被接受，达到任务终点时便命中同一原稠密集。
完整历史由这条真实根边延长；零轮与本后继共用原机器公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ab_original_d.step_l {Ω cY Y S G F : M.Domain} {v : Fin 26 → M.Domain}
    (h : Ab_original_d hZF Ω cY Y S G F v) (hΩ : M.IsOmega Ω) :
    ∃ r, ∃ w : Fin 26 → M.Domain, ∃ j K,
      Rt_tuple_d w r ∧ Ab_original_d hZF Ω cY Y S G F w ∧
      Ab_machine_step_d hZF Ω v w j K (v 13) ∧
      (∀ k : Fin 7, w (k.castAdd 19) = v (k.castAdd 19)) ∧
      ∀ a, M.mem a (v 1) → Rd_entry_d a a j := by
  -- 一、读取原帧，并从同一个 G 选择仍属 G 的实际工作块。
  have q := h.machine.queue
  have a := q.frame
  let N := smdl_structure_l I (R := v 2) a.model.1.2.1
  have native := ZFC.models_zf_l (a.theory.native_l I hZF hΩ)
  obtain ⟨hω,hA,hP,hT,hn,hC,hU,_⟩ := a.inside
  let ω : N.Domain := ⟨Ω,hω⟩
  let A : N.Domain := ⟨v 4,hA⟩
  let P : N.Domain := ⟨v 5,hP⟩
  let T : N.Domain := ⟨v 6,hT⟩
  let n : N.Domain := ⟨v 7,hn⟩
  let C : N.Domain := ⟨v 8,hC⟩
  let U : N.Domain := ⟨v 9,hU⟩
  let x : N.Domain := ⟨v 13,h.real_inside⟩
  obtain ⟨hw,sequence,product,_⟩ := (ab_kernel_read_l I a.model a.transitive native ω A P T n C U).mp a.kernel
  have member {b c : N.Domain} : N.mem b c ↔ M.mem b.val c.val := smem_member_l I a.model.1 a.model.2 b c
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I a.model a.transitive
  obtain ⟨k,D,m,d,work,gd⟩ := h.work_l hZF hΩ
  let m₀ : N.Domain := ⟨m,a.transitive Ω hω m work.task.finite⟩
  let d₀ : N.Domain := ⟨d,work.task.condition_inside⟩
  have fd := (ab_block_read_l I a.model a.transitive (ZF.modelsKP native) ω A m₀ d₀).mp work.task.block
  -- 二、唯一坐标成员方程识别重新构造的整列，下一帧仍截取原 F。
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction native (kp_pair_l (ZF.modelsKP native))
    sequence.function sequence.domain
  have fa : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω W :=
    ⟨sequence.function,sequence.domain,fun i hi => ((sequence.domain i).mp hi).elim fun δ edge =>
      ⟨δ,(range δ).mpr ⟨i,edge⟩,edge⟩⟩
  obtain ⟨F',seq,rows,prefixes⟩ := Smem_d.product_coordinates_l hZF a.model a.transitive native hw fa product h.generic
  have eF : F' = F := seq.2.1.1.eq_of_pairMember_iff hZF.1 h.sequence.2.1.1
    (fun i K => (rows i K).trans (h.coordinates i K).symm)
  subst F'
  obtain ⟨n',succ,hn'⟩ := hw.1.2 n ((member (b := n) (c := ω)).mpr a.index)
  obtain ⟨C',U',stage'⟩ := product.prefix_l native hn'
  obtain ⟨f,H,sf,cut,projection,accepted,frozen,gH⟩ := prefixes n' C' U' hn' stage'
  have successor := image_successor_l (hEN := hZF.1) Subtype.val inj full native.1 succ
  have keep : M.IsRestrictionOf I (v 10) f (v 7) := by
    refine ⟨a.function.1,fun i K => ?_⟩
    constructor
    · intro edge
      obtain ⟨hi,iK⟩ := (h.cut.2 i K).mp edge
      exact ⟨hi,(cut.2 i K).mpr ⟨(successor i).mpr (Or.inl hi),iK⟩⟩
    · rintro ⟨hi,edge⟩
      exact (h.cut.2 i K).mpr ⟨hi,((cut.2 i K).mp edge).2⟩
  obtain ⟨K,last⟩ := (sf.2.2 (v 7)).mp successor.predecessor_mem
  have fx := (smem_fn0_l I hZF.1 a.model a.transitive ω ω x).mpr a.real
  have g := ((a.model.generic_code_l I hZF.1 a.transitive (ZF.modelsKP native) C' U' C' H).mp gH).2
  have name := fn_bg_ground_l I hZF.1 a.model a.transitive native C' U' C' ω ω x H (stage'.order_l native) g fx
  have kernel := (ab_kernel_read_l I a.model a.transitive native ω A P T n' C' U').mpr ⟨hw,sequence,product,stage'⟩
  let v' : Fin 14 → M.Domain := fun i =>
    [v 0,v 1,v 2,v 3,v 4,v 5,v 6,n'.val,C'.val,U'.val,f,H,Ω,v 13].get i
  have frame : Ab_frame_d I Ω cY Y v' :=
    ⟨a.model,a.theory,a.transitive,a.count,a.returns,
      ⟨hω,hA,hP,hT,n'.property,C'.property,U'.property,hω⟩,
      member.mp hn',kernel,sf.2.1,sf.2.2,accepted,gH,a.real,name⟩
  have task : Ab_task_d I Ω v' D m d :=
    ⟨work.task.dense_inside,work.task.condition_inside,work.task.finite,
      fun i hi => ((successor i).mp hi).elim (work.task.remaining i)
        (fun eq => (hZF.1.eq_of_same_members i (v 7) eq).symm ▸ work.active),
      work.task.dense,work.task.hit,work.task.block,frozen d gd⟩
  have done (eq : n'.val = m) : M.mem d H := by
    have eq' : n' = m₀ := Subtype.ext eq
    have hd := (stage'.conditions d₀).mpr (eq'.symm ▸ fd)
    exact (accepted d).mpr ⟨member.mp hd,frozen d gd⟩
  -- 三、恒等根图保留源对象，并将实际出生枚举行及完整返回历史同步追加。
  obtain ⟨j,map,identity⟩ := smap_identity_l I hZF (X := v 1) (c := v 0) hΩ
  have fixed z (hz : M.mem z (v 1)) : Rd_entry_d z z j := (identity z z).mpr ⟨hz,rfl⟩
  have square : It_comp_d j (v 3) (v 3) := by
    refine ⟨a.returns.1.1.1.1,fun z y => ⟨?_,?_⟩⟩
    · intro zy
      exact ⟨z,fixed z (a.returns.1.1.input_mem_of_pairMember zy),zy⟩
    · rintro ⟨z',zz,zy⟩
      exact ((identity z z').mp zz).2.symm ▸ zy
  obtain ⟨t,E,e,B,depth,birth,family,table⟩ := q.birth.step_l hZF hΩ a.model a.model
    a.transitive a.transitive map (ZF.modelsKP native) (ZF.modelsKP native) a.count
    (P := P) (T := T) (P' := P) (T' := T) (fixed _ hP) (fixed _ hT)
  have et : t = v 7 := depth.eq hZF.1 q.stage
  have birth' : Ab_birth_d I Ω (v 1) (v 2) (v 5) (v 6) (v 7) E e B := by
    simpa only [et] using! birth
  have available : M.mem k (v 7) := ordinal_down_l (ZF.modelsKP hZF)
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) k work.cursor)
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 7) a.index) work.bound q.stage.predecessor_mem
  have pick := work.pick.step_l I (e' := e) q.stage table (fixed D work.task.dense_inside)
  have queue : Ab_queue_d I Ω cY Y v' (v 7) E e B k D m d :=
    ⟨frame,birth',successor,work.cursor,
      (hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 7) a.index).transitive k available,
      pick,task,fun eq => ⟨available,done eq⟩⟩
  have step : Ab_step_d I Ω (ab_head_v v) v' (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21)
      E B k D m d j K (v 13) :=
    ⟨⟨D,d,work,fixed D work.task.dense_inside,fixed d work.task.condition_inside⟩,
      map,square,successor,keep,last,fixed _ hA,fixed _ hP,fixed _ hT,fixed _ hC,
      fun z hz => fixed z (a.transitive (v 8) hC z hz),family,table,rfl⟩
  obtain ⟨L,Q,J,U₀,hist,extension,code,returns,edge⟩ :=
    step.history_l hZF hΩ a.model frame h.machine.history q.stage h.machine.code h.machine.returns
  let w : Fin 26 → M.Domain := Fin.addCases (m := 14) (n := 12) v'
    (fun i => [v 7,E,e,B,k,D,m,d,L,Q,J,U₀].get i)
  have head : ab_head_v w = v' := by
    funext i
    simp only [ab_head_v,w,Fin.addCases_left]
  have machine : Ab_machine_d hZF Ω cY Y S w := ⟨head.symm ▸ queue,hist,code,returns⟩
  have original : Ab_original_d hZF Ω cY Y S G F w :=
    ⟨machine,h.generic,h.sequence,h.coordinates,h.real_inside,cut,projection,gd,frozen⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) w
  refine ⟨r,w,j,K,tuple,original,⟨head.symm ▸ step,rfl,extension.keep_l hZF h.machine.history,edge⟩,?_,fixed⟩
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原泛型启动记录及恒等转移的内部公式

原七项源坐标打包为同一个 B，统一实数 x 与原 G、F 一同固定。
记录及恒等根边转移均有实际满足关系，供模型内部递归读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Ab_original_record_d (Ω cY Y S G F B x i r : M.Domain) : Prop :=
  ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r ∧ Ab_original_d hZF Ω cY Y S G F v ∧
    Rt_tuple_d (fun k : Fin 7 => v (k.castAdd 19)) B ∧ v 14 = i ∧ v 13 = x

def ab_original_record_m {n} (Ω cY Y S G F B x i r : Term n) : Formula 1 n :=
  let g : Term n → Term (26+n) := fun t => t.rename (Fin.natAdd 26)
  let v : Fin 26 → Term (26+n) := fun k => .bound (k.castAdd n)
  rb_exists_m (.conj (rt_tuple_m v (g r)) (.conj (ab_original_m (g Ω) (g cY) (g Y) (g S) (g G) (g F) v)
    (.conj (rt_tuple_m (fun k : Fin 7 => v (k.castAdd 19)) (g B))
      (.conj (Formula.extensionalEq (v 14) (g i)) (Formula.extensionalEq (v 13) (g x))))))

@[simp] theorem ab_original_record_closed_l {n} (Ω cY Y S G F B x i r : Term n)
    (hΩ : Ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = []) (hS : S.freeSupport = [])
    (hG : G.freeSupport = []) (hF : F.freeSupport = []) (hB : B.freeSupport = []) (hx : x.freeSupport = [])
    (hi : i.freeSupport = []) (hr : r.freeSupport = []) : (ab_original_record_m Ω cY Y S G F B x i r).FreeClosed := by
  simp -implicitDefEqProofs [ab_original_record_m,Definitional.Formula.FreeClosed,hΩ,hcY,hY,hS,hG,hF,hx,hi]
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr),
    rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hB)⟩

theorem ab_original_record_sat_l {n} (ρ : Env M n) (Ω cY Y S G F B x i r : Term n) :
    Formula.satisfies ρ (ab_original_record_m Ω cY Y S G F B x i r) ↔
      Ab_original_record_d hZF (Ω.eval ρ) (cY.eval ρ) (Y.eval ρ) (S.eval ρ) (G.eval ρ)
        (F.eval ρ) (B.eval ρ) (x.eval ρ) (i.eval ρ) (r.eval ρ) := by
  simp only [ab_original_record_m,Ab_original_record_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hZF.1,ab_original_sat_l hZF,Formula.satisfies_extensionalEq_iff_eq hZF.1,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left]

def Ab_original_step_d (Ω r s x : M.Domain) : Prop :=
  ∃ v w : Fin 26 → M.Domain, ∃ j K, Rt_tuple_d v r ∧ Rt_tuple_d w s ∧
    Ab_machine_step_d hZF Ω v w j K x ∧ ∀ a, M.mem a (v 1) → Rd_entry_d a a j

def ab_original_step_m {n} (Ω r s x : Term n) : Formula 1 n :=
  let g : Term n → Term (54+n) := fun t => t.rename (Fin.natAdd 54)
  let u : Fin 54 → Term (54+n) := fun k => .bound (k.castAdd n)
  let v : Fin 26 → Term (54+n) := fun k => u (k.castAdd 28)
  let w : Fin 26 → Term (54+n) := fun k => u (Fin.natAdd 26 (k.castAdd 2))
  rb_exists_m (.conj (rt_tuple_m v (g r)) (.conj (rt_tuple_m w (g s))
    (.conj (ab_machine_step_m (g Ω) v w (u 52) (u 53) (g x))
      (Formula.forallMem (v 1) (rd_entry0_m .newest .newest (u 52).weaken)))))

@[simp] theorem ab_original_step_closed_l {n} (Ω r s x : Term n)
    (hΩ : Ω.freeSupport = []) (hr : r.freeSupport = []) (hs : s.freeSupport = []) (hx : x.freeSupport = []) :
    (ab_original_step_m Ω r s x).FreeClosed := by
  simp -implicitDefEqProofs [ab_original_step_m,Definitional.Formula.FreeClosed,hΩ,hx]
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr),
    rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs)⟩

theorem ab_original_step_sat_l {n} (ρ : Env M n) (Ω r s x : Term n) :
    Formula.satisfies ρ (ab_original_step_m Ω r s x) ↔
      Ab_original_step_d hZF (Ω.eval ρ) (r.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [ab_original_step_m,rb_exists_sat_l,Formula.satisfies_conj_iff,rt_tuple_sat_l hZF.1,
    ab_machine_step_sat_l hZF,Formula.satisfies_forallMem_iff,rd_entry0_sat_l hZF.1,
    rb_old_eval_l,Term.eval_bound,Fin.addCases_left,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨u,first,second,step,points⟩
    exact ⟨(fun k => u (k.castAdd 28)),(fun k => u (Fin.natAdd 26 (k.castAdd 2))),u 52,u 53,first,second,step,points⟩
  · rintro ⟨v,w,j,K,first,second,step,points⟩
    let tail : Fin 28 → M.Domain := Fin.addCases (m := 26) (n := 2) w (Fin.cases j (fun _ => K))
    let u : Fin 54 → M.Domain := Fin.addCases (m := 26) (n := 28) v tail
    have left : (fun k : Fin 26 => u (k.castAdd 28)) = v := by
      funext k
      simp only [u,Fin.addCases_left]
    have right : (fun k : Fin 26 => u (Fin.natAdd 26 (k.castAdd 2))) = w := by
      funext k
      simp only [u,tail,Fin.addCases_right,Fin.addCases_left]
    exact ⟨u,left.symm ▸ first,right.symm ▸ second,left.symm ▸ right.symm ▸ step,points⟩

/-- 原公式记录的后继由实际恒等机器后继产生，原七项源坐标与实数均保持。 -/
theorem Ab_original_record_d.step_l {Ω cY Y S G F B x i j r : M.Domain}
    (h : Ab_original_record_d hZF Ω cY Y S G F B x i r) (hΩ : M.IsOmega Ω)
    (succ : M.SuccessorOf j i) :
    ∃ s, Ab_original_record_d hZF Ω cY Y S G F B x j s ∧ Ab_original_step_d hZF Ω r s x := by
  obtain ⟨v,tuple,original,header,index,real⟩ := h
  obtain ⟨s,w,e,K,tuple',original',step,same,points⟩ := original.step_l hZF hΩ
  have stage : M.SuccessorOf (v 7) i := index ▸ original.machine.queue.stage
  have nextIndex : w 14 = j := step.2.1.trans (stage.eq hZF.1 succ)
  have newHeader : Rt_tuple_d (fun k : Fin 7 => w (k.castAdd 19)) B := by
    rw [show (fun k : Fin 7 => w (k.castAdd 19)) = (fun k => v (k.castAdd 19)) from funext same]
    exact header
  exact ⟨s,⟨w,tuple',original',newHeader,nextIndex,step.1.real.trans real⟩,
    v,w,e,K,tuple,tuple',real ▸ step,points⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 G 上的内部启动历史及任意有限终点

原零轮及恒等后继进入同一对象公式递归，产生实际背景记录列。
每个内部有限终点都有同列的有限限制及完整机器历史；原源、G、坐标列和实数始终相同。
这里只构造原泛型启动段，不把它当作已经覆盖测试壳实数的吸收运行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_original_run_l {Ω c X R cY Y S π G : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω) (target : Smem_d I cY Y S) (embed : Smap_d I Ω c cY X Y π)
    {ω A P T : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A P T)
    (generic : Gset_d P.val T.val P.val X G) :
    ∃ o F B x r₀ Z H, (∀ a, ¬ M.mem a o) ∧
      Rt_tuple_d (fun k : Fin 7 => ([c,X,R,π,A.val,P.val,T.val] : List M.Domain).get k) B ∧
      M.mem x X ∧ M.IsSetFunctionFromTo I H Ω Z ∧ Rd_entry_d o r₀ H ∧
      (∀ i r, Rd_entry_d i r H → Ab_original_record_d hZF Ω cY Y S G F B x i r) ∧
      (∀ i j r s, M.SuccessorOf j i → Rd_entry_d i r H → Rd_entry_d j s H →
        Ab_original_step_d hZF Ω r s x) ∧
      ∀ i, M.mem i Ω → ∃ n K r, M.SuccessorOf n i ∧ M.mem n Ω ∧ M.IsSequenceOfLength I K n ∧
        M.IsRestrictionOf I K H n ∧ Rd_entry_d i r K ∧ Ab_original_record_d hZF Ω cY Y S G F B x i r := by
  obtain ⟨o,F,r₀,v,empty,tuple,original,index,_,same⟩ :=
    ab_original_zero_l hZF hΩ certificate source xt count target embed hw sequence product generic
  obtain ⟨B,header⟩ := rt_tuple_exists_l (ZF.modelsKP hZF)
    (fun k : Fin 7 => ([c,X,R,π,A.val,P.val,T.val] : List M.Domain).get k)
  have vB : Rt_tuple_d (fun k : Fin 7 => v (k.castAdd 19)) B := by
    rw [funext same]
    exact header
  let x := v 13
  let ρ : Env M 8 := ⟨fun k => [Ω,cY,Y,S,G,F,B,x].get k,fun _ => Ω⟩
  let V : BinarySchema 8 := { body := (ab_original_record_m (.bound 2) (.bound 3) (.bound 4) (.bound 5)
    (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 1) .newest) }
  let φ : UnarySchema 10 := { body := ab_original_step_m (.bound 3) (.bound 1) .newest (.bound 10) }
  have valid i r : V.denote ρ i r ↔ Ab_original_record_d hZF Ω cY Y S G F B x i r := ab_original_record_sat_l hZF ..
  have move i r s : φ.denote ((ρ.push i).push r) s ↔ Ab_original_step_d hZF Ω r s x := ab_original_step_sat_l hZF ..
  obtain ⟨Z,H,fn,start,rows,steps⟩ := ZFC.class_indexed_choice_l I hZFC V φ ρ hΩ empty
    ((valid o r₀).mpr ⟨v,tuple,original,vB,index,rfl⟩) (by
      intro i j r _ succ old
      obtain ⟨s,new,step⟩ := ((valid i r).mp old).step_l hZF hΩ succ
      exact ⟨s,(valid j s).mpr new,(move i r s).mpr step⟩)
  have row i r (ir : Rd_entry_d i r H) := (valid i r).mp (rows i r ir)
  have hx : M.mem x X := by simpa only [show v 1 = X from same 1] using! original.real_inside
  refine ⟨o,F,B,x,r₀,Z,H,empty,header,hx,fn,start,row,
    fun i j r s succ ir js => (move i r s).mp (steps i j r s succ ir js),?_⟩
  intro i hi
  obtain ⟨n,succ,hn⟩ := hΩ.1.2 i hi
  obtain ⟨K,cut⟩ := ZF.exists_restriction hZF I H n
  have finite := cut.isSetFunctionFromTo fn (hΩ.transitive (ZF.modelsKP hZF) n hn)
  obtain ⟨r,_,ir⟩ := fn.2.2 i hi
  exact ⟨n,K,r,succ,hn,⟨hΩ.members_areOrdinals (ZF.modelsKP hZF) n hn,finite.1,finite.2.1⟩,
    cut,(cut.2 i r).mpr ⟨succ.predecessor_mem,ir⟩,row i r ir⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原有限启动历史沿反坍塌进入测试壳

有限记录图及其实际值域作为已有有限参数取原像。函数图的 Δ₀ 方程
保留整个定义域；原记录和相邻转移只使用已经选定的两个反射公式。
不要求测试壳满足 ZF、KP，也不另外假设壳内有限递归。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_relative_finite_l {ω T α V d Q P c R π : M.Domain} {a b}
    {φ : Formula 1 a} {hc : φ.FreeClosed} {v : Fin b → M.Domain}
    (test : Rf_hull_d hZF ω T (ab_test_queries_l φ hc) v α V d Q P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    {cY Y S x Z K : (smdl_structure_l I (R := R) test.model.1.2.1).Domain}
    {C W U n L B : M.Domain} (hn : M.mem n ω) (fx : Fn0_d ω ω x.val)
    (code : Rd_entry_d cY.val C π) (domain : Rd_entry_d Y.val W π) (relation : Rd_entry_d S.val U π)
    (range : Rd_entry_d Z.val B π) (graph : Rd_entry_d K.val L π)
    (fn : M.IsSetFunctionFromTo I L n B)
    (rows : ∀ i r, Rd_entry_d i r L → Ab_record_d hZF ω C W U i x.val r)
    (steps : ∀ i j r s, M.SuccessorOf j i → Rd_entry_d i r L → Rd_entry_d j s L →
      Ab_record_step_d hZF ω r s x.val) :
    M.IsSetFunctionFromTo I K.val n P ∧
      (∀ i r, Rd_entry_d i r K.val → Ab_relative_d P ω cY.val Y.val S.val i x.val r) ∧
      ∀ i j r s, M.SuccessorOf j i → Rd_entry_d i r K.val → Rd_entry_d j s K.val →
        Ab_relative_step_d P ω r s x.val := by
  let N := smdl_structure_l I (R := R) test.model.1.2.1
  let Ω : N.Domain := ⟨ω,hω⟩
  have vt := v_transitive_l I test.rank
  have natural := test.map.natural_l hZF hw test.transitive vt test.model test.target hω
  have fw := test.map.omega_l I hZF hw test.transitive vt test.model test.target hω
  have fixed := test.real_fixed_l hZF hw hω x.property fx
  have fK := fn0_function_l (ZF.modelsKP hZF)
    (((test.map.function_l hZF hw test.transitive vt test.model test.target (natural n hn) range graph).mpr
      (fn0_of_function_l (ZF.modelsKP hZF) fn)).mono_target_l (test.transitive Z.val Z.property))
  have inside i (hi : M.mem i n) := (hw.transitive (ZF.modelsKP hZF)) n hn i hi
  have lift i r (ir : Rd_entry_d i r K.val) : ∃ r', Rd_entry_d i r' L ∧ Rd_entry_d r r' π := by
    obtain ⟨r',_,rr⟩ := test.map.1.1.2.2 r (fK.output_mem_of_pairMember ir)
    exact ⟨r',(test.map.entry_l hZF hw test.transitive vt test.model test.target
      (natural i (inside i (fK.input_mem_of_pairMember ir))) rr graph).mp ir,rr⟩
  refine ⟨fK,?_,?_⟩
  · intro i r ir
    obtain ⟨r',ir',rr⟩ := lift i r ir
    have hi := inside i (fK.input_mem_of_pairMember ir)
    let i₀ : N.Domain := ⟨i,test.transitive ω hω i hi⟩
    let r₀ : N.Domain := ⟨r,fK.output_mem_of_pairMember ir⟩
    let ρ : Env N 7 := ⟨fun k => [Ω,cY,Y,S,i₀,x,r₀].get k,fun _ => Ω⟩
    let η : Env M 7 := ⟨fun k => [ω,C,W,U,i,x.val,r'].get k,fun _ => ω⟩
    have images : ∀ k, Rd_entry_d (ρ.bound k).val (η.bound k) π :=
      Fin.cases fw (Fin.cases code (Fin.cases domain (Fin.cases relation
        (Fin.cases (natural i hi) (Fin.cases fixed (Fin.cases rr (fun k => Fin.elim0 k)))))))
    have old := (ab_record_sat_l hZF η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).mpr (rows i r' ir')
    exact (ab_relative_read_l I test.model test.transitive Ω cY Y S i₀ x r₀).mpr
      ((test.formula_l hZF hw ab_record_native_m ab_record_native_closed_l
        (by simp [ab_test_queries_l]) ρ η images).mpr old)
  · intro i j r s succ ir js
    obtain ⟨r',ir',rr⟩ := lift i r ir
    obtain ⟨s',js',ss⟩ := lift j s js
    let r₀ : N.Domain := ⟨r,fK.output_mem_of_pairMember ir⟩
    let s₀ : N.Domain := ⟨s,fK.output_mem_of_pairMember js⟩
    let ρ : Env N 4 := ⟨fun k => [Ω,r₀,s₀,x].get k,fun _ => Ω⟩
    let η : Env M 4 := ⟨fun k => [ω,r',s',x.val].get k,fun _ => ω⟩
    let ψ := ab_record_step_m (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)
    have images : ∀ k, Rd_entry_d (ρ.bound k).val (η.bound k) π :=
      Fin.cases fw (Fin.cases rr (Fin.cases ss (Fin.cases fixed (fun k => Fin.elim0 k))))
    have old := (ab_record_step_sat_l hZF η (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mpr (steps i j r' s' succ ir' js')
    exact (ab_relative_step_read_l I test.model test.transitive Ω r₀ s₀ x).mpr
      ((test.formula_l hZF hw ψ (by simp -implicitDefEqProofs [ψ])
        (by simp [ab_test_queries_l,ψ]) ρ η images).mpr old)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限反射恢复原队列及完整返回历史

先反射记录的有限坐标矩阵。像帧的可数性单射仍在极限秩层中，
故反坍塌固定传递行模型及其全部成员，再识别原代码、乘积和历史列。
枚举行与出生表的输入由自然数对界定，输出属于固定行模型，因而两张原图也固定。
完整 ZFC 与内部初等性来自同一原对象，不要求测试壳满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_relative_queue_l {ω T α V d Q P c R π : M.Domain} {n m}
    {ψ : Formula 1 n} {hc : ψ.FreeClosed} {a : Fin m → M.Domain}
    (h : Rf_hull_d hZF ω T (ab_test_queries_l ψ hc) a α V d Q P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    (cY Y S i x r : (smdl_structure_l I (R := R) h.model.1.2.1).Domain)
    (row : Ab_relative_d P ω cY.val Y.val S.val i.val x.val r.val) :
    ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r.val ∧
      Ab_queue_d I ω cY.val Y.val (ab_head_v v) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21) ∧
      Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω (v 7) (v 22) (v 23) (v 24) cY.val Y.val S.val (v 25) := by
  let N := smdl_structure_l I (R := R) h.model.1.2.1
  have ext := smem_ext_l I h.model.1 h.model.2 h.transitive hZF.1
  have full := smem_full_l I h.model h.transitive
  let Ω : N.Domain := ⟨ω,hω⟩
  let ρ : Env N 7 := ⟨fun k => [Ω,cY,Y,S,i,x,r].get k,fun _ => Ω⟩
  let φ := ab_record_body_m (.bound 0 : Term 7) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
  -- 读取原坐标只需要外延性。
  obtain ⟨v,body⟩ := (rb_exists_sat_l ρ φ).mp
    ((ab_relative_read_l I h.model h.transitive Ω cY Y S i x r).mp row)
  let τ : Env N 33 := ⟨Fin.addCases (m := 26) (n := 7) (motive := fun _ => N.Domain) v ρ.bound,ρ.free⟩
  let g (t : Term 7) : Term 33 := t.rename (Fin.natAdd 26)
  let b (k : Fin 26) : Term 33 := .bound (k.castAdd 7)
  have tuple : Rt_tuple_d v r := by
    simpa only [b,g,τ,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] using!
      (rt_tuple_sat_l ext τ b (g (.bound 6))).mp body.1
  -- 同一有限矩阵在背景成立，因而像帧携带真实的完整 ZFC 证书。
  obtain ⟨w,images⟩ := Classical.axiomOfChoice (fun k : Fin 33 =>
    (h.map.1.1.2.2 (τ.bound k).val (τ.bound k).property).imp fun y hy => hy.2)
  let η : Env M 33 := ⟨w,fun _ => ω⟩
  have copied := (h.formula_l hZF hw φ (by simp -implicitDefEqProofs [φ])
    (by simp [ab_test_queries_l,φ]) τ η images).mp body
  have state : Ab_machine_d hZF (w 26) (w 27) (w 28) (w 29) (fun k => w (k.castAdd 7)) := by
    have machine := copied.2.1
    exact (ab_machine_sat_l hZF η _ _ _ _ _).mp machine
  have vt := v_transitive_l I h.rank
  have fw := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have ew : w 26 = ω := h.map.1.1.1.2 ω (w 26) ω (images 26) fw
  have queue := ew ▸ state.queue
  have out := queue.frame
  -- 像模型的可数性见证留在极限秩层中，回收后固定原代码及全部成员。
  obtain ⟨fc,fx,point⟩ := h.model_fixed_l hZF hw hω (images 0) out.model out.transitive out.count
  have ec : (v 0).val = w 0 := h.map.1.2 _ _ _ (images 0) fc
  have ex : w 1 = (v 1).val := (h.map.1.2 _ _ _ (images 1) fx).symm
  have er : (v 2).val = w 2 := h.map.relation_preimage_l hZF hw h.transitive vt h.model h.target
    fx point (images 2) out.model.1.2.2
  have eqk (k : Fin 26) (hk : M.mem (w (k.castAdd 7)) (w 1)) : w (k.castAdd 7) = (v k).val :=
    (h.map.1.2 _ _ _ (by simpa only [τ,Fin.addCases_left] using images (k.castAdd 7))
      (point _ hk)).symm
  have e4 := eqk 4 out.inside.2.1
  have e5 := eqk 5 out.inside.2.2.1
  have e6 := eqk 6 out.inside.2.2.2.1
  have e7 := eqk 7 out.inside.2.2.2.2.1
  have e8 := eqk 8 out.inside.2.2.2.2.2.1
  have e9 := eqk 9 out.inside.2.2.2.2.2.2.1
  have history : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω (w 7) (w 22) (w 23) (w 24) (w 27) (w 28) (w 29) (w 25) :=
    ew ▸ state.history
  obtain ⟨stage,order,models,maps⟩ := wi_reflected_fixed_l hZF h hw hω history.toWi_models_d out.index
    (images 7) (images 22) (images 23) (images 24)
  have core : Wi_models_d I ω (v 7).val (v 22).val (v 23).val (v 24).val :=
    stage.symm ▸ order.symm ▸ models.symm ▸ maps.symm ▸ history.toWi_models_d
  have qq : Rd_entry_d (w 23) (w 23) π := models ▸ images 23
  have returns := wi_reflected_returns_l hZF h hw hω history out.index qq (images 27) (images 28) (images 29) (images 25)
  have original : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω (v 7).val (v 22).val (v 23).val (v 24).val cY.val Y.val S.val (v 25).val :=
    ⟨core,stage.symm ▸ models.symm ▸ maps.symm ▸ returns⟩
  have source : Smem_d I (v 0).val (v 1).val (v 2).val := ec.symm ▸ er.symm ▸ ex ▸ out.model
  have current := (h.map.entry_l hZF hw h.transitive vt h.model h.target
    (images 14) (images 0) (images 23)).mpr state.code
  have returned := (h.map.entry_l hZF hw h.transitive vt h.model h.target
    (images 14) (images 3) (images 25)).mpr state.returns
  have leg := original.returns.elementary (v 14).val (v 3).val (v 0).val (v 1).val (v 2).val
    returned current source.1
  have e12 := eqk 12 out.inside.2.2.2.2.2.2.2
  -- 前缀滤子是固定模型的子集，故恢复为同一个实际集合。
  have e11 : (v 11).val = w 11 := h.map.fixed_preimage_l hZF hw h.transitive h.model h.target
    (images 11) (fun q hq => point q (out.transitive _ out.inside.2.2.2.2.2.1 q ((out.accepted q).mp hq).1))
  have nat := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  have real := fn0_function_l (ZF.modelsKP hZF) out.real
  have e13 : (v 13).val = w 13 := h.function_fixed_l hZF hw (images 13) real.1
    (fun a b ab => nat a (real.input_mem_of_pairMember ab))
    (fun a b _ ab _ => nat b (real.output_mem_of_pairMember ab))
  -- 原滤子列只恢复函数性和定义域；接受关系逐条搬运，不宣称整列固定。
  obtain ⟨function,domain⟩ := h.map.function_preimage_l hZF hw h.transitive vt h.model h.target
    (images 7) (images 10) out.function out.domain
  have ready q (hq : M.mem q (w 1)) : Fp_ready_d I (v 7).val (v 10).val q ↔ Fp_ready_d I (w 7) (w 10) q := by
    rw [← e7]
    apply fp_ready_fixed_l hZF hw h.transitive vt h.model h.target h.map (images 10) out.function
    intro a b _ ab
    have pair := ab.choose_spec.1.mem_l M out.transitive (out.transitive q hq _ ab.choose_spec.2)
    exact ⟨point a pair.1,point b pair.2⟩
  have accepted q : M.mem q (v 11).val ↔ M.mem q (v 8).val ∧ Fp_ready_d I (v 7).val (v 10).val q := by
    rw [e11,← e8]
    exact (out.accepted q).trans (and_congr_right fun hq =>
      (ready q (out.transitive _ out.inside.2.2.2.2.2.1 q hq)).symm)
  have frame : Ab_frame_d I ω cY.val Y.val (ab_head_v (fun k => (v k).val)) := by
    constructor <;> dsimp only [ab_head_v]
    · exact source
    · exact (ec.symm ▸ er.symm ▸ ex ▸ out.theory : Zc_model_d I ω (v 0).val (v 1).val (v 2).val)
    · exact (ex ▸ out.transitive : M.TransitiveSet (v 1).val)
    · exact (ex ▸ out.count : M.CardinalLessOrEqual I (v 1).val ω)
    · exact leg
    · simpa only [ab_head_v] using! ex ▸ e4 ▸ e5 ▸ e6 ▸ e7 ▸ e8 ▸ e9 ▸ e12 ▸ out.inside
    · exact (e7 ▸ out.index : M.mem (v 7).val ω)
    · simpa only [ab_head_v] using! ex ▸ e4 ▸ e5 ▸ e6 ▸ e7 ▸ e8 ▸ e9 ▸ out.kernel
    · exact function
    · exact domain
    · exact accepted
    · simpa only [ab_head_v] using! ex ▸ e8 ▸ e9 ▸ e11.symm ▸ out.generic
    · exact (e13.symm ▸ out.real : Fn0_d ω ω (v 13).val)
    · simpa only [ab_head_v] using! ex ▸ e8 ▸ e9 ▸ e12 ▸ e11.symm ▸ e13.symm ▸ out.name
  -- 枚举行的输出属于固定模型；旧表的输入为自然数对，故两张原图整体固定。
  have en (k : Fin 26) (hk : M.mem (w (k.castAdd 7)) ω) : w (k.castAdd 7) = (v k).val := by
    simpa only [τ,Fin.addCases_left] using! (h.map.1.2 _ _ _ (images (k.castAdd 7)) (nat _ hk)).symm
  have e14 := en 14 queue.birth.history.natural
  have e15 := eqk 15 queue.birth.family.inside
  have e18 := en 18 queue.cursor
  have e19 := eqk 19 queue.task.dense_inside
  have e20 := en 20 queue.task.finite
  have e21 := eqk 21 queue.task.condition_inside
  have enum := fn0_function_l (ZF.modelsKP hZF) queue.birth.enumeration.function
  have e16 : w 16 = (v 16).val := (h.function_fixed_l hZF hw (images 16) enum.1
    (fun i D edge => nat i (enum.input_mem_of_pairMember edge))
    (fun i D _ edge _ => point D (enum.output_mem_of_pairMember edge))).symm
  obtain ⟨D,prod,table⟩ := queue.birth.history.table
  have tab := fn0_function_l (ZF.modelsKP hZF) table
  have e17 : w 17 = (v 17).val := (h.function_fixed_l hZF hw (images 17) tab.1 (by
    intro p z edge
    obtain ⟨i,hi,l,hl,pair⟩ := (prod p).mp (tab.input_mem_of_pairMember edge)
    exact h.pair_fixed_l hZF hw pair
      (nat i (hw.transitive (ZF.modelsKP hZF) _ queue.birth.history.natural i hi)) (nat l hl))
    (fun p z _ edge _ => point z (tab.output_mem_of_pairMember edge))).symm
  refine ⟨fun k => (v k).val,tuple.image_l Subtype.val full,⟨frame,?_,?_,?_,?_,?_,?_,?_⟩,original⟩
  · simpa only [ab_head_v] using! ex ▸ er.symm ▸ e5 ▸ e6 ▸ e14 ▸ e15 ▸ e16 ▸ e17 ▸ queue.birth
  · simpa only [ab_head_v] using! e7 ▸ e14 ▸ queue.stage
  · exact (e18 ▸ queue.cursor : M.mem (v 18).val ω)
  · simpa only using! e18 ▸ e14 ▸ queue.bound
  · simpa only using! e14 ▸ e17 ▸ e16 ▸ e18 ▸ e19 ▸ queue.pick
  · constructor <;> dsimp only [ab_head_v]
    · simpa only using! ex ▸ e19 ▸ queue.task.dense_inside
    · simpa only using! ex ▸ e21 ▸ queue.task.condition_inside
    · exact (e20 ▸ queue.task.finite : M.mem (v 20).val ω)
    · simpa only using! e7 ▸ e20 ▸ queue.task.remaining
    · simpa only using! e5 ▸ e6 ▸ e19 ▸ queue.task.dense
    · simpa only using! e21 ▸ e19 ▸ queue.task.hit
    · simpa only using! ex ▸ e4 ▸ e20 ▸ e21 ▸ queue.task.block
    · exact e21 ▸ (ready (w 21) queue.task.condition_inside).mpr queue.task.ready
  · simpa only [ab_head_v] using! e7 ▸ e20 ▸ e18 ▸ e14 ▸ e21 ▸ e11.symm ▸ queue.done

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限反射实际生产原相对机器的后继

从壳内旧状态读取其反坍塌像，背景的原吸收定理产生真实后继。
后继存在句再回到同一壳，保留原相对记录及转移。测试壳不承担 ZF/ZFC；
自然数和实数固定性由原隶属初等图证明，而不是额外的后继或固定性假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_relative_next_l {ω T α V d Q P c R π : M.Domain} {n m}
    {φ : Formula 1 n} {hc : φ.FreeClosed} {v : Fin m → M.Domain}
    (h : Rf_hull_d hZF ω T (ab_test_queries_l φ hc) v α V d Q P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    {cY Y S i j a x r : (smdl_structure_l I (R := R) h.model.1.2.1).Domain}
    {C Z U θ : M.Domain} (rank : V_d I θ Z) (target : Smem_d I C Z U)
    (code : Rd_entry_d cY.val C π) (domain : Rd_entry_d Y.val Z π) (relation : Rd_entry_d S.val U π)
    (hi : M.mem i.val ω)
    (old : Ab_relative_d P ω cY.val Y.val S.val i.val a.val r.val)
    (succ : M.SuccessorOf j.val i.val) (fx : Fn0_d ω ω x.val) :
    ∃ s, Ab_relative_d P ω cY.val Y.val S.val j.val x.val s ∧ Ab_relative_step_d P ω r.val s x.val := by
  let N := smdl_structure_l I (R := R) h.model.1.2.1
  let w : N.Domain := ⟨ω,hω⟩
  obtain ⟨k,sk,hk⟩ := hw.1.2 i.val hi
  have hj : M.mem j.val ω := sk.eq hZF.1 succ ▸ hk
  have vt := v_transitive_l I h.rank
  have fixedω := h.map.omega_l I hZF hw h.transitive vt h.model h.target hω
  have natural := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  have real (z : N.Domain) (fz : Fn0_d ω ω z.val) : Rd_entry_d z.val z.val π :=
    h.map.fixed_function_l hZF hw h.transitive vt h.model h.target fixedω natural hω z.property fz
      (fun _ _ edge => natural _ (fz.bound_l edge).2)
  obtain ⟨r',_,rr⟩ := h.map.1.1.2.2 r.val r.property
  obtain ⟨a',_,aa⟩ := h.map.1.1.2.2 a.val a.property
  let ρ : Env N 7 := ⟨fun k => [w,cY,Y,S,i,a,r].get k,fun _ => w⟩
  let η : Env M 7 := ⟨fun k => [ω,C,Z,U,i.val,a',r'].get k,fun _ => ω⟩
  have images : ∀ k, Rd_entry_d (ρ.bound k).val (η.bound k) π :=
    Fin.cases fixedω (Fin.cases code (Fin.cases domain (Fin.cases relation
      (Fin.cases (natural i.val hi) (Fin.cases aa (Fin.cases rr (fun k => Fin.elim0 k)))))))
  have old' := (ab_record_sat_l hZF η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).mp
    ((h.formula_l hZF hw ab_record_native_m ab_record_native_closed_l (by simp [ab_test_queries_l]) ρ η images).mp
      ((ab_relative_read_l I h.model h.transitive w cY Y S i a r).mp old))
  obtain ⟨s',next,step⟩ := old'.step_l hZFC hw rank target succ fx
  let ρ' : Env N 7 := ⟨fun k => [w,cY,Y,S,j,r,x].get k,fun _ => w⟩
  let η' : Env M 7 := ⟨fun k => [ω,C,Z,U,j.val,r',x.val].get k,fun _ => ω⟩
  have image' : ∀ k, Rd_entry_d (ρ'.bound k).val (η'.bound k) π :=
    Fin.cases fixedω (Fin.cases code (Fin.cases domain (Fin.cases relation
      (Fin.cases (natural j.val hj) (Fin.cases rr (Fin.cases (real x fx) (fun k => Fin.elim0 k)))))))
  have existsNext : Formula.satisfies η' ab_next_m := by
    apply (Formula.satisfies_exists_iff η' _).mpr
    refine ⟨s',?_⟩
    simp only [Formula.satisfies_conj_iff,Formula.satisfies_bind]
    exact ⟨(ab_record_sat_l hZF _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).mpr next,
      (ab_record_step_sat_l hZF _ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mpr step⟩
  have pulled := (h.formula_l hZF hw ab_next_m ab_next_closed_l (by simp [ab_test_queries_l]) ρ' η' image').mpr existsNext
  obtain ⟨s,new,move⟩ := (Formula.satisfies_exists_iff ρ' _).mp pulled
  refine ⟨s.val,(ab_relative_read_l I h.model h.transitive w cY Y S j x s).mpr ?_,
    (ab_relative_step_read_l I h.model h.transitive w r s x).mpr ?_⟩
  · have new := (Formula.satisfies_bind (env := ρ'.push s) _ _).mp new
    exact (Formula.closed_env_l ab_record_native_m ab_record_native_closed_l
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))).mp new
  · have move := (Formula.satisfies_bind (env := ρ'.push s) _ _).mp move
    exact (Formula.closed_env_l _ (by simp -implicitDefEqProofs)
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))).mp move

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限反射驱动的原内部无限吸收运行

给定原有限启动段和实数枚举，背景依赖选择先保留全部旧行，再逐轮调用同一有限反射后继工厂。
测试模型只提供已构造的反射壳及原返回目标的像，不要求其满足 ZF/ZFC。
生成的仍是原 Ab_run_d，包含每个真实相邻转移和全部枚举实数的覆盖。
每行原模型的完整 ZFC、乘积数据及全部历史返回图由有限反射实际恢复。
原返回目标的隶属结构、传递性及实际序数界均由同一反坍塌回收。
全部测试壳实数及其最小传递种子也实际留在壳内，随运行一起交付。
历史、泛型及真值的后续装配由同一运行的 finish_l 消费，不另造运行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_relative_run_l {ω T α V d Q P c R π : M.Domain} {n m}
    {ψ : Formula 1 n} {hc : ψ.FreeClosed} {v : Fin m → M.Domain}
    (test : Rf_hull_d hZF ω T (ab_test_queries_l ψ hc) v α V d Q P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    {cY Y S : (smdl_structure_l I (R := R) test.model.1.2.1).Domain}
    {C Z U θ B e o r₀ x₀ t H : M.Domain}
    (rank : V_d I θ Z) (target : Smem_d I C Z U)
    (code : Rd_entry_d cY.val C π) (domain : Rd_entry_d Y.val Z π) (relation : Rd_entry_d S.val U π)
    (space : Rb_reals_d P ω B)
    (enumeration : M.IsSetFunctionFromTo I e ω B) (onto : M.IsSetSurjectiveOnto I e ω B)
    (ht : M.mem t ω) (initial_fn : M.IsSetFunctionFromTo I H t P)
    (values : ∀ i, M.mem i t → Rd_entry_d i x₀ e)
    (empty : ∀ z, ¬ M.mem z o) (first : Rd_entry_d o r₀ H)
    (initial : ∀ i r, Rd_entry_d i r H → Ab_relative_d P ω cY.val Y.val S.val i x₀ r)
    (initial_step : ∀ i j r s, M.SuccessorOf j i → Rd_entry_d i r H → Rd_entry_d j s H →
      Ab_relative_step_d P ω r s x₀) :
    ∃ F, M.IsSetFunctionFromTo I F ω P ∧ Rd_entry_d o r₀ F ∧ M.IsRestrictionOf I H F t ∧
      (∀ i r, Rd_entry_d i r F → ∃ x, Rd_entry_d i x e ∧ Ab_relative_d P ω cY.val Y.val S.val i x r) ∧
      (∀ i j r s x, M.SuccessorOf j i → Rd_entry_d i r F → Rd_entry_d j s F → Rd_entry_d j x e →
        Ab_relative_step_d P ω r s x) ∧
      (∀ x, M.mem x B → ∃ i r, M.mem i ω ∧ Rd_entry_d i r F ∧ Ab_relative_d P ω cY.val Y.val S.val i x r) ∧
      Ab_run_d I P ω cY.val Y.val S.val F := by
  classical
  let N := smdl_structure_l I (R := R) test.model.1.2.1
  have inside : M.MemberSubset B P := fun x hx => ((space x).mp hx).1
  have real : ∀ x, M.mem x B → Fn0_d ω ω x := fun x hx => ((space x).mp hx).2
  have firstReal := values o (initial_fn.input_mem_of_pairMember first)
  have initial₀ := initial o r₀ first
  let ρ : Env M 8 := ⟨fun k => [P,ω,cY.val,Y.val,S.val,e,t,H].get k,fun _ => P⟩
  let A : BinarySchema 8 := { body := (.conj (.existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 8))
    (ab_relative_m (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 2) .newest (.bound 1))))
    (.imp (.mem (.bound 1) (.bound 8)) (rd_entry0_m (.bound 1) .newest (.bound 9)))) }
  let φ : UnarySchema 10 := { body := .existsE (.existsE (.conj (Formula.isSuccessor (.bound 1) (.bound 4))
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 10))
      (ab_relative_step_m (.bound 5) (.bound 6) (.bound 3) (.bound 2) .newest)))) }
  have valid i r : A.denote ρ i r ↔
      (∃ x, Rd_entry_d i x e ∧ Ab_relative_d P ω cY.val Y.val S.val i x r) ∧
        (M.mem i t → Rd_entry_d i r H) := by
    simp only [A,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,ab_relative_sat_l,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff]
    rfl
  have move i r s : φ.denote ((ρ.push i).push r) s ↔
      ∃ j x, M.SuccessorOf j i ∧ Rd_entry_d j x e ∧ Ab_relative_step_d P ω r s x := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_isSuccessor_iff,rd_entry0_sat_l hZF.1,ab_relative_step_sat_l]
    rfl
  obtain ⟨_,F,fn,start,rows,steps⟩ := ZFC.class_indexed_choice_l I hZFC A φ ρ hw empty
    ((valid o r₀).mpr ⟨⟨x₀,firstReal,initial₀⟩,fun _ => first⟩) (by
      intro i j r hi succ row
      obtain ⟨⟨a,ia,old⟩,saved⟩ := (valid i r).mp row
      obtain ⟨j₀,sj,hj₀⟩ := hw.1.2 i hi
      have hj : M.mem j ω := sj.eq hZF.1 succ ▸ hj₀
      -- 启动段内读取同一旧记录，越过指定端点后才调用吸收工厂。
      by_cases before : M.mem j t
      · obtain ⟨s,_,js⟩ := initial_fn.2.2 j before
        have it := (hw.members_areOrdinals (ZF.modelsKP hZF) t ht).transitive j before i succ.predecessor_mem
        exact ⟨s,(valid j s).mpr ⟨⟨x₀,values j before,initial j s js⟩,fun _ => js⟩,
          (move i r s).mpr ⟨j,x₀,succ,values j before,initial_step i j r s succ (saved it) js⟩⟩
      · obtain ⟨x,hx,jx⟩ := enumeration.2.2 j hj
        let i₀ : N.Domain := ⟨i,test.transitive ω hω i hi⟩
        let j₁ : N.Domain := ⟨j,test.transitive ω hω j hj⟩
        let a₀ : N.Domain := ⟨a,inside a (enumeration.output_mem_of_pairMember ia)⟩
        let x₁ : N.Domain := ⟨x,inside x hx⟩
        let r₁ : N.Domain := ⟨r,old.1⟩
        obtain ⟨s,new,step⟩ := ab_relative_next_l hZFC test hw hω
          (cY := cY) (Y := Y) (S := S) (i := i₀) (j := j₁) (a := a₀) (x := x₁) (r := r₁)
          rank target code domain relation hi old succ (real x hx)
        exact ⟨s,(valid j s).mpr ⟨⟨x,jx,new⟩,fun h => (before h).elim⟩,(move i r s).mpr ⟨j,x,succ,jx,step⟩⟩)
  have row i r (ir : Rd_entry_d i r F) := ((valid i r).mp (rows i r ir)).1
  have run : M.IsSetFunctionFromTo I F ω P := ⟨fn.1,fn.2.1,fun i hi => by
    obtain ⟨r,_,ir⟩ := fn.2.2 i hi
    obtain ⟨_,_,owned⟩ := row i r ir
    exact ⟨r,owned.1,ir⟩⟩
  -- 保留整张旧图的实际限制方程，供原前缀及其名字接入最终运行。
  have keep : M.IsRestrictionOf I H F t := by
    refine ⟨initial_fn.1.1,fun i r => ⟨?_,?_⟩⟩
    · intro ir
      have hi := initial_fn.input_mem_of_pairMember ir
      obtain ⟨s,_,is⟩ := run.2.2 i (hw.transitive (ZF.modelsKP hZF) t ht i hi)
      have old := ((valid i s).mp (rows i s is)).2 hi
      exact ⟨hi,initial_fn.1.2 i s r old ir ▸ is⟩
    · rintro ⟨hi,ir⟩
      exact ((valid i r).mp (rows i r ir)).2 hi
  have next i j r s x (succ : M.SuccessorOf j i) (ir : Rd_entry_d i r F)
      (js : Rd_entry_d j s F) (jx : Rd_entry_d j x e) : Ab_relative_step_d P ω r s x := by
    obtain ⟨j',x',succ',jx',step⟩ := (move i r s).mp (steps i j r s succ ir js)
    have ej := succ'.eq hZF.1 succ
    subst j'
    exact enumeration.1.2 j x' x jx' jx ▸ step
  have cover x (hx : M.mem x B) : ∃ i r, M.mem i ω ∧ Rd_entry_d i r F ∧ Ab_relative_d P ω cY.val Y.val S.val i x r := by
    obtain ⟨i,hi,ix⟩ := onto x hx
    obtain ⟨r,_,ir⟩ := run.2.2 i hi
    obtain ⟨y,iy,old⟩ := row i r ir
    exact ⟨i,r,hi,ir,enumeration.1.2 i y x iy ix ▸ old⟩
  have data i r (v : Fin 26 → M.Domain) (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r) :
      Ab_queue_d I ω cY.val Y.val (ab_head_v v) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21) ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω (v 7) (v 22) (v 23) (v 24) cY.val Y.val S.val (v 25) := by
    obtain ⟨x,ix,old⟩ := row i r ir
    obtain ⟨w,wr,data⟩ := ab_relative_queue_l hZF test hw hω cY Y S
      ⟨i,test.transitive ω hω i (run.input_mem_of_pairMember ir)⟩
      ⟨x,inside x (enumeration.output_mem_of_pairMember ix)⟩
      ⟨r,run.output_mem_of_pairMember ir⟩ old
    exact rt_tuple_inj_l wr vr ▸ data
  have original := test.map.smem_preimage_l hZF hw test.transitive (v_transitive_l I test.rank) test.model test.target
    code domain relation target (v_transitive_l I rank)
  obtain ⟨_,_,firstQueue,_⟩ := ab_relative_queue_l hZF test hw hω cY Y S
    ⟨o,test.transitive ω hω o (enumeration.input_mem_of_pairMember firstReal)⟩
    ⟨x₀,inside x₀ (enumeration.output_mem_of_pairMember firstReal)⟩ ⟨r₀,initial₀.1⟩ initial₀
  obtain ⟨nativeY,hwY⟩ := firstQueue.frame.target_l hZF hw original.1 original.2
  obtain ⟨B₁,Z₁,hB₁,_,seedReals,seed⟩ := test.real_seed_l hZF hw hω
  have hBY := test.reals_in_rank_l hZF hw hω original.1 nativeY hwY target rank domain relation hB₁ seedReals
  obtain ⟨Z₂,hZ₂,seed₂⟩ := smem_real_seed_l hZF original.1 original.2 nativeY hwY hBY
    (hw.transitive (ZF.modelsKP hZF)) (fun x hx => ((seedReals x).mp hx).2)
    ⟨x₀,(seedReals x₀).mpr ⟨inside x₀ (enumeration.output_mem_of_pairMember firstReal),
      real x₀ (enumeration.output_mem_of_pairMember firstReal)⟩⟩
  have hZY : M.mem Z₁ Y.val := tc_unique_l hZF.1 seed₂ seed ▸ hZ₂
  refine ⟨F,run,start,keep,row,next,cover,fn0_of_function_l (ZF.modelsKP hZF) run,?_,?_,
    fun i r v ir vr => (data i r v ir vr).1,fun i r v ir vr => (data i r v ir vr).2,
    original.1,original.2,test.filter_project_l hZF hw,test.graph_l hZF hw,
    test.height_l hZF hw Y.property original.2,⟨B₁,Z₁,hBY,hZY,seedReals,seed⟩,
    fun x hx fx => cover x ((space x).mpr ⟨hx,fx⟩)⟩
  · intro i r ir
    obtain ⟨x,ix,old⟩ := row i r ir
    exact ⟨x,inside x (enumeration.output_mem_of_pairMember ix),old⟩
  · intro i j r s succ ir js
    obtain ⟨x,jx,_⟩ := row j s js
    exact ⟨x,inside x (enumeration.output_mem_of_pairMember jx),next i j r s x succ ir js jx⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 保留实际有限启动段并吸收全部测试壳实数

从壳的实际可数性构造满枚举，再把指定有限前段改为统一旧实数；每个
壳实数仍在尾部出现。有限段原样保留，之后使用同一有限反射吸收工厂。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_relative_continue_l {ω T α V d Q P c R π : M.Domain} {n m}
    {ψ : Formula 1 n} {hc : ψ.FreeClosed} {v : Fin m → M.Domain}
    (test : Rf_hull_d hZF ω T (ab_test_queries_l ψ hc) v α V d Q P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    {cY Y S : (smdl_structure_l I (R := R) test.model.1.2.1).Domain}
    {C Z U θ x₀ t H : M.Domain} (rank : V_d I θ Z) (target : Smem_d I C Z U)
    (code : Rd_entry_d cY.val C π) (domain : Rd_entry_d Y.val Z π) (relation : Rd_entry_d S.val U π)
    (hx : M.mem x₀ P) (fx : Fn0_d ω ω x₀) (ht : M.mem t ω) (ne : ∃ i, M.mem i t)
    (initial_fn : M.IsSetFunctionFromTo I H t P)
    (initial : ∀ i r, Rd_entry_d i r H → Ab_relative_d P ω cY.val Y.val S.val i x₀ r)
    (initial_step : ∀ i j r s, M.SuccessorOf j i → Rd_entry_d i r H → Rd_entry_d j s H →
      Ab_relative_step_d P ω r s x₀) :
    ∃ F, M.IsSetFunctionFromTo I F ω P ∧ M.IsRestrictionOf I H F t ∧
      Ab_run_d I P ω cY.val Y.val S.val F ∧
      ∀ x, M.mem x P → Fn0_d ω ω x → ∃ i r, M.mem i ω ∧ ¬ M.mem i t ∧
        Rd_entry_d i r F ∧ Ab_relative_d P ω cY.val Y.val S.val i x r := by
  obtain ⟨B,_,space⟩ := test.reals_l hZF hw hω
  have sub : M.MemberSubset B P := fun x hx => ((space x).mp hx).1
  obtain ⟨j,hj⟩ := ZF.exists_inclusionInjection hZF I sub
  obtain ⟨k,hk⟩ := test.count
  obtain ⟨l,hl⟩ := ZF.exists_compositionInjection hZF I hj hk
  have real := (space x₀).mpr ⟨hx,fx⟩
  obtain ⟨e,fe,onto⟩ := countable_surjection_zf_l hZF ⟨l,hl⟩ ⟨x₀,real⟩
  obtain ⟨e',fe',constant,tail⟩ := ce_prefix_l hZF hw ht real fe onto
  have onto' : M.IsSetSurjectiveOnto I e' ω B := fun x hx =>
    (tail x hx).elim fun i hi => ⟨i,hi.1,hi.2.2⟩
  obtain ⟨o,empty,_⟩ := hw.1.1
  have ho := (hw.members_areOrdinals (ZF.modelsKP hZF) t ht).empty_mem_of_nonempty (ZF.modelsKP hZF) ne empty
  obtain ⟨r₀,_,first⟩ := initial_fn.2.2 o ho
  obtain ⟨F,fn,_,keep,rows,_,_,run⟩ := ab_relative_run_l hZFC test hw hω
    rank target code domain relation space fe' onto' ht initial_fn constant empty first initial initial_step
  refine ⟨F,fn,keep,run,?_⟩
  intro x hx fx
  obtain ⟨i,hi,outside,ix⟩ := tail x ((space x).mpr ⟨hx,fx⟩)
  obtain ⟨r,_,ir⟩ := fn.2.2 i hi
  obtain ⟨y,iy,row⟩ := rows i r ir
  exact ⟨i,r,hi,outside,ir,fe'.1.2 i y x iy ix ▸ row⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原泛型前缀构造测试壳及完整吸收运行

先由原 G 构造所需有限历史，再将该图及其值域加入已有有限参数。
反坍塌逐条取回原记录和转移；原源全部对象固定，前缀滤子作为原源的
子集也由成员方程固定。完整运行原样接续这段历史，尾部吸收全部壳实数，
指定端点仍保留同一个 G↾m 及原源中的全部名字。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_test_run_l {Ω c X R cY Y S θ j G i : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω) (target : Smem_d I cY Y S) (rank : V_d I θ Y)
    (embed : Smap_d I Ω c cY X Y j)
    {ω A Q U : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A Q U)
    (generic : Gset_d Q.val U.val Q.val X G) (hi : M.mem i Ω)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (x : Fin n → M.Domain) (real : ∀ k, Fn0_d Ω Ω (x k))
    {l} (z : Fin l → M.Domain) :
    ∃ m L Z x₀ T α V d W P b R₀ π,
    ∃ test : Rf_hull_d hZF Ω T (ab_test_queries_l φ hc)
      (Fin.addCases (fun k : Fin 5 => [cY,Y,S,L,Z].get k) z) α V d W P b R₀ π,
      M.SuccessorOf m i ∧ M.mem m Ω ∧ M.mem x₀ X ∧ M.mem Ω P ∧
      M.mem X P ∧ M.MemberSubset X P ∧ M.mem G P ∧
      Rd_entry_d X X π ∧ Rd_entry_d G G π ∧
      (∀ a, M.mem a X → Rd_entry_d a a π) ∧
      (∀ k, M.mem (x k) P ∧ Rd_entry_d (x k) (x k) π) ∧
      ∃ C Y₀ S₀ B H : (smdl_structure_l I (R := R₀) test.model.1.2.1).Domain,
        Rd_entry_d C.val cY π ∧ Rd_entry_d Y₀.val Y π ∧ Rd_entry_d S₀.val S π ∧
        Rd_entry_d B.val Z π ∧ Rd_entry_d H.val L π ∧ M.IsSetFunctionFromTo I H.val m P ∧
        (∀ k r, Rd_entry_d k r H.val → Ab_relative_d P Ω C.val Y₀.val S₀.val k x₀ r) ∧
        (∀ k l r s, M.SuccessorOf l k → Rd_entry_d k r H.val → Rd_entry_d l s H.val →
          Ab_relative_step_d P Ω r s x₀) ∧
        ∃ J, M.IsSetFunctionFromTo I J Ω P ∧ M.IsRestrictionOf I H.val J m ∧
          Ab_run_d I P Ω C.val Y₀.val S₀.val J ∧
          (∀ z, M.mem z P → Fn0_d Ω Ω z → ∃ k r, M.mem k Ω ∧ ¬ M.mem k m ∧
            Rd_entry_d k r J ∧ Ab_relative_d P Ω C.val Y₀.val S₀.val k z r) ∧
        ∃ r, Rd_entry_d i r H.val ∧ Rd_entry_d i r J ∧ ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r ∧
          v 7 = m ∧ v 0 = c ∧ v 1 = X ∧ v 2 = R ∧ v 4 = A.val ∧ v 5 = Q.val ∧ v 6 = U.val ∧
          Rd_entry_d (v 3) j π ∧ Fp_filter_project_d (v 8) U.val G (v 11) := by
  -- 一、实际生成原有限启动段；其端点仍是原源模型中的原前缀。
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  obtain ⟨_,F,B₀,x₀,_,Z,J,_,header,hx,fn,_,rows,steps,finite⟩ :=
    ab_original_run_l hZFC hΩ certificate source xt count target embed hw sequence product generic
  obtain ⟨m,L,r,succ,hm,_,cut,ir,last⟩ := finite i hi
  obtain ⟨v,tuple,original,header',index,value⟩ := last
  have heads := rt_tuple_inj_l header' header
  have old := original.machine.queue.frame
  have hωX : M.mem Ω X := (show v 1 = X from congrFun heads 1) ▸ (show M.mem Ω (v 1) from old.inside.1)
  have subG : M.MemberSubset G X := by
    have sub := ((source.generic_code_l I hZF.1 xt (ZF.modelsKP native) Q U Q G).mp generic).1
    exact fun a ha => xt Q.val Q.property a (sub a ha)
  have fx : Fn0_d Ω Ω x₀ := value ▸ (show Fn0_d Ω Ω (v 13) from old.real)
  have length : v 7 = m := (show M.SuccessorOf (v 7) i from index ▸ original.machine.queue.stage).eq hZF.1 succ
  have fl := cut.isSetFunctionFromTo fn (hΩ.transitive (ZF.modelsKP hZF) m hm)
  -- 二、启动历史与指定有限参数一同入壳；所需反射公式族保持原样。
  obtain ⟨T,α,V,d,W,P,b,R₀,π,test,hωP,hXP,subX,hGP,_,fixedX,fixedG,points,params⟩ :=
    ab_test_l hZFC hΩ source xt hωX (ZF.modelsKP native) count subG φ hc x real
      (v := Fin.addCases (fun k : Fin 5 => [cY,Y,S,L,Z].get k) z)
  let N := smdl_structure_l I (R := R₀) test.model.1.2.1
  have head (k : Fin 5) : ∃ a, Rd_entry_d a ([cY,Y,S,L,Z].get k) π := by
    simpa only [Fin.addCases_left] using test.params (k.castAdd l)
  obtain ⟨a,ac⟩ := head 0
  obtain ⟨y,yy⟩ := head 1
  obtain ⟨s,ss⟩ := head 2
  obtain ⟨k,kl⟩ := head 3
  obtain ⟨z,zz⟩ := head 4
  let C : N.Domain := ⟨a,test.map.1.1.input_mem_of_pairMember ac⟩
  let Y₀ : N.Domain := ⟨y,test.map.1.1.input_mem_of_pairMember yy⟩
  let S₀ : N.Domain := ⟨s,test.map.1.1.input_mem_of_pairMember ss⟩
  let H : N.Domain := ⟨k,test.map.1.1.input_mem_of_pairMember kl⟩
  let B : N.Domain := ⟨z,test.map.1.1.input_mem_of_pairMember zz⟩
  let x' : N.Domain := ⟨x₀,subX x₀ hx⟩
  have ordinary l t (lt : Rd_entry_d l t L) : Ab_record_d hZF Ω cY Y S l x₀ t := by
    obtain ⟨u,code,state,_,stage,real⟩ := rows l t ((cut.2 l t).mp lt).2
    exact ⟨u,code,state.machine,stage,real⟩
  have transition l l' t t' (sl : M.SuccessorOf l' l) (lt : Rd_entry_d l t L) (lt' : Rd_entry_d l' t' L) :
      Ab_record_step_d hZF Ω t t' x₀ := by
    obtain ⟨u,w,e,K,code,code',move,_⟩ := steps l l' t t' sl ((cut.2 l t).mp lt).2 ((cut.2 l' t').mp lt').2
    exact ⟨u,w,e,K,code,code',move⟩
  obtain ⟨fH,relative,move⟩ := ab_relative_finite_l hZF test hΩ hωP
    (cY := C) (Y := Y₀) (S := S₀) (x := x') (Z := B) (K := H)
    hm fx ac yy ss zz kl fl ordinary transition
  obtain ⟨J',fn',keep,run,cover⟩ := ab_relative_continue_l hZFC test hΩ hωP
    (cY := C) (Y := Y₀) (S := S₀) rank target ac yy ss (subX x₀ hx) fx hm
    ⟨i,succ.predecessor_mem⟩ fH relative move
  -- 三、完整运行保留端点的同一元组；原源对象及原前缀滤子逐项固定。
  have vt := v_transitive_l I test.rank
  have natural := test.map.natural_l hZF hΩ test.transitive vt test.model test.target hωP
  obtain ⟨r',ir',rr⟩ := test.map.value_preimage_l hZF hΩ test.transitive vt test.model test.target
    (natural i hi) kl fl.1 ir
  obtain ⟨v',tuple',images⟩ := test.map.tuple_preimage_l hZF hΩ test.transitive vt test.model test.target rr tuple
  have fixed (l : Fin 26) (hl : Rd_entry_d (v l) (v l) π) : v' l = v l :=
    test.map.1.2 _ _ _ (images l) hl
  have sourceEq : v' 1 = X := (fixed 1 (by simpa only [show v 1 = X from congrFun heads 1] using fixedX)).trans (congrFun heads 1)
  have sourceCode : Rd_entry_d (v' 0) c π := by simpa only [show v 0 = c from congrFun heads 0] using! images 0
  obtain ⟨fixedCode,_,_⟩ := test.model_fixed_l hZF hΩ hωP sourceCode source xt count
  have codeEq : v' 0 = c := test.map.1.2 _ _ _ sourceCode fixedCode
  obtain ⟨u,ur,queue,_⟩ := ab_relative_queue_l hZF test hΩ hωP C Y₀ S₀
    ⟨i,test.transitive Ω hωP i hi⟩ x' ⟨r',fH.output_mem_of_pairMember ir'⟩ (relative i r' ir')
  have frame : Ab_frame_d I Ω C.val Y₀.val (ab_head_v v') := rt_tuple_inj_l ur tuple' ▸ queue.frame
  have pair : KPair_d M c X (v' 2) := by
    have pair : KPair_d M (v' 0) (v' 1) (v' 2) := frame.model.1.1
    simpa only [codeEq,sourceEq] using pair
  have relationEq : v' 2 = R := (kpair_injective_l M pair source.1.1).2
  have fixedField (l : Fin 26) (hl : M.mem (v l) (v 1)) : v' l = v l :=
    fixed l (points (v l) ((show v 1 = X from congrFun heads 1) ▸ hl))
  have hC : M.mem (v 8) (v 1) := old.inside.2.2.2.2.2.1
  have eC := fixedField 8 hC
  have eH : v' 11 = v 11 := test.map.fixed_preimage_l hZF hΩ test.transitive test.model test.target (images 11)
    (fun a ha => points a ((show v 1 = X from congrFun heads 1) ▸
      old.transitive (v 8) hC a ((old.accepted a).mp ha).1))
  have projection : Fp_filter_project_d (v' 8) U.val G (v' 11) := by
    simpa only [eC,eH,show v 6 = U.val from congrFun heads 6] using! original.projection
  refine ⟨m,L,Z,x₀,T,α,V,d,W,P,b,R₀,π,test,succ,hm,hx,hωP,hXP,subX,hGP,fixedX,fixedG,points,params,
    C,Y₀,S₀,B,H,ac,yy,ss,zz,kl,fH,relative,move,J',fn',keep,run,cover,
    r',ir',((keep.2 i r').mp ir').2,v',tuple',?_,codeEq,sourceEq,relationEq,?_,?_,?_,?_,projection⟩
  · exact (fixed 7 (length.symm ▸ natural m hm)).trans length
  · exact (fixedField 4 old.inside.2.1).trans (congrFun heads 4)
  · exact (fixedField 5 old.inside.2.2.1).trans (congrFun heads 5)
  · exact (fixedField 6 old.inside.2.2.2.1).trans (congrFun heads 6)
  · have image := images 3
    simpa only [show v 3 = j from congrFun heads 3] using! image

end YesMetaZFC.SetTheory.LargeCardinal
