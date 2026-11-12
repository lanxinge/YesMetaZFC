import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinInitial
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Ground.DenseEnumeration
import YesMetaZFC.Model.Forcing.Ground.ProductCoordinates
import YesMetaZFC.Model.Forcing.Ground.RealGround
import YesMetaZFC.Model.SetTheory.Embedding.Theory

/-! # 吸收阶段的实际集合帧及原公式

十四项记录保存模型、返回图、Woodin 字母表列、全乘积、前缀、滤子列和实数见证。
模型内部的乘积规格相对化于该模型；泛型性与名字解释使用已经实现的背景集合公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u

def ab_native_m : Formula 1 7 := .conj (Formula.isOmega (.bound 0))
  (.conj (wd_sequence_m (.bound 0) (.bound 1))
    (.conj (fp_product_m (.bound 0) (.bound 1) (.bound 2) (.bound 3))
      (fp_prefix_m (.bound 0) (.bound 1) (.bound 4) (.bound 5) (.bound 6))))
@[simp] theorem ab_native_closed_l : ab_native_m.FreeClosed := by
  simp -implicitDefEqProofs [ab_native_m,Definitional.Formula.FreeClosed]

def ab_kernel0_m : Formula 1 8 := lr_rel_m ab_native_m (.bound 0) (fun i => .bound i.succ)
@[simp] theorem ab_kernel0_closed_l : ab_kernel0_m.FreeClosed :=
  lr_rel_closed_l _ ab_native_closed_l _ _ rfl (fun _ => rfl)

theorem ab_kernel0_delta_l : ab_kernel0_m.IsDelta0 := lr_rel_delta_l ab_native_m (.bound 0) (fun i => .bound i.succ)

def Ab_kernel_d {M : Structure.{u}} (X ω A P U n C T : M.Domain) : Prop :=
  Formula.satisfies (⟨fun i => [X,ω,A,P,U,n,C,T].get i,fun _ => X⟩ : Env M 8) ab_kernel0_m

def ab_kernel_m {d} (X ω A P U n C T : Term d) : Formula 1 d :=
  ab_kernel0_m.bind (Fin.cases X (Fin.cases ω (Fin.cases A (Fin.cases P
    (Fin.cases U (Fin.cases n (Fin.cases C (fun _ => T))))))))
@[simp] theorem ab_kernel_closed_l {d} (X ω A P U n C T : Term d)
    (hX : X.freeSupport = []) (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hP : P.freeSupport = [])
    (hU : U.freeSupport = []) (hn : n.freeSupport = []) (hC : C.freeSupport = []) (hT : T.freeSupport = []) :
    (ab_kernel_m X ω A P U n C T).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hX (Fin.cases hω (Fin.cases hA (Fin.cases hP
      (Fin.cases hU (Fin.cases hn (Fin.cases hC (fun _ => hT)))))))) _).mpr ab_kernel0_closed_l

theorem ab_kernel_sat_l {M : Structure.{u}} {d} (ρ : Env M d) (X ω A P U n C T : Term d) :
    Formula.satisfies ρ (ab_kernel_m X ω A P U n C T) ↔
      Ab_kernel_d (X.eval ρ) (ω.eval ρ) (A.eval ρ) (P.eval ρ) (U.eval ρ) (n.eval ρ) (C.eval ρ) (T.eval ρ) := by
  rw [ab_kernel_m,Formula.satisfies_bind]
  apply Formula.closed_env_l _ ab_kernel0_closed_l
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) i

theorem ab_kernel_read_l {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    {c X R : M.Domain} (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (ω A P U n C T : (smdl_structure_l I (R := R) source.1.2.1).Domain) :
    Ab_kernel_d X ω.val A.val P.val U.val n.val C.val T.val ↔
      (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω ∧
      Wd_sequence_d (kp_pair_l (ZF.modelsKP native)) ω A ∧
      Fp_product_d native ω A P U ∧ Fp_prefix_d native ω A n C T := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let ρ : Env N 7 := ⟨fun i => [ω,A,P,U,n,C,T].get i,fun _ => ω⟩
  let η : Env M 8 := ⟨fun i => [X,ω.val,A.val,P.val,U.val,n.val,C.val,T.val].get i,fun _ => X⟩
  have read := lr_rel_decode_l I source.1 source.2 trans ab_native_m ab_native_closed_l ρ η
    (.bound 0) (fun i => .bound i.succ) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))
  apply read.trans
  simp only [ab_native_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
    wd_sequence_sat_l (kp_pair_l (ZF.modelsKP native)) native.1,fp_product_sat_l native,fp_prefix_sat_l native]
  rfl

variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 坐标依次为 c、X、R、返回图、A、P、U、n、C、T、滤子列、前缀滤子、名字目标、实数。 -/
structure Ab_frame_d (ω cY Y : M.Domain) (v : Fin 14 → M.Domain) : Prop where
  model : Smem_d I (v 0) (v 1) (v 2)
  theory : Zc_model_d I ω (v 0) (v 1) (v 2)
  transitive : M.TransitiveSet (v 1)
  count : M.CardinalLessOrEqual I (v 1) ω
  returns : Smap_d I ω (v 0) cY (v 1) Y (v 3)
  inside : M.mem ω (v 1) ∧ M.mem (v 4) (v 1) ∧ M.mem (v 5) (v 1) ∧ M.mem (v 6) (v 1) ∧
    M.mem (v 7) (v 1) ∧ M.mem (v 8) (v 1) ∧ M.mem (v 9) (v 1) ∧ M.mem (v 12) (v 1)
  index : M.mem (v 7) ω
  kernel : Ab_kernel_d (v 1) ω (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
  function : M.IsSetFunction I (v 10)
  domain : M.IsDomainOf I (v 7) (v 10)
  accepted : ∀ q, M.mem q (v 11) ↔ M.mem q (v 8) ∧ Fp_ready_d I (v 7) (v 10) q
  generic : Gset_d (v 8) (v 9) (v 8) (v 1) (v 11)
  real : Fn0_d ω ω (v 13)
  name : Fn_bg_d (v 1) (v 8) (v 9) (v 8) ω (v 12) (v 11) (v 13)

def ab_frame_m {d} (ω cY Y : Term d) (v : Fin 14 → Term d) : Formula 1 d := set[d] ⟪
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ) ∧
  ⌜zc_model_m⌝ₚ(⌜ω⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ) ∧
  ⌜Formula.isTransitive⌝ₚ(⌜v 1⌝ₛ) ∧ ⌜Formula.cardinalLessOrEqual kpair_convention_l⌝ₚ(⌜v 1⌝ₛ,⌜ω⌝ₛ) ∧
  ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜v 0⌝ₛ,⌜cY⌝ₛ,⌜v 1⌝ₛ,⌜Y⌝ₛ,⌜v 3⌝ₛ) ∧
  (⌜ω⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜v 4⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜v 5⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜v 6⌝ₛ ∈ ⌜v 1⌝ₛ ∧
    ⌜v 7⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜v 8⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜v 9⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜v 12⌝ₛ ∈ ⌜v 1⌝ₛ) ∧
  ⌜v 7⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜ab_kernel_m⌝ₚ(⌜v 1⌝ₛ,⌜ω⌝ₛ,⌜v 4⌝ₛ,⌜v 5⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜v 10⌝ₛ) ∧ ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜v 7⌝ₛ,⌜v 10⌝ₛ) ∧
  (∀ q, q ∈ ⌜v 11⌝ₛ ↔ q ∈ ⌜v 8⌝ₛ ∧ ⌜fp_ready_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 7⌝ₛ,⌜v 10⌝ₛ,q)) ∧
  ⌜gset_m⌝ₚ(⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 8⌝ₛ,⌜v 1⌝ₛ,⌜v 11⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜v 13⌝ₛ) ∧
  ⌜fn_bg_m⌝ₚ(⌜v 1⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 8⌝ₛ,⌜ω⌝ₛ,⌜v 12⌝ₛ,⌜v 11⌝ₛ,⌜v 13⌝ₛ)⟫

@[simp] theorem ab_frame_closed_l {d} (ω cY Y : Term d) (v : Fin 14 → Term d)
    (hω : ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) : (ab_frame_m ω cY Y v).FreeClosed := by
  simp -implicitDefEqProofs [ab_frame_m,Definitional.Formula.FreeClosed,hω,hcY,hY,hv]

theorem ab_frame_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω cY Y : Term d) (v : Fin 14 → Term d) :
    Formula.satisfies ρ (ab_frame_m ω cY Y v) ↔
      Ab_frame_d I (ω.eval ρ) (cY.eval ρ) (Y.eval ρ) (fun i => (v i).eval ρ) := by
  simp only [ab_frame_m,Formula.satisfies_conj_iff,smem_sat_l I,zc_model_sat_l I hE,
    Formula.satisfies_isTransitive_iff,Formula.satisfies_cardinalLessOrEqual_iff I hE,smap_sat_l I hE,
    Formula.satisfies_mem_iff,ab_kernel_sat_l,Formula.satisfies_isFunction_iff I hE,Formula.satisfies_isDomain_iff I,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,fp_ready_sat_l I,gset_sat_l hE,fn0_sat_l hE,fn_bg_sat_l,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩,
    fun h => ⟨h.model,h.theory,h.transitive,h.count,h.returns,h.inside,h.index,h.kernel,h.function,h.domain,
      h.accepted,h.generic,h.real,h.name⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 阶段记录上的实际稠密任务

任务保存原稠密集、有限终点和已选条件。条件类型在原模型内解释；
稠密性和已接受坐标用背景集合公式表达，因而同一任务可以进入内部递归的状态。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u

def ab_block0_m : Formula 1 5 := lr_rel_m
  (fp_at_m (𝒞 := kpair_convention_l) (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3))
  (.bound 0) (fun i => .bound i.succ)
@[simp] theorem ab_block0_closed_l : ab_block0_m.FreeClosed :=
  lr_rel_closed_l _ (by simp -implicitDefEqProofs) _ _ rfl (fun _ => rfl)

def Ab_block_d {M : Structure.{u}} (X ω A m d : M.Domain) : Prop :=
  Formula.satisfies (⟨fun i => [X,ω,A,m,d].get i,fun _ => X⟩ : Env M 5) ab_block0_m

def ab_block_m {k} (X ω A m d : Term k) : Formula 1 k :=
  ab_block0_m.bind (Fin.cases X (Fin.cases ω (Fin.cases A (Fin.cases m (fun _ => d)))))
@[simp] theorem ab_block_closed_l {k} (X ω A m d : Term k)
    (hX : X.freeSupport = []) (hω : ω.freeSupport = []) (hA : A.freeSupport = [])
    (hm : m.freeSupport = []) (hd : d.freeSupport = []) : (ab_block_m X ω A m d).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hX (Fin.cases hω (Fin.cases hA (Fin.cases hm (fun _ => hd))))) _).mpr ab_block0_closed_l

theorem ab_block_sat_l {M : Structure.{u}} {k} (ρ : Env M k) (X ω A m d : Term k) :
    Formula.satisfies ρ (ab_block_m X ω A m d) ↔
      Ab_block_d (X.eval ρ) (ω.eval ρ) (A.eval ρ) (m.eval ρ) (d.eval ρ) := by
  rw [ab_block_m,Formula.satisfies_bind]
  apply Formula.closed_env_l _ ab_block0_closed_l
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun i => Fin.elim0 i))))) i

theorem ab_block_read_l {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    {c X R : M.Domain} (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models KP)
    (ω A m d : (smdl_structure_l I (R := R) source.1.2.1).Domain) :
    Ab_block_d X ω.val A.val m.val d.val ↔ Fp_at_d (kp_pair_l native) ω A m d := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let φ := fp_at_m (𝒞 := kpair_convention_l) (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)
  let ρ : Env N 4 := ⟨fun i => [ω,A,m,d].get i,fun _ => ω⟩
  let η : Env M 5 := ⟨fun i => [X,ω.val,A.val,m.val,d.val].get i,fun _ => X⟩
  have read := lr_rel_decode_l I source.1 source.2 trans φ (by simp -implicitDefEqProofs [φ]) ρ η
    (.bound 0) (fun i => .bound i.succ) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  exact read.trans (fp_at_sat_l (kp_pair_l native) native.1 ρ ..)

variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Ab_task_d (ω : M.Domain) (v : Fin 14 → M.Domain) (D m d : M.Domain) : Prop where
  dense_inside : M.mem D (v 1)
  condition_inside : M.mem d (v 1)
  finite : M.mem m ω
  remaining : M.MemberSubset (v 7) m
  dense : Dense_set_d M (v 5) (v 6) (v 5) D
  hit : M.mem d D
  block : Ab_block_d (v 1) ω (v 4) m d
  ready : Fp_ready_d I (v 7) (v 10) d

def ab_task_m {k} (ω : Term k) (v : Fin 14 → Term k) (D m d : Term k) : Formula 1 k := set[k] ⟪
  ⌜D⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜d⌝ₛ ∈ ⌜v 1⌝ₛ ∧ ⌜m⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜v 7⌝ₛ ⊆ ⌜m⌝ₛ ∧
  ⌜dense_set_m⌝ₚ(⌜v 5⌝ₛ,⌜v 6⌝ₛ,⌜v 5⌝ₛ,⌜D⌝ₛ) ∧ ⌜d⌝ₛ ∈ ⌜D⌝ₛ ∧
  ⌜ab_block_m⌝ₚ(⌜v 1⌝ₛ,⌜ω⌝ₛ,⌜v 4⌝ₛ,⌜m⌝ₛ,⌜d⌝ₛ) ∧
  ⌜fp_ready_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 7⌝ₛ,⌜v 10⌝ₛ,⌜d⌝ₛ)⟫

@[simp] theorem ab_task_closed_l {k} (ω : Term k) (v : Fin 14 → Term k) (D m d : Term k)
    (hω : ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = [])
    (hD : D.freeSupport = []) (hm : m.freeSupport = []) (hd : d.freeSupport = []) :
    (ab_task_m ω v D m d).FreeClosed := by
  simp -implicitDefEqProofs [ab_task_m,Definitional.Formula.FreeClosed,hω,hv,hD,hm,hd,dense_set_m_freeClosed]

theorem ab_task_sat_l (hE : Extensional M) {k} (ρ : Env M k)
    (ω : Term k) (v : Fin 14 → Term k) (D m d : Term k) :
    Formula.satisfies ρ (ab_task_m ω v D m d) ↔
      Ab_task_d I (ω.eval ρ) (fun i => (v i).eval ρ) (D.eval ρ) (m.eval ρ) (d.eval ρ) := by
  simp only [ab_task_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff,dense_set_sat_l M hE,ab_block_sat_l,fp_ready_sat_l I]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h⟩ => ⟨a,b,c,d,e,f,g,h⟩,
    fun h => ⟨h.dense_inside,h.condition_inside,h.finite,h.remaining,h.dense,h.hit,h.block,h.ready⟩⟩

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 每个帧的全部出生稠密任务都有实际背景 ω 满枚举。 -/
theorem Ab_frame_d.tasks_l {Ω cY Y : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d J Ω cY Y v) (hΩ : M.IsOmega Ω) :
    ∃ E e, M.mem E (v 1) ∧
      (∀ D, M.mem D E ↔ M.mem D (v 1) ∧ Dense_set_d M (v 5) (v 6) (v 5) D) ∧
      M.IsSetFunctionFromTo J e Ω E ∧ M.IsSetSurjectiveOnto J e Ω E := by
  let N := smdl_structure_l J (R := v 2) h.model.1.2.1
  have native := ZFC.models_zf_l (h.theory.native_l J hZF hΩ)
  obtain ⟨hω,hA,hP,hU,hn,hC,hT,_⟩ := h.inside
  let ω : N.Domain := ⟨Ω,hω⟩
  let A : N.Domain := ⟨v 4,hA⟩
  let P : N.Domain := ⟨v 5,hP⟩
  let U : N.Domain := ⟨v 6,hU⟩
  let n : N.Domain := ⟨v 7,hn⟩
  let C : N.Domain := ⟨v 8,hC⟩
  let T : N.Domain := ⟨v 9,hT⟩
  obtain ⟨_,_,product,_⟩ := (ab_kernel_read_l J h.model h.transitive native ω A P U n C T).mp h.kernel
  obtain ⟨E,family,e,fn,onto⟩ := h.model.dense_enumeration_l hZF h.transitive native h.count
    P U (product.order_l native)
  refine ⟨E.val,e,E.property,?_,fn,onto⟩
  intro D
  constructor
  · intro hd
    have inside := h.transitive E.val E.property D hd
    let D₀ : N.Domain := ⟨D,inside⟩
    exact ⟨inside,(h.model.dense_code_l J hZF.1 h.transitive (ZF.modelsKP native) P U P D₀).mpr
      ((family D₀).mp ((h.model.2 D E.val).mpr ⟨inside,E.property,hd⟩))⟩
  · rintro ⟨inside,dense⟩
    let D₀ : N.Domain := ⟨D,inside⟩
    exact ((h.model.2 D E.val).mp ((family D₀).mpr
      ((h.model.dense_code_l J hZF.1 h.transitive (ZF.modelsKP native) P U P D₀).mp dense))).2.2

/-- 全乘积稠密性与现有前缀泛型实际选出一个非空的后续任务。 -/
theorem Ab_frame_d.select_l {Ω cY Y D : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d J Ω cY Y v) (hΩ : M.IsOmega Ω) (hD : M.mem D (v 1))
    (dense : Dense_set_d M (v 5) (v 6) (v 5) D) :
    ∃ m d, Ab_task_d J Ω v D m d ∧ M.mem (v 7) m := by
  let N := smdl_structure_l J (R := v 2) h.model.1.2.1
  have native := ZFC.models_zf_l (h.theory.native_l J hZF hΩ)
  obtain ⟨hω,hA,hP,hU,hn,hC,hT,_⟩ := h.inside
  let ω : N.Domain := ⟨Ω,hω⟩
  let A : N.Domain := ⟨v 4,hA⟩
  let P : N.Domain := ⟨v 5,hP⟩
  let U : N.Domain := ⟨v 6,hU⟩
  let n : N.Domain := ⟨v 7,hn⟩
  let C : N.Domain := ⟨v 8,hC⟩
  let T : N.Domain := ⟨v 9,hT⟩
  let D₀ : N.Domain := ⟨D,hD⟩
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l J h.model h.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  have entry := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  obtain ⟨hw,sequence,product,stage⟩ := (ab_kernel_read_l J h.model h.transitive native ω A P U n C T).mp h.kernel
  -- 背景泛型码解回原模型泛型；其接受关系就是已经登记的同一滤子前缀。
  have generic := ((h.model.generic_code_l J hZF.1 h.transitive (ZF.modelsKP native) C T C (v 11)).mp h.generic).2
  have eq : (fun q : N.Domain => M.mem q.val (v 11)) =
      (fun q => N.mem q C ∧ Fp_ready_d J n.val (v 10) q.val) :=
    funext fun q => propext ((h.accepted q.val).trans (and_congr (member (a := q) (b := C)) Iff.rfl))
  rw [eq] at generic
  have hn₀ : N.mem n ω := member.mp h.index
  obtain ⟨δ,alphabet⟩ := (sequence.domain n).mp hn₀
  obtain ⟨m,d,q,hm,lt,hit,fd,cut,_,ready⟩ := product.task_l native hw hn₀ alphabet stage generic
    ((h.model.dense_code_l J hZF.1 h.transitive (ZF.modelsKP native) P U P D₀).mp dense)
  -- 投影 q 已被接受，且 q 正是 d 的原前缀，故已有坐标无需重新选择。
  have ready' : Fp_ready_d J n.val (v 10) d.val := by
    intro i p hi ip
    obtain ⟨i₀,p₀,edge,ei,ep⟩ := (image_entries_l (M := N) (N := M) Subtype.val full fd.function.1 i p).mp ip
    have hi₀ : M.mem i₀.val n.val := ei.symm ▸ hi
    obtain ⟨K,iK,pK⟩ := ready i₀.val p₀.val hi₀
      ((entry i₀ p₀ q).mp ((cut.2 i₀ p₀).mpr ⟨member.mp hi₀,edge⟩))
    exact ⟨K,ei ▸ iK,ep ▸ pK⟩
  have sub : M.MemberSubset n.val m.val :=
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) m.val (member.mpr hm)).transitive n.val (member.mpr lt)
  exact ⟨m.val,d.val,⟨hD,d.property,member.mpr hm,sub,dense,member.mpr hit,
    (ab_block_read_l J h.model h.transitive (ZF.modelsKP native) ω A m d).mpr fd,ready'⟩,member.mpr lt⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 保留原 G 的任意有限前缀帧

从同一个原全乘积泛型构造全部坐标滤子及其有限限制。各帧保留原模型、
Woodin 列、返回图与原前缀偏序；统一地实数的检查名字给出实际名字证书。
这部分只需背景 ZF，不在启动时另选首轮泛型或施加吸收嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_frame_prefix_l {Ω c X R cY Y π G : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω) (embed : Smap_d I Ω c cY X Y π)
    {ω A P T : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A P T)
    (generic : Gset_d P.val T.val P.val X G) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let hN := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    ∃ x : N.Domain, Fn0_d ω ω x ∧ ∃ F, M.IsSequenceOfLength I F Ω ∧
      (∀ i K, Rd_entry_d i K F ↔ M.mem i Ω ∧ Fp_coord_d X P.val G i K) ∧
      ∀ n C S : N.Domain, N.mem n ω → Fp_prefix_d hN ω A n C S →
        ∃ f H r, M.IsSequenceOfLength I f n.val ∧ M.IsRestrictionOf I f F n.val ∧
          Fp_filter_project_d C.val T.val G H ∧
          let v : Fin 14 → M.Domain := fun k =>
            [c,X,R,π,A.val,P.val,T.val,n.val,C.val,S.val,f,H,ω.val,x.val].get k
          Rt_tuple_d v r ∧ Ab_frame_d I Ω cY Y v ∧
          (∀ d, M.mem d G → Fp_ready_d I n.val f d) ∧
          ∀ D : N.Domain, Dense_set_d N P T P D →
            ∃ m d, Ab_task_d I Ω v D.val m d ∧ M.mem n.val m ∧ M.mem d G := by
  -- 一、识别原 ω，并选取所有前缀共用的实际地实数。
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have hw₀ := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ ne => KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have eqω : ω.val = Ω := hZF.1.eq_of_same_members ω.val Ω
    (fun i => ⟨hw₀.2 Ω hΩ.1 i,hΩ.2 ω.val hw₀.1 i⟩)
  obtain ⟨x,identity⟩ := ZF.exists_identityBijection native (kp_pair_l (ZF.modelsKP native)) ω
  have fx : Fn0_d ω ω x := fn0_of_function_l (ZF.modelsKP native) identity.1.1
  have ambient : Fn0_d Ω Ω x.val := by
    have fn := image_function_l (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full identity.1.1
    simpa only [eqω] using! fn0_of_function_l (ZF.modelsKP hZF) fn
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction native (kp_pair_l (ZF.modelsKP native))
    sequence.function sequence.domain
  have fa : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω W :=
    ⟨sequence.function,sequence.domain,fun i hi => ((sequence.domain i).mp hi).elim fun δ edge =>
      ⟨δ,(range δ).mpr ⟨i,edge⟩,edge⟩⟩
  -- 二、同一坐标列的有限限制给出原前缀，检查名字补齐帧的实数证书。
  obtain ⟨F,seq,rows,prefixes⟩ := Smem_d.product_coordinates_l hZF source xt native hw fa product generic
  refine ⟨x,fx,F,eqω ▸ seq,eqω ▸ rows,?_⟩
  intro n C S hn stage
  obtain ⟨f,H,sf,cut,projection,accepted,frozen,gH⟩ := prefixes n C S hn stage
  have g := ((source.generic_code_l I hZF.1 xt (ZF.modelsKP native) C S C H).mp gH).2
  have name := fn_bg_ground_l I hZF.1 source xt native C S C ω ω x H (stage.order_l native) g fx
  have kernel := (ab_kernel_read_l I source xt native ω A P T n C S).mpr ⟨hw,sequence,product,stage⟩
  let v : Fin 14 → M.Domain := fun k =>
    [c,X,R,π,A.val,P.val,T.val,n.val,C.val,S.val,f,H,ω.val,x.val].get k
  have frame : Ab_frame_d I Ω cY Y v :=
    ⟨source,certificate,xt,count,embed,
      ⟨eqω ▸ ω.property,A.property,P.property,T.property,n.property,C.property,S.property,ω.property⟩,
      eqω ▸ ((source.2 n.val ω.val).mp hn).2.2,eqω ▸ kernel,
      sf.2.1,sf.2.2,accepted,gH,ambient,eqω ▸ name⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) v
  refine ⟨f,H,r,sf,cut,projection,tuple,frame,frozen,?_⟩
  -- 三、任务条件属于原 G，因而在每个已冻结坐标上均已被接受。
  intro D dense
  have gG := ((source.generic_code_l I hZF.1 xt (ZF.modelsKP native) P T P G).mp generic).2
  obtain ⟨m,d,hm,nm,gd,dD,fd⟩ := product.task_in_generic_l native hw hn fa gG dense
  have member {a b : N.Domain} : N.mem a b ↔ M.mem a.val b.val :=
    (image_member_l (M := N) (N := M) Subtype.val inj full).symm
  have block := (ab_block_read_l I source xt (ZF.modelsKP native) ω A m d).mpr fd
  have bound : M.MemberSubset n.val m.val :=
    (image_ord_l native hZF Subtype.val inj full (hw.members_areOrdinals (ZF.modelsKP native) m hm)).transitive
      n.val (member.mp nm)
  exact ⟨m.val,d.val,⟨D.property,d.property,eqω ▸ member.mp hm,bound,
    (source.dense_code_l I hZF.1 xt (ZF.modelsKP native) P T P D).mpr dense,
    member.mp dD,eqω ▸ block,frozen d.val gd⟩,member.mp nm,gd⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原吸收行的背景模型与全乘积数据

证书记录原行模型的完整内部 ZFC，以及同一字母表、条件域、顺序和
有限前缀。有限反射运行逐行构造此证书，消费端无需测试模型的 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Ab_product_data_d (ω : M.Domain) (v : Fin 26 → M.Domain) : Prop where
  model : Smem_d I (v 0) (v 1) (v 2)
  theory : Zc_model_d I ω (v 0) (v 1) (v 2)
  transitive : M.TransitiveSet (v 1)
  inside : M.mem ω (v 1) ∧ M.mem (v 4) (v 1) ∧ M.mem (v 5) (v 1) ∧ M.mem (v 6) (v 1) ∧
    M.mem (v 7) (v 1) ∧ M.mem (v 8) (v 1) ∧ M.mem (v 9) (v 1)
  kernel : Ab_kernel_d (v 1) ω (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原返回目标的完整 ZF 来自真实行的返回嵌入 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ab_frame_d.target_l {ω cY Y S : M.Domain} {v : Fin 14 → M.Domain}
    (hw : M.IsOmega ω) (target : Smem_d I cY Y S) (yt : M.TransitiveSet Y)
    (frame : Ab_frame_d I ω cY Y v) :
    (smdl_structure_l I (R := S) target.1.2.1).Models ZF ∧ M.mem ω Y := by
  have source := ZFC.models_zf_l (frame.theory.native_l I hZF hw)
  have theory := frame.returns.native_models_l hZF hw frame.model.1 target.1 source
  have fixed := frame.returns.omega_l I hZF hw frame.transitive yt frame.model target frame.inside.1
  exact ⟨theory,frame.returns.1.1.output_mem_of_pairMember fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal
