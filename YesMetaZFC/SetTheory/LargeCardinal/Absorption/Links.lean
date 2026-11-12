import YesMetaZFC.SetTheory.LargeCardinal.Absorption.QueueStep
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswer
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswerTreeSyntax
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.KeepTransfer
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # 吸收队列的实际模型与返回列

内部 ZFC 证书自动产生已有线性历史接口所需的完整源。
实际队列根图直接延长模型、全部复合箭头及返回列；不再另外假设源证书或交换三角形。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel LargeCardinal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Zc_model_d.mem_source_l {Ω c X R : M.Domain} (h : Zc_model_d I Ω c X R)
    (hΩ : M.IsOmega Ω) (model : Smem_d I c X R) (trans : M.TransitiveSet X) (inside : M.mem Ω X) :
    ∃ K, Ep_source_d I Ω Ω K X R := by
  obtain ⟨z,numbers,_⟩ := rr_layer_mem_l I hZF model trans inside (hΩ.transitive (ZF.modelsKP hZF))
  obtain ⟨K,core⟩ := h.source_l hZF hΩ numbers
  exact ⟨K,core,hΩ,fun _ hx => hx,trans,inside,inside,c,model⟩

end YesMetaZFC.SetTheory.Internal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 首帧的模型和返回因子成为同一线性历史的唯一根节点。 -/
theorem Ab_frame_d.history_zero_l {Ω cY Y S o : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d I Ω cY Y v) (hΩ : M.IsOmega Ω) (target : Smem_d I cY Y S)
    (empty : ∀ a, ¬ M.mem a o) (succ : M.SuccessorOf (v 7) o) :
    ∃ T Q G P, Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) Ω (v 7) T Q G cY Y S P ∧ Rd_entry_d o (v 0) Q ∧ Rd_entry_d o (v 3) P := by
  obtain ⟨K,source⟩ := h.theory.mem_source_l hZF hΩ h.model h.transitive h.inside.1
  obtain ⟨z,α,T,Q,G,P,hz,sz,hist,code,ret⟩ := wi_root_l hZF source h.model h.count target h.returns
  have eqz := hZF.1.eq_of_same_members z o (fun a => iff_of_false (hz a) (empty a))
  subst z
  have eqα := sz.eq hZF.1 succ
  exact ⟨T,Q,G,P,eqα ▸ hist,code,ret⟩

/-- 同一个吸收根图接入完整历史；所有旧图保持，新返回因子与每条旧腿交换。 -/
theorem Ab_step_d.history_l {Ω cY Y S t E e B k D m d E' B' k' D' m' d' j K x T Q G P : M.Domain}
    {v v' : Fin 14 → M.Domain}
    (h : Ab_step_d I Ω v v' t E e B k D m d E' B' k' D' m' d' j K x)
    (hΩ : M.IsOmega Ω) (source : Smem_d I (v 0) (v 1) (v 2)) (next : Ab_frame_d I Ω cY Y v')
    (hist : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) Ω (v 7) T Q G cY Y S P) (stage : M.SuccessorOf (v 7) t)
    (code : Rd_entry_d t (v 0) Q) (ret : Rd_entry_d t (v 3) P) :
    ∃ T' Q' G' P', Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) Ω (v' 7) T' Q' G' cY Y S P' ∧
      Wi_extension_d (v 7) Q G P (v' 7) Q' G' P' ∧
      Rd_entry_d (v 7) (v' 0) Q' ∧ Rd_entry_d (v 7) (v' 3) P' ∧ It_map_d G' t (v 7) j := by
  have ready := next.theory.mem_source_l hZF hΩ next.model next.transitive next.inside.1
  obtain ⟨β,T',Q',G',P',hist',extension,qs,ps,edge⟩ :=
    hist.extend_l hZF hΩ stage code ret source.1 next.model ready next.count h.map next.returns h.square
  have eqβ := extension.1.eq hZF.1 h.stage
  exact ⟨T',Q',G',P',eqβ ▸ hist',eqβ ▸ extension,
    (qs (v 7) (v' 0)).mpr (Or.inr ⟨rfl,rfl⟩),(ps (v 7) (v' 3)).mpr (Or.inr ⟨rfl,rfl⟩),edge⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 带完整模型历史的二十六项吸收状态

前十四项为原吸收帧；随后为出生深度、稠密集族、当前枚举、出生表、游标、
稠密集、终点及条件块；最后四项为线性序、模型列、嵌入列和返回列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u

def ab_head_v {α : Type u} (v : Fin 26 → α) : Fin 14 → α := fun i => v (i.castAdd 12)

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Ab_machine_d (Ω cY Y S : M.Domain) (v : Fin 26 → M.Domain) : Prop where
  queue : Ab_queue_d I Ω cY Y (ab_head_v v) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21)
  history : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) Ω (v 7) (v 22) (v 23) (v 24) cY Y S (v 25)
  code : Rd_entry_d (v 14) (v 0) (v 23)
  returns : Rd_entry_d (v 14) (v 3) (v 25)

def ab_machine_m {n} (Ω cY Y S : Term n) (v : Fin 26 → Term n) : Formula 1 n :=
  .conj (ab_queue_m Ω cY Y (ab_head_v v) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21))
    (set[n] ⟪⌜wi_state_m⌝ₚ(⌜Ω⌝ₛ,⌜v 7⌝ₛ,⌜v 22⌝ₛ,⌜v 23⌝ₛ,⌜v 24⌝ₛ,⌜cY⌝ₛ,⌜Y⌝ₛ,⌜S⌝ₛ,⌜v 25⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜v 14⌝ₛ,⌜v 0⌝ₛ,⌜v 23⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 14⌝ₛ,⌜v 3⌝ₛ,⌜v 25⌝ₛ)⟫)

@[simp] theorem ab_machine_closed_l {n} (Ω cY Y S : Term n) (v : Fin 26 → Term n)
    (hΩ : Ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = []) (hS : S.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) : (ab_machine_m Ω cY Y S v).FreeClosed := by
  simp -implicitDefEqProofs [ab_machine_m,ab_head_v,Definitional.Formula.FreeClosed,hΩ,hcY,hY,hS,hv]

theorem ab_machine_sat_l {n} (ρ : Env M n) (Ω cY Y S : Term n) (v : Fin 26 → Term n) :
    Formula.satisfies ρ (ab_machine_m Ω cY Y S v) ↔
      Ab_machine_d hZF (Ω.eval ρ) (cY.eval ρ) (Y.eval ρ) (S.eval ρ) (fun i => (v i).eval ρ) := by
  simp only [ab_machine_m,Formula.satisfies_conj_iff,ab_queue_sat_l I hZF.1,
    wi_state_sat_l hZF,rd_entry0_sat_l hZF.1]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.queue,h.history,h.code,h.returns⟩⟩

/-- 原吸收方块与完整模型历史共用同一条根边。 -/
def Ab_machine_step_d (Ω : M.Domain) (v w : Fin 26 → M.Domain) (j K x : M.Domain) : Prop :=
  Ab_step_d I Ω (ab_head_v v) (ab_head_v w) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21)
    (w 15) (w 17) (w 18) (w 19) (w 20) (w 21) j K x ∧ w 14 = v 7 ∧
    Wi_keep_d (v 23) (v 24) (v 25) (w 23) (w 24) (w 25) ∧ It_map_d (w 24) (v 14) (v 7) j

def ab_machine_step_m {n} (Ω : Term n) (v w : Fin 26 → Term n) (j K x : Term n) : Formula 1 n :=
  .conj (ab_step_m Ω (ab_head_v v) (ab_head_v w) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21)
    (w 15) (w 17) (w 18) (w 19) (w 20) (w 21) j K x)
    (set[n] ⟪⌜w 14⌝ₛ = ⌜v 7⌝ₛ ∧ ⌜wi_keep_m⌝ₚ(⌜v 23⌝ₛ,⌜v 24⌝ₛ,⌜v 25⌝ₛ,⌜w 23⌝ₛ,⌜w 24⌝ₛ,⌜w 25⌝ₛ) ∧
      ⌜it_map_m⌝ₚ(⌜w 24⌝ₛ,⌜v 14⌝ₛ,⌜v 7⌝ₛ,⌜j⌝ₛ)⟫)

@[simp] theorem ab_machine_step_closed_l {n} (Ω : Term n) (v w : Fin 26 → Term n) (j K x : Term n)
    (hΩ : Ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = [])
    (hj : j.freeSupport = []) (hK : K.freeSupport = []) (hx : x.freeSupport = []) :
    (ab_machine_step_m Ω v w j K x).FreeClosed := by
  simp -implicitDefEqProofs [ab_machine_step_m,ab_head_v,Definitional.Formula.FreeClosed,hΩ,hv,hw,hj,hK,hx]

theorem ab_machine_step_sat_l {n} (ρ : Env M n) (Ω : Term n) (v w : Fin 26 → Term n) (j K x : Term n) :
    Formula.satisfies ρ (ab_machine_step_m Ω v w j K x) ↔
      Ab_machine_step_d hZF (Ω.eval ρ) (fun i => (v i).eval ρ) (fun i => (w i).eval ρ) (j.eval ρ) (K.eval ρ) (x.eval ρ) := by
  simp only [ab_machine_step_m,Ab_machine_step_d,Formula.satisfies_conj_iff,ab_step_sat_l I hZF.1,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,wi_keep_sat_l hZF.1,it_map_sat_l hZF.1]
  rfl

/-- 已吸收首个实数的真实首帧自动成为完整机器的初始集合状态。 -/
theorem Ab_frame_d.machine_zero_l {Ω cY Y S o : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d I Ω cY Y v) (hΩ : M.IsOmega Ω) (target : Smem_d I cY Y S)
    (empty : ∀ a, ¬ M.mem a o) (succ : M.SuccessorOf (v 7) o) :
    ∃ r : M.Domain, ∃ w : Fin 26 → M.Domain,
      Rt_tuple_d w r ∧ Ab_machine_d hZF Ω cY Y S w ∧ ab_head_v w = v ∧ w 14 = o := by
  obtain ⟨E,e,B,D,m,d,_,queue,_,_⟩ := h.queue_zero_l hZF hΩ empty succ
  obtain ⟨T,Q,G,P,hist,code,ret⟩ := h.history_zero_l hZF hΩ target empty succ
  let w : Fin 26 → M.Domain := Fin.addCases (m := 14) (n := 12) v (fun i => [o,E,e,B,o,D,m,d,T,Q,G,P].get i)
  have head : ab_head_v w = v := by
    funext i
    simp only [ab_head_v,w,Fin.addCases_left]
  have machine : Ab_machine_d hZF Ω cY Y S w := ⟨head.symm ▸ queue,hist,code,ret⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) w
  exact ⟨r,w,tuple,machine,head,rfl⟩

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际总后继同时延长队列与模型历史，并保留进入新模型的原根边。 -/
theorem Ab_machine_d.step_l {Ω cY Y S θ x : M.Domain} {v : Fin 26 → M.Domain}
    (h : Ab_machine_d hZF Ω cY Y S v) (hΩ : M.IsOmega Ω)
    (rank : V_d I θ Y) (target : Smem_d I cY Y S) (fx : Fn0_d Ω Ω x) :
    ∃ r : M.Domain, ∃ w : Fin 26 → M.Domain, ∃ j K,
      Rt_tuple_d w r ∧ Ab_machine_d hZF Ω cY Y S w ∧ Ab_machine_step_d hZF Ω v w j K x := by
  obtain ⟨_,v',E',e',B',k',D',m',d',j,K,queue,step,_⟩ := h.queue.step_l hZFC hΩ rank target fx
  obtain ⟨T',Q',G',P',hist,extension,code,ret,edge⟩ :=
    step.history_l hZF hΩ h.queue.frame.model queue.frame h.history h.queue.stage h.code h.returns
  let w : Fin 26 → M.Domain := Fin.addCases (m := 14) (n := 12) v'
    (fun i => [v 7,E',e',B',k',D',m',d',T',Q',G',P'].get i)
  have head : ab_head_v w = v' := by
    funext i
    simp only [ab_head_v,w,Fin.addCases_left]
  have machine : Ab_machine_d hZF Ω cY Y S w := ⟨head.symm ▸ queue,hist,code,ret⟩
  have move : Ab_machine_step_d hZF Ω v w j K x :=
    ⟨head.symm ▸ step,rfl,extension.keep_l hZF h.history,edge⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) w
  exact ⟨r,w,j,K,tuple,machine,move⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际吸收机器的单一集合记录及转移公式

固定二十六项坐标只用于语法量词；运行指标仍是模型内部自然数。
记录保存当前指标及已吸收实数，转移保存原根映射和实际新滤子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Ab_record_d (Ω cY Y S i x r : M.Domain) : Prop :=
  ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r ∧ Ab_machine_d hZF Ω cY Y S v ∧ v 14 = i ∧ v 13 = x

def ab_record_body_m {n} (Ω cY Y S i x r : Term n) : Formula 1 (26+n) :=
  let g : Term n → Term (26+n) := fun t => t.rename (Fin.natAdd 26)
  let v : Fin 26 → Term (26+n) := fun k => .bound (k.castAdd n)
  .conj (rt_tuple_m v (g r)) (.conj (ab_machine_m (g Ω) (g cY) (g Y) (g S) v)
    (.conj (Formula.extensionalEq (v 14) (g i)) (Formula.extensionalEq (v 13) (g x))))

def ab_record_m {n} (Ω cY Y S i x r : Term n) : Formula 1 n :=
  rb_exists_m (ab_record_body_m Ω cY Y S i x r)

@[simp] theorem ab_record_body_closed_l {n} (Ω cY Y S i x r : Term n)
    (hΩ : Ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = []) (hS : S.freeSupport = [])
    (hi : i.freeSupport = []) (hx : x.freeSupport = []) (hr : r.freeSupport = []) :
    (ab_record_body_m Ω cY Y S i x r).FreeClosed := by
  simp -implicitDefEqProofs [ab_record_body_m,Definitional.Formula.FreeClosed,hΩ,hcY,hY,hS,hi,hx]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr)
@[simp] theorem ab_record_closed_l {n} (Ω cY Y S i x r : Term n)
    (hΩ : Ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = []) (hS : S.freeSupport = [])
    (hi : i.freeSupport = []) (hx : x.freeSupport = []) (hr : r.freeSupport = []) :
    (ab_record_m Ω cY Y S i x r).FreeClosed := by
  exact (rb_exists_closed_l _).mpr (ab_record_body_closed_l _ _ _ _ _ _ _ hΩ hcY hY hS hi hx hr)

theorem ab_record_sat_l {n} (ρ : Env M n) (Ω cY Y S i x r : Term n) :
    Formula.satisfies ρ (ab_record_m Ω cY Y S i x r) ↔
      Ab_record_d hZF (Ω.eval ρ) (cY.eval ρ) (Y.eval ρ) (S.eval ρ) (i.eval ρ) (x.eval ρ) (r.eval ρ) := by
  simp only [ab_record_m,ab_record_body_m,Ab_record_d,rb_exists_sat_l,Formula.satisfies_conj_iff,rt_tuple_sat_l hZF.1,
    ab_machine_sat_l hZF,Formula.satisfies_extensionalEq_iff_eq hZF.1,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]

def Ab_record_step_d (Ω r s x : M.Domain) : Prop :=
  ∃ v w : Fin 26 → M.Domain, ∃ j K, Rt_tuple_d v r ∧ Rt_tuple_d w s ∧ Ab_machine_step_d hZF Ω v w j K x

def ab_record_step_m {n} (Ω r s x : Term n) : Formula 1 n :=
  let g : Term n → Term (54+n) := fun t => t.rename (Fin.natAdd 54)
  let u : Fin 54 → Term (54+n) := fun k => .bound (k.castAdd n)
  let v : Fin 26 → Term (54+n) := fun k => u (k.castAdd 28)
  let w : Fin 26 → Term (54+n) := fun k => u (Fin.natAdd 26 (k.castAdd 2))
  rb_exists_m (.conj (rt_tuple_m v (g r)) (.conj (rt_tuple_m w (g s))
    (ab_machine_step_m (g Ω) v w (u 52) (u 53) (g x))))
@[simp] theorem ab_record_step_closed_l {n} (Ω r s x : Term n)
    (hΩ : Ω.freeSupport = []) (hr : r.freeSupport = []) (hs : s.freeSupport = []) (hx : x.freeSupport = []) :
    (ab_record_step_m Ω r s x).FreeClosed := by
  simp -implicitDefEqProofs [ab_record_step_m,Definitional.Formula.FreeClosed,hΩ,hx]
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr),
    rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs)⟩

omit hZF in
/-- 只读取两条原记录与三列保持，不解码吸收模型所满足的理论。 -/
theorem ab_record_keep_l (hE : Extensional M) {n} (ρ : Env M n) (Ω r s x : Term n)
    (step : Formula.satisfies ρ (ab_record_step_m Ω r s x)) :
    ∃ v w : Fin 26 → M.Domain, Rt_tuple_d v (r.eval ρ) ∧ Rt_tuple_d w (s.eval ρ) ∧
      Wi_keep_d (v 23) (v 24) (v 25) (w 23) (w 24) (w 25) := by
  obtain ⟨u,body⟩ := (rb_exists_sat_l ρ _).mp step
  let τ : Env M (54+n) := ⟨Fin.addCases (m := 54) (n := n) (motive := fun _ => M.Domain) u ρ.bound,ρ.free⟩
  let g (t : Term n) : Term (54+n) := t.rename (Fin.natAdd 54)
  let v (k : Fin 26) : Term (54+n) := .bound ((k.castAdd 28).castAdd n)
  let w (k : Fin 26) : Term (54+n) := .bound ((Fin.natAdd 26 (k.castAdd 2)).castAdd n)
  have left := (rt_tuple_sat_l hE τ v (g r)).mp body.1
  have right := (rt_tuple_sat_l hE τ w (g s)).mp body.2.1
  have keep := (wi_keep_sat_l hE τ (v 23) (v 24) (v 25) (w 23) (w 24) (w 25)).mp body.2.2.2.2.1
  simp only [τ,v,w,g,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] at left right keep
  exact ⟨fun k => u (k.castAdd 28),fun k => u (Fin.natAdd 26 (k.castAdd 2)),left,right,keep⟩

theorem ab_record_step_sat_l {n} (ρ : Env M n) (Ω r s x : Term n) :
    Formula.satisfies ρ (ab_record_step_m Ω r s x) ↔
      Ab_record_step_d hZF (Ω.eval ρ) (r.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [ab_record_step_m,rb_exists_sat_l,Formula.satisfies_conj_iff,rt_tuple_sat_l hZF.1,
    ab_machine_step_sat_l hZF,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  constructor
  · rintro ⟨u,first,second,step⟩
    exact ⟨(fun k => u (k.castAdd 28)),(fun k => u (Fin.natAdd 26 (k.castAdd 2))),u 52,u 53,first,second,step⟩
  · rintro ⟨v,w,j,K,first,second,step⟩
    let tail : Fin 28 → M.Domain := Fin.addCases (m := 26) (n := 2) (motive := fun _ => M.Domain) w (fun k : Fin 2 => [j,K].get k)
    let u : Fin 54 → M.Domain := Fin.addCases (m := 26) (n := 28) (motive := fun _ => M.Domain) v tail
    have left : (fun k : Fin 26 => u (k.castAdd 28)) = v := by
      funext k
      simp only [u,Fin.addCases_left]
    have right : (fun k : Fin 26 => u (Fin.natAdd 26 (k.castAdd 2))) = w := by
      funext k
      simp only [u,tail,Fin.addCases_right,Fin.addCases_left]
    exact ⟨u,left.symm ▸ first,right.symm ▸ second,left.symm ▸ right.symm ▸ step⟩

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 指定下一内部指标与实数后，实际状态记录有同一机器转移的后继。 -/
theorem Ab_record_d.step_l {Ω cY Y S θ i j a x r : M.Domain}
    (h : Ab_record_d hZF Ω cY Y S i a r) (hΩ : M.IsOmega Ω)
    (rank : V_d I θ Y) (target : Smem_d I cY Y S) (succ : M.SuccessorOf j i) (fx : Fn0_d Ω Ω x) :
    ∃ s, Ab_record_d hZF Ω cY Y S j x s ∧ Ab_record_step_d hZF Ω r s x := by
  obtain ⟨v,tuple,machine,index,_⟩ := h
  obtain ⟨s,w,e,K,tuple',machine',step⟩ := machine.step_l hZFC hΩ rank target fx
  have stage : M.SuccessorOf (v 7) i := index ▸ machine.queue.stage
  have nextIndex : w 14 = j := step.2.1.trans (stage.eq hZF.1 succ)
  exact ⟨s,⟨w,tuple',machine',nextIndex,step.1.real⟩,v,w,e,K,tuple,tuple',step⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原机器记录收集历史坐标

投影只读取最后四项，模型、复合箭头和返回图没有重新选择。
唯一性由原二十六项记录的唯一坐标保证，因此外层替代直接给出整列历史函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ab_history_d (r s : M.Domain) : Prop := ∃ v : Fin 26 → M.Domain,
  Rt_tuple_d v r ∧ Rd_quad_d s (v 22) (v 23) (v 24) (v 25)

def ab_history_m {n} (r s : Term n) : Formula 1 n :=
  let g : Term n → Term (26+n) := fun t => t.rename (Fin.natAdd 26)
  let v : Fin 26 → Term (26+n) := fun k => .bound (k.castAdd n)
  rb_exists_m (.conj (rt_tuple_m v (g r)) (rd_quad_m (g s) (v 22) (v 23) (v 24) (v 25)))

@[simp] theorem ab_history_closed_l {n} (r s : Term n) (hr : r.freeSupport = []) (hs : s.freeSupport = []) :
    (ab_history_m r s).FreeClosed := by
  simp -implicitDefEqProofs [ab_history_m,Definitional.Formula.FreeClosed,hs]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hr)

theorem ab_history_sat_l (hE : Extensional M) {n} (ρ : Env M n) (r s : Term n) :
    Formula.satisfies ρ (ab_history_m r s) ↔ Ab_history_d (r.eval ρ) (s.eval ρ) := by
  simp only [ab_history_m,Ab_history_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hE,rd_quad_sat_l hE,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]

theorem Ab_history_d.unique_l (hE : Extensional M) {r s t : M.Domain}
    (h : Ab_history_d r s) (g : Ab_history_d r t) : s = t := by
  obtain ⟨v,vr,p,pp,q,qp,sp⟩ := h
  obtain ⟨w,wr,p',pp',q',qp',tp⟩ := g
  have eq := rt_tuple_inj_l vr wr
  subst w
  have ep := kpair_unique_l M hE pp' pp
  subst p'
  have eq := kpair_unique_l M hE qp' qp
  subst q'
  exact kpair_unique_l M hE sp tp

theorem ab_history_function_l (hZF : M.Models ZF) {ω P F : M.Domain}
    (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) F ω P)
    (rows : ∀ i r, Rd_entry_d i r F → ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r) :
    ∃ D H, Fn0_d ω D H ∧ ∀ i s, Rd_entry_d i s H ↔ ∃ r, Rd_entry_d i r F ∧ Ab_history_d r s := by
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ r, ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,r,⌜(.bound 2 : Term 3)⌝ₛ) ∧
    ⌜ab_history_m⌝ₚ(r,⌜(.bound 0 : Term 3)⌝ₛ)⟫ }
  let ρ : Env M 1 := ⟨fun _ => F,fun _ => F⟩
  have read i s : φ.denote ρ i s ↔ ∃ r, Rd_entry_d i r F ∧ Ab_history_d r s := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,ab_history_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have total i (hi : M.mem i ω) : ∃ s, φ.denote ρ i s := by
    obtain ⟨r,_,ir⟩ := fn.2.2 i hi
    obtain ⟨v,tuple⟩ := rows i r ir
    obtain ⟨s,quad⟩ := rd_quad_exists_l (ZF.modelsKP hZF) (v 22) (v 23) (v 24) (v 25)
    exact ⟨s,(read i s).mpr ⟨r,ir,v,tuple,quad⟩⟩
  have unique i s t (hs : φ.denote ρ i s) (ht : φ.denote ρ i t) : s = t := by
    obtain ⟨r,ir,rs⟩ := (read i s).mp hs
    obtain ⟨q,iq,qt⟩ := (read i t).mp ht
    exact rs.unique_l hZF.1 (fn.1.2 i q r iq ir ▸ qt)
  obtain ⟨D,range⟩ := ZF.exists_functionalImage hZF φ ρ ω total unique
  obtain ⟨H,function,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF))
    φ ρ total (fun i _ => unique i) (fun i s hi hs => (range s).mpr ⟨i,hi,hs⟩)
  refine ⟨D,H,fn0_of_function_l (ZF.modelsKP hZF) function,fun i s => (graph i s).trans ?_⟩
  exact ⟨fun h => (read i s).mp h.2,fun h => ⟨fn.input_mem_of_pairMember h.choose_spec.1,(read i s).mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 测试模型内的有限状态与外层驱动

状态和转移的全部量词限制于固定测试模型 P；原模型的力迫与源证书仍由 P 内部解释。
读取只用传递隶属结构和原公式语义。实际后继由有限反射入口构造，
不在相对化接口中要求测试模型满足 ZF 或 ZFC。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u

def ab_record_native_m : Formula 1 7 := ab_record_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
@[simp] theorem ab_record_native_closed_l : ab_record_native_m.FreeClosed := by
  simp -implicitDefEqProofs [ab_record_native_m]

def ab_relative0_m : Formula 1 8 := .conj (.mem (.bound 7) (.bound 0))
  (lr_rel_m ab_record_native_m (.bound 0) (fun i => .bound i.succ))
@[simp] theorem ab_relative0_closed_l : ab_relative0_m.FreeClosed :=
  ⟨⟨rfl,rfl⟩,lr_rel_closed_l _ ab_record_native_closed_l _ _ rfl (fun _ => rfl)⟩

def Ab_relative_d {M : Structure.{u}} (P Ω cY Y S i x r : M.Domain) : Prop :=
  Formula.satisfies (⟨fun k => [P,Ω,cY,Y,S,i,x,r].get k,fun _ => P⟩ : Env M 8) ab_relative0_m

def ab_relative_m {n} (P Ω cY Y S i x r : Term n) : Formula 1 n :=
  ab_relative0_m.bind (fun k => [P,Ω,cY,Y,S,i,x,r].get k)
@[simp] theorem ab_relative_closed_l {n} (P Ω cY Y S i x r : Term n)
    (hP : P.freeSupport = []) (hΩ : Ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = [])
    (hS : S.freeSupport = []) (hi : i.freeSupport = []) (hx : x.freeSupport = []) (hr : r.freeSupport = []) :
    (ab_relative_m P Ω cY Y S i x r).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hP (Fin.cases hΩ (Fin.cases hcY (Fin.cases hY (Fin.cases hS
      (Fin.cases hi (Fin.cases hx (Fin.cases hr (fun k => Fin.elim0 k))))))))) _).mpr ab_relative0_closed_l

theorem ab_relative_sat_l {M : Structure.{u}} {n} (ρ : Env M n) (P Ω cY Y S i x r : Term n) :
    Formula.satisfies ρ (ab_relative_m P Ω cY Y S i x r) ↔
      Ab_relative_d (P.eval ρ) (Ω.eval ρ) (cY.eval ρ) (Y.eval ρ) (S.eval ρ) (i.eval ρ) (x.eval ρ) (r.eval ρ) := by
  rw [ab_relative_m,Formula.satisfies_bind]
  apply Formula.closed_env_l _ ab_relative0_closed_l
  funext k
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) k

def ab_relative_step0_m : Formula 1 5 := .conj (.mem (.bound 2) (.bound 0)) (.conj (.mem (.bound 3) (.bound 0))
  (lr_rel_m (ab_record_step_m (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)) (.bound 0) (fun i => .bound i.succ)))
@[simp] theorem ab_relative_step0_closed_l : ab_relative_step0_m.FreeClosed :=
  ⟨⟨rfl,rfl⟩,⟨⟨rfl,rfl⟩,lr_rel_closed_l _ (by simp -implicitDefEqProofs) _ _ rfl (fun _ => rfl)⟩⟩

def Ab_relative_step_d {M : Structure.{u}} (P Ω r s x : M.Domain) : Prop :=
  Formula.satisfies (⟨fun k => [P,Ω,r,s,x].get k,fun _ => P⟩ : Env M 5) ab_relative_step0_m

def ab_relative_step_m {n} (P Ω r s x : Term n) : Formula 1 n :=
  ab_relative_step0_m.bind (fun k => [P,Ω,r,s,x].get k)
@[simp] theorem ab_relative_step_closed_l {n} (P Ω r s x : Term n)
    (hP : P.freeSupport = []) (hΩ : Ω.freeSupport = []) (hr : r.freeSupport = []) (hs : s.freeSupport = [])
    (hx : x.freeSupport = []) : (ab_relative_step_m P Ω r s x).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hP (Fin.cases hΩ (Fin.cases hr (Fin.cases hs (Fin.cases hx (fun k => Fin.elim0 k)))))) _).mpr
      ab_relative_step0_closed_l

theorem ab_relative_step_sat_l {M : Structure.{u}} {n} (ρ : Env M n) (P Ω r s x : Term n) :
    Formula.satisfies ρ (ab_relative_step_m P Ω r s x) ↔
      Ab_relative_step_d (P.eval ρ) (Ω.eval ρ) (r.eval ρ) (s.eval ρ) (x.eval ρ) := by
  rw [ab_relative_step_m,Formula.satisfies_bind]
  apply Formula.closed_env_l _ ab_relative_step0_closed_l
  funext k
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) k

variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
  {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
include trans

theorem ab_relative_read_l (ω cY Y S i x r : (smdl_structure_l I (R := R) model.1.2.1).Domain) :
    Ab_relative_d P ω.val cY.val Y.val S.val i.val x.val r.val ↔
      Formula.satisfies (⟨fun k => [ω,cY,Y,S,i,x,r].get k,fun _ => ω⟩ :
        Env (smdl_structure_l I (R := R) model.1.2.1) 7) ab_record_native_m := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let ρ : Env N 7 := ⟨fun k => [ω,cY,Y,S,i,x,r].get k,fun _ => ω⟩
  let η : Env M 8 := ⟨fun k => [P,ω.val,cY.val,Y.val,S.val,i.val,x.val,r.val].get k,fun _ => P⟩
  have decode := lr_rel_decode_l I model.1 model.2 trans ab_record_native_m ab_record_native_closed_l ρ η
    (.bound 0) (fun k => .bound k.succ) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))
  exact ⟨fun h => decode.mp h.2,fun h => ⟨r.property,decode.mpr h⟩⟩

theorem ab_relative_step_read_l (ω r s x : (smdl_structure_l I (R := R) model.1.2.1).Domain) :
    Ab_relative_step_d P ω.val r.val s.val x.val ↔
      Formula.satisfies (⟨fun k => [ω,r,s,x].get k,fun _ => ω⟩ :
        Env (smdl_structure_l I (R := R) model.1.2.1) 4)
        (ab_record_step_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let φ := ab_record_step_m (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)
  let ρ : Env N 4 := ⟨fun k => [ω,r,s,x].get k,fun _ => ω⟩
  let η : Env M 5 := ⟨fun k => [P,ω.val,r.val,s.val,x.val].get k,fun _ => P⟩
  have decode := lr_rel_decode_l I model.1 model.2 trans φ (by simp -implicitDefEqProofs [φ]) ρ η
    (.bound 0) (fun k => .bound k.succ) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))
  exact ⟨fun h => decode.mp h.2.2,fun h => ⟨r.property,s.property,decode.mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相对吸收状态的外层模型及实际根边

完整初等图通过有限支撑真值定理读到外层；两次解码的模型由成员满图实际同构。
记录、滤子追加及返回复合始终使用原集合值，不另选替代模型或替代嵌入。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem Rt_tuple_d.image_l (e : M.Domain → N.Domain)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {n} {v : Fin (n+1) → M.Domain} {p : M.Domain} (h : Rt_tuple_d v p) : Rt_tuple_d (fun i => e (v i)) (e p) := by
  induction n generalizing p with
  | zero => exact congrArg e h
  | succ n ih =>
    obtain ⟨q,pair,tail⟩ := h
    exact ⟨e q,image_kpair_l e full pair,ih tail⟩

end YesMetaZFC.SetTheory.InnerModel

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem It_comp_d.image_l (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y) {f g h : M.Domain}
    (ff : ∀ p, M.mem p f → ∃ x y, KPair_d M p x y)
    (fg : ∀ p, M.mem p g → ∃ x y, KPair_d M p x y) (comp : It_comp_d f g h) :
    It_comp_d (e f) (e g) (e h) := by
  refine ⟨?_,fun x z => ⟨?_,?_⟩⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := (full h p).mp hp
    obtain ⟨a,b,ab⟩ := comp.1 q hq
    exact ⟨e a,e b,image_kpair_l e full ab⟩
  · intro xz
    obtain ⟨a,c,ac,rfl,rfl⟩ := (image_entries_l e full comp.1 x z).mp xz
    obtain ⟨b,ab,bc⟩ := (comp.2 a c).mp ac
    exact ⟨e b,(image_entries_l e full ff _ _).mpr ⟨a,b,ab,rfl,rfl⟩,
      (image_entries_l e full fg _ _).mpr ⟨b,c,bc,rfl,rfl⟩⟩
  · rintro ⟨y,xy,yz⟩
    obtain ⟨a,b,ab,rfl,by'⟩ := (image_entries_l e full ff x y).mp xy
    obtain ⟨b',c,bc,b'y,rfl⟩ := (image_entries_l e full fg y z).mp yz
    have eq := inj (by'.trans b'y.symm)
    subst b'
    exact (image_entries_l e full comp.1 _ _).mpr ⟨a,c,(comp.2 a c).mpr ⟨b,ab,bc⟩,rfl,rfl⟩

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) model.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

/-- 每个实际相对状态给出外层的同一可数传递 ZFC 模型及完整返回嵌入。 -/
theorem Ab_relative_d.outer_l {ω cY Y S i x r : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) model.1.2.1).IsOmega ω) (hΩ : M.IsOmega ω.val)
    (target : Smem_d (kp_pair_l (ZF.modelsKP native)) cY Y S)
    (h : Ab_relative_d P ω.val cY.val Y.val S.val i.val x.val r.val) :
    ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r.val ∧ v 14 = i.val ∧ v 13 = x.val ∧
      Smem_d I (v 0) (v 1) (v 2) ∧ M.TransitiveSet (v 1) ∧ M.CardinalLessOrEqual I (v 1) ω.val ∧
        Zc_model_d I ω.val (v 0) (v 1) (v 2) ∧ Smap_d I ω.val (v 0) cY.val (v 1) Y.val (v 3) := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I model trans
  obtain ⟨v,tuple,state,index,real⟩ := (ab_record_sat_l native _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).mp
    ((ab_relative_read_l I model trans ω cY Y S i x r).mp h)
  have frame := state.queue.frame
  have source := image_smem_l (M := N) (N := M) Subtype.val inj full (ZF.modelsKP native) (ZF.modelsKP hZF) frame.model
  obtain ⟨f,fn⟩ := frame.count
  have count := image_injection_l (M := N) (N := M) (hEN := hZF.1) (hPN := KP.exists_pair (ZF.modelsKP hZF)) Subtype.val inj full fn
  have theory := image_zc_model_l (M := N) (N := M) Subtype.val inj full native hZF hw hΩ frame.theory
  have ret := image_smap_l (M := N) (N := M) Subtype.val inj full native hZF hw hΩ frame.model.1 target.1 frame.returns
  exact ⟨fun k => (v k).val,tuple.image_l Subtype.val full,congrArg Subtype.val index,congrArg Subtype.val real,
    source,image_transitive_l (M := N) (N := M) Subtype.val full frame.transitive,⟨f.val,count⟩,theory,ret⟩

/-- 相邻记录的原根边与返回复合在外层成立，旧滤子前缀和固定条件仍为原集合。 -/
theorem Ab_relative_step_d.outer_l
    {ω cY Y S i l a x r s : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) model.1.2.1).IsOmega ω) (hΩ : M.IsOmega ω.val)
    (target : Smem_d (kp_pair_l (ZF.modelsKP native)) cY Y S)
    (old : Ab_relative_d P ω.val cY.val Y.val S.val i.val a.val r.val)
    (next : Ab_relative_d P ω.val cY.val Y.val S.val l.val x.val s.val)
    (move : Ab_relative_step_d P ω.val r.val s.val x.val) :
    ∃ v w : Fin 26 → M.Domain, ∃ j K, Rt_tuple_d v r.val ∧ Rt_tuple_d w s.val ∧
      Smap_d I ω.val (v 0) (w 0) (v 1) (w 1) j ∧ Smap_d I ω.val (w 0) cY.val (w 1) Y.val (w 3) ∧
      It_comp_d j (w 3) (v 3) ∧ M.SuccessorOf (w 7) (v 7) ∧
      M.IsRestrictionOf I (v 10) (w 10) (v 7) ∧ Rd_entry_d (v 7) K (w 10) ∧
      Rd_entry_d (v 4) (w 4) j ∧ Rd_entry_d (v 5) (w 5) j ∧ Rd_entry_d (v 6) (w 6) j ∧
      Rd_entry_d (v 8) (v 8) j ∧ (∀ p, M.mem p (v 8) → Rd_entry_d p p j) := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I model trans
  have entry := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  obtain ⟨v,vr,source,_,_⟩ := (ab_record_sat_l native _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).mp
    ((ab_relative_read_l I model trans ω cY Y S i a r).mp old)
  obtain ⟨w,ws,dest,_,_⟩ := (ab_record_sat_l native _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).mp
    ((ab_relative_read_l I model trans ω cY Y S l x s).mp next)
  obtain ⟨v₀,w₀,j,K,vr₀,ws₀,step,_,_,_⟩ := (ab_record_step_sat_l native _ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mp
    ((ab_relative_step_read_l I model trans ω r s x).mp move)
  have ev := rt_tuple_inj_l vr₀ vr
  have ew := rt_tuple_inj_l ws₀ ws
  subst v₀ w₀
  have map := image_smap_l (M := N) (N := M) Subtype.val inj full native hZF hw hΩ source.queue.frame.model.1 dest.queue.frame.model.1 step.map
  have ret := image_smap_l (M := N) (N := M) Subtype.val inj full native hZF hw hΩ dest.queue.frame.model.1 target.1 dest.queue.frame.returns
  have square := step.square.image_l Subtype.val inj full step.map.1.1.1.1 dest.queue.frame.returns.1.1.1.1
  have successor := image_successor_l (hEN := hZF.1) Subtype.val inj full native.1 step.stage
  have keep := image_restriction_l native hZF Subtype.val inj full dest.queue.frame.function.1 step.keep
  refine ⟨(fun k => (v k).val),(fun k => (w k).val),j.val,K.val,vr.image_l Subtype.val full,ws.image_l Subtype.val full,
    map,ret,square,successor,keep,(entry (v 7) K (w 10)).mp step.last,
    (entry (v 4) (w 4) j).mp step.alphabet,(entry (v 5) (w 5) j).mp step.product,
    (entry (v 6) (w 6) j).mp step.order,(entry (v 8) (v 8) j).mp step.fixed,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := (full (v 8) p).mp hp
  exact (entry q q j).mp (step.points q hq)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相对无限运行的原记录读取

运行本身在外层，所有行及其真实后继留在测试模型 P。
证书保存原运行图、行公式、相邻转移，以及有限反射恢复的完整原队列和全部历史。
返回目标的实际隶属结构、传递性及壳内三参数投影的留壳性质均由原运行工厂证明。
原有界图、序数界、返回目标中的实数集及传递种子均由同一反射工厂实际构造。
全部壳内实数的覆盖由原实数枚举的满射性保证。
其中完整 ZFC 只属于各行模型，不作为测试模型的额外公理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

structure Ab_run_d (J : kpair_convention_l.Interpretation M) (P ω cY Y S F : M.Domain) : Prop where
  function : Fn0_d ω P F
  rows : ∀ i r, Rd_entry_d i r F → ∃ x, M.mem x P ∧ Ab_relative_d P ω cY Y S i x r
  steps : ∀ i j r s, M.SuccessorOf j i → Rd_entry_d i r F → Rd_entry_d j s F →
    ∃ x, M.mem x P ∧ Ab_relative_step_d P ω r s x
  queues : ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    Ab_queue_d J ω cY Y (ab_head_v v) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21)
  histories : ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    Wi_state_d J ω (v 7) (v 22) (v 23) (v 24) cY Y S (v 25)
  target : Smem_d J cY Y S
  transitive : M.TransitiveSet Y
  projects : ∀ C U H, M.mem C P → M.mem U P → M.mem H P →
    ∃ K, M.mem K P ∧ Fp_filter_project_d C U H K
  graphs : Rg_closed_d J P
  height : ∃ θ, M.mem θ P ∧ Oh_bound_d Y θ
  seed : ∃ B Z, M.mem B Y ∧ M.mem Z Y ∧ Rb_reals_d P ω B ∧ Tc_d B Z
  cover : ∀ x, M.mem x P → Fn0_d ω ω x → ∃ i r, M.mem i ω ∧ Rd_entry_d i r F ∧ Ab_relative_d P ω cY Y S i x r

/-- 原记录的模型列与返回列只需外延性和传递性即可读取。 -/
theorem Ab_run_d.columns_l {J : kpair_convention_l.Interpretation M} (hE : Extensional M)
    {c P R : M.Domain} (model : Smem_d J c P R) (trans : M.TransitiveSet P)
    {ω cY Y S : (smdl_structure_l J (R := R) model.1.2.1).Domain} {F i r : M.Domain}
    (run : Ab_run_d J P ω.val cY.val Y.val S.val F) (ir : Rd_entry_d i r F) :
    ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r ∧
      Rd_entry_d i (v 0) (v 23) ∧ Rd_entry_d i (v 3) (v 25) ∧ M.SuccessorOf (v 7) i := by
  let N := smdl_structure_l J (R := R) model.1.2.1
  have ext := smem_ext_l J model.1 model.2 trans hE
  have full := smem_full_l J model trans
  obtain ⟨x,hx,row⟩ := run.rows i r ir
  let i₀ : N.Domain := ⟨i,trans ω.val ω.property i (run.function.bound_l ir).1⟩
  let r₀ : N.Domain := ⟨r,(run.function.bound_l ir).2⟩
  let x₀ : N.Domain := ⟨x,hx⟩
  let ρ : Env N 7 := ⟨fun k => [ω,cY,Y,S,i₀,x₀,r₀].get k,fun _ => ω⟩
  obtain ⟨v,body⟩ := (rb_exists_sat_l ρ _).mp
    ((ab_relative_read_l J model trans ω cY Y S i₀ x₀ r₀).mp row)
  let τ : Env N 33 := ⟨Fin.addCases (m := 26) (n := 7) (motive := fun _ => N.Domain) v ρ.bound,ρ.free⟩
  let g (t : Term 7) : Term 33 := t.rename (Fin.natAdd 26)
  let b (k : Fin 26) : Term 33 := .bound (k.castAdd 7)
  have tuple : Rt_tuple_d v r₀ := by
    simpa only [b,g,τ,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] using!
      (rt_tuple_sat_l ext τ b (g (.bound 6))).mp body.1
  have index : (v 14).val = i := congrArg Subtype.val
    ((Formula.satisfies_extensionalEq_iff_eq ext τ (b 14) (g (.bound 4))).mp body.2.2.1)
  have entries {a b f : N.Domain} (edge : Rd_entry_d a b f) : Rd_entry_d a.val b.val f.val := by
    obtain ⟨q,pair,mem⟩ := edge
    exact ⟨q.val,image_kpair_l (M := N) (N := M) Subtype.val full pair,
      (smem_member_l J model.1 model.2 q f).mp mem⟩
  have code : Rd_entry_d (v 14) (v 0) (v 23) := by
    simpa only [b,τ,Term.eval_bound,Fin.addCases_left] using!
      (rd_entry0_sat_l ext τ (b 14) (b 0) (b 23)).mp body.2.1.2.2.1
  have ret : Rd_entry_d (v 14) (v 3) (v 25) := by
    simpa only [b,τ,Term.eval_bound,Fin.addCases_left] using!
      (rd_entry0_sat_l ext τ (b 14) (b 3) (b 25)).mp body.2.1.2.2.2
  have stage : N.SuccessorOf (v 7) (v 14) :=
    (Formula.satisfies_isSuccessor_iff τ (b 7) (b 14)).mp body.2.1.1.2.2.1
  exact ⟨fun k => (v k).val,tuple.image_l Subtype.val full,index ▸ entries code,index ▸ entries ret,
    index ▸ image_successor_l (M := N) (N := M) (hEN := hE) Subtype.val
      (fun _ _ eq => Subtype.ext eq) full ext stage⟩

/-- 相邻原记录的三列保持只消费原转移公式，测试壳无需 ZF。 -/
theorem Ab_run_d.keep_l {J : kpair_convention_l.Interpretation M} (hE : Extensional M)
    {c P R : M.Domain} (model : Smem_d J c P R) (trans : M.TransitiveSet P)
    {ω cY Y S : (smdl_structure_l J (R := R) model.1.2.1).Domain} {F i j r s : M.Domain}
    {v w : Fin 26 → M.Domain} (run : Ab_run_d J P ω.val cY.val Y.val S.val F)
    (succ : M.SuccessorOf j i) (ir : Rd_entry_d i r F) (js : Rd_entry_d j s F)
    (vr : Rt_tuple_d v r) (ws : Rt_tuple_d w s) :
    Wi_keep_d (v 23) (v 24) (v 25) (w 23) (w 24) (w 25) := by
  let N := smdl_structure_l J (R := R) model.1.2.1
  obtain ⟨x,hx,step⟩ := run.steps i j r s succ ir js
  let r₀ : N.Domain := ⟨r,(run.function.bound_l ir).2⟩
  let s₀ : N.Domain := ⟨s,(run.function.bound_l js).2⟩
  let x₀ : N.Domain := ⟨x,hx⟩
  obtain ⟨a,b,ar,bs,keep⟩ := ab_record_keep_l (smem_ext_l J model.1 model.2 trans hE) _
    (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    ((ab_relative_step_read_l J model trans ω r₀ s₀ x₀).mp step)
  have full := smem_full_l J model trans
  have ea := rt_tuple_inj_l (ar.image_l Subtype.val full) vr
  have eb := rt_tuple_inj_l (bs.image_l Subtype.val full) ws
  exact ea ▸ eb ▸ wi_keep_outer_l J hE model trans keep

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原有限阶段的实数并集恰为测试模型的全部实数

正向用原名字见证的有界图回收，反向用同一运行已完成的逐实数吸收。
此处的实数族来自原阶段扩张；与极限前缀扩张的对应由后续名字比较完成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Ab_stage_real_d (ω F x : M.Domain) : Prop := Fn0_d ω ω x ∧
  ∃ i r, ∃ v : Fin 26 → M.Domain, ∃ A, Rd_entry_d i r F ∧ Rt_tuple_d v r ∧ M.mem A (v 1) ∧
    Fn_bg_d (v 1) (v 8) (v 9) (v 8) ω A (v 11) x

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ab_run_d.stage_real_inside_l {P ω cY Y S F x : M.Domain} (trans : M.TransitiveSet P)
    (run : Ab_run_d I P ω cY Y S F) (real : Ab_stage_real_d ω F x) : M.mem x P := by
  obtain ⟨fx,i,r,v,_,ir,vr,_,code⟩ := real
  have inside := Internal.Rt_tuple_d.members_l vr trans (run.function.bound_l ir).2
  exact Rg_closed_d.real_code_inside_l hZF run.graphs trans (inside 1) (inside 8) (inside 9)
    (inside 8) (inside 11) code (fn0_function_l (ZF.modelsKP hZF) fx).1.1

theorem Ab_run_d.stage_reals_l {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
    {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F B : M.Domain}
    (space : Rb_reals_d P ω.val B) (run : Ab_run_d I P ω.val cY.val Y.val S.val F) :
    ∀ x, Ab_stage_real_d ω.val F x ↔ M.mem x B := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  have ext := smem_ext_l I model.1 model.2 trans hZF.1
  have full := smem_full_l I model trans
  intro x
  refine ⟨fun real => (space x).mpr ⟨run.stage_real_inside_l hZF trans real,real.1⟩,fun hx => ?_⟩
  obtain ⟨i,r,hi,ir,row⟩ := run.cover x ((space x).mp hx).1 ((space x).mp hx).2
  let i₀ : N.Domain := ⟨i,trans ω.val ω.property i hi⟩
  let r₀ : N.Domain := ⟨r,(run.function.bound_l ir).2⟩
  let x₀ : N.Domain := ⟨x,((space x).mp hx).1⟩
  let ρ : Env N 7 := ⟨fun k => [ω,cY,Y,S,i₀,x₀,r₀].get k,fun _ => ω⟩
  obtain ⟨v,body⟩ := (rb_exists_sat_l ρ _).mp ((ab_relative_read_l I model trans ω cY Y S i₀ x₀ r₀).mp row)
  let τ : Env N 33 := ⟨Fin.addCases (m := 26) (n := 7) (motive := fun _ => N.Domain) v ρ.bound,ρ.free⟩
  let g (t : Term 7) : Term 33 := t.rename (Fin.natAdd 26)
  let b (k : Fin 26) : Term 33 := .bound (k.castAdd 7)
  have tuple : Rt_tuple_d v r₀ := by
    simpa only [b,g,τ,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] using!
      (rt_tuple_sat_l ext τ b (g (.bound 6))).mp body.1
  have eq : (v 13).val = x := congrArg Subtype.val
    ((Formula.satisfies_extensionalEq_iff_eq ext τ (b 13) (g (.bound 5))).mp body.2.2.2)
  have vr := tuple.image_l Subtype.val full
  have frame := (run.queues i r (fun k => (v k).val) ir vr).frame
  have named : Ab_stage_real_d ω.val F (v 13).val :=
    ⟨frame.real,i,r,(fun k => (v k).val),(v 12).val,ir,vr,frame.inside.2.2.2.2.2.2.2,frame.name⟩
  exact eq ▸ named

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原可数源、原泛型和指定实数构造有限反射测试模型

种子由原传递模型及有限个子集组成，故仍传递可数。测试壳逐点固定原源、
原泛型和全部实数参数；状态、后继存在句和最后的派生模型断言均有实际
反射证书。这里不声称有限反射能产生完整 ZFC 测试模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def ab_next_m : Formula 1 7 := .existsE
  (.conj (ab_record_native_m.bind (fun i => ([.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 7,.newest] : List (Term 8)).get i))
    ((ab_record_step_m (.bound 0 : Term 4) (.bound 1) (.bound 2) (.bound 3)).bind
      (fun i => ([.bound 1,.bound 6,.newest,.bound 7] : List (Term 8)).get i)))

@[simp] theorem ab_next_closed_l : ab_next_m.FreeClosed := by
  change _ ∧ _
  exact ⟨(Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) _).mpr ab_record_native_closed_l,
    (Definitional.Formula.freeClosed_bind_iff_of_closed _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) _).mpr
        (by simp -implicitDefEqProofs)⟩

def ab_test_queries_l {n} (φ : Formula 1 n) (hc : φ.FreeClosed) : List Lr_formula :=
  [⟨7,ab_record_native_m,ab_record_native_closed_l⟩,
   ⟨4,ab_record_step_m (.bound 0) (.bound 1) (.bound 2) (.bound 3),by simp -implicitDefEqProofs⟩,
   ⟨7,ab_next_m,ab_next_closed_l⟩,
   ⟨n+1,Relative.dr_m φ .newest (fun i => .bound i.succ),Relative.dr_closed_l φ hc _ _ rfl (fun _ => rfl)⟩,
   ⟨33,ab_record_body_m (.bound 0 : Term 7) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6),
     by simp -implicitDefEqProofs⟩]

theorem ab_test_l (hZFC : M.Models ZFC) {ω X G c R : M.Domain} (hw : M.IsOmega ω)
    (source : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (trans : M.TransitiveSet X) (hω : M.mem ω X)
    (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (R := R) source.1.2.1).Models KP)
    (count : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X ω)
    (subG : M.MemberSubset G X) {n} (φ : Formula 1 n) (hc : φ.FreeClosed)
    (x : Fin n → M.Domain) (real : ∀ i, Fn0_d ω ω (x i)) {m} (v : Fin m → M.Domain) :
    ∃ T α V d S P b U π,
      Rf_hull_d (ZFC.models_zf_l hZFC) ω T (ab_test_queries_l φ hc) v α V d S P b U π ∧
      M.mem ω P ∧ M.mem X P ∧ M.MemberSubset X P ∧ M.mem G P ∧
      Rd_entry_d ω ω π ∧ Rd_entry_d X X π ∧ Rd_entry_d G G π ∧
      (∀ a, M.mem a X → Rd_entry_d a a π) ∧ ∀ i, M.mem (x i) P ∧ Rd_entry_d (x i) (x i) π := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let N := smdl_structure_l I (R := R) source.1.2.1
  have full := smem_full_l I source trans
  have realSub i : M.MemberSubset (x i) X := by
    intro p hp
    obtain ⟨a,ha,b,hb,pair⟩ := (real i).1 p hp
    let a₀ : N.Domain := ⟨a,trans ω hω a ha⟩
    let b₀ : N.Domain := ⟨b,trans ω hω b hb⟩
    obtain ⟨q,hq⟩ := (kp_pair_l native).total a₀ b₀
    have eq : q.val = p := kpair_unique_l M hZF.1 (image_kpair_l (M := N) (N := M) Subtype.val full hq) pair
    exact eq ▸ q.property
  let w : Fin (n+2) → M.Domain := Fin.cases X (Fin.cases G x)
  have sub i : M.MemberSubset (w i) X := Fin.cases (fun _ h => h) (Fin.cases subG realSub) i
  obtain ⟨B,finite,points⟩ := ZF.finite_params_l I hZF hw w
  obtain ⟨T,union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) X B
  have small := ZF.countable_union_two_l I hZF hw count (ZF.finite_countable_l I hZF hw finite) union
  have xt : M.MemberSubset X T := fun a ha => (union a).mpr (Or.inl ha)
  have wt i : M.mem (w i) T := (union (w i)).mpr (Or.inr ((points (w i)).mpr ⟨i,rfl⟩))
  have tt : M.TransitiveSet T := by
    intro a ha b hb
    rcases (union a).mp ha with ha | ha
    · exact xt b (trans a ha b hb)
    · obtain ⟨i,rfl⟩ := (points a).mp ha
      exact xt b (sub i b hb)
  obtain ⟨α,V,d,S,P,b,U,π,hull⟩ := rf_hull_l hZFC hw tt small (ab_test_queries_l φ hc) v
  exact ⟨T,α,V,d,S,P,b,U,π,hull,hull.seed ω (xt ω hω),hull.seed X (wt 0),
    (fun a ha => hull.seed a (xt a ha)),hull.seed G (wt 1),hull.fixed ω (xt ω hω),
    hull.fixed X (wt 0),hull.fixed G (wt 1),(fun a ha => hull.fixed a (xt a ha)),
    fun i => ⟨hull.seed (x i) (wt i.succ.succ),hull.fixed (x i) (wt i.succ.succ)⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原队列时钟和两种工作回合的弱读取

只读取原记录中已有的游标、有限终点、条件命中和工作选择。
这些断言均由外延性与成员满包含运输，不解码测试模型的集合论模式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

structure Ab_timing_d (ω i : M.Domain) (v : Fin 26 → M.Domain) : Prop where
  index : v 14 = i
  stage : M.SuccessorOf (v 7) i
  cursor : M.mem (v 18) ω
  endpoint : M.mem (v 20) ω
  bound : M.MemberSubset (v 18) i
  future : M.mem i (v 20)
  hit : M.mem (v 21) (v 19)
  done : v 7 = v 20 → M.mem (v 21) (v 11)

theorem ab_record_timing_l (hE : Extensional M) {n} (ρ : Env M n) (ω cY Y S i x r : Term n)
    (row : Formula.satisfies ρ (ab_record_m ω cY Y S i x r)) :
    ∃ v : Fin 26 → M.Domain, Rt_tuple_d v (r.eval ρ) ∧ Ab_timing_d (ω.eval ρ) (i.eval ρ) v := by
  obtain ⟨v,body⟩ := (rb_exists_sat_l ρ _).mp row
  let τ : Env M (26+n) := ⟨Fin.addCases (m := 26) (n := n) (motive := fun _ => M.Domain) v ρ.bound,ρ.free⟩
  let g (t : Term n) : Term (26+n) := t.rename (Fin.natAdd 26)
  let b (k : Fin 26) : Term (26+n) := .bound (k.castAdd n)
  have tuple : Rt_tuple_d v (r.eval ρ) := by
    simpa only [b,g,τ,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] using!
      (rt_tuple_sat_l hE τ b (g r)).mp body.1
  have index : v 14 = i.eval ρ := by
    simpa only [b,g,τ,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] using!
      (Formula.satisfies_extensionalEq_iff_eq hE τ (b 14) (g i)).mp body.2.2.1
  have stage : M.SuccessorOf (v 7) (v 14) := by
    simpa only [b,τ,Term.eval_bound,Fin.addCases_left] using!
      (Formula.satisfies_isSuccessor_iff τ (b 7) (b 14)).mp body.2.1.1.2.2.1
  have cursor : M.mem (v 18) (ω.eval ρ) := by
    simpa only [b,g,τ,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] using!
      (Formula.satisfies_mem_iff τ (b 18) (g ω)).mp body.2.1.1.2.2.2.1
  have bound : M.MemberSubset (v 18) (v 14) := by
    simpa only [b,τ,Term.eval_bound,Fin.addCases_left] using!
      (Formula.satisfies_subset_iff τ (b 18) (b 14)).mp body.2.1.1.2.2.2.2.1
  have task := body.2.1.1.2.2.2.2.2.2.1
  have endpoint : M.mem (v 20) (ω.eval ρ) := by
    simpa only [b,g,τ,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] using!
      (Formula.satisfies_mem_iff τ (b 20) (g ω)).mp task.2.2.1
  have remaining : M.MemberSubset (v 7) (v 20) := by
    simpa only [b,τ,Term.eval_bound,Fin.addCases_left] using!
      (Formula.satisfies_subset_iff τ (b 7) (b 20)).mp task.2.2.2.1
  have hit : M.mem (v 21) (v 19) := by
    simpa only [b,τ,Term.eval_bound,Fin.addCases_left] using!
      (Formula.satisfies_mem_iff τ (b 21) (b 19)).mp task.2.2.2.2.2.1
  have done : v 7 = v 20 → M.mem (v 21) (v 11) := by
    intro eq
    have eq' : Formula.satisfies τ (Formula.extensionalEq (b 7) (b 20)) :=
      (Formula.satisfies_extensionalEq_iff_eq hE τ (b 7) (b 20)).mpr (by simpa only [b,τ,Term.eval_bound,Fin.addCases_left] using eq)
    exact (body.2.1.1.2.2.2.2.2.2.2 eq').2
  exact ⟨v,tuple,index ▸ ⟨rfl,stage,cursor,endpoint,bound,remaining _ stage.predecessor_mem,hit,done⟩⟩

def Ab_clock_step_d (v w : Fin 26 → M.Domain) : Prop :=
  (M.mem (v 7) (v 20) ∧ w 18 = v 18 ∧ w 20 = v 20) ∨
    (v 7 = v 20 ∧ M.SuccessorOf (w 18) (v 18))

theorem ab_record_clock_step_l (hE : Extensional M) {n} (ρ : Env M n) (ω r s x : Term n)
    (step : Formula.satisfies ρ (ab_record_step_m ω r s x)) :
    ∃ v w : Fin 26 → M.Domain, Rt_tuple_d v (r.eval ρ) ∧ Rt_tuple_d w (s.eval ρ) ∧ Ab_clock_step_d v w := by
  obtain ⟨u,body⟩ := (rb_exists_sat_l ρ _).mp step
  let τ : Env M (54+n) := ⟨Fin.addCases (m := 54) (n := n) (motive := fun _ => M.Domain) u ρ.bound,ρ.free⟩
  let g (t : Term n) : Term (54+n) := t.rename (Fin.natAdd 54)
  let v (k : Fin 26) : Term (54+n) := .bound ((k.castAdd 28).castAdd n)
  let w (k : Fin 26) : Term (54+n) := .bound ((Fin.natAdd 26 (k.castAdd 2)).castAdd n)
  have left := (rt_tuple_sat_l hE τ v (g r)).mp body.1
  have right := (rt_tuple_sat_l hE τ w (g s)).mp body.2.1
  obtain ⟨D,d,work,_,_⟩ := body.2.2.1.1
  have choice := work.2.2.2.2.2
  have read (a b : Term (54+n+2)) := Formula.satisfies_extensionalEq_iff_eq hE ((τ.push D).push d) a b
  have timing : Ab_clock_step_d (fun k => (v k).eval τ) (fun k => (w k).eval τ) := by
    rcases choice with old | next
    · exact Or.inl ⟨old.1,(read ..).mp old.2.1,(read ..).mp old.2.2.2.1⟩
    · exact Or.inr ⟨(read ..).mp next.1,next.2⟩
  simp only [τ,v,w,g,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] at left right timing
  exact ⟨fun k => u (k.castAdd 28),fun k => u (Fin.natAdd 26 (k.castAdd 2)),left,right,timing⟩

variable {J : kpair_convention_l.Interpretation M} (hE : Extensional M) {c P R : M.Domain}
  (model : Smem_d J c P R) (trans : M.TransitiveSet P)
include hE trans

theorem Ab_run_d.timing_l {ω cY Y S : (smdl_structure_l J (R := R) model.1.2.1).Domain} {F i r : M.Domain}
    (run : Ab_run_d J P ω.val cY.val Y.val S.val F) (ir : Rd_entry_d i r F) :
    ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r ∧ Ab_timing_d ω.val i v := by
  let N := smdl_structure_l J (R := R) model.1.2.1
  have ext := smem_ext_l J model.1 model.2 trans hE
  have full := smem_full_l J model trans
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have mem {a b : N.Domain} := image_member_l (M := N) (N := M) Subtype.val inj full (a := a) (b := b)
  obtain ⟨x,hx,row⟩ := run.rows i r ir
  let i₀ : N.Domain := ⟨i,trans ω.val ω.property i (run.function.bound_l ir).1⟩
  let r₀ : N.Domain := ⟨r,(run.function.bound_l ir).2⟩
  let x₀ : N.Domain := ⟨x,hx⟩
  obtain ⟨v,tuple,timing⟩ := ab_record_timing_l ext _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
    ((ab_relative_read_l J model trans ω cY Y S i₀ x₀ r₀).mp row)
  exact ⟨fun k => (v k).val,tuple.image_l Subtype.val full,
    congrArg Subtype.val timing.index,
    image_successor_l (M := N) (N := M) (hEN := hE) Subtype.val inj full ext timing.stage,
    mem.mpr timing.cursor,mem.mpr timing.endpoint,
    (image_subset_iff_l (M := N) (N := M) Subtype.val inj full).mpr timing.bound,
    mem.mpr timing.future,mem.mpr timing.hit,fun eq => mem.mpr (timing.done (Subtype.ext eq))⟩

theorem Ab_run_d.clock_step_l {ω cY Y S : (smdl_structure_l J (R := R) model.1.2.1).Domain}
    {F i j r s : M.Domain} {v w : Fin 26 → M.Domain}
    (run : Ab_run_d J P ω.val cY.val Y.val S.val F) (succ : M.SuccessorOf j i)
    (ir : Rd_entry_d i r F) (js : Rd_entry_d j s F) (vr : Rt_tuple_d v r) (ws : Rt_tuple_d w s) :
    Ab_clock_step_d v w := by
  let N := smdl_structure_l J (R := R) model.1.2.1
  have ext := smem_ext_l J model.1 model.2 trans hE
  have full := smem_full_l J model trans
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  obtain ⟨x,hx,step⟩ := run.steps i j r s succ ir js
  let r₀ : N.Domain := ⟨r,(run.function.bound_l ir).2⟩
  let s₀ : N.Domain := ⟨s,(run.function.bound_l js).2⟩
  let x₀ : N.Domain := ⟨x,hx⟩
  obtain ⟨a,b,ar,bs,move⟩ := ab_record_clock_step_l ext _ (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    ((ab_relative_step_read_l J model trans ω r₀ s₀ x₀).mp step)
  have ea := rt_tuple_inj_l (ar.image_l Subtype.val full) vr
  have eb := rt_tuple_inj_l (bs.image_l Subtype.val full) ws
  rw [← ea,← eb]
  rcases move with ⟨active,ek,em⟩ | ⟨done,next⟩
  · exact Or.inl ⟨(image_member_l (M := N) (N := M) Subtype.val inj full).mpr active,
      congrArg Subtype.val ek,congrArg Subtype.val em⟩
  · exact Or.inr ⟨congrArg Subtype.val done,
      image_successor_l (M := N) (N := M) (hEN := hE) Subtype.val inj full ext next⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相邻原记录共用的乘积箭头

根图及其乘积、顺序条目从原转移公式读取；同一图在新历史的箭头列中登记。
读取只需外延性和传递性，完整初等性与返回交换律由已构造的背景历史提供。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

theorem ab_record_links_l (hE : Extensional M) {n} (ρ : Env M n) (ω r s x : Term n)
    (step : Formula.satisfies ρ (ab_record_step_m ω r s x)) :
    ∃ v w : Fin 26 → M.Domain, ∃ f, Rt_tuple_d v (r.eval ρ) ∧ Rt_tuple_d w (s.eval ρ) ∧
      It_map_d (w 24) (v 14) (v 7) f ∧ Rd_entry_d (v 5) (w 5) f ∧ Rd_entry_d (v 6) (w 6) f ∧
      Rd_entry_d (v 4) (w 4) f ∧ M.SuccessorOf (w 7) (v 7) ∧
      (∀ a b, Rd_entry_d a b (v 10) ↔ M.mem a (v 7) ∧ Rd_entry_d a b (w 10)) ∧
      (∀ q, M.mem q (v 8) → Rd_entry_d q q f) ∧
      (∀ p Z, Rd_entry_d p Z (w 17) ↔ Td_depth_next_d (ω.eval ρ) (v 14) (v 17) (v 16) f p Z) := by
  obtain ⟨u,body⟩ := (rb_exists_sat_l ρ _).mp step
  let τ : Env M (54+n) := ⟨Fin.addCases (m := 54) (n := n) (motive := fun _ => M.Domain) u ρ.bound,ρ.free⟩
  let g (t : Term n) : Term (54+n) := t.rename (Fin.natAdd 54)
  let v (k : Fin 26) : Term (54+n) := .bound ((k.castAdd 28).castAdd n)
  let w (k : Fin 26) : Term (54+n) := .bound ((Fin.natAdd 26 (k.castAdd 2)).castAdd n)
  let f : Term (54+n) := .bound ((52 : Fin 54).castAdd n)
  have left := (rt_tuple_sat_l hE τ v (g r)).mp body.1
  have right := (rt_tuple_sat_l hE τ w (g s)).mp body.2.1
  have edge := (it_map_sat_l hE τ (w 24) (v 14) (v 7) f).mp body.2.2.2.2.2
  have data := body.2.2.1.2
  have product := (rd_entry0_sat_l hE τ (v 5) (w 5) f).mp data.2.2.2.2.2.2.1
  have order := (rd_entry0_sat_l hE τ (v 6) (w 6) f).mp data.2.2.2.2.2.2.2.1
  have alphabet := (rd_entry0_sat_l hE τ (v 4) (w 4) f).mp data.2.2.2.2.2.1
  have stage := (Formula.satisfies_isSuccessor_iff τ (w 7) (v 7)).mp data.2.2.1
  have keep : ∀ a b, Rd_entry_d a b ((v 10).eval τ) ↔
      M.mem a ((v 7).eval τ) ∧ Rd_entry_d a b ((w 10).eval τ) := by
    have rule : Formula.satisfies τ (.forallE (.forallE (.iff
        (rd_entry_m (.bound 1) .newest (v 10).weaken.weaken)
        (.conj (.mem (.bound 1) (v 7).weaken.weaken)
          (rd_entry_m (.bound 1) .newest (w 10).weaken.weaken))))) := data.2.2.2.1.2
    simpa only [Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,rd_entry_sat_l hE,Definitional.Term.eval_weaken] using! rule
  have points : ∀ q, M.mem q ((v 8).eval τ) → Rd_entry_d q q (f.eval τ) := by
    have rule : Formula.satisfies τ (.forallE (.imp (.mem .newest (v 8).weaken)
        (rd_entry0_m .newest .newest f.weaken))) := data.2.2.2.2.2.2.2.2.2.1
    simpa only [Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
      rd_entry0_sat_l hE,Definitional.Term.eval_weaken] using! rule
  have table : ∀ p Z, Rd_entry_d p Z ((w 17).eval τ) ↔
      Td_depth_next_d (ω.eval ρ) ((v 14).eval τ) ((v 17).eval τ) ((v 16).eval τ) (f.eval τ) p Z := by
    have rule : Formula.satisfies τ (.forallE (.forallE (.iff
        (rd_entry0_m (.bound 1) .newest (w 17).weaken.weaken)
        (td_depth_next_m (g ω).weaken.weaken (v 14).weaken.weaken (v 17).weaken.weaken
          (v 16).weaken.weaken f.weaken.weaken (.bound 1) .newest)))) := data.2.2.2.2.2.2.2.2.2.2.2.1
    simpa only [Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,rd_entry0_sat_l hE,
      td_depth_next_sat_l hE,Definitional.Term.eval_weaken,g,τ,rb_old_eval_l] using! rule
  simp only [τ,v,w,f,g,rb_old_eval_l,Term.eval_bound,Fin.addCases_left] at left right edge product order alphabet stage keep points table
  exact ⟨fun k => u (k.castAdd 28),fun k => u (Fin.natAdd 26 (k.castAdd 2)),u 52,left,right,edge,product,order,alphabet,stage,keep,points,table⟩

theorem Ab_run_d.step_links_l {J : kpair_convention_l.Interpretation M} (hE : Extensional M)
    {c P R : M.Domain} (model : Smem_d J c P R) (trans : M.TransitiveSet P)
    {ω cY Y S : (smdl_structure_l J (R := R) model.1.2.1).Domain}
    {F i j r s : M.Domain} {v w : Fin 26 → M.Domain}
    (run : Ab_run_d J P ω.val cY.val Y.val S.val F) (succ : M.SuccessorOf j i)
    (ir : Rd_entry_d i r F) (js : Rd_entry_d j s F) (vr : Rt_tuple_d v r) (ws : Rt_tuple_d w s) :
    ∃ f, It_map_d (w 24) i j f ∧ Rd_entry_d (v 5) (w 5) f ∧ Rd_entry_d (v 6) (w 6) f ∧
      Rd_entry_d (v 4) (w 4) f ∧ M.SuccessorOf (w 7) (v 7) ∧
      (∀ a b, Rd_entry_d a b (v 10) ↔ M.mem a (v 7) ∧ Rd_entry_d a b (w 10)) ∧
      (∀ q, M.mem q (v 8) → Rd_entry_d q q f) ∧
      (∀ p Z, Rd_entry_d p Z (w 17) ↔ Td_depth_next_d ω.val (v 14) (v 17) (v 16) f p Z) := by
  let N := smdl_structure_l J (R := R) model.1.2.1
  have ext := smem_ext_l J model.1 model.2 trans hE
  have full := smem_full_l J model trans
  obtain ⟨x,hx,step⟩ := run.steps i j r s succ ir js
  let r₀ : N.Domain := ⟨r,(run.function.bound_l ir).2⟩
  let s₀ : N.Domain := ⟨s,(run.function.bound_l js).2⟩
  let x₀ : N.Domain := ⟨x,hx⟩
  obtain ⟨a,b,f,ar,bs,edge,product,order,alphabet,stage,keep,points,table⟩ := ab_record_links_l ext _ (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    ((ab_relative_step_read_l J model trans ω r₀ s₀ x₀).mp step)
  have entries {x y F : N.Domain} (edge : Rd_entry_d x y F) : Rd_entry_d x.val y.val F.val := by
    obtain ⟨p,pair,hp⟩ := edge
    exact ⟨p.val,image_kpair_l (M := N) (N := M) Subtype.val full pair,(smem_member_l J model.1 model.2 p F).mp hp⟩
  have ea := rt_tuple_inj_l (ar.image_l Subtype.val full) vr
  have eb := rt_tuple_inj_l (bs.image_l Subtype.val full) ws
  have edge' : It_map_d (w 24) (v 14) (v 7) f.val := by
    obtain ⟨p,pair,pf⟩ := edge
    exact ea ▸ eb ▸ ⟨p.val,image_kpair_l (M := N) (N := M) Subtype.val full pair,entries pf⟩
  obtain ⟨z,zr,timing⟩ := run.timing_l hE model trans ir
  have timing := rt_tuple_inj_l zr vr ▸ timing
  have entry (x y F : N.Domain) : Rd_entry_d x y F ↔ Rd_entry_d x.val y.val F.val := by
    let ρ : Env N 3 := ⟨fun k => [x,y,F].get k,fun _ => x⟩
    exact (rd_entry0_sat_l ext ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l J model trans (rd_entry0_delta_l ..) ρ).trans
        (rd_entry0_sat_l hE (image_env_l (M := N) (N := M) Subtype.val ρ) (.bound 0) (.bound 1) (.bound 2)))
  have bounds {x y : M.Domain} {F : N.Domain} (xy : Rd_entry_d x y F.val) :=
    xy.choose_spec.1.mem_l M trans (trans F.val F.property _ xy.choose_spec.2)
  have restriction : ∀ x y, Rd_entry_d x y (a 10).val ↔ M.mem x (a 7).val ∧ Rd_entry_d x y (b 10).val := by
    intro x y
    constructor
    · intro xy
      let x₀ : N.Domain := ⟨x,(bounds xy).1⟩
      let y₀ : N.Domain := ⟨y,(bounds xy).2⟩
      have saved := (keep x₀ y₀).mp ((entry x₀ y₀ (a 10)).mpr xy)
      exact ⟨(smem_member_l J model.1 model.2 x₀ (a 7)).mp saved.1,entries saved.2⟩
    · rintro ⟨hx,xy⟩
      let x₀ : N.Domain := ⟨x,(bounds xy).1⟩
      let y₀ : N.Domain := ⟨y,(bounds xy).2⟩
      exact entries ((keep x₀ y₀).mpr ⟨(smem_member_l J model.1 model.2 x₀ (a 7)).mpr hx,
        (entry x₀ y₀ (b 10)).mpr xy⟩)
  have frozen : ∀ q, M.mem q (a 8).val → Rd_entry_d q q f.val := by
    intro q hq
    let q₀ : N.Domain := ⟨q,trans (a 8).val (a 8).property q hq⟩
    exact entries (points q₀ ((smem_member_l J model.1 model.2 q₀ (a 8)).mpr hq))
  -- 新表的完整定义域给出每个出生编号的真实壳内有序对。
  -- 这一步只用于恢复同一原表的成员，不要求壳额外满足配对公理。
  obtain ⟨z,zs,next⟩ := run.timing_l hE model trans js
  have next := rt_tuple_inj_l zs ws ▸ next
  have ai := (congrFun ea 14).trans timing.index
  have bj := (congrFun eb 14).trans next.index
  have newborn := run.queues j s (fun k => (b k).val) js (bs.image_l Subtype.val full)
  obtain ⟨D,prod,fn⟩ := newborn.birth.history.table
  have transport : ∀ p Z, Rd_entry_d p Z (b 17).val ↔
      Td_depth_next_d ω.val (a 14).val (a 17).val (a 16).val f.val p Z := by
    intro p Z
    constructor
    · intro pZ
      let p₀ : N.Domain := ⟨p,(bounds pZ).1⟩
      let Z₀ : N.Domain := ⟨Z,(bounds pZ).2⟩
      obtain ⟨i,l,x,pair,hl,choice,xZ⟩ := (table p₀ Z₀).mp ((entry p₀ Z₀ (b 17)).mpr pZ)
      refine ⟨i.val,l.val,x.val,image_kpair_l (M := N) (N := M) Subtype.val full pair,
        (smem_member_l J model.1 model.2 l ω).mp hl,?_,entries xZ⟩
      exact choice.elim (fun h => Or.inl ⟨(smem_member_l J model.1 model.2 i (a 14)).mp h.1,entries h.2⟩)
        (fun h => Or.inr ⟨congrArg Subtype.val h.1,entries h.2⟩)
    · rintro ⟨i,l,x,pair,hl,choice,xZ⟩
      have hi : M.mem i (b 14).val := by
        rw [bj]
        exact choice.elim (fun h => (succ i).mpr (Or.inl (ai ▸ h.1)))
          (fun h => (h.1.trans ai).symm ▸ succ.predecessor_mem)
      let ξ : Env M 3 := ⟨fun k => [p,i,l].get k,fun _ => p⟩
      have code : J.Codes p i l := (J.realizes ξ (.bound 0) (.bound 1) (.bound 2)).mp
        ((kpair_sat_l M hE ξ (.bound 0) (.bound 1) (.bound 2)).mpr pair)
      obtain ⟨z,_,pz⟩ := fn.2.1 p ((prod p).mpr ⟨i,hi,l,hl,code⟩)
      let p₀ : N.Domain := ⟨p,(bounds pz).1⟩
      have coords := pair.mem_l M trans p₀.property
      let i₀ : N.Domain := ⟨i,coords.1⟩
      let l₀ : N.Domain := ⟨l,coords.2⟩
      let x₀ : N.Domain := ⟨x,(bounds xZ).1⟩
      let Z₀ : N.Domain := ⟨Z,(bounds xZ).2⟩
      let η : Env N 3 := ⟨fun k => [p₀,i₀,l₀].get k,fun _ => p₀⟩
      have pair₀ : KPair_d N p₀ i₀ l₀ := (kpair0_sat_l ext η (.bound 0) (.bound 1) (.bound 2)).mp
        ((smem_delta_image_l J model trans (kpair0_delta_l ..) η).mpr
          ((kpair0_sat_l hE (image_env_l (M := N) (N := M) Subtype.val η) (.bound 0) (.bound 1) (.bound 2)).mpr pair))
      apply entries ((table p₀ Z₀).mpr ⟨i₀,l₀,x₀,pair₀,(smem_member_l J model.1 model.2 l₀ ω).mpr hl,?_,
        (entry x₀ Z₀ f).mpr xZ⟩)
      exact choice.elim (fun h => Or.inl ⟨(smem_member_l J model.1 model.2 i₀ (a 14)).mpr h.1,
        (entry p₀ x₀ (a 17)).mpr h.2⟩)
        (fun h => Or.inr ⟨Subtype.ext h.1,(entry l₀ x₀ (a 16)).mpr h.2⟩)
  exact ⟨f.val,timing.index ▸ timing.stage.eq hE succ ▸ edge',
    ea ▸ eb ▸ entries product,ea ▸ eb ▸ entries order,ea ▸ eb ▸ entries alphabet,
    ea ▸ eb ▸ image_successor_l (M := N) (N := M) (hEN := hE) Subtype.val
      (fun _ _ eq => Subtype.ext eq) full ext stage,ea ▸ eb ▸ restriction,ea ▸ frozen,ea ▸ eb ▸ transport⟩

end YesMetaZFC.SetTheory.LargeCardinal
