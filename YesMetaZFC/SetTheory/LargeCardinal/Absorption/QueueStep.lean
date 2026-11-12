import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Ground.DenseEnumeration
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Return
import YesMetaZFC.Model.Forcing.Collapse.ProductGroundComparison
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Target
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Pending

/-! # 全乘积稠密任务的出生表

深度 t 的旧表保存前 t 个出生模型的完整枚举行在当前模型中的像。
当前模型的枚举行单独保存；推进时将它追加为第 t 行，再沿实际根图运输整张表。
任务游标独立于吸收轮号，允许一个有限条件块占用多轮。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Ab_birth_d (Ω X R P T t E e F : M.Domain) : Prop where
  family : Df_family_d X P T E
  enumeration : Td_enum_d Ω X R E e
  history : Td_depth_d I Ω X R E t F

def ab_birth_m {n} (Ω X R P T t E e F : Term n) : Formula 1 n := set[n] ⟪
  ⌜df_family_m⌝ₚ(⌜X⌝ₛ,⌜P⌝ₛ,⌜T⌝ₛ,⌜E⌝ₛ) ∧ ⌜td_enum_m⌝ₚ(⌜Ω⌝ₛ,⌜X⌝ₛ,⌜R⌝ₛ,⌜E⌝ₛ,⌜e⌝ₛ) ∧
  ⌜td_depth_m⌝ₚ(⌜Ω⌝ₛ,⌜X⌝ₛ,⌜R⌝ₛ,⌜E⌝ₛ,⌜t⌝ₛ,⌜F⌝ₛ)⟫
derive_free_closed ab_birth_m

theorem ab_birth_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Ω X R P T t E e F : Term n) :
    Formula.satisfies ρ (ab_birth_m Ω X R P T t E e F) ↔
      Ab_birth_d I (Ω.eval ρ) (X.eval ρ) (R.eval ρ) (P.eval ρ) (T.eval ρ) (t.eval ρ) (E.eval ρ) (e.eval ρ) (F.eval ρ) := by
  simp only [ab_birth_m,Formula.satisfies_conj_iff,df_family_sat_l hE,td_enum_sat_l hE,td_depth_sat_l I hE]
  exact ⟨fun ⟨a,b,c⟩ => ⟨a,b,c⟩,fun h => ⟨h.family,h.enumeration,h.history⟩⟩

/-- 游标 k 读取出生编号 (i,l)；当前出生行尚未进入旧表时直接读取其完整枚举。 -/
def Ab_pick_d (Ω t F e k D : M.Domain) : Prop :=
  ∀ i l p, M.mem i Ω → M.mem l Ω → Oc_pair_d I i l k → KPair_d M p i l →
    (M.mem i t ∧ Rd_entry_d p D F) ∨ (i = t ∧ Rd_entry_d l D e)

def ab_pick_m {n} (Ω t F e k D : Term n) : Formula 1 n := set[n] ⟪∀ i l p,
  i ∈ ⌜Ω⌝ₛ → l ∈ ⌜Ω⌝ₛ → ⌜oc_pair_m (𝒞 := kpair_convention_l)⌝ₚ(i,l,⌜k⌝ₛ) → ⌜kpair0_m⌝ₚ(p,i,l) →
    ((i ∈ ⌜t⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(p,⌜D⌝ₛ,⌜F⌝ₛ)) ∨ (i = ⌜t⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(l,⌜D⌝ₛ,⌜e⌝ₛ)))⟫
derive_free_closed ab_pick_m

theorem ab_pick_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Ω t F e k D : Term n) :
    Formula.satisfies ρ (ab_pick_m Ω t F e k D) ↔
      Ab_pick_d I (Ω.eval ρ) (t.eval ρ) (F.eval ρ) (e.eval ρ) (k.eval ρ) (D.eval ρ) := by
  simp only [ab_pick_m,Ab_pick_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,oc_pair_sat_l I hE,kpair0_sat_l hE,rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 初始历史为空，但当前模型的全部稠密集已经实际枚举。 -/
theorem ab_birth_zero_l {Ω c X R : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d J c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l J (R := R) source.1.2.1).Models ZF)
    (count : M.CardinalLessOrEqual J X Ω)
    (P T : (smdl_structure_l J (R := R) source.1.2.1).Domain)
    (order : Cond_order_d (smdl_structure_l J (R := R) source.1.2.1) P T P) :
    ∃ t E e F, (∀ x, ¬ M.mem x t) ∧ Ab_birth_d J Ω X R P.val T.val t E e F := by
  obtain ⟨E,family,e,fn,onto⟩ := source.dense_enumeration_l hZF trans native count P T order
  have family' := (df_family_read_l J hZF.1 source trans (ZF.modelsKP native) P T E).mpr family
  have enum : Td_enum_d Ω X R E.val e :=
    ⟨(fn0_of_function_l (ZF.modelsKP hZF) fn).mono_target_l (trans E.val E.property),
      fun _ D edge => (source.2 D E.val).mpr ⟨trans E.val E.property D (fn.output_mem_of_pairMember edge),
        E.property,fn.output_mem_of_pairMember edge⟩,
      fun D _ hD => onto D ((source.2 D E.val).mp hD).2.2⟩
  obtain ⟨t,F,empty,table,_⟩ := td_depth_zero_l J (X := X) (R := R) (U := E.val) (z := P.val) hΩ
  exact ⟨t,E.val,e,F,empty,⟨family',enum,table⟩⟩

/-- 旧出生行和本轮完整枚举行一并运输，目标的当前枚举重新覆盖其全部稠密集。 -/
theorem Ab_birth_d.step_l {Ω c X R c' X' R' j t E e F : M.Domain}
    (hΩ : M.IsOmega Ω) (source : Smem_d J c X R) (target : Smem_d J c' X' R')
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet X') (map : Smap_d J Ω c c' X X' j)
    (native : (smdl_structure_l J (R := R) source.1.2.1).Models KP)
    (native' : (smdl_structure_l J (R := R') target.1.2.1).Models KP)
    (count : M.CardinalLessOrEqual J X' Ω)
    {P T : (smdl_structure_l J (R := R) source.1.2.1).Domain}
    {P' T' : (smdl_structure_l J (R := R') target.1.2.1).Domain}
    (old : Ab_birth_d J Ω X R P.val T.val t E e F)
    (pP : Rd_entry_d P.val P'.val j) (tT : Rd_entry_d T.val T'.val j) :
    ∃ t' E' e' F', M.SuccessorOf t' t ∧ Ab_birth_d J Ω X' R' P'.val T'.val t' E' e' F' ∧
      Rd_entry_d E E' j ∧ ∀ p D, Rd_entry_d p D F' ↔ Td_depth_next_d Ω t F e j p D := by
  let E₀ : (smdl_structure_l J (R := R) source.1.2.1).Domain := ⟨E,old.family.inside⟩
  obtain ⟨E',family,eE⟩ := old.family.image_l J hZF hΩ source target xt yt map native native'
    (E := E₀) pP tT
  have transport D D' (edge : Rd_entry_d D D' j) (letter : Rd_entry_d D E R) : Rd_entry_d D' E' R' :=
    (map.relation_l J hZF hΩ source.1 target.1 edge eE).mp letter
  obtain ⟨t',F',succ,table,law⟩ := old.history.step_l hZF hΩ map.1.1 transport old.enumeration.function old.enumeration.letters
  -- 可数性来自目标载体；反向函数仅在原单射像外使用一个实际稠密集。
  obtain ⟨o,_,ho⟩ := hΩ.1.1
  obtain ⟨D,hD,oD⟩ := old.enumeration.function.2.1 o ho
  obtain ⟨D',hD',dD⟩ := map.1.1.2.2 D hD
  have nonempty : M.mem D' E' := ((target.2 D' E').mp (transport D D' dD (old.enumeration.letters o D oD))).2.2
  obtain ⟨a,fa⟩ := ZF.exists_inclusionInjection hZF J (yt E' family.inside)
  obtain ⟨b,fb⟩ := count
  obtain ⟨c,fc⟩ := ZF.exists_compositionInjection hZF J fa fb
  obtain ⟨e',fn,onto⟩ := countable_surjection_zf_l hZF ⟨c,fc⟩ ⟨D',nonempty⟩
  have enum : Td_enum_d Ω X' R' E' e' :=
    ⟨(fn0_of_function_l (ZF.modelsKP hZF) fn).mono_target_l (yt E' family.inside),
      fun _ D edge => (target.2 D E').mpr ⟨yt E' family.inside D (fn.output_mem_of_pairMember edge),
        family.inside,fn.output_mem_of_pairMember edge⟩,
      fun D _ hD => onto D ((target.2 D E').mp hD).2.2⟩
  exact ⟨t',E',e',F',succ,⟨family,enum,table⟩,eE,law⟩

/-- 游标不超过当前出生深度时，规范配对的第一坐标必已出生。 -/
theorem Ab_birth_d.pick_l {Ω X R P T t E e F k : M.Domain} (hΩ : M.IsOmega Ω)
    (old : Ab_birth_d J Ω X R P T t E e F) (hk : M.MemberSubset k t) :
    ∃ D, M.mem D X ∧ Rd_entry_d D E R ∧ Ab_pick_d J Ω t F e k D := by
  classical
  by_cases code : ∃ i l, M.mem i Ω ∧ M.mem l Ω ∧ Oc_pair_d J i l k
  · obtain ⟨i,l,hi,hl,pair⟩ := code
    have bound := oc_pair_left_bound_l J hZF hΩ hi hl pair
    have sub : M.MemberSubset i t := fun a ha => hk a (bound a ha)
    have oi := hΩ.members_areOrdinals (ZF.modelsKP hZF) i hi
    have ot := hΩ.members_areOrdinals (ZF.modelsKP hZF) t old.history.natural
    obtain ⟨p,ip⟩ := (J).total i l
    have value : ∃ D, M.mem D X ∧ Rd_entry_d D E R ∧
        ((M.mem i t ∧ Rd_entry_d p D F) ∨ (i = t ∧ Rd_entry_d l D e)) := by
      rcases oi.trichotomy hZF.1 ot (KP.difference_exists_d (ZF.modelsKP hZF))
          (KP.intersection_exists_d (ZF.modelsKP hZF) i t) with eq | it | ti
      · obtain ⟨D,hD,edge⟩ := old.enumeration.function.2.1 l hl
        exact ⟨D,hD,old.enumeration.letters l D edge,Or.inr ⟨hZF.1.eq_of_same_members i t eq,edge⟩⟩
      · obtain ⟨W,product,fn⟩ := old.history.table
        obtain ⟨D,hD,edge⟩ := fn.2.1 p ((product p).mpr ⟨i,it,l,hl,ip⟩)
        exact ⟨D,hD,old.history.letters p D edge,Or.inl ⟨it,edge⟩⟩
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) t (sub t ti)).elim
    obtain ⟨D,hD,letter,value⟩ := value
    refine ⟨D,hD,letter,?_⟩
    intro i' l' p' _ _ pair' ip'
    obtain ⟨ei,el⟩ := oc_pair_injective_l J hZF pair' pair
    subst i' l'
    exact (J).unique ip ip' ▸ value
  · obtain ⟨o,_,ho⟩ := hΩ.1.1
    obtain ⟨D,hD,edge⟩ := old.enumeration.function.2.1 o ho
    exact ⟨D,hD,old.enumeration.letters o D edge,fun i l _ hi hl pair _ => (code ⟨i,l,hi,hl,pair⟩).elim⟩

/-- 原任务的出生编号不变；原当前行在下一步转为历史行。 -/
theorem Ab_pick_d.step_l {Ω t F e k D t' F' e' D' j : M.Domain}
    (pick : Ab_pick_d I Ω t F e k D) (succ : M.SuccessorOf t' t)
    (law : ∀ p y, Rd_entry_d p y F' ↔ Td_depth_next_d Ω t F e j p y)
    (image : Rd_entry_d D D' j) : Ab_pick_d I Ω t' F' e' k D' := by
  intro i l p hi hl pair ip
  have old := pick i l p hi hl pair ip
  refine Or.inl ⟨?_,(law p D').mpr ⟨i,l,D,ip,hl,old,image⟩⟩
  exact (succ i).mpr (old.elim (fun h => Or.inl h.1) (fun h => Or.inr (h.1 ▸ fun _ => Iff.rfl)))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从实际有限前缀启动 7.23 吸收

由前缀滤子列构造专用博弈的小泛型集合。原前缀扩张与该小扩张保持地参数同构；
随后对每个指定实数调用同一实际吸收工厂，保留原树的返回枝和返回因子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
theorem ag_absorb_prefix_l {Ω c X R d Y S θ π F : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I d Y S) (embed : Smap_d I Ω c d X Y π)
    {ω κ δ B Z A n m C T : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ Z)
    (letters : (smdl_structure_l I (R := R) certificate.model.2.1).mem B Z)
    (inh : ∃ x, (smdl_structure_l I (R := R) certificate.model.2.1).mem x B)
    (small : (smdl_structure_l I (R := R) certificate.model.2.1).mem κ δ)
    (stage : Fp_prefix_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A m C T)
    (hn : (smdl_structure_l I (R := R) certificate.model.2.1).mem n ω)
    (hm : (smdl_structure_l I (R := R) certificate.model.2.1).mem m ω)
    (succ : (smdl_structure_l I (R := R) certificate.model.2.1).SuccessorOf m n)
    (fa : (smdl_structure_l I (R := R) certificate.model.2.1).IsSetFunction
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) A)
    (alphabet : Entry_d (smdl_structure_l I (R := R) certificate.model.2.1) n κ A)
    (hκ : (smdl_structure_l I (R := R) certificate.model.2.1).IsUncountableCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω κ)
    (bound : ∀ i α, (smdl_structure_l I (R := R) certificate.model.2.1).mem i m →
      Entry_d (smdl_structure_l I (R := R) certificate.model.2.1) i α A →
        (smdl_structure_l I (R := R) certificate.model.2.1).MemberSubset α κ)
    (generic : Generic_d (smdl_structure_l I (R := R) certificate.model.2.1) C T C
      (fun q => (smdl_structure_l I (R := R) certificate.model.2.1).mem q C ∧ Fp_ready_d I m.val F q.val)) :
    let N := smdl_structure_l I (R := R) certificate.model.2.1
    let hNZF := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    let H := fun q : N.Domain => N.mem q C ∧ Fp_ready_d I m.val F q.val
    ∃ p : Ag_forcing_d hNZF ω κ δ B, ∃ s : Ag_system_d hNZF p,
      ∃ a Γ : N.Domain, ∃ K z : M.Domain,
        H a ∧ Dmap_at_d p.Q p.T p.Q C T C Γ a ∧ M.MemberSubset K p.Q.val ∧
        (∀ q : N.Domain, M.mem q.val K ↔ Pull_generic_d N Γ H q) ∧
        Generic_d N p.Q p.T p.Q (fun q => M.mem q.val K) ∧
        Miso_over_d (extension_l N hNZF p.Q p.T p.Q (fun q => M.mem q.val K)) (extension_l N hNZF C T C H)
          (Gval_d N p.Q p.T p.Q (fun q => M.mem q.val K)) (Gval_d N C T C H) ∧
        (∀ a, ¬ M.mem a z) ∧
        ∀ x, Fn0_d Ω B.val x → ∃ f,
          Ag_trace_d hZF Ω B.val s.A.val s.F₀.val s.R₀.val f x K ∧
          Ag_return_d hZF Ω z c X d Y π (fun i => (s.aux_params_l hNZF i).val) f K x := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have hN := certificate.native_l I hZF hΩ
  obtain ⟨p,s,z,empty,absorb⟩ :=
    ag_absorb_l hZFC hΩ certificate source trans count targetRank target embed hw woodin rank letters inh small
  have ki : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have kf := smem_full_l I source trans
  obtain ⟨a,Γ,K,ha,reg,sub,read,genericK,iso⟩ := fp_ground_comparison_l hN hZF Subtype.val ki kf
    stage hw hn hm succ fa alphabet hκ bound p.small_space p.small_order p.small_edges generic
  exact ⟨p,s,a,Γ,K,z,ha,reg,sub,read,genericK,iso,empty,fun x fx => absorb K x sub genericK fx⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际吸收帧的后继

由帧中相邻的 Woodin 自动恢复全部吸收参数，沿原返回枝推进同一个有限任务。
新集合记录保留旧滤子前缀、返回复合式及任务终点；到达终点时给出真正的稠密集命中。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ab_frame_d.next_pending_l {Ω cY Y S θ i D m d x : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d I Ω cY Y v) (hΩ : M.IsOmega Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I cY Y S)
    (hi : M.mem i Ω) (succ : M.SuccessorOf (v 7) i)
    (task : Ab_task_d I Ω v D m d) (active : M.mem (v 7) m) (fx : Fn0_d Ω Ω x) :
    ∃ r : M.Domain, ∃ v' : Fin 14 → M.Domain, ∃ j K D' d',
      Rt_tuple_d v' r ∧ Ab_frame_d I Ω cY Y v' ∧
      Smap_d I Ω (v 0) (v' 0) (v 1) (v' 1) j ∧ It_comp_d j (v' 3) (v 3) ∧
      M.SuccessorOf (v' 7) (v 7) ∧ M.IsRestrictionOf I (v 10) (v' 10) (v 7) ∧ Entry_d M (v 7) K (v' 10) ∧
      Rd_entry_d (v 4) (v' 4) j ∧ Rd_entry_d (v 5) (v' 5) j ∧ Rd_entry_d (v 6) (v' 6) j ∧
      Rd_entry_d (v 8) (v 8) j ∧ (∀ q, M.mem q (v 8) → Rd_entry_d q q j) ∧
      Rd_entry_d D D' j ∧ Rd_entry_d d d' j ∧ Ab_task_d I Ω v' D' m d' ∧
      (v' 7 = m → M.mem d' (v' 11)) ∧ v' 13 = x := by
  -- 一、恢复帧的原模型，并从相邻 Woodin 取得本轮小坍缩与吸收参数。
  let N := smdl_structure_l I (R := v 2) h.model.1.2.1
  have native := ZFC.models_zf_l (h.theory.native_l I hZF hΩ)
  let J := kp_pair_l (ZF.modelsKP native)
  obtain ⟨hω,hA,hP,hU,hn,hC,hT,_⟩ := h.inside
  let ω : N.Domain := ⟨Ω,hω⟩
  let A : N.Domain := ⟨v 4,hA⟩
  let P : N.Domain := ⟨v 5,hP⟩
  let U : N.Domain := ⟨v 6,hU⟩
  let n : N.Domain := ⟨v 7,hn⟩
  let C : N.Domain := ⟨v 8,hC⟩
  let T : N.Domain := ⟨v 9,hT⟩
  let i₀ : N.Domain := ⟨i,h.transitive Ω hω i hi⟩
  let m₀ : N.Domain := ⟨m,h.transitive Ω hω m task.finite⟩
  let D₀ : N.Domain := ⟨D,task.dense_inside⟩
  let d₀ : N.Domain := ⟨d,task.condition_inside⟩
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I h.model h.transitive
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  obtain ⟨hw,sequence,product,stage⟩ := (ab_kernel_read_l I h.model h.transitive native ω A P U n C T).mp h.kernel
  have hn₀ : N.mem n ω := member.mp h.index
  have hi₀ : N.mem i₀ ω := member.mp hi
  have sn : N.SuccessorOf n i₀ := (image_successor_iff_l (ZF.modelsKP native) hZF.1 Subtype.val inj full).mpr succ
  obtain ⟨κ,δ,V,smallAlphabet,alphabet,uncountable,below,woodin,rank,letters,bound⟩ :=
    sequence.successor_l J native hw hi₀ sn
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction native J sequence.function sequence.domain
  have fa : N.IsSetFunctionFromTo J A ω W := ⟨sequence.function,sequence.domain,fun k hk => by
    obtain ⟨α,edge⟩ := (sequence.domain k).mp hk
    exact ⟨α,(range α).mpr ⟨k,edge⟩,edge⟩⟩
  have generic := ((h.model.generic_code_l I hZF.1 h.transitive (ZF.modelsKP native) C T C (v 11)).mp h.generic).2
  have eq : (fun q : N.Domain => M.mem q.val (v 11)) =
      (fun q => N.mem q C ∧ Fp_ready_d I n.val (v 10) q.val) :=
    funext fun q => propext ((h.accepted q.val).trans (and_congr (member (a := q) (b := C)) Iff.rfl))
  rw [eq] at generic
  -- 二、原前缀比较产生实际小泛型；同一返回枝推进已选条件的下一坐标。
  have inhabited : ∃ y, N.mem y ω := hw.1.1.imp fun _ h => h.2
  obtain ⟨p,s,a,Γ,H,z,ha,map,subH,read,_,_,_,absorb⟩ :=
    ag_absorb_prefix_l hZFC hΩ h.theory h.model h.transitive h.count targetRank target h.returns
      hw woodin rank letters inhabited below stage hi₀ hn₀ sn sequence.function smallAlphabet uncountable bound generic
  obtain ⟨f,_,returned⟩ := absorb x fx
  have fd := (ab_block_read_l I h.model h.transitive (ZF.modelsKP native) ω A m₀ d₀).mp task.block
  have dense := (h.model.dense_code_l I hZF.1 h.transitive (ZF.modelsKP native) P U P D₀).mp task.dense
  have seq : M.IsSequenceOfLength I (v 10) n.val :=
    ⟨hΩ.members_areOrdinals (ZF.modelsKP hZF) n.val h.index,h.function,h.domain⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,r,σ,ret,square,count,cert,e,elem,values,en,em,
      product',dense',hit',fd',n',C',T',F',K,Z,sn',hn',bound',seq',keep,last,ready,_,stage',_,members,_,gset,done,
      _,_,_,B',_,name,_,_,_⟩ :=
    returned.pending_l hZF hΩ h.model h.transitive h.theory native s hw inhabited fa product stage hn₀
      (member.mp task.finite) (member.mp active) fd dense (member.mp task.hit) alphabet bound generic ha map subH read seq task.ready
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  have ew : e ω = r.w 0 :=
    Subtype.ext (r.map.1.1.1.2 _ _ _ (values ω) (r.images 0))
  have sequence' := sequence.image_l J (kp_pair_l (ZF.modelsKP r.native)) native.1 r.native.1 e elem
  rw [ew] at sequence'
  have kernel := (ab_kernel_read_l I r.target r.transitive r.native (r.w 0) (e A) (e P) (e U) n' C' T').mpr
    ⟨r.frame.omega,sequence',product',stage'⟩
  -- 三、把新模型、实际滤子及实数名字重新编码为可被下一轮直接读取的帧。
  let v' : Fin 14 → M.Domain := fun k =>
    [r.d,r.N,r.W,σ,(e A).val,(e P).val,(e U).val,n'.val,C'.val,T'.val,F',Z,B'.val,x].get k
  have frame : Ab_frame_d I Ω cY Y v' :=
    ⟨r.target,cert,r.transitive,count,ret,
      ⟨r.omega ▸ (r.w 0).property,(e A).property,(e P).property,(e U).property,n'.property,C'.property,T'.property,B'.property⟩,
      r.omega ▸ ((r.target.2 n'.val (r.w 0).val).mp hn').2.2,r.omega ▸ kernel,
      seq'.2.1,seq'.2.2,members,gset,fx,r.omega ▸ name⟩
  have block := (ab_block_read_l I r.target r.transitive (ZF.modelsKP r.native) (r.w 0) (e A) (e m₀) (e d₀)).mpr fd'
  have block' : Ab_block_d r.N Ω (e A).val m (e d₀).val := by
    simpa only [r.omega,em] using block
  -- 终点 m 固定，条件随原根图运输；完成时的命中由同一个新前缀泛型给出。
  have task' : Ab_task_d I Ω v' (e D₀).val m (e d₀).val :=
    ⟨(e D₀).property,(e d₀).property,task.finite,bound',
      (r.target.dense_code_l I hZF.1 r.transitive (ZF.modelsKP r.native) (e P) (e U) (e P) (e D₀)).mpr dense',
      ((r.target.2 (e d₀).val (e D₀).val).mp hit').2.2,block',ready⟩
  have inj' : Function.Injective (Subtype.val : N'.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have sn'' := image_successor_l (hEN := hZF.1) Subtype.val inj' (smem_full_l I r.target r.transitive) r.native.1 sn'
  have successor : M.SuccessorOf n'.val n.val := en ▸ sn''
  have fixed := s.fixed_prefix_l hZF hΩ h.model r.target h.transitive r.transitive r.map native hw inhabited
    r.fixed r.point stage hn₀ bound
  obtain ⟨t,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) v'
  exact ⟨t,v',r.j,K,(e D₀).val,(e d₀).val,tuple,frame,r.map,square,successor,keep,last,
    values A,values P,values U,fixed.1,fixed.2,values D₀,values d₀,task',
    fun eq => done (Subtype.ext (eq.trans em.symm)),rfl⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 出生任务表接入实际吸收后继

调度先从已出生行读取全乘积稠密集，再由前缀泛型选出有限任务。
每次吸收同时追加滤子与出生枚举行；原游标和原任务一起运输，且下一阶段已有空间推进游标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 零历史及当前完整枚举都由帧本身构造，供首轮初始化。 -/
theorem Ab_frame_d.birth_zero_l {Ω cY Y : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d I Ω cY Y v) (hΩ : M.IsOmega Ω) :
    ∃ t E e B, (∀ a, ¬ M.mem a t) ∧ Ab_birth_d I Ω (v 1) (v 2) (v 5) (v 6) t E e B := by
  let N := smdl_structure_l I (R := v 2) h.model.1.2.1
  have native := ZFC.models_zf_l (h.theory.native_l I hZF hΩ)
  obtain ⟨hω,hA,hP,hU,hn,hC,hT,_⟩ := h.inside
  let ω : N.Domain := ⟨Ω,hω⟩
  let A : N.Domain := ⟨v 4,hA⟩
  let P : N.Domain := ⟨v 5,hP⟩
  let U : N.Domain := ⟨v 6,hU⟩
  let n : N.Domain := ⟨v 7,hn⟩
  let C : N.Domain := ⟨v 8,hC⟩
  let T : N.Domain := ⟨v 9,hT⟩
  obtain ⟨_,_,product,_⟩ := (ab_kernel_read_l I h.model h.transitive native ω A P U n C T).mp h.kernel
  exact ab_birth_zero_l hZF hΩ h.model h.transitive native h.count P U (product.order_l native)

/-- 任务来自指定出生编号的当前像；有限块由真实前缀泛型选择。 -/
theorem Ab_frame_d.scheduled_l {Ω cY Y t E e B k : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d I Ω cY Y v) (hΩ : M.IsOmega Ω)
    (birth : Ab_birth_d I Ω (v 1) (v 2) (v 5) (v 6) t E e B) (bound : M.MemberSubset k t) :
    ∃ D m d, Ab_pick_d I Ω t B e k D ∧ Ab_task_d I Ω v D m d ∧ M.mem (v 7) m := by
  obtain ⟨D,inside,letter,pick⟩ := birth.pick_l hZF hΩ bound
  have dense := ((birth.family.members D).mp ((h.model.2 D E).mp letter).2.2).2
  obtain ⟨m,d,task,active⟩ := h.select_l hZF hΩ inside dense
  exact ⟨D,m,d,pick,task,active⟩

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一原任务、出生表和返回图共同推进，旧游标在新出生深度内严格有界。 -/
theorem Ab_frame_d.next_scheduled_l {Ω cY Y S θ t E e B k D m d x : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d I Ω cY Y v) (hΩ : M.IsOmega Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I cY Y S)
    (birth : Ab_birth_d I Ω (v 1) (v 2) (v 5) (v 6) t E e B) (succ : M.SuccessorOf (v 7) t)
    (hk : M.mem k Ω) (bound : M.MemberSubset k t) (pick : Ab_pick_d I Ω t B e k D)
    (task : Ab_task_d I Ω v D m d) (active : M.mem (v 7) m) (fx : Fn0_d Ω Ω x) :
    ∃ r : M.Domain, ∃ v' : Fin 14 → M.Domain, ∃ j K D' d' E' e' B',
      Rt_tuple_d v' r ∧ Ab_frame_d I Ω cY Y v' ∧
      Smap_d I Ω (v 0) (v' 0) (v 1) (v' 1) j ∧ It_comp_d j (v' 3) (v 3) ∧
      M.SuccessorOf (v' 7) (v 7) ∧ M.IsRestrictionOf I (v 10) (v' 10) (v 7) ∧ Entry_d M (v 7) K (v' 10) ∧
      Rd_entry_d (v 4) (v' 4) j ∧ Rd_entry_d (v 5) (v' 5) j ∧ Rd_entry_d (v 6) (v' 6) j ∧
      Rd_entry_d (v 8) (v 8) j ∧ (∀ q, M.mem q (v 8) → Rd_entry_d q q j) ∧
      Rd_entry_d D D' j ∧ Rd_entry_d d d' j ∧ Ab_task_d I Ω v' D' m d' ∧
      (v' 7 = m → M.mem d' (v' 11)) ∧ v' 13 = x ∧
      Ab_birth_d I Ω (v' 1) (v' 2) (v' 5) (v' 6) (v 7) E' e' B' ∧
      Rd_entry_d E E' j ∧ (∀ p Z, Rd_entry_d p Z B' ↔ Td_depth_next_d Ω t B e j p Z) ∧
      Ab_pick_d I Ω (v 7) B' e' k D' ∧ M.mem k (v 7) := by
  obtain ⟨r,v',j,K,D',d',tuple,next,map,square,succ',keep,last,alphabet,product,order,
      fixed,points,denseImage,conditionImage,task',done,real⟩ :=
    h.next_pending_l hZFC hΩ targetRank target birth.history.natural succ task active fx
  let N := smdl_structure_l I (R := v 2) h.model.1.2.1
  let N' := smdl_structure_l I (R := v' 2) next.model.1.2.1
  have native := ZFC.models_zf_l (h.theory.native_l I hZF hΩ)
  have native' := ZFC.models_zf_l (next.theory.native_l I hZF hΩ)
  let P : N.Domain := ⟨v 5,h.inside.2.2.1⟩
  let T : N.Domain := ⟨v 6,h.inside.2.2.2.1⟩
  let P' : N'.Domain := ⟨v' 5,next.inside.2.2.1⟩
  let T' : N'.Domain := ⟨v' 6,next.inside.2.2.2.1⟩
  obtain ⟨t',E',e',B',depth,birth',family,table⟩ := birth.step_l hZF hΩ h.model next.model
    h.transitive next.transitive map (ZF.modelsKP native) (ZF.modelsKP native') next.count
    (P := P) (T := T) (P' := P') (T' := T') product order
  have depthEq := depth.eq hZF.1 succ
  have available : M.mem k (v 7) := ordinal_down_l (ZF.modelsKP hZF)
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) k hk)
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 7) h.index) bound succ.predecessor_mem
  exact ⟨r,v',j,K,D',d',E',e',B',tuple,next,map,square,succ',keep,last,alphabet,product,order,
    fixed,points,denseImage,conditionImage,task',done,real,depthEq ▸ birth',family,table,
    pick.step_l I succ table denseImage,available⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 吸收与全乘积任务的统一队列状态

状态由实际帧、出生表、任务游标和有限条件块组成。块完成时已有严格的出生深度余量，
所以游标可递增；未完成时继续原块。这个不变量来自每个新任务至少消耗一轮。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Ab_queue_d (Ω cY Y : M.Domain) (v : Fin 14 → M.Domain) (t E e B k D m d : M.Domain) : Prop where
  frame : Ab_frame_d I Ω cY Y v
  birth : Ab_birth_d I Ω (v 1) (v 2) (v 5) (v 6) t E e B
  stage : M.SuccessorOf (v 7) t
  cursor : M.mem k Ω
  bound : M.MemberSubset k t
  pick : Ab_pick_d I Ω t B e k D
  task : Ab_task_d I Ω v D m d
  done : v 7 = m → M.mem k t ∧ M.mem d (v 11)

def ab_queue_m {n} (Ω cY Y : Term n) (v : Fin 14 → Term n) (t E e B k D m d : Term n) : Formula 1 n :=
  .conj (ab_frame_m Ω cY Y v) (.conj (ab_birth_m Ω (v 1) (v 2) (v 5) (v 6) t E e B)
    (.conj (Formula.isSuccessor (v 7) t) (.conj (.mem k Ω) (.conj (Formula.subset k t)
      (.conj (ab_pick_m Ω t B e k D) (.conj (ab_task_m Ω v D m d)
        (.imp (Formula.extensionalEq (v 7) m) (.conj (.mem k t) (.mem d (v 11))))))))))

@[simp] theorem ab_queue_closed_l {n} (Ω cY Y : Term n) (v : Fin 14 → Term n) (t E e B k D m d : Term n)
    (hΩ : Ω.freeSupport = []) (hcY : cY.freeSupport = []) (hY : Y.freeSupport = []) (hv : ∀ i, (v i).freeSupport = [])
    (ht : t.freeSupport = []) (hE : E.freeSupport = []) (he : e.freeSupport = []) (hB : B.freeSupport = [])
    (hk : k.freeSupport = []) (hD : D.freeSupport = []) (hm : m.freeSupport = []) (hd : d.freeSupport = []) :
    (ab_queue_m Ω cY Y v t E e B k D m d).FreeClosed := by
  simp -implicitDefEqProofs [ab_queue_m,Definitional.Formula.FreeClosed,hΩ,hcY,hY,hv,ht,hE,he,hB,hk,hD,hm,hd]

theorem ab_queue_sat_l (hE : Extensional M) {n} (ρ : Env M n)
    (Ω cY Y : Term n) (v : Fin 14 → Term n) (t E e B k D m d : Term n) :
    Formula.satisfies ρ (ab_queue_m Ω cY Y v t E e B k D m d) ↔
      Ab_queue_d I (Ω.eval ρ) (cY.eval ρ) (Y.eval ρ) (fun i => (v i).eval ρ)
        (t.eval ρ) (E.eval ρ) (e.eval ρ) (B.eval ρ) (k.eval ρ) (D.eval ρ) (m.eval ρ) (d.eval ρ) := by
  simp only [ab_queue_m,Formula.satisfies_conj_iff,ab_frame_sat_l I hE,ab_birth_sat_l I hE,
    Formula.satisfies_isSuccessor_iff,Formula.satisfies_mem_iff,Formula.satisfies_subset_iff,
    ab_pick_sat_l I hE,ab_task_sat_l I hE,Formula.satisfies_imp_iff,Formula.satisfies_extensionalEq_iff_eq hE]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h⟩ => ⟨a,b,c,d,e,f,g,h⟩,
    fun h => ⟨h.frame,h.birth,h.stage,h.cursor,h.bound,h.pick,h.task,h.done⟩⟩

/-- 吸收前实际服务的块：沿用旧块，或在旧块完成后服务恰好下一个编号。 -/
structure Ab_work_d (Ω : M.Domain) (v : Fin 14 → M.Domain) (t B e k D m d k' D' m' d' : M.Domain) : Prop where
  cursor : M.mem k' Ω
  bound : M.MemberSubset k' t
  pick : Ab_pick_d I Ω t B e k' D'
  task : Ab_task_d I Ω v D' m' d'
  active : M.mem (v 7) m'
  choice : (M.mem (v 7) m ∧ k' = k ∧ D' = D ∧ m' = m ∧ d' = d) ∨
    (v 7 = m ∧ M.SuccessorOf k' k)

def ab_work_m {n} (Ω : Term n) (v : Fin 14 → Term n) (t B e k D m d k' D' m' d' : Term n) : Formula 1 n :=
  .conj (.mem k' Ω) (.conj (Formula.subset k' t) (.conj (ab_pick_m Ω t B e k' D')
    (.conj (ab_task_m Ω v D' m' d') (.conj (.mem (v 7) m') (set[n] ⟪
      (⌜v 7⌝ₛ ∈ ⌜m⌝ₛ ∧ ⌜k'⌝ₛ = ⌜k⌝ₛ ∧ ⌜D'⌝ₛ = ⌜D⌝ₛ ∧ ⌜m'⌝ₛ = ⌜m⌝ₛ ∧ ⌜d'⌝ₛ = ⌜d⌝ₛ) ∨
        (⌜v 7⌝ₛ = ⌜m⌝ₛ ∧ ⌜Formula.isSuccessor⌝ₚ(⌜k'⌝ₛ,⌜k⌝ₛ))⟫)))))

@[simp] theorem ab_work_closed_l {n} (Ω : Term n) (v : Fin 14 → Term n) (t B e k D m d k' D' m' d' : Term n)
    (hΩ : Ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = [])
    (ht : t.freeSupport = []) (hB : B.freeSupport = []) (he : e.freeSupport = []) (hk : k.freeSupport = [])
    (hD : D.freeSupport = []) (hm : m.freeSupport = []) (hd : d.freeSupport = []) (hk' : k'.freeSupport = [])
    (hD' : D'.freeSupport = []) (hm' : m'.freeSupport = []) (hd' : d'.freeSupport = []) :
    (ab_work_m Ω v t B e k D m d k' D' m' d').FreeClosed := by
  simp -implicitDefEqProofs [ab_work_m,Definitional.Formula.FreeClosed,hΩ,hv,ht,hB,he,hk,hD,hm,hd,hk',hD',hm',hd']

theorem ab_work_sat_l (hE : Extensional M) {n} (ρ : Env M n)
    (Ω : Term n) (v : Fin 14 → Term n) (t B e k D m d k' D' m' d' : Term n) :
    Formula.satisfies ρ (ab_work_m Ω v t B e k D m d k' D' m' d') ↔
      Ab_work_d I (Ω.eval ρ) (fun i => (v i).eval ρ) (t.eval ρ) (B.eval ρ) (e.eval ρ) (k.eval ρ)
        (D.eval ρ) (m.eval ρ) (d.eval ρ) (k'.eval ρ) (D'.eval ρ) (m'.eval ρ) (d'.eval ρ) := by
  simp only [ab_work_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Formula.satisfies_subset_iff,
    ab_pick_sat_l I hE,ab_task_sat_l I hE,Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,Formula.satisfies_isSuccessor_iff]
  exact ⟨fun ⟨a,b,c,d,e,f⟩ => ⟨a,b,c,d,e,f⟩,
    fun h => ⟨h.cursor,h.bound,h.pick,h.task,h.active,h.choice⟩⟩

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 首帧立即带上真实任务，并打包为二十二项背景集合记录。 -/
theorem Ab_frame_d.queue_zero_l {Ω cY Y o : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_frame_d J Ω cY Y v) (hΩ : M.IsOmega Ω) (empty : ∀ a, ¬ M.mem a o)
    (succ : M.SuccessorOf (v 7) o) :
    ∃ E e B D m d r, Ab_queue_d J Ω cY Y v o E e B o D m d ∧ M.mem (v 7) m ∧
      Rt_tuple_d (Fin.addCases (m := 14) (n := 8) v (fun i => [o,E,e,B,o,D,m,d].get i)) r := by
  obtain ⟨t,E,e,B,empty',birth⟩ := h.birth_zero_l hZF hΩ
  have eq := hZF.1.eq_of_same_members t o (fun a => iff_of_false (empty' a) (empty a))
  subst t
  obtain ⟨D,m,d,pick,task,active⟩ := h.scheduled_l hZF hΩ birth (fun _ hx => hx)
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF)
    (Fin.addCases (m := 14) (n := 8) v (fun i => [o,E,e,B,o,D,m,d].get i))
  exact ⟨E,e,B,D,m,d,r,⟨h,birth,succ,birth.history.natural,fun _ hx => hx,pick,task,
    fun eq => (KP.mem_irrefl_d (ZF.modelsKP hZF) m (eq ▸ active)).elim⟩,active,tuple⟩

/-- 当前状态总有下一项可服务；完成分支由已证明的严格游标余量支持。 -/
theorem Ab_queue_d.work_l {Ω cY Y t E e B k D m d : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_queue_d J Ω cY Y v t E e B k D m d) (hΩ : M.IsOmega Ω) :
    ∃ k' D' m' d', Ab_work_d J Ω v t B e k D m d k' D' m' d' := by
  classical
  by_cases done : v 7 = m
  · obtain ⟨k',succ,hk'⟩ := hΩ.1.2 k h.cursor
    have kt := (h.done done).1
    have bound : M.MemberSubset k' t := by
      intro a ha
      rcases (succ a).mp ha with ak | eq
      · exact (hΩ.members_areOrdinals (ZF.modelsKP hZF) t h.birth.history.natural).transitive k kt a ak
      · exact (hZF.1.eq_of_same_members a k eq).symm ▸ kt
    obtain ⟨D',m',d',pick,task,active⟩ := h.frame.scheduled_l hZF hΩ h.birth bound
    exact ⟨k',D',m',d',⟨hk',bound,pick,task,active,Or.inr ⟨done,succ⟩⟩⟩
  · have active : M.mem (v 7) m := by
      have on := hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 7) h.frame.index
      have om := hΩ.members_areOrdinals (ZF.modelsKP hZF) m h.task.finite
      rcases on.trichotomy hZF.1 om (KP.difference_exists_d (ZF.modelsKP hZF))
          (KP.intersection_exists_d (ZF.modelsKP hZF) (v 7) m) with eq | nm | mn
      · exact (done (hZF.1.eq_of_same_members (v 7) m eq)).elim
      · exact nm
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) m (h.task.remaining m mn)).elim
    exact ⟨k,D,m,d,⟨h.cursor,h.bound,h.pick,h.task,active,Or.inl ⟨active,rfl,rfl,rfl,rfl⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 统一队列的实际总后继及原公式

工作选择、原根图、返回复合、滤子追加和出生表运输都记录在同一个转移公式中。
后继定理实际构造下一集合状态；不把无限运行、队列公平性或后继存在性当成输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Ab_step_d (Ω : M.Domain) (v v' : Fin 14 → M.Domain)
    (t E e B k D m d E' B' k' D' m' d' j K x : M.Domain) : Prop where
  work : ∃ D₀ d₀, Ab_work_d I Ω v t B e k D m d k' D₀ m' d₀ ∧ Rd_entry_d D₀ D' j ∧ Rd_entry_d d₀ d' j
  map : Smap_d I Ω (v 0) (v' 0) (v 1) (v' 1) j
  square : It_comp_d j (v' 3) (v 3)
  stage : M.SuccessorOf (v' 7) (v 7)
  keep : M.IsRestrictionOf I (v 10) (v' 10) (v 7)
  last : Rd_entry_d (v 7) K (v' 10)
  alphabet : Rd_entry_d (v 4) (v' 4) j
  product : Rd_entry_d (v 5) (v' 5) j
  order : Rd_entry_d (v 6) (v' 6) j
  fixed : Rd_entry_d (v 8) (v 8) j
  points : ∀ q, M.mem q (v 8) → Rd_entry_d q q j
  family : Rd_entry_d E E' j
  table : ∀ p Z, Rd_entry_d p Z B' ↔ Td_depth_next_d Ω t B e j p Z
  real : v' 13 = x

def ab_step_m {n} (Ω : Term n) (v v' : Fin 14 → Term n)
    (t E e B k D m d E' B' k' D' m' d' j K x : Term n) : Formula 1 n :=
  let work : Formula 1 n := .existsE (.existsE (.conj
    (ab_work_m Ω.weaken.weaken (fun i => (v i).weaken.weaken) t.weaken.weaken B.weaken.weaken e.weaken.weaken
      k.weaken.weaken D.weaken.weaken m.weaken.weaken d.weaken.weaken k'.weaken.weaken (.bound 1) m'.weaken.weaken .newest)
    (.conj (rd_entry0_m (.bound 1) D'.weaken.weaken j.weaken.weaken) (rd_entry0_m .newest d'.weaken.weaken j.weaken.weaken))))
  .conj work (set[n] ⟪⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜Ω⌝ₛ,⌜v 0⌝ₛ,⌜v' 0⌝ₛ,⌜v 1⌝ₛ,⌜v' 1⌝ₛ,⌜j⌝ₛ) ∧
    ⌜it_comp_m⌝ₚ(⌜j⌝ₛ,⌜v' 3⌝ₛ,⌜v 3⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜v' 7⌝ₛ,⌜v 7⌝ₛ) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(⌜v 10⌝ₛ,⌜v' 10⌝ₛ,⌜v 7⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 7⌝ₛ,⌜K⌝ₛ,⌜v' 10⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 4⌝ₛ,⌜v' 4⌝ₛ,⌜j⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 5⌝ₛ,⌜v' 5⌝ₛ,⌜j⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 6⌝ₛ,⌜v' 6⌝ₛ,⌜j⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 8⌝ₛ,⌜v 8⌝ₛ,⌜j⌝ₛ) ∧ (∀ q, q ∈ ⌜v 8⌝ₛ → ⌜rd_entry0_m⌝ₚ(q,q,⌜j⌝ₛ)) ∧
    ⌜rd_entry0_m⌝ₚ(⌜E⌝ₛ,⌜E'⌝ₛ,⌜j⌝ₛ) ∧
    (∀ p Z, ⌜rd_entry0_m⌝ₚ(p,Z,⌜B'⌝ₛ) ↔ ⌜td_depth_next_m⌝ₚ(⌜Ω⌝ₛ,⌜t⌝ₛ,⌜B⌝ₛ,⌜e⌝ₛ,⌜j⌝ₛ,p,Z)) ∧
    ⌜v' 13⌝ₛ = ⌜x⌝ₛ⟫)

@[simp] theorem ab_step_closed_l {n} (Ω : Term n) (v v' : Fin 14 → Term n)
    (t E e B k D m d E' B' k' D' m' d' j K x : Term n)
    (hΩ : Ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) (hv' : ∀ i, (v' i).freeSupport = [])
    (ht : t.freeSupport = []) (hE : E.freeSupport = []) (he : e.freeSupport = []) (hB : B.freeSupport = [])
    (hk : k.freeSupport = []) (hD : D.freeSupport = []) (hm : m.freeSupport = []) (hd : d.freeSupport = [])
    (hE' : E'.freeSupport = []) (hB' : B'.freeSupport = []) (hk' : k'.freeSupport = [])
    (hD' : D'.freeSupport = []) (hm' : m'.freeSupport = []) (hd' : d'.freeSupport = [])
    (hj : j.freeSupport = []) (hK : K.freeSupport = []) (hx : x.freeSupport = []) :
    (ab_step_m Ω v v' t E e B k D m d E' B' k' D' m' d' j K x).FreeClosed := by
  simp -implicitDefEqProofs [ab_step_m,Definitional.Formula.FreeClosed,hΩ,hv,hv',ht,hE,he,hB,hk,hD,hm,hd,
    hE',hB',hk',hD',hm',hd',hj,hK,hx]

theorem ab_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Ω : Term n) (v v' : Fin 14 → Term n)
    (t E e B k D m d E' B' k' D' m' d' j K x : Term n) :
    Formula.satisfies ρ (ab_step_m Ω v v' t E e B k D m d E' B' k' D' m' d' j K x) ↔
      Ab_step_d I (Ω.eval ρ) (fun i => (v i).eval ρ) (fun i => (v' i).eval ρ)
        (t.eval ρ) (E.eval ρ) (e.eval ρ) (B.eval ρ) (k.eval ρ) (D.eval ρ) (m.eval ρ) (d.eval ρ)
        (E'.eval ρ) (B'.eval ρ) (k'.eval ρ) (D'.eval ρ) (m'.eval ρ) (d'.eval ρ) (j.eval ρ) (K.eval ρ) (x.eval ρ) := by
  simp only [ab_step_m,Formula.satisfies_conj_iff,Formula.satisfies_exists_iff,ab_work_sat_l I hE,
    rd_entry0_sat_l hE,smap_sat_l I hE,it_comp_sat_l hE,Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_isRestriction_iff I,Formula.satisfies_forall_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_iff_iff,td_depth_next_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩,
    fun h => ⟨h.work,h.map,h.square,h.stage,h.keep,h.last,h.alphabet,h.product,h.order,h.fixed,h.points,h.family,h.table,h.real⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 对每个实际状态和指定实数，总能构造保持全部队列不变量的实际后继。 -/
theorem Ab_queue_d.step_l {Ω cY Y S θ t E e B k D m d x : M.Domain} {v : Fin 14 → M.Domain}
    (h : Ab_queue_d I Ω cY Y v t E e B k D m d) (hΩ : M.IsOmega Ω)
    (rank : V_d I θ Y) (target : Smem_d I cY Y S) (fx : Fn0_d Ω Ω x) :
    ∃ r : M.Domain, ∃ v' : Fin 14 → M.Domain, ∃ E' e' B' k' D' m' d' j K,
      Ab_queue_d I Ω cY Y v' (v 7) E' e' B' k' D' m' d' ∧
      Ab_step_d I Ω v v' t E e B k D m d E' B' k' D' m' d' j K x ∧
      Rt_tuple_d (Fin.addCases (m := 14) (n := 8) v' (fun i => [v 7,E',e',B',k',D',m',d'].get i)) r := by
  obtain ⟨k',D₀,m',d₀,work⟩ := h.work_l hZF hΩ
  obtain ⟨_,v',j,K,D',d',E',e',B',_,frame,map,square,stage,keep,last,alphabet,product,order,
      fixed,points,denseImage,conditionImage,task,done,real,birth,family,table,pick,available⟩ :=
    h.frame.next_scheduled_l hZFC hΩ rank target h.birth h.stage work.cursor work.bound work.pick work.task work.active fx
  have bound := (hΩ.members_areOrdinals (ZF.modelsKP hZF) (v 7) h.frame.index).transitive k' available
  have queue : Ab_queue_d I Ω cY Y v' (v 7) E' e' B' k' D' m' d' :=
    ⟨frame,birth,stage,work.cursor,bound,pick,task,fun eq => ⟨available,done eq⟩⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF)
    (Fin.addCases (m := 14) (n := 8) v' (fun i => [v 7,E',e',B',k',D',m',d'].get i))
  exact ⟨r,v',E',e',B',k',D',m',d',j,K,queue,
    ⟨⟨D₀,d₀,work,denseImage,conditionImage⟩,map,square,stage,keep,last,alphabet,product,order,
      fixed,points,family,table,real⟩,tuple⟩

end YesMetaZFC.SetTheory.LargeCardinal
