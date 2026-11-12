import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 成员满嵌入不增加内部有限程序

指令字母属于三个自然数坐标的实际乘积。有限函数回拉恢复整个程序，
有界指令检验反射合法性，故公式码全集也保持完整，而不只覆盖标准公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (e : M.Domain → N.Domain)
  (inj : Function.Injective e) (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full

theorem image_sop_l (hM : M.Models KP) (hN : N.Models KP) (k : Nat) (c i j : M.Domain) :
    Sop_d (kp_pair_l hM) k c i j ↔ Sop_d (kp_pair_l hN) k (e c) (e i) (e j) := by
  let ρ : Env M 3 := ⟨fun a => [c,i,j].get a,fun _ => c⟩
  exact (sop0_sat_l hM k ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
    ((delta0_image_l e inj full (sop0_delta_l k ..) ρ).trans
      (sop0_sat_l hN k (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2)))

theorem image_sfm_node_l (hM : M.Models KP) (hN : N.Models KP) (ω r c : M.Domain) :
    Sfm_node_d (kp_pair_l hM) ω r c ↔ Sfm_node_d (kp_pair_l hN) (e ω) (e r) (e c) := by
  have op k A B : (∃ i j, Sop_d (kp_pair_l hM) k c i j ∧ M.mem i A ∧ M.mem j B) ↔
      ∃ i j, Sop_d (kp_pair_l hN) k (e c) i j ∧ N.mem i (e A) ∧ N.mem j (e B) := by
    constructor
    · rintro ⟨i,j,h,hi,hj⟩
      exact ⟨e i,e j,(image_sop_l e inj full hM hN k c i j).mp h,
        (image_member_l e inj full).mpr hi,(image_member_l e inj full).mpr hj⟩
    · rintro ⟨i,j,h,hi,hj⟩
      obtain ⟨a,ha,rfl⟩ := (full A i).mp hi
      obtain ⟨b,hb,rfl⟩ := (full B j).mp hj
      exact ⟨a,b,(image_sop_l e inj full hM hN k c a b).mpr h,ha,hb⟩
  exact or_congr (op 0 ω ω) (or_congr (op 1 ω ω) (or_congr (op 2 r r) (op 3 ω r)))

omit inj full in
private theorem si_sfm_function_l {M : Structure.{u}} (hZF : M.Models ZF) {ω n F P Q : M.Domain}
    (hw : M.IsOmega ω) (h : Sfm_d (kp_pair_l (ZF.modelsKP hZF)) ω n F)
    (product : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω)
    (letters : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) Q ω P) :
    M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) F n Q := by
  refine ⟨h.2.1.2.1,h.2.1.2.2,fun i hi => ?_⟩
  obtain ⟨c,ic⟩ := (h.2.1.2.2 i).mp hi
  exact ⟨c,sfm_node_mem_l _ hZF hw product letters (hw.transitive (ZF.modelsKP hZF) n h.1 i hi) (h.2.2 i c ic),ic⟩

variable (hM : M.Models ZF) (hN : N.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN

theorem image_sfm_l {ω n F : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) :
    Sfm_d I ω n F ↔ Sfm_d J (e ω) (e n) (e F) := by
  obtain ⟨P,product⟩ := ZF.exists_cartesianProduct hM I ω ω
  obtain ⟨Q,letters⟩ := ZF.exists_cartesianProduct hM I ω P
  have product' := image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full product
  have letters' := image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full letters
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  constructor
  · intro h
    have fn := si_sfm_function_l hM hw h product letters
    have fn' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full fn
    have hn := (image_member_l e inj full).mpr h.1
    refine ⟨hn,⟨hw'.members_areOrdinals (ZF.modelsKP hN) (e n) hn,fn'.1,fn'.2.1⟩,?_⟩
    intro i c ic
    obtain ⟨a,b,ab,rfl,rfl⟩ := (image_entries_l e full fn.1.1 i c).mp ic
    exact (image_sfm_node_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) ω a b).mp (h.2.2 a b ab)
  · intro h
    have fn' := si_sfm_function_l hN hw' h product' letters'
    let ρ : Env M 3 := ⟨fun k => [n,Q,F].get k,fun _ => F⟩
    have fn0 : Fn0_d n Q F := (fn0_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2)).mp
      ((delta0_image_l e inj full (fn0_delta_l ..) ρ).mpr
        ((fn0_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2)).mpr (fn0_of_function_l (ZF.modelsKP hN) fn')))
    have fn := fn0_function_l (ZF.modelsKP hM) fn0
    have hn := (image_member_l e inj full).mp h.1
    exact ⟨hn,⟨hw.members_areOrdinals (ZF.modelsKP hM) n hn,fn.1,fn.2.1⟩,fun i c ic =>
      (image_sfm_node_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) ω i c).mpr (h.2.2 (e i) (e c) ((entry i c F).mp ic))⟩

/-- 任意目标内部有限程序连同其精确长度回拉，未假定目标程序预先来自源。 -/
theorem image_sfm_pull_l {ω : M.Domain} {n F : N.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (h : Sfm_d J (e ω) n F) : ∃ m G, Sfm_d I ω m G ∧ e m = n ∧ e G = F := by
  obtain ⟨P,product⟩ := ZF.exists_cartesianProduct hM I ω ω
  obtain ⟨Q,letters⟩ := ZF.exists_cartesianProduct hM I ω P
  have product' := image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full product
  have letters' := image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full letters
  obtain ⟨m,G,_,_,mn,gF⟩ := image_finite_function_pull_l hM hN e inj full hw hw' h.1
    (si_sfm_function_l hN hw' h product' letters')
  exact ⟨m,G,(image_sfm_l e inj full hM hN hw hw').mpr (mn.symm ▸ gF.symm ▸ h),mn,gF⟩

theorem image_scode_l {ω C : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (h : Scode_d I ω C) :
    Scode_d J (e ω) (e C) := by
  intro a
  constructor
  · intro ha
    obtain ⟨b,hb,rfl⟩ := (full C a).mp ha
    obtain ⟨n,F,k,code,program,root⟩ := (h b).mp hb
    exact ⟨e n,e F,e k,image_kpair_l e full code,(image_sfm_l e inj full hM hN hw hw').mp program,
      (image_member_l e inj full).mpr root⟩
  · rintro ⟨n,F,k,code,program,root⟩
    obtain ⟨m,G,pg,mn,gF⟩ := image_sfm_pull_l e inj full hM hN hw hw' program
    obtain ⟨r,hr,rk⟩ := (full m k).mp (mn.symm ▸ root)
    obtain ⟨b,bc⟩ := (I).total G r
    have eq : e b = a := kpair_unique_l N hN.1 (image_kpair_l e full bc) (gF.symm ▸ rk.symm ▸ code)
    exact (full C a).mpr ⟨b,(h b).mpr ⟨m,G,r,bc,pg,hr⟩,eq⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 成员满嵌入保持全部内部有限赋值的真值

目标的有限赋值全部回拉到源，故旧有限赋值空间仍完整。
源内实际求值表经 Δ₀ 方程运输，唯一恢复目标真值；不要求完整 ω 赋值空间保持。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (e : M.Domain → N.Domain)
  (inj : Function.Injective e) (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full

theorem image_fb_program_l (hM : M.Models KP) (hN : N.Models KP) (ω b n L F : M.Domain) :
    Fb_program_d hM ω b n L F ↔ Fb_program_d hN (e ω) (e b) (e n) (e L) (e F) := by
  let ρ : Env M 5 := ⟨fun k => [ω,b,n,L,F].get k,fun _ => F⟩
  exact (fb_program_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).symm.trans
    ((delta0_image_l e inj full (fb_program_delta_l ..) ρ).trans
      (fb_program_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)))

private theorem image_fv_eval_l (hM : M.Models KP) (hN : N.Models KP) (b A R E n L F C H : M.Domain) :
    Fv_eval_d hM b A R E n L F C H ↔ Fv_eval_d hN (e b) (e A) (e R) (e E) (e n) (e L) (e F) (e C) (e H) := by
  let ρ : Env M 9 := ⟨fun k => [b,A,R,E,n,L,F,C,H].get k,fun _ => F⟩
  exact (fv_eval_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)).symm.trans
    ((delta0_image_l e inj full (fv_eval_delta_l ..) ρ).trans
      (fv_eval_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)))

variable (hM : M.Models ZF) (hN : N.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN

/-- 程序的原坐标界随同一有界语法证书运输。 -/
theorem image_sbound_l {ω b n F : M.Domain} (hw' : N.IsOmega (e ω))
    (program : Sfm_d I ω n F) (hb : M.mem b ω) (bound : Sbound_d I F b) : Sbound_d J (e F) (e b) := by
  obtain ⟨L,range⟩ := ZF.exists_range_of_setFunction hM I program.2.1.2.1 program.2.1.2.2
  have fn : Fn0_d n L F := fn0_of_function_l (ZF.modelsKP hM)
    ⟨program.2.1.2.1,program.2.1.2.2,fun i hi => by
      obtain ⟨a,ia⟩ := (program.2.1.2.2 i).mp hi
      exact ⟨a,(range a).mpr ⟨i,ia⟩,ia⟩⟩
  exact (((image_fb_program_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) ω b n L F).mp
    (fb_program_of_l (ZF.modelsKP hM) program hb bound fn)).read_l hN hw').2

theorem image_finite_space_l {ω b A E : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (hb : M.mem b ω) (space : M.IsFunctionSpace I E b A) : N.IsFunctionSpace J (e E) (e b) (e A) := by
  intro f
  constructor
  · intro hf
    obtain ⟨s,hs,rfl⟩ := (full E f).mp hf
    exact image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full ((space s).mp hs)
  · intro ff
    obtain ⟨k,s,_,fs,kb,sf⟩ := image_finite_function_pull_l hM hN e inj full hw hw'
      ((image_member_l e inj full).mpr hb) ff
    have eq := inj kb
    subst k
    exact (full E f).mpr ⟨s,(space s).mpr fs,sf⟩

/-- 原有限赋值上的内部真值与同一实际有限赋值像上的目标真值双向相同。 -/
theorem image_finite_sat_l {ω A R E F n b r s : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (program : Sfm_d I ω n F) (hb : M.mem b ω) (bound : Sbound_d I F b)
    (space : M.IsFunctionSpace I E b A) (hr : M.mem r n) :
    Ssat_d I A R E F n r s ↔ Ssat_d J (e A) (e R) (e E) (e F) (e n) (e r) (e s) := by
  -- 程序及真值表的值域都是源内实际集合，不把可用表作为额外假设。
  obtain ⟨L,rangeF⟩ := ZF.exists_range_of_setFunction hM I program.2.1.2.1 program.2.1.2.2
  have ff : Fn0_d n L F := fn0_of_function_l (ZF.modelsKP hM)
    ⟨program.2.1.2.1,program.2.1.2.2,fun i hi => by
      obtain ⟨c,ic⟩ := (program.2.1.2.2 i).mp hi
      exact ⟨c,(rangeF c).mpr ⟨i,ic⟩,ic⟩⟩
  have pg := fb_program_of_l (ZF.modelsKP hM) program hb bound ff
  obtain ⟨H,eval⟩ := seval_exists_l I hM A R E F program.2.1.1
  obtain ⟨C,rangeH⟩ := ZF.exists_range_of_setFunction hM I eval.1.2.1 eval.1.2.2
  have hf : Fn0_d n C H := fn0_of_function_l (ZF.modelsKP hM)
    ⟨eval.1.2.1,eval.1.2.2,fun i hi => by
      obtain ⟨Y,iY⟩ := (eval.1.2.2 i).mp hi
      exact ⟨Y,(rangeH Y).mpr ⟨i,iY⟩,iY⟩⟩
  have cert := fv_eval_of_l hM hw pg space eval hf
  have pg' := (image_fb_program_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) ω b n L F).mp pg
  have cert' := (image_fv_eval_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) b A R E n L F C H).mp cert
  have space' := image_finite_space_l e inj full hM hN hw hw' hb space
  let ρ : Env M 4 := ⟨fun k => [C,H,r,s].get k,fun _ => s⟩
  have truth := (fv_at_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).symm.trans
    ((delta0_image_l e inj full (fv_at_delta_l ..) ρ).trans
      (fv_at_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3)))
  exact (cert.truth_l hM hw pg space hr).symm.trans
    (truth.trans (cert'.truth_l hN hw' pg' space' ((image_member_l e inj full).mpr hr)))

end YesMetaZFC.SetTheory.Internal

/-! ## 完整赋值的有限支撑回拉与实参真值运输

外层赋值在指定内部有限支撑上由源赋值实现。旧完整赋值的单次、两次更新
与成员满映射交换；有限真值比较因而覆盖分离与收集的全部实参。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (e : M.Domain → N.Domain)
  (inj : Function.Injective e) (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full

theorem image_update_l (hM : M.Models KP) (hN : N.Models KP) {ω A f i x g : M.Domain}
    (fn : M.IsSetFunctionFromTo (kp_pair_l hM) f ω A) (hi : M.mem i ω) (hx : M.mem x A)
    (update : Senv_update_d (kp_pair_l hM) f i x g) : Senv_update_d (kp_pair_l hN) (e f) (e i) (e x) (e g) := by
  let ρ : Env M 6 := ⟨fun k => [ω,A,f,i,x,g].get k,fun _ => f⟩
  have old := (se_update0_l hM (fn0_of_function_l hM fn) hi hx).mpr update
  have moved := (se_update0_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).mp
    ((delta0_image_l e inj full (se_update0_delta_l ..) ρ).mp
      ((se_update0_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).mpr old))
  have fn' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair hN) e inj full fn
  exact (se_update0_l hN (fn0_of_function_l hN fn') ((image_member_l e inj full).mpr hi)
    ((image_member_l e inj full).mpr hx)).mp moved

variable (hM : M.Models ZF) (hN : N.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN

/-- 任意目标完整赋值的指定有限支撑由一个实际源完整赋值实现。 -/
theorem image_assignment_l {ω b X : M.Domain} {g : N.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (hb : M.mem b ω) (ne : ∃ x, M.mem x X)
    (fg : N.IsSetFunctionFromTo J g (e ω) (e X)) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ Senv_agree_d J (e b) g (e f) := by
  have sub := hw'.transitive (ZF.modelsKP hN) (e b) ((image_member_l e inj full).mpr hb)
  obtain ⟨s₀,cut⟩ := ZF.exists_restriction hN J g (e b)
  obtain ⟨k,s,_,fs,kb,ss⟩ := image_finite_function_pull_l hM hN e inj full hw hw'
    ((image_member_l e inj full).mpr hb) (cut.isSetFunctionFromTo fg sub)
  have eq := inj kb
  subst k
  obtain ⟨u,hu⟩ := ne
  obtain ⟨f,fill,fn⟩ := senv_fill_exists_l I hM (ω := ω) fs hu
  have rest : M.IsRestrictionOf I s f b := ⟨fs.1.1,fun i x => ⟨fun h =>
    ⟨fs.input_mem_of_pairMember h,(fill.2 i x).mpr
      ⟨hw.transitive (ZF.modelsKP hM) b hb i (fs.input_mem_of_pairMember h),Or.inl ⟨fs.input_mem_of_pairMember h,h⟩⟩⟩,
    fun ⟨hi,h⟩ => ((fill.2 i x).mp h).2.elim And.right (fun h => (h.1 hi).elim)⟩⟩
  have rest' := image_restriction_l hM hN e inj full fn.1.1 rest
  refine ⟨f,fn,fun i x hi => ?_⟩
  have old : N.PairMember J i x (e s) ↔ N.PairMember J i x g := by
    rw [ss]
    exact (cut.2 i x).trans (and_iff_right hi)
  exact old.symm.trans ((rest'.2 i x).trans (and_iff_right hi))

/-- 旧完整赋值的真值在目标的完整赋值空间中保持。 -/
theorem image_ssat_l {ω X R E F n r f : M.Domain} {D : N.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (program : Sfm_d I ω n F) (hr : M.mem r n)
    (space : M.IsFunctionSpace I E ω X) (space' : N.IsFunctionSpace J D (e ω) (e X)) (hf : M.mem f E) :
    Ssat_d I X R E F n r f ↔ Ssat_d J (e X) (e R) D (e F) (e n) (e r) (e f) := by
  obtain ⟨b,hb,bound⟩ := sbound_exists_l I hM hw program
  obtain ⟨K,finiteSpace⟩ := ZF.exists_functionSpace hM I b X
  obtain ⟨s,cut⟩ := ZF.exists_restriction hM I f b
  have sub := hw.transitive (ZF.modelsKP hM) b hb
  have fs := cut.isSetFunctionFromTo ((space f).mp hf) sub
  have agree : Senv_agree_d I b f s := fun i x hi => ((cut.2 i x).trans (and_iff_right hi)).symm
  have cut' := image_restriction_l hM hN e inj full ((space f).mp hf).1.1 cut
  have agree' : Senv_agree_d J (e b) (e f) (e s) := fun i x hi => ((cut'.2 i x).trans (and_iff_right hi)).symm
  have ff' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full ((space f).mp hf)
  have fs' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full fs
  have finiteSpace' := image_finite_space_l e inj full hM hN hw hw' hb finiteSpace
  have old := ssat_spaces_l I hM (R := R) program bound space finiteSpace sub (fun _ h => h) hr hf ((finiteSpace s).mpr fs) agree
  have new := ssat_spaces_l J hN (R := e R) ((image_sfm_l e inj full hM hN hw hw').mp program)
    (image_sbound_l e inj full hM hN hw' program hb bound) space' finiteSpace'
    (hw'.transitive (ZF.modelsKP hN) (e b) ((image_member_l e inj full).mpr hb)) (fun _ h => h)
    ((image_member_l e inj full).mpr hr) ((space' (e f)).mpr ff') ((finiteSpace' (e s)).mpr fs') agree'
  exact old.trans ((image_finite_sat_l e inj full hM hN hw hw' program hb bound finiteSpace hr).trans new.symm)

theorem image_unary_truth_l {ω X R E F n r i f x : M.Domain} {D : N.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (program : Sfm_d I ω n F) (hr : M.mem r n)
    (space : M.IsFunctionSpace I E ω X) (space' : N.IsFunctionSpace J D (e ω) (e X))
    (hf : M.mem f E) (hi : M.mem i ω) (hx : M.mem x X) :
    (∃ g, Senv_update_d I f i x g ∧ Ssat_d I X R E F n r g) ↔
      ∃ g, Senv_update_d J (e f) (e i) (e x) g ∧ Ssat_d J (e X) (e R) D (e F) (e n) (e r) g := by
  obtain ⟨g,update,fn⟩ := senv_update_exists_l I hM ((space f).mp hf) hi hx
  have update' := image_update_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) ((space f).mp hf) hi hx update
  have truth := image_ssat_l e inj full hM hN (R := R) hw hw' program hr space space' ((space g).mpr fn)
  exact ⟨fun ⟨u,hu,ht⟩ => ⟨e g,update',truth.mp (senv_update_unique_l I hM.1 hu update ▸ ht)⟩,
    fun ⟨u,hu,ht⟩ => ⟨g,update,truth.mpr (senv_update_unique_l J hN.1 hu update' ▸ ht)⟩⟩

theorem image_sbin_l {ω X R E F n r i j f x y : M.Domain} {D : N.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (program : Sfm_d I ω n F) (hr : M.mem r n)
    (space : M.IsFunctionSpace I E ω X) (space' : N.IsFunctionSpace J D (e ω) (e X))
    (hf : M.mem f E) (hi : M.mem i ω) (hj : M.mem j ω) (hx : M.mem x X) (hy : M.mem y X) :
    Sbin_d I X R E F n r i j f x y ↔ Sbin_d J (e X) (e R) D (e F) (e n) (e r) (e i) (e j) (e f) (e x) (e y) := by
  obtain ⟨g,ug,fg⟩ := senv_update_exists_l I hM ((space f).mp hf) hi hx
  obtain ⟨h,uh,fh⟩ := senv_update_exists_l I hM fg hj hy
  have ug' := image_update_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) ((space f).mp hf) hi hx ug
  have uh' := image_update_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) fg hj hy uh
  exact (sbin_value_l I hM.1 ug uh).trans
    ((image_ssat_l e inj full hM hN hw hw' program hr space space' ((space h).mpr fh)).trans
      (sbin_value_l J hN.1 ug' uh').symm)

end YesMetaZFC.SetTheory.Internal
