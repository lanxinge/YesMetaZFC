import YesMetaZFC.Model.SetTheory.Internal.TruthImage
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv

/-! # 成员满嵌入保持集合模型之间的完整内部初等图

外层完整赋值先限制到程序的内部有限支撑，再回拉到源模型。
源初等性作用于同一有限程序与有限赋值，有限真值绝对性最后恢复外层完整真值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (e : M.Domain → N.Domain)
  (inj : Function.Injective e) (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full

omit inj in
theorem image_transitive_l {A : M.Domain} (h : M.TransitiveSet A) : N.TransitiveSet (e A) := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := (full A x).mp hx
  obtain ⟨b,hb,rfl⟩ := (full a y).mp hy
  exact (full A (e b)).mpr ⟨b,h a ha b hb,rfl⟩

theorem image_smdl_l (hM : M.Models KP) (hN : N.Models KP) {c A R : M.Domain}
    (h : Smdl_d (kp_pair_l hM) c A R) : Smdl_d (kp_pair_l hN) (e c) (e A) (e R) := by
  obtain ⟨a,ha⟩ := h.2.1
  refine ⟨image_kpair_l e full h.1,⟨e a,(image_member_l e inj full).mpr ha⟩,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := (full R p).mp hp
    obtain ⟨a,b,ab⟩ := h.2.2.1 q hq
    exact ⟨e a,e b,image_kpair_l e full ab⟩
  · intro a b ab
    obtain ⟨x,y,xy,rfl,rfl⟩ := (image_entries_l e full h.2.2.1 a b).mp ab
    exact ⟨(image_member_l e inj full).mpr (h.2.2.2 x y xy).1,(image_member_l e inj full).mpr (h.2.2.2 x y xy).2⟩

theorem image_smem_l (hM : M.Models KP) (hN : N.Models KP) {c A R : M.Domain}
    (h : Smem_d (kp_pair_l hM) c A R) : Smem_d (kp_pair_l hN) (e c) (e A) (e R) := by
  refine ⟨image_smdl_l e inj full hM hN h.1,fun a b => ⟨?_,?_⟩⟩
  · intro ab
    obtain ⟨x,y,xy,rfl,rfl⟩ := (image_entries_l e full h.1.2.2.1 a b).mp ab
    obtain ⟨hx,hy,mem⟩ := (h.2 x y).mp xy
    exact ⟨(image_member_l e inj full).mpr hx,(image_member_l e inj full).mpr hy,(image_member_l e inj full).mpr mem⟩
  · rintro ⟨ha,hb,mem⟩
    obtain ⟨x,hx,rfl⟩ := (full A a).mp ha
    obtain ⟨y,hy,rfl⟩ := (full A b).mp hb
    exact (image_entry_iff_l e inj full (KP.exists_pair hM) hN.1 x y R).mp
      ((h.2 x y).mpr ⟨hx,hy,(image_member_l e inj full).mp mem⟩)

/-- 原集合模型及其规范像的实际同构；每个对象仍是原对象的规范像。 -/
theorem image_smdl_iso_l (hM : M.Models KP) (hN : N.Models KP) {c A R : M.Domain}
    (model : Smdl_d (kp_pair_l hM) c A R) :
    let X := smdl_structure_l (kp_pair_l hM) (R := R) model.2.1
    let Y := smdl_structure_l (kp_pair_l hN) (R := e R) (image_smdl_l e inj full hM hN model).2.1
    ∃ f : X.Domain → Y.Domain, Function.Injective f ∧ Function.Surjective f ∧
      (∀ a, (f a).val = e a.val) ∧ ∀ a b, X.mem a b ↔ Y.mem (f a) (f b) := by
  let X := smdl_structure_l (kp_pair_l hM) (R := R) model.2.1
  let Y := smdl_structure_l (kp_pair_l hN) (R := e R) (image_smdl_l e inj full hM hN model).2.1
  let f : X.Domain → Y.Domain := fun a => ⟨e a.val,(image_member_l e inj full).mpr a.property⟩
  have onto : Function.Surjective f := by
    intro y
    obtain ⟨a,ha,eq⟩ := (full A y.val).mp y.property
    exact ⟨⟨a,ha⟩,Subtype.ext eq⟩
  exact ⟨f,fun a b eq => Subtype.ext (inj (congrArg Subtype.val eq)),onto,fun _ => rfl,
    fun a b => image_entry_iff_l e inj full (KP.exists_pair hM) hN.1 a.val b.val R⟩

/-- 两次解码的集合结构由同一成员满图实际同构，因而保留原生理论。 -/
theorem image_smdl_models_l (hM : M.Models KP) (hN : N.Models KP) {c A R : M.Domain}
    (model : Smdl_d (kp_pair_l hM) c A R) {𝒯 : Theory}
    (theory : (smdl_structure_l (kp_pair_l hM) (R := R) model.2.1).Models 𝒯) :
    (smdl_structure_l (kp_pair_l hN) (R := e R) (image_smdl_l e inj full hM hN model).2.1).Models 𝒯 := by
  let X := smdl_structure_l (kp_pair_l hM) (R := R) model.2.1
  obtain ⟨f,_,onto,_,rel⟩ := image_smdl_iso_l e inj full hM hN model
  refine ⟨⟨?_⟩,fun φ hφ => ?_⟩
  · intro x y same
    obtain ⟨a,rfl⟩ := onto x
    obtain ⟨b,rfl⟩ := onto y
    exact congrArg f (theory.1.eq_of_same_members a b (fun z => (rel z a).trans ((same (f z)).trans (rel z b).symm)))
  · rw [Structure.satisfiesSentence_iff]
    intro g
    obtain ⟨a⟩ := X.nonempty
    let ρ : Env X 0 := ⟨Fin.elim0,fun _ => a⟩
    have truth := (formula_image_l f onto rel φ.formula ρ).mp
      ((Structure.satisfiesSentence_iff X φ).mp (theory.2 φ hφ) ρ.free)
    exact (Formula.closed_env_l _ φ.freeClosed (funext (fun k => Fin.elim0 k))).mp truth

variable (hM : M.Models ZF) (hN : N.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN

/-- 完整初等性覆盖目标全部内部公式和全部赋值，不要求目标赋值来自源。 -/
theorem image_smap_l {ω c d A R B S j : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (left : Smdl_d I c A R) (right : Smdl_d I d B S) (map : Smap_d I ω c d A B j) :
    Smap_d J (e ω) (e c) (e d) (e A) (e B) (e j) := by
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have left' := image_smdl_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) left
  have right' := image_smdl_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) right
  have injection := image_injection_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full map.1
  obtain ⟨C,codes,_⟩ := map.2
  refine ⟨injection,e C,image_scode_l e inj full hM hN hw hw' codes,?_⟩
  intro a f g ha hf hg assign
  obtain ⟨a₀,ha₀,rfl⟩ := (full C a).mp ha
  obtain ⟨n,F,r,code,program,root⟩ := (codes a₀).mp ha₀
  obtain ⟨b,hb,bound⟩ := sbound_exists_l I hM hw program
  -- 运输有界程序证书，从而保留同一支撑界 b。
  have program' := (image_sfm_l e inj full hM hN hw hw').mp program
  have bound' := image_sbound_l e inj full hM hN hw' program hb bound
  have hb' := (image_member_l e inj full).mpr hb
  have sub := hw'.transitive (ZF.modelsKP hN) (e b) hb'
  -- 只回拉实际读取的有限前缀；完整外层赋值 f、g 无须属于源。
  obtain ⟨s₀,cut⟩ := ZF.exists_restriction hN J f (e b)
  have finite := cut.isSetFunctionFromTo hf sub
  obtain ⟨b₀,s,_,fs,bb,ss⟩ := image_finite_function_pull_l hM hN e inj full hw hw' hb' finite
  have eq := inj bb
  subst b₀
  have hs := fn0_of_function_l (ZF.modelsKP hM) fs
  obtain ⟨t,comp⟩ := cp0_exists_l (ZF.modelsKP hM) hs (fn0_of_function_l (ZF.modelsKP hM) map.1.1)
  have ft := fn0_function_l (ZF.modelsKP hM) comp.1
  have ft' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full ft
  have agree : Senv_agree_d J (e b) f (e s) := by
    intro i x hi
    rw [ss]
    exact ⟨fun h => (cut.2 i x).mpr ⟨hi,h⟩,fun h => ((cut.2 i x).mp h).2⟩
  have agree' : Senv_agree_d J (e b) g (e t) := by
    intro i x hi
    obtain ⟨k,hk,rfl⟩ := (full b i).mp hi
    obtain ⟨a,ha,y,hy,ka,ay,ky⟩ := comp.2 k hk
    have kf := (agree (e k) (e a) ((image_member_l e inj full).mpr hk)).mpr ((entry k a s).mp ka)
    have kg := assign (e k) (sub (e k) ((image_member_l e inj full).mpr hk)) (e a) (e y) kf ((entry a y j).mp ay)
    have kt := (entry k y t).mp ky
    exact ⟨fun h => hg.1.2 (e k) (e y) x kg h ▸ kt,
      fun h => ft'.1.2 (e k) (e y) x kt h ▸ kg⟩
  -- 同一有限真值先由源初等图比较，再由有界求值证书搬到目标。
  obtain ⟨E,space⟩ := ZF.exists_functionSpace hM I b A
  obtain ⟨D,spaceD⟩ := ZF.exists_functionSpace hM I b B
  have finiteTruth := map.finite_sat_l hM hw left right hb program bound root space spaceD hs comp
  have truth : Ssat_d J (e A) (e R) (e E) (e F) (e n) (e r) (e s) ↔
      Ssat_d J (e B) (e S) (e D) (e F) (e n) (e r) (e t) :=
    (image_finite_sat_l e inj full hM hN hw hw' program hb bound space root).symm.trans
      (finiteTruth.trans (image_finite_sat_l e inj full hM hN hw hw' program hb bound spaceD root))
  obtain ⟨E₀,fullA⟩ := ZF.exists_functionSpace hN J (e ω) (e A)
  obtain ⟨D₀,fullB⟩ := ZF.exists_functionSpace hN J (e ω) (e B)
  have root' := (image_member_l e inj full).mpr root
  have space' := image_finite_space_l e inj full hM hN hw hw' hb space
  have spaceD' := image_finite_space_l e inj full hM hN hw hw' hb spaceD
  have fs' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full fs
  have firstTruth := ssat_spaces_l J hN (R := e R) program' bound' fullA space' sub (fun _ h => h)
    root' ((fullA f).mpr hf) ((space' (e s)).mpr fs') agree
  have secondTruth := ssat_spaces_l J hN (R := e S) program' bound' fullB spaceD' sub (fun _ h => h)
    root' ((fullB g).mpr hg) ((spaceD' (e t)).mpr ft') agree'
  have formula : Sformula_d J (e ω) (e a₀) (e n) (e F) (e r) := ⟨image_kpair_l e full code,program',root'⟩
  exact (satisfies_decode_l J hN.1 left' formula fullA).trans
    (firstTruth.trans (truth.trans (secondTruth.symm.trans (satisfies_decode_l J hN.1 right' formula fullB).symm)))

end YesMetaZFC.SetTheory.Internal

/-! ## 成员满包含反射完整内部初等图

源中的任意内部程序及完整赋值沿包含送入背景；实际真值绝对性再将背景
初等性读回。谓词结构在源中重新构造规范呈示，其像由关系外延性识别，
故不必额外假定背景选取的结构码属于源模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (e : M.Domain → N.Domain)
  (inj : Function.Injective e) (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full

theorem image_spred_l (hM : M.Models KP) (hN : N.Models KP) {c X A R : M.Domain}
    (h : Spred_d (kp_pair_l hM) c X A R) :
    Spred_d (kp_pair_l hN) (e c) (e X) (e A) (e R) := by
  have mem {a b : M.Domain} : N.mem (e a) (e b) ↔ M.mem a b := image_member_l e inj full
  refine ⟨image_smdl_l e inj full hM hN h.1,(image_subset_iff_l e inj full).mpr h.2.1,fun x y => ⟨?_,?_⟩⟩
  · intro xy
    obtain ⟨a,b,ab,rfl,rfl⟩ := (image_entries_l e full h.1.2.2.1 x y).mp xy
    obtain ⟨ha,hb,edge⟩ := (h.2.2 a b).mp ab
    exact ⟨mem.mpr ha,mem.mpr hb,edge.elim (fun t => Or.inl (mem.mpr t))
      (fun ⟨eq,ha⟩ => Or.inr ⟨congrArg e eq,mem.mpr ha⟩)⟩
  · rintro ⟨hx,hy,edge⟩
    obtain ⟨a,ha,rfl⟩ := (full X x).mp hx
    obtain ⟨b,hb,rfl⟩ := (full X y).mp hy
    exact (image_entry_iff_l e inj full (KP.exists_pair hM) hN.1 a b R).mp
      ((h.2.2 a b).mpr ⟨ha,hb,edge.elim (fun t => Or.inl (mem.mp t))
        (fun ⟨eq,ha⟩ => Or.inr ⟨inj eq,mem.mp ha⟩)⟩)

variable (hM : M.Models ZF) (hN : N.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)

theorem reflect_smap_l {ω c d X R Y S j : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (left : Smdl_d I c X R) (right : Smdl_d I d Y S)
    (map : Smap_d J (e ω) (e c) (e d) (e X) (e Y) (e j)) : Smap_d I ω c d X Y j := by
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have mem {a b : M.Domain} : N.mem (e a) (e b) ↔ M.mem a b := image_member_l e inj full
  let ρ : Env M 3 := ⟨fun i => [X,Y,j].get i,fun _ => X⟩
  have fn : Fn0_d X Y j := (fn0_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2)).mp
    ((delta0_image_l e inj full (fn0_delta_l ..) ρ).mpr
      ((fn0_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2)).mpr
        (fn0_of_function_l (ZF.modelsKP hN) map.1.1)))
  have ji : M.IsSetInjectionFromTo I j X Y := ⟨fn0_function_l (ZF.modelsKP hM) fn,
    fun a b z az bz => inj (map.1.2 (e a) (e b) (e z) ((entry a z j).mp az) ((entry b z j).mp bz))⟩
  obtain ⟨C,codes⟩ := scode_exists_l I hM hw
  obtain ⟨E,space⟩ := ZF.exists_functionSpace hM I ω X
  obtain ⟨D,spaceD⟩ := ZF.exists_functionSpace hM I ω Y
  obtain ⟨E',space'⟩ := ZF.exists_functionSpace hN J (e ω) (e X)
  obtain ⟨D',spaceD'⟩ := ZF.exists_functionSpace hN J (e ω) (e Y)
  have left' := image_smdl_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) left
  have right' := image_smdl_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) right
  refine ⟨ji,C,codes,fun a f g ha hf hg assign => ?_⟩
  obtain ⟨n,F,r,code,program,root⟩ := (codes a).mp ha
  have hf' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full hf
  have hg' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full hg
  have assign' : Smap_assign_d J (e ω) (e j) (e f) (e g) := by
    intro i hi x y ix xy
    obtain ⟨i,hi₀,rfl⟩ := (full ω i).mp hi
    obtain ⟨x,_,rfl⟩ := (full X x).mp (hf'.output_mem_of_pairMember ix)
    obtain ⟨y,_,rfl⟩ := (full Y y).mp (map.1.1.output_mem_of_pairMember xy)
    exact (entry i y g).mp (assign i hi₀ x y ((entry i x f).mpr ix) ((entry x y j).mpr xy))
  have compare := map.ssat_l J hN.1 left' right' ((image_sfm_l e inj full hM hN hw hw').mp program)
    (mem.mpr root) space' spaceD' ((space' (e f)).mpr hf') ((spaceD' (e g)).mpr hg') assign'
  exact (satisfies_decode_l I hM.1 left ⟨code,program,root⟩ space).trans
    ((image_ssat_l e inj full hM hN hw hw' program root space space' ((space f).mpr hf)).trans
      (compare.trans ((image_ssat_l e inj full hM hN hw hw' program root spaceD spaceD' ((spaceD g).mpr hg)).symm.trans
        (satisfies_decode_l I hM.1 right ⟨code,program,root⟩ spaceD).symm)))

theorem reflect_spred_emb_l {ω X A Y B j : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (h : Spred_emb_d J (e ω) (e X) (e A) (e Y) (e B) (e j)) : Spred_emb_d I ω X A Y B j := by
  obtain ⟨c,R,d,S,left,right,map⟩ := h
  obtain ⟨c₀,R₀,left₀⟩ := spred_exists_l I hM
    (left.1.2.1.elim fun x hx => (full X x).mp hx |>.imp fun a ha => ha.1)
    ((image_subset_iff_l e inj full).mp left.2.1)
  obtain ⟨d₀,S₀,right₀⟩ := spred_exists_l I hM
    (right.1.2.1.elim fun y hy => (full Y y).mp hy |>.imp fun a ha => ha.1)
    ((image_subset_iff_l e inj full).mp right.2.1)
  have unique {X A c R d S : N.Domain} (p : Spred_d J c X A R) (q : Spred_d J d X A S) : c = d := by
    have eq := p.1.2.2.1.eq_of_pairMember_iff hN.1 q.1.2.2.1
      (fun a b => (p.2.2 a b).trans (q.2.2 a b).symm)
    exact kpair_unique_l N hN.1 (eq ▸ p.1.1) q.1.1
  have ec := unique left (image_spred_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) left₀)
  have ed := unique right (image_spred_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) right₀)
  exact ⟨c₀,R₀,d₀,S₀,left₀,right₀,reflect_smap_l e inj full hM hN hw hw' left₀.1 right₀.1 (ec ▸ ed ▸ map)⟩

end YesMetaZFC.SetTheory.Internal
