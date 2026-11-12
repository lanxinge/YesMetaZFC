import YesMetaZFC.Model.SetTheory.Reflection.RankSkolem
import YesMetaZFC.Model.SetTheory.Internal.TruthImage
import YesMetaZFC.Model.SetTheory.Embedding.Reflect

/-! # 原司寇伦选择图在成员满扩张中保持

有限参数列按同一基点补成完整赋值，再作同一坐标更新。完整真值的有限支撑
保持识别原见证；目标载体中的候选元素全部来自源，故无见证的默认值也保持。
整个结论覆盖内部全部公式码，不要求公式或参数列长度外部标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (j : M.Domain → N.Domain)
  (inj : Function.Injective j) (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
  (hM : M.Models ZF) (hN : N.Models ZF)
include inj full hM hN
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)

omit hM hN in
private theorem ssk_fill_image_l (hP : M.Models KP) (hQ : N.Models KP) {ω u n s f : M.Domain}
    (fs : M.IsSetRelation (kp_pair_l hP) s)
    (fill : Senv_fill_d (kp_pair_l hP) ω u n s f) :
    Senv_fill_d (kp_pair_l hQ) (j ω) (j u) (j n) (j s) (j f) := by
  have mem {a b : M.Domain} : N.mem (j a) (j b) ↔ M.mem a b := image_member_l j inj full
  have edge := image_entry_iff_l j inj full (KP.exists_pair hP) hQ.1
  have relation : N.IsSetRelation (kp_pair_l hQ) (j f) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := (full f p).mp hp
    obtain ⟨i,x,pair⟩ := fill.1 q hq
    exact ⟨j i,j x,image_kpair_l j full pair⟩
  refine ⟨relation,fun i x => ?_⟩
  constructor
  · intro ix
    obtain ⟨a,b,ab,rfl,rfl⟩ := (image_entries_l j full fill.1 i x).mp ix
    obtain ⟨ha,h⟩ := (fill.2 a b).mp ab
    exact ⟨mem.mpr ha,h.elim (fun h => Or.inl ⟨mem.mpr h.1,(edge a b s).mp h.2⟩)
      (fun h => Or.inr ⟨fun hn => h.1 (mem.mp hn),congrArg j h.2⟩)⟩
  · rintro ⟨hi,⟨hn,ix⟩ | ⟨hn,rfl⟩⟩
    · obtain ⟨a,b,ab,rfl,rfl⟩ := (image_entries_l j full fs i x).mp ix
      exact (edge a b f).mp ((fill.2 a b).mpr ⟨mem.mp hi,Or.inl ⟨mem.mp hn,ab⟩⟩)
    · obtain ⟨a,ha,rfl⟩ := (full ω i).mp hi
      exact (edge a u f).mp ((fill.2 a u).mpr ⟨ha,Or.inr ⟨fun h => hn (mem.mpr h),rfl⟩⟩)

/-- 真实有限赋值上的司寇伦见证与同一内部公式一起保持。 -/
theorem image_ssk_wit_l {ω c X R u a i n s x l F r : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω)) (model : Smdl_d I c X R)
    (point : M.mem u X) (code : Sformula_d I ω a l F r) (hi : M.mem i ω)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X) (hx : M.mem x X) :
    Ssk_wit_d I ω c X u a i s x ↔ Ssk_wit_d J (j ω) (j c) (j X) (j u) (j a) (j i) (j s) (j x) := by
  obtain ⟨f,fill,ff⟩ := senv_fill_exists_l I hM (ω := ω) fs point
  obtain ⟨g,update,fg⟩ := senv_update_exists_l I hM ff hi hx
  obtain ⟨E,space⟩ := ZF.exists_functionSpace hM I ω X
  -- 目标的完整赋值空间重新构造；只搬运本次规范补值和更新得到的赋值。
  obtain ⟨D,space'⟩ := ZF.exists_functionSpace hN J (j ω) (j X)
  have model' := image_smdl_l j inj full (ZF.modelsKP hM) (ZF.modelsKP hN) model
  have code' : Sformula_d J (j ω) (j a) (j l) (j F) (j r) :=
    ⟨image_kpair_l j full code.1,(image_sfm_l j inj full hM hN hw hw').mp code.2.1,
      (image_member_l j inj full).mpr code.2.2⟩
  have truth := (satisfies_decode_l I hM.1 model code space).trans
    ((image_ssat_l j inj full hM hN hw hw' code.2.1 code.2.2 space space' ((space g).mpr fg)).trans
      (satisfies_decode_l J hN.1 model' code' space').symm)
  exact (ssk_wit_decode_l I hM.1 hn fs fill update).trans (truth.trans
    (ssk_wit_decode_l J hN.1 ((image_member_l j inj full).mpr hn)
      (image_function_l j inj full fs) (ssk_fill_image_l j inj full (ZF.modelsKP hM) (ZF.modelsKP hN) fs.1.1 fill)
      (image_update_l j inj full (ZF.modelsKP hM) (ZF.modelsKP hN) ff hi hx update)).symm)

theorem image_ssk_l {ω c X R u C S T D K : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    (model : Smdl_d I c X R) (skolem : Ssk_d I ω c X u C S T D K) :
    Ssk_d J (j ω) (j c) (j X) (j u) (j C) (j S) (j T) (j D) (j K) := by
  refine ⟨(image_member_l j inj full).mpr skolem.point,image_scode_l j inj full hM hN hw hw' skolem.codes,
    image_fseq_l hM hN j inj full hw hw' skolem.params,image_product_l j inj full skolem.labels,
    image_product_l j inj full skolem.domain,image_function_l j inj full skolem.graph,?_⟩
  intro p x px
  obtain ⟨p₀,x₀,px₀,rfl,rfl⟩ := (image_entries_l j full skolem.graph.1.1 p x).mp px
  obtain ⟨t,ht,s,hs,pair⟩ := (skolem.domain p₀).mp (skolem.graph.input_mem_of_pairMember px₀)
  obtain ⟨a,ha,i,hi,ti⟩ := (skolem.labels t).mp ht
  obtain ⟨n,hn,fs⟩ := (skolem.params s).mp hs
  obtain ⟨l,F,r,code⟩ := (skolem.codes a).mp ha
  have truth y (hy : M.mem y X) := image_ssk_wit_l j inj full hM hN hw hw' model skolem.point code hi hn fs hy
  refine ⟨j a,j i,j t,j s,image_kpair_l j full ti,image_kpair_l j full pair,?_⟩
  rcases skolem.value_l I ti pair px₀ with wit | ⟨none,eq⟩
  · exact Or.inl ((truth x₀ (skolem.graph.output_mem_of_pairMember px₀)).mp wit)
  · refine Or.inr ⟨?_,congrArg j eq⟩
    rintro ⟨y,hy,wit⟩
    obtain ⟨y₀,hy₀,rfl⟩ := (full X y).mp hy
    exact none ⟨y₀,hy₀,(truth y₀ hy₀).mpr wit⟩

end YesMetaZFC.SetTheory.Internal
