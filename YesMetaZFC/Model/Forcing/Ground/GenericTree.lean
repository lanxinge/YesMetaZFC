import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.SetTheory.Internal.ClosureLetters
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.SetTheory.Reflection.SkolemImage
import YesMetaZFC.Model.SetTheory.Reflection.SkolemWitnessTree
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround

/-! # 有限闭包检查沿成员满嵌入保持

任务编号的旧图条目回收任务及输入位置列。求值列由原模型中的函数复合
构造，再由目标中的唯一性识别。因此局部检查只需源的 KP 和目标的外延性，
不需要自然数标准性、目标替代或整个树谓词的 Δ₀ 断言。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models KP) (hN : Extensional N)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include hM hN inj full

omit hM in
private theorem cl_fn_image_l (hE : Extensional M) (a b f : M.Domain) :
    Fn0_d a b f ↔ Fn0_d (j a) (j b) (j f) := by
  let ρ : Env M 3 := ⟨fun i => [a,b,f].get i,fun _ => a⟩
  exact (fn0_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
    ((delta0_image_l j inj full (fn0_delta_l ..) ρ).trans (fn0_sat_l hN _ _ _ _))

omit hM in
private theorem cl_cp_image_l (hE : Extensional M) (m n X q e s : M.Domain) :
    Cp0_d m n X q e s ↔ Cp0_d (j m) (j n) (j X) (j q) (j e) (j s) := by
  let ρ : Env M 6 := ⟨fun i => [m,n,X,q,e,s].get i,fun _ => m⟩
  exact (cp0_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).symm.trans
    ((delta0_image_l j inj full (cp0_delta_l ..) ρ).trans (cp0_sat_l hN _ _ _ _ _ _ _))

theorem image_cl_at_l {ω X T J K n e u : M.Domain} (fe : Fn0_d n X e) :
    Cl_at_d ω X T J K n e u ↔ Cl_at_d (j ω) (j X) (j T) (j J) (j K) (j n) (j e) (j u) := by
  have edge := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  have mem {a b : M.Domain} : N.mem (j a) (j b) ↔ M.mem a b := image_member_l j inj full
  have typed := cl_fn_image_l hN j inj full hM.1
  have comp := cl_cp_image_l hN j inj full hM.1
  have pull {r : M.Domain} {a b : N.Domain} (ab : Rd_entry_d a b (j r)) :
      ∃ x y, Rd_entry_d x y r ∧ j x = a ∧ j y = b := by
    obtain ⟨p,pair,hp⟩ := ab
    obtain ⟨p₀,hp₀,rfl⟩ := (full r p).mp hp
    obtain ⟨x,y,xy,rfl,rfl⟩ := image_kpair_pull_l hM hN j inj full pair
    exact ⟨x,y,⟨p₀,xy,hp₀⟩,rfl,rfl⟩
  constructor
  · intro check m t q v k l s p x hm ht fq pair vk hk kl hl cs pp lx
    -- 任务条目及有序对坐标均为旧对象，不对无界节点公式直接使用绝对性。
    obtain ⟨m₀,hm₀,rfl⟩ := (full ω m).mp hm
    obtain ⟨v₀,k₀,vk₀,rfl,rfl⟩ := pull vk
    obtain ⟨t₀,q₀,pair₀,rfl,rfl⟩ := image_kpair_pull_l hM hN j inj full pair
    obtain ⟨l₀,hl₀,rfl⟩ := (full n l).mp hl
    obtain ⟨l',x₀,lx₀,eq,rfl⟩ := pull lx
    have eq := inj eq
    subst l'
    have fq₀ := (typed m₀ n q₀).mpr fq
    -- 原模型中重建求值列，目标中的复合唯一性给出字面识别。
    obtain ⟨s₀,cs₀⟩ := cp0_exists_l hM fq₀ fe
    have eq := cp0_unique_l hN fq ((typed n X e).mp fe) ((comp m₀ n X q₀ e s₀).mp cs₀) cs
    subst s
    obtain ⟨p₀,pp₀⟩ := (kp_pair_l hM).total t₀ s₀
    have eq := kpair_unique_l N hN (image_kpair_l j full pp₀) pp
    subst p
    exact (edge p₀ x₀ K).mp (check m₀ t₀ q₀ v₀ k₀ l₀ s₀ p₀ x₀ hm₀ (mem.mp ht) fq₀ pair₀
      vk₀ (mem.mp hk) ((edge k₀ l₀ u).mpr kl) hl₀ cs₀ pp₀ lx₀)
  · intro check m t q v k l s p x hm ht fq pair vk hk kl hl cs pp lx
    exact (edge p x K).mpr (check (j m) (j t) (j q) (j v) (j k) (j l) (j s) (j p) (j x)
      (mem.mpr hm) (mem.mpr ht) ((typed m n q).mp fq) (image_kpair_l j full pair)
      ((edge v k J).mp vk) (mem.mpr hk) ((edge k l u).mp kl) (mem.mpr hl)
      ((comp m n X q e s).mp cs) (image_kpair_l j full pp) ((edge l x e).mp lx))

/-- 原节点的完整检查在扩张中双向成立；不假设整个嵌入初等。 -/
theorem image_cl_node_l {ω X T J K n e u : M.Domain} :
    Cl_node_d ω X T J K n e u ↔ Cl_node_d (j ω) (j X) (j T) (j J) (j K) (j n) (j e) (j u) := by
  have fe := cl_fn_image_l hN j inj full hM.1 n X e
  have fu := cl_fn_image_l hN j inj full hM.1 n ω u
  constructor
  · intro node
    exact ⟨(image_member_l j inj full).mpr node.natural,fe.mp node.enumeration,fu.mp node.witnesses,
      (image_cl_at_l hM hN j inj full node.enumeration).mp node.check⟩
  · intro node
    exact ⟨(image_member_l j inj full).mp node.natural,fe.mpr node.enumeration,fu.mpr node.witnesses,
      (image_cl_at_l hM hN j inj full (fe.mpr node.enumeration)).mpr node.check⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原闭包树在扩张中的精确节点识别

旧节点的两坐标按原字母映射搬运。反向将整个有限单词连同内部长度拉回，
在原模型重建两坐标，并用复合唯一性识别目标坐标。因此扩张仍按同一节点
谓词读取原树；这不限制扩张中的无限枝来自原模型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include hM hN inj full
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)

theorem image_cl_tree_l {ω X T C K Y d h F A : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    (fd : M.IsSetFunctionFromTo I d Y X) (fh : M.IsSetFunctionFromTo I h Y ω)
    (tree : Tree_d F A) (nodes : ∀ p, M.mem p A ↔ Cl_word_d hM ω X T C K Y d h p) :
    Tree_d (j F) (j A) ∧ ∀ p, N.mem p (j A) ↔ Cl_word_d hN (j ω) (j X) (j T) (j C) (j K) (j Y) (j d) (j h) p := by
  refine ⟨image_tree_l j inj full tree,fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨s,hs,rfl⟩ := (full A p).mp hp
    obtain ⟨n,e,u,fs,de,hu,node⟩ := (nodes s).mp hs
    have fs := fn0_function_l (ZF.modelsKP hM) fs
    exact ⟨j n,j e,j u,fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full fs),
      image_fseq_recode_l hM hN j inj full fd fs de,image_fseq_recode_l hM hN j inj full fh fs hu,
      (image_cl_node_l (ZF.modelsKP hM) hN.1 j inj full).mp node⟩
  · rintro ⟨n,e,u,fp,de,hu,node⟩
    obtain ⟨k,s,_,fs,rfl,rfl⟩ := image_finite_function_pull_l hM hN j inj full hw hw' node.natural
      (fn0_function_l (ZF.modelsKP hN) fp)
    obtain ⟨g,_,dg⟩ := ZF.fseq_compose_l I hM fd fs
    obtain ⟨v,_,hv⟩ := ZF.fseq_compose_l I hM fh fs
    have eq := (image_fseq_recode_l hM hN j inj full fd fs dg).unique_l J hN.1 de
    subst e
    have eq := (image_fseq_recode_l hM hN j inj full fh fs hv).unique_l J hN.1 hu
    subst u
    exact (image_member_l j inj full).mpr ((nodes s).mpr ⟨k,g,v,fn0_of_function_l (ZF.modelsKP hM) fs,dg,hv,
      (image_cl_node_l (ZF.modelsKP hM) hN.1 j inj full).mpr node⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 见证树及其新枝的内部初等性

原选择图保持完整内部司寇伦性质，原有限树保持精确节点定义。因此目标中的
任意新枝可直接调用 `Sh_tree_d.elementary_l`，得到目标内部的可数初等子模型；
没有把新无限枝或其值域预先放回原模型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include hM hN inj full

theorem image_sh_tree_l {ω c X R u C L T E K Q D H Y d h F A : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    (tree : Sh_tree_d hM ω c X R u C L T E K Q D H Y d h F A) :
    Sh_tree_d hN (j ω) (j c) (j X) (j R) (j u) (j C) (j L) (j T) (j E) (j K)
      (j Q) (j D) (j H) (j Y) (j d) (j h) (j F) (j A) := by
  obtain ⟨tree',nodes⟩ := image_cl_tree_l hM hN j inj full hw hw' tree.left tree.right tree.tree tree.nodes
  refine ⟨image_smdl_l j inj full (ZF.modelsKP hM) (ZF.modelsKP hN) tree.model,
    image_ssk_l j inj full hM hN hw hw' tree.model tree.skolem,
    image_fseq_l hM hN j inj full hw hw' tree.positions,image_product_l j inj full tree.tasks,
    image_injection_l j inj full tree.index,image_product_l j inj full tree.letters,
    image_function_l j inj full tree.left,image_function_l j inj full tree.right,?_,
    image_fseq_l hM hN j inj full hw hw' tree.sequences,tree',nodes⟩
  intro v x l hv pair
  obtain ⟨v₀,hv₀,rfl⟩ := (full Y v).mp hv
  obtain ⟨x₀,l₀,pair₀,rfl,rfl⟩ := image_kpair_pull_l (ZF.modelsKP hM) hN.1 j inj full pair
  have edge := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have reads := tree.coordinates v₀ x₀ l₀ hv₀ pair₀
  exact ⟨(edge v₀ x₀ d).mp reads.1,(edge v₀ l₀ h).mp reads.2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原稠密任务树在扩张中的精确保持

旧条件域、稠密对象和关系条目按成员满性回拉，故局部稠密性判断双向保持。
整个有限单词再由内部有限列回拉识别；扩张可以有新无限枝，原任务检查仍有效。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models KP) (hN : Extensional N)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include hM hN inj full

private theorem gn_dense_image_l (Q T D : M.Domain) :
    Dense_set_d M Q T Q D ↔ Dense_set_d N (j Q) (j T) (j Q) (j D) := by
  have mem {a b : M.Domain} : N.mem (j a) (j b) ↔ M.mem a b := image_member_l j inj full
  have edge := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  have below p q : Below_d M Q T Q p q ↔ Below_d N (j Q) (j T) (j Q) (j p) (j q) :=
    and_congr mem.symm (and_congr (not_congr inj.eq_iff.symm) (edge p q T))
  constructor
  · intro dense
    constructor
    · intro p hp
      obtain ⟨p₀,hp₀,rfl⟩ := (full D p).mp hp
      exact ⟨mem.mpr (dense.1 p₀ hp₀).1,fun eq => (dense.1 p₀ hp₀).2 (inj eq)⟩
    · intro p hp nz
      obtain ⟨p₀,hp₀,rfl⟩ := (full Q p).mp hp
      obtain ⟨q,qp,qD⟩ := dense.2 p₀ hp₀ (fun eq => nz (congrArg j eq))
      exact ⟨j q,(below q p₀).mp qp,mem.mpr qD⟩
  · intro dense
    constructor
    · intro p hp
      have good := dense.1 (j p) (mem.mpr hp)
      exact ⟨mem.mp good.1,fun eq => good.2 (congrArg j eq)⟩
    · intro p hp nz
      obtain ⟨q,qp,qD⟩ := dense.2 (j p) (mem.mpr hp) (fun eq => nz (inj eq))
      obtain ⟨q₀,_,rfl⟩ := (full Q q).mp qp.1
      exact ⟨q₀,(below q₀ p).mpr qp,mem.mp qD⟩

theorem image_gn_node_l {ω X Q T n e f u : M.Domain} :
    Gn_node_d ω X Q T n e f u ↔ Gn_node_d (j ω) (j X) (j Q) (j T) (j n) (j e) (j f) (j u) := by
  have mem {a b : M.Domain} : N.mem (j a) (j b) ↔ M.mem a b := image_member_l j inj full
  have edge := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  have typed a b f : Fn0_d a b f ↔ Fn0_d (j a) (j b) (j f) := by
    let ρ : Env M 3 := ⟨fun i => [a,b,f].get i,fun _ => a⟩
    exact (fn0_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((delta0_image_l j inj full (fn0_delta_l ..) ρ).trans (fn0_sat_l hN _ _ _ _))
  constructor
  · intro node
    have fe := (typed n X e).mp node.enumeration
    have ff := (typed n Q f).mp node.conditions
    refine ⟨mem.mpr node.natural,fe,ff,(typed n ω u).mp node.witnesses,⟨?_,?_⟩⟩
    · intro i k p q hi hk succ ip kq
      obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
      obtain ⟨k₀,hk₀,rfl⟩ := (full n k).mp hk
      obtain ⟨p₀,_,rfl⟩ := (full Q p).mp (ff.bound_l ip).2
      obtain ⟨q₀,_,rfl⟩ := (full Q q).mp (ff.bound_l kq).2
      exact (edge q₀ p₀ T).mp (node.check.decreasing i₀ k₀ p₀ q₀ hi₀ hk₀
        ((image_successor_iff_l hM hN j inj full).mpr succ) ((edge i₀ p₀ f).mpr ip) ((edge k₀ q₀ f).mpr kq))
    · intro i k D p hi hk iD ik kp dense
      obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
      obtain ⟨k₀,hk₀,rfl⟩ := (full n k).mp hk
      obtain ⟨D₀,_,rfl⟩ := (full X D).mp (fe.bound_l iD).2
      obtain ⟨p₀,_,rfl⟩ := (full Q p).mp (ff.bound_l kp).2
      exact mem.mpr (node.check.hits i₀ k₀ D₀ p₀ hi₀ hk₀ ((edge i₀ D₀ e).mpr iD)
        ((edge i₀ k₀ u).mpr ik) ((edge k₀ p₀ f).mpr kp) ((gn_dense_image_l hM hN j inj full Q T D₀).mpr dense))
  · intro node
    refine ⟨mem.mp node.natural,(typed n X e).mpr node.enumeration,(typed n Q f).mpr node.conditions,
      (typed n ω u).mpr node.witnesses,⟨?_,?_⟩⟩
    · intro i k p q hi hk succ ip kq
      exact (edge q p T).mpr (node.check.decreasing (j i) (j k) (j p) (j q) (mem.mpr hi) (mem.mpr hk)
        ((image_successor_iff_l hM hN j inj full).mp succ) ((edge i p f).mp ip) ((edge k q f).mp kq))
    · intro i k D p hi hk iD ik kp dense
      exact mem.mp (node.check.hits (j i) (j k) (j D) (j p) (mem.mpr hi) (mem.mpr hk)
        ((edge i D e).mp iD) ((edge i k u).mp ik) ((edge k p f).mp kp)
        ((gn_dense_image_l hM hN j inj full Q T D).mp dense))

omit hM hN in
/-- 保持原树的全部节点定义，所以目标中的新枝仍可直接调用原调度解码。 -/
theorem image_gn_tree_l (hM : M.Models ZF) (hN : N.Models ZF)
    {ω X Q T Z Y d h l r F A : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    (tree : Gn_tree_d hM ω X Q T Z Y d h l r F A) :
    Gn_tree_d hN (j ω) (j X) (j Q) (j T) (j Z) (j Y) (j d) (j h) (j l) (j r) (j F) (j A) := by
  let I₀ := kp_pair_l (ZF.modelsKP hM)
  let J₀ := kp_pair_l (ZF.modelsKP hN)
  have edge := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have reads {Y d h : M.Domain}
      (read : ∀ v x b, M.mem v Y → KPair_d M v x b → Entry_d M v x d ∧ Entry_d M v b h) :
      ∀ v x b, N.mem v (j Y) → KPair_d N v x b → Entry_d N v x (j d) ∧ Entry_d N v b (j h) := by
    intro v x b hv pair
    obtain ⟨v₀,hv₀,rfl⟩ := (full Y v).mp hv
    obtain ⟨x₀,b₀,pair₀,rfl,rfl⟩ := image_kpair_pull_l (ZF.modelsKP hM) hN.1 j inj full pair
    exact ⟨(edge v₀ x₀ d).mp (read v₀ x₀ b₀ hv₀ pair₀).1,(edge v₀ b₀ h).mp (read v₀ x₀ b₀ hv₀ pair₀).2⟩
  refine ⟨image_product_l j inj full tree.inner,image_product_l j inj full tree.outer,
    image_function_l j inj full tree.left,image_function_l j inj full tree.right,
    image_function_l j inj full tree.condition,image_function_l j inj full tree.witness,reads tree.inner_read,reads tree.outer_read,
    image_fseq_l hM hN j inj full hw hw' tree.sequences,image_tree_l j inj full tree.tree,fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨p₀,hp₀,rfl⟩ := (full A p).mp hp
    obtain ⟨n,e,b,f,u,fp,de,hb,lf,ru,node⟩ := (tree.nodes p₀).mp hp₀
    have fp := fn0_function_l (ZF.modelsKP hM) fp
    have fb := hb.function_l I₀ hM tree.right fp
    exact ⟨j n,j e,j b,j f,j u,fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full fp),
      image_fseq_recode_l hM hN j inj full tree.left fp de,image_fseq_recode_l hM hN j inj full tree.right fp hb,
      image_fseq_recode_l hM hN j inj full tree.condition fb lf,image_fseq_recode_l hM hN j inj full tree.witness fb ru,
      (image_gn_node_l (ZF.modelsKP hM) hN.1 j inj full).mp node⟩
  · rintro ⟨n,e,b,f,u,fp,de,hb,lf,ru,node⟩
    obtain ⟨k,p₀,_,fp₀,rfl,rfl⟩ := image_finite_function_pull_l hM hN j inj full hw hw' node.natural
      (fn0_function_l (ZF.modelsKP hN) fp)
    obtain ⟨e₀,_,de₀⟩ := ZF.fseq_compose_l I₀ hM tree.left fp₀
    obtain ⟨b₀,fb₀,hb₀⟩ := ZF.fseq_compose_l I₀ hM tree.right fp₀
    have eq := (image_fseq_recode_l hM hN j inj full tree.left fp₀ de₀).unique_l J₀ hN.1 de
    subst e
    have eq := (image_fseq_recode_l hM hN j inj full tree.right fp₀ hb₀).unique_l J₀ hN.1 hb
    subst b
    obtain ⟨f₀,_,lf₀⟩ := ZF.fseq_compose_l I₀ hM tree.condition fb₀
    obtain ⟨u₀,_,ru₀⟩ := ZF.fseq_compose_l I₀ hM tree.witness fb₀
    have eq := (image_fseq_recode_l hM hN j inj full tree.condition fb₀ lf₀).unique_l J₀ hN.1 lf
    subst f
    have eq := (image_fseq_recode_l hM hN j inj full tree.witness fb₀ ru₀).unique_l J₀ hN.1 ru
    subst u
    exact (image_member_l j inj full).mpr ((tree.nodes p₀).mpr
      ⟨k,e₀,b₀,f₀,u₀,fn0_of_function_l (ZF.modelsKP hM) fp₀,de₀,hb₀,lf₀,ru₀,
        (image_gn_node_l (ZF.modelsKP hM) hN.1 j inj full).mpr node⟩)

end YesMetaZFC.Model.Forcing.Internal
