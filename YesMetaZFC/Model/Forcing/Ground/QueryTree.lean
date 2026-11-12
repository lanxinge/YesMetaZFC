import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.Forcing.Order.NameLetters
import YesMetaZFC.Model.Forcing.Order.JointParameters
import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.Model.Forcing.Order.NameContext
import YesMetaZFC.Model.Forcing.Order.QueryTree

/-! # 联合字母、坐标图形与登记检查的保持

旧图中的每条有序对条目连同两个坐标都能回拉；登记检查因而不要求原图
预先为全函数。实际字母和坐标复合图随后由同一成员满嵌入运输。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem image_rg_at_l (hM : M.Models KP) (hN : Extensional N) (j : M.Domain → N.Domain)
    (inj : Function.Injective j) (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    {n e f v : M.Domain} : Rg_at_d n e f v ↔ Rg_at_d (j n) (j e) (j f) (j v) := by
  have edge := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  constructor
  · intro check i k x hi hk ik ix
    obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
    obtain ⟨k₀,hk₀,rfl⟩ := (full n k).mp hk
    obtain ⟨p,pair,hp⟩ := ix
    obtain ⟨p₀,hp₀,rfl⟩ := (full f p).mp hp
    obtain ⟨i',x₀,pair₀,eq,rfl⟩ := image_kpair_pull_l hM hN j inj full pair
    have eq := inj eq
    subst i'
    exact (edge k₀ x₀ e).mp (check i₀ k₀ x₀ hi₀ hk₀ ((edge i₀ k₀ v).mpr ik) ⟨p₀,pair₀,hp₀⟩)
  · intro check i k x hi hk ik ix
    exact (edge k x e).mpr (check (j i) (j k) (j x) ((image_member_l j inj full).mpr hi)
      ((image_member_l j inj full).mpr hk) ((edge i k v).mp ik) ((edge i x f).mp ix))

variable (hM : M.Models ZF) (hN : N.Models ZF) (j : M.Domain → N.Domain)
  (inj : Function.Injective j) (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include hM hN inj full
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem image_jt_letters_l {ω X Y Z W A a b c d l r : M.Domain}
    (letters : Jt_letters_d hM ω X Y Z W A a b c d l r) :
    Jt_letters_d hN (j ω) (j X) (j Y) (j Z) (j W) (j A) (j a) (j b) (j c) (j d) (j l) (j r) := by
  have edge := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have reads {A d h : M.Domain}
      (read : ∀ v x b, M.mem v A → KPair_d M v x b → Rd_entry_d v x d ∧ Rd_entry_d v b h) :
      ∀ v x b, N.mem v (j A) → KPair_d N v x b → Rd_entry_d v x (j d) ∧ Rd_entry_d v b (j h) := by
    intro v x b hv pair
    obtain ⟨v₀,hv₀,rfl⟩ := (full A v).mp hv
    obtain ⟨x₀,b₀,pair₀,rfl,rfl⟩ := image_kpair_pull_l (ZF.modelsKP hM) hN.1 j inj full pair
    exact ⟨(edge v₀ x₀ d).mp (read v₀ x₀ b₀ hv₀ pair₀).1,(edge v₀ b₀ h).mp (read v₀ x₀ b₀ hv₀ pair₀).2⟩
  exact ⟨image_product_l j inj full letters.pair₁,image_product_l j inj full letters.pair₂,image_product_l j inj full letters.pair₃,
    image_function_l j inj full letters.a_fn,image_function_l j inj full letters.b_fn,image_function_l j inj full letters.c_fn,
    image_function_l j inj full letters.d_fn,image_function_l j inj full letters.l_fn,image_function_l j inj full letters.r_fn,
    reads letters.read₁,reads letters.read₂,reads letters.read₃⟩

theorem image_jt_cols_l {ω X Y Z W A a b c d l r n q t z s p v w : M.Domain}
    (letters : Jt_letters_d hM ω X Y Z W A a b c d l r) (fq : M.IsSetFunctionFromTo I q n A)
    (cols : Jt_cols_d hM a b c d l r q t z s p v w) :
    Jt_cols_d hN (j a) (j b) (j c) (j d) (j l) (j r) (j q) (j t) (j z) (j s) (j p) (j v) (j w) := by
  obtain ⟨ft,fz,_,_,_,_⟩ := cols.functions_l hM letters fq
  exact ⟨image_fseq_recode_l hM hN j inj full letters.a_fn fq cols.qt,
    image_fseq_recode_l hM hN j inj full letters.b_fn fq cols.qz,
    image_fseq_recode_l hM hN j inj full letters.c_fn ft cols.ts,
    image_fseq_recode_l hM hN j inj full letters.d_fn ft cols.tp,
    image_fseq_recode_l hM hN j inj full letters.l_fn fz cols.zv,
    image_fseq_recode_l hM hN j inj full letters.r_fn fz cols.zw⟩

theorem image_jt_params_l {ω X Q T C : M.Domain} (params : Jt_params_d ω X Q T C) :
    Jt_params_d (j ω) (j X) (j Q) (j T) (j C) := by
  have edge := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  obtain ⟨i,iQ⟩ := params.conditions
  obtain ⟨k,kT⟩ := params.order
  exact ⟨fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full (fn0_function_l (ZF.modelsKP hM) params.function)),
    ⟨j i,(edge i Q C).mp iQ⟩,⟨j k,(edge k T C).mp kT⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一联合有限树向强迫扩张保持

正向搬运全部坐标及登记。反向先回拉整个内部有限单词，再在源模型重建坐标；
两侧共享枚举由目标中的唯一性及嵌入单射性识别。因此目标读取的是原树的像，
不另造一棵只在扩张中存在的联合树。
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

theorem image_jt_tree_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    (tree : Jt_tree_d hM ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A) :
    Jt_tree_d hN (j ω) (j X) (j Q) (j C) (j Ys) (j Yg) (j Zg) (j Fs) (j As) (j Fg) (j Ag)
      (j ds) (j dg) (j hg) (j lg) (j Z) (j W) (j Y) (j a) (j b) (j c) (j d) (j l) (j r) (j F) (j A) := by
  refine ⟨image_jt_letters_l hM hN j inj full tree.letters,image_function_l j inj full tree.sh_enum,
    image_function_l j inj full tree.gn_enum,image_function_l j inj full tree.gn_pair,image_function_l j inj full tree.gn_cond,
    image_fseq_l hM hN j inj full hw hw' tree.sh_space,image_fseq_l hM hN j inj full hw hw' tree.gn_space,
    image_tree_l j inj full tree.sh_tree,image_tree_l j inj full tree.gn_tree,
    image_fseq_l hM hN j inj full hw hw' tree.sequences,image_tree_l j inj full tree.tree,fun q => ?_⟩
  constructor
  · intro hq
    obtain ⟨q₀,hq₀,rfl⟩ := (full A q).mp hq
    obtain ⟨n,t,z,s,p,v,w,e,g,f,hn,fq,cols,hs,hp,se,pe,pg,gf,reg,params⟩ := (tree.nodes q₀).mp hq₀
    have fq := fn0_function_l (ZF.modelsKP hM) fq
    obtain ⟨_,_,fs,fp,_,_⟩ := cols.functions_l hM tree.letters fq
    have fg := pg.function_l I hM tree.gn_pair fp
    exact ⟨j n,j t,j z,j s,j p,j v,j w,j e,j g,j f,(image_member_l j inj full).mpr hn,
      fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full fq),image_jt_cols_l hM hN j inj full tree.letters fq cols,
      (image_member_l j inj full).mpr hs,(image_member_l j inj full).mpr hp,
      image_fseq_recode_l hM hN j inj full tree.sh_enum fs se,image_fseq_recode_l hM hN j inj full tree.gn_enum fp pe,
      image_fseq_recode_l hM hN j inj full tree.gn_pair fp pg,image_fseq_recode_l hM hN j inj full tree.gn_cond fg gf,
      (image_rg_at_l (ZF.modelsKP hM) hN.1 j inj full).mp reg,(image_rg_at_l (ZF.modelsKP hM) hN.1 j inj full).mp params⟩
  · rintro ⟨n,t,z,s,p,v,w,e,g,f,hn,fq,cols,hs,hp,se,pe,pg,gf,reg,params⟩
    obtain ⟨k,q₀,hk,fq₀,rfl,rfl⟩ := image_finite_function_pull_l hM hN j inj full hw hw' hn
      (fn0_function_l (ZF.modelsKP hN) fq)
    obtain ⟨t₀,z₀,s₀,p₀,v₀,w₀,cols₀⟩ := tree.letters.columns_l hM fq₀
    obtain ⟨et,ez,es,ep,ev,ew⟩ := (image_jt_cols_l hM hN j inj full tree.letters fq₀ cols₀).unique_l hN cols
    subst t z s p v w
    obtain ⟨_,_,fs₀,fp₀,_,_⟩ := cols₀.functions_l hM tree.letters fq₀
    obtain ⟨e₀,_,se₀⟩ := ZF.fseq_compose_l I hM tree.sh_enum fs₀
    have eq := (image_fseq_recode_l hM hN j inj full tree.sh_enum fs₀ se₀).unique_l J hN.1 se
    subst e
    obtain ⟨e',_,pe₀⟩ := ZF.fseq_compose_l I hM tree.gn_enum fp₀
    have eq := inj ((image_fseq_recode_l hM hN j inj full tree.gn_enum fp₀ pe₀).unique_l J hN.1 pe)
    subst e'
    obtain ⟨g₀,fg₀,pg₀⟩ := ZF.fseq_compose_l I hM tree.gn_pair fp₀
    have eq := (image_fseq_recode_l hM hN j inj full tree.gn_pair fp₀ pg₀).unique_l J hN.1 pg
    subst g
    obtain ⟨f₀,_,gf₀⟩ := ZF.fseq_compose_l I hM tree.gn_cond fg₀
    have eq := (image_fseq_recode_l hM hN j inj full tree.gn_cond fg₀ gf₀).unique_l J hN.1 gf
    subst f
    exact (image_member_l j inj full).mpr ((tree.nodes q₀).mpr ⟨k,t₀,z₀,s₀,p₀,v₀,w₀,e₀,g₀,f₀,hk,
      fn0_of_function_l (ZF.modelsKP hM) fq₀,cols₀,(image_member_l j inj full).mp hs,(image_member_l j inj full).mp hp,
      se₀,pe₀,pg₀,gf₀,(image_rg_at_l (ZF.modelsKP hM) hN.1 j inj full).mpr reg,
      (image_rg_at_l (ZF.modelsKP hM) hN.1 j inj full).mpr params⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 查询字母及实际复合投影向同一扩张保持 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include hM hN inj full
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem image_nr_letters_l {ω A Z W H a b c d l r Y dx dh : M.Domain}
    (letters : Nr_letters_d hM ω A Z W H a b c d l r Y dx dh) :
    Nr_letters_d hN (j ω) (j A) (j Z) (j W) (j H) (j a) (j b) (j c) (j d) (j l) (j r) (j Y) (j dx) (j dh) := by
  refine ⟨image_jt_letters_l hM hN j inj full letters.auxiliary,image_product_l j inj full letters.product,
    image_function_l j inj full letters.query,image_function_l j inj full letters.witness,?_⟩
  intro q x h hq pair
  obtain ⟨q₀,hq₀,rfl⟩ := (full Y q).mp hq
  obtain ⟨x₀,h₀,pair₀,rfl,rfl⟩ := image_kpair_pull_l (ZF.modelsKP hM) hN.1 j inj full pair
  have edge := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  exact ⟨(edge q₀ x₀ dx).mp (letters.read q₀ x₀ h₀ hq₀ pair₀).1,(edge q₀ h₀ dh).mp (letters.read q₀ x₀ h₀ hq₀ pair₀).2⟩

theorem image_nr_cols_l {ω A Z W H a b c d l r Y dx dh n q x h t z s u v w : M.Domain}
    (letters : Nr_letters_d hM ω A Z W H a b c d l r Y dx dh) (fq : M.IsSetFunctionFromTo I q n Y)
    (cols : Nr_cols_d hM a b c d l r dx dh q x h t z s u v w) :
    Nr_cols_d hN (j a) (j b) (j c) (j d) (j l) (j r) (j dx) (j dh) (j q) (j x) (j h) (j t) (j z) (j s) (j u) (j v) (j w) := by
  have fh := cols.witness.function_l I hM letters.witness fq
  exact ⟨image_fseq_recode_l hM hN j inj full letters.query fq cols.query,
    image_fseq_recode_l hM hN j inj full letters.witness fq cols.witness,
    image_jt_cols_l hM hN j inj full letters.auxiliary fh cols.auxiliary⟩

theorem image_jt_projection_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A de df : M.Domain}
    (joint : Jt_tree_d hM ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A)
    (projection : Jt_projection_d hM a c d ds hg lg de df) :
    Jt_projection_d hN (j a) (j c) (j d) (j ds) (j hg) (j lg) (j de) (j df) := by
  obtain ⟨s,p,g,cs,se,dp,pg,gf⟩ := projection
  have fs := cs.function_l I hM joint.letters.c_fn joint.letters.a_fn
  have fp := dp.function_l I hM joint.letters.d_fn joint.letters.a_fn
  have fg := pg.function_l I hM joint.gn_pair fp
  exact ⟨j s,j p,j g,image_fseq_recode_l hM hN j inj full joint.letters.c_fn joint.letters.a_fn cs,
    image_fseq_recode_l hM hN j inj full joint.sh_enum fs se,
    image_fseq_recode_l hM hN j inj full joint.letters.d_fn joint.letters.a_fn dp,
    image_fseq_recode_l hM hN j inj full joint.gn_pair fp pg,image_fseq_recode_l hM hN j inj full joint.gn_cond fg gf⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原源名字判值及全部有限检查在成员满扩张中保持

原源的力迫公式已经相对化为有界公式。任意旧图中的条目都可回拉两个坐标，
所以有限检查的全称量词不会在扩张中产生额外未覆盖的旧图值。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include inj full

theorem image_nr_base_l {X Q T ω b τ p : M.Domain} :
    Nr_base_d X Q T ω b τ p ↔ Nr_base_d (j X) (j Q) (j T) (j ω) (j b) (j τ) (j p) := by
  let ρ : Env M 7 := ⟨fun i => [X,Q,T,ω,b,τ,p].get i,fun _ => X⟩
  let φ : Formula 1 7 := nr_base_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
  have tr : Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l j ρ) φ :=
    delta0_image_l j inj full (nr_base_delta_l ..) ρ
  exact tr.trans (nr_base_sat_l (image_env_l j ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6))

theorem image_nr_edge_l {X Q T b τ i y p : M.Domain} :
    Nr_edge_d X Q T b τ i y p ↔ Nr_edge_d (j X) (j Q) (j T) (j b) (j τ) (j i) (j y) (j p) := by
  let ρ : Env M 8 := ⟨fun k => [X,Q,T,b,τ,i,y,p].get k,fun _ => X⟩
  let φ : Formula 1 8 := nr_edge_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
  have tr : Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l j ρ) φ :=
    delta0_image_l j inj full (nr_edge_delta_l ..) ρ
  exact tr.trans (nr_edge_sat_l (image_env_l j ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7))

theorem image_nr_at_l (hM : M.Models KP) (hN : Extensional N) {ω X Q T n e f x u v w : M.Domain} :
    Nr_at_d ω X Q T n e f x u v w ↔ Nr_at_d (j ω) (j X) (j Q) (j T) (j n) (j e) (j f) (j x) (j u) (j v) (j w) := by
  have edge := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  have member {a b : M.Domain} : N.mem (j a) (j b) ↔ M.mem a b := image_member_l j inj full
  have value {F i : M.Domain} {y : N.Domain} (iy : Rd_entry_d (j i) y (j F)) : ∃ z, Rd_entry_d i z F ∧ j z = y := by
    obtain ⟨p,pair,hp⟩ := iy
    obtain ⟨p₀,hp₀,rfl⟩ := (full F p).mp hp
    obtain ⟨i₀,z,pair₀,eq,yz⟩ := image_kpair_pull_l hM hN j inj full pair
    exact ⟨z,inj eq ▸ (⟨p₀,pair₀,hp₀⟩ : Rd_entry_d i₀ z F),yz⟩
  have empty o : (∀ y, ¬ M.mem y o) ↔ ∀ y, ¬ N.mem y (j o) :=
    ⟨fun h y hy => ((full o y).mp hy).elim fun z hz => h z hz.1,
      fun h y hy => h (j y) (member.mpr hy)⟩
  constructor
  · intro check
    constructor
    · intro i k a b hi hk ia kb
      obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
      obtain ⟨k₀,hk₀,rfl⟩ := (full n k).mp hk
      obtain ⟨a₀,ia₀,rfl⟩ := value ia
      obtain ⟨b₀,kb₀,rfl⟩ := value kb
      exact congrArg j (check.base_index i₀ k₀ a₀ b₀ hi₀ hk₀ ia₀ kb₀)
    · intro i k a b hi hk ia kb
      obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
      obtain ⟨k₀,hk₀,rfl⟩ := (full n k).mp hk
      obtain ⟨a₀,ia₀,rfl⟩ := value ia
      obtain ⟨b₀,kb₀,rfl⟩ := value kb
      exact congrArg j (check.name_index i₀ k₀ a₀ b₀ hi₀ hk₀ ia₀ kb₀)
    · intro o a b p h τ ho ha hb hz oa ob ah bτ op
      obtain ⟨o₀,ho₀,rfl⟩ := (full n o).mp ho
      obtain ⟨a₀,ha₀,rfl⟩ := (full n a).mp ha
      obtain ⟨b₀,hb₀,rfl⟩ := (full n b).mp hb
      obtain ⟨p₀,op₀,rfl⟩ := value op
      obtain ⟨h₀,ah₀,rfl⟩ := value ah
      obtain ⟨τ₀,bτ₀,rfl⟩ := value bτ
      obtain ⟨hQ,ph,base⟩ := check.root o₀ a₀ b₀ p₀ h₀ τ₀ ho₀ ha₀ hb₀ ((empty o₀).mpr hz)
        ((edge o₀ a₀ v).mpr oa) ((edge o₀ b₀ w).mpr ob) ah₀ bτ₀ op₀
      exact ⟨member.mpr hQ,(edge p₀ h₀ T).mp ph,(image_nr_base_l j inj full).mp base⟩
    · intro i k a b y p h τ hi hk ha hb iy ik kp ia ib ah bτ
      obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
      obtain ⟨k₀,hk₀,rfl⟩ := (full n k).mp hk
      obtain ⟨a₀,ha₀,rfl⟩ := (full n a).mp ha
      obtain ⟨b₀,hb₀,rfl⟩ := (full n b).mp hb
      obtain ⟨y₀,iy₀,rfl⟩ := value iy
      obtain ⟨p₀,kp₀,rfl⟩ := value kp
      obtain ⟨h₀,ah₀,rfl⟩ := value ah
      obtain ⟨τ₀,bτ₀,rfl⟩ := value bτ
      exact (image_nr_edge_l j inj full).mp (check.digits i₀ k₀ a₀ b₀ y₀ p₀ h₀ τ₀ hi₀ hk₀ ha₀ hb₀ iy₀
        ((edge i₀ k₀ u).mpr ik) kp₀ ((edge i₀ a₀ v).mpr ia) ((edge i₀ b₀ w).mpr ib) ah₀ bτ₀)
  · intro check
    refine ⟨fun i k a b hi hk ia kb => inj (check.base_index (j i) (j k) (j a) (j b)
      (member.mpr hi) (member.mpr hk) ((edge i a v).mp ia) ((edge k b v).mp kb)),
      fun i k a b hi hk ia kb => inj (check.name_index (j i) (j k) (j a) (j b)
        (member.mpr hi) (member.mpr hk) ((edge i a w).mp ia) ((edge k b w).mp kb)),?_,?_⟩
    · intro o a b p h τ ho ha hb hz oa ob ah bτ op
      obtain ⟨hQ,ph,base⟩ := check.root (j o) (j a) (j b) (j p) (j h) (j τ)
        (member.mpr ho) (member.mpr ha) (member.mpr hb) ((empty o).mp hz)
        ((edge o a v).mp oa) ((edge o b w).mp ob) ((edge a h e).mp ah) ((edge b τ e).mp bτ) ((edge o p f).mp op)
      exact ⟨member.mp hQ,(edge p h T).mpr ph,(image_nr_base_l j inj full).mpr base⟩
    · intro i k a b y p h τ hi hk ha hb iy ik kp ia ib ah bτ
      exact (image_nr_edge_l j inj full).mpr (check.digits (j i) (j k) (j a) (j b) (j y) (j p) (j h) (j τ)
        (member.mpr hi) (member.mpr hk) (member.mpr ha) (member.mpr hb)
        ((edge i y x).mp iy) ((edge i k u).mp ik) ((edge k p f).mp kp)
        ((edge i a v).mp ia) ((edge i b w).mp ib) ((edge a h e).mp ah) ((edge b τ e).mp bτ))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原名字树及其联合坐标在强迫扩张中保持

反向先回拉整个旧字母表上的内部有限节点，坐标唯一性再识别全部名字检查。
保存的真实复合图继续作用于扩张中的新无限列，故保持原树而非重选解释树。
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

theorem image_nr_tree_l {ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    (tree : Nr_tree_d hM ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S) :
    Nr_tree_d hN (j ω) (j X) (j Q) (j T) (j A) (j F₀) (j A₀) (j de) (j df) (j Z) (j W) (j H)
      (j a) (j b) (j c) (j d) (j l) (j r) (j Y) (j dx) (j dh) (j F) (j S) := by
  refine ⟨image_nr_letters_l hM hN j inj full tree.letters,image_function_l j inj full tree.enumeration,
    image_function_l j inj full tree.conditions,image_fseq_l hM hN j inj full hw hw' tree.base_space,
    image_tree_l j inj full tree.base_tree,image_fseq_l hM hN j inj full hw hw' tree.sequences,
    image_tree_l j inj full tree.tree,fun q => ?_⟩
  constructor
  · intro hq
    obtain ⟨q₀,hq₀,rfl⟩ := (full S q).mp hq
    obtain ⟨n,x,h,t,z,s,u,v,w,e,f,hn,fq,cols,hs,se,sf,run⟩ := (tree.nodes q₀).mp hq₀
    have fq := fn0_function_l (ZF.modelsKP hM) fq
    obtain ⟨_,_,fs,_,_,_⟩ := cols.functions_l hM tree.letters fq
    exact ⟨j n,j x,j h,j t,j z,j s,j u,j v,j w,j e,j f,(image_member_l j inj full).mpr hn,
      fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full fq),image_nr_cols_l hM hN j inj full tree.letters fq cols,
      (image_member_l j inj full).mpr hs,image_fseq_recode_l hM hN j inj full tree.enumeration fs se,
      image_fseq_recode_l hM hN j inj full tree.conditions fs sf,(image_nr_at_l j inj full (ZF.modelsKP hM) hN.1).mp run⟩
  · rintro ⟨n,x,h,t,z,s,u,v,w,e,f,hn,fq,cols,hs,se,sf,run⟩
    obtain ⟨m,q₀,hm,fq₀,rfl,rfl⟩ := image_finite_function_pull_l hM hN j inj full hw hw' hn (fn0_function_l (ZF.modelsKP hN) fq)
    obtain ⟨x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,cols₀⟩ := tree.letters.columns_l hM fq₀
    obtain ⟨ex,eh,et,ez,es,eu,ev,ew⟩ := (image_nr_cols_l hM hN j inj full tree.letters fq₀ cols₀).unique_l hN cols
    subst x h t z s u v w
    obtain ⟨_,_,fs₀,_,_,_⟩ := cols₀.functions_l hM tree.letters fq₀
    obtain ⟨e₀,_,se₀⟩ := ZF.fseq_compose_l I hM tree.enumeration fs₀
    have ee := (image_fseq_recode_l hM hN j inj full tree.enumeration fs₀ se₀).unique_l J hN.1 se
    subst e
    obtain ⟨f₀,_,sf₀⟩ := ZF.fseq_compose_l I hM tree.conditions fs₀
    have ef := (image_fseq_recode_l hM hN j inj full tree.conditions fs₀ sf₀).unique_l J hN.1 sf
    subst f
    exact (image_member_l j inj full).mpr ((tree.nodes q₀).mpr ⟨m,x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,e₀,f₀,hm,
      fn0_of_function_l (ZF.modelsKP hM) fq₀,cols₀,(image_member_l j inj full).mp hs,se₀,sf₀,
      (image_nr_at_l j inj full (ZF.modelsKP hM) hN.1).mpr run⟩)

theorem image_nr_link_l {ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A
    T de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    (joint : Jt_tree_d hM ω X Q C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c d l r F A)
    (link : Nr_link_d hM joint T de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An) :
    Nr_link_d hN (image_jt_tree_l hM hN j inj full hw hw' joint) (j T) (j de) (j df) (j Zn) (j Wn) (j Hn)
      (j an) (j bn) (j cn) (j dn) (j ln) (j rn) (j Yn) (j dx) (j dh) (j Fn) (j An) :=
  ⟨image_nr_tree_l hM hN j inj full hw hw' link.tree,image_jt_projection_l hM hN j inj full joint link.projections⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 固定源的正负根检查在成员满扩张中保持 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include inj full

theorem image_qs_check_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool} {X Q T σ ω a b τ p : M.Domain} :
    Qs_check_d φ sign X Q T σ ω a b τ p ↔ Qs_check_d φ sign (j X) (j Q) (j T) (j σ) (j ω) (j a) (j b) (j τ) (j p) := by
  let ρ : Env M 9 := ⟨fun i => [X,Q,T,σ,ω,a,b,τ,p].get i,fun _ => X⟩
  let ψ : Formula 1 9 := qs_check_m φ sign (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)
  have tr : Formula.satisfies ρ ψ ↔ Formula.satisfies (image_env_l j ρ) ψ := delta0_image_l j inj full (qs_check_delta_l ..) ρ
  exact tr.trans (qs_check_sat_l hc sign (image_env_l j ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8))

theorem image_qs_at_l (hM : M.Models KP) (hN : Extensional N) {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {X Q T σ ω a n e f v w : M.Domain} :
    Qs_at_d φ sign X Q T σ ω a n e f v w ↔
      Qs_at_d φ sign (j X) (j Q) (j T) (j σ) (j ω) (j a) (j n) (j e) (j f) (j v) (j w) := by
  have edge := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  have member {a b : M.Domain} : N.mem (j a) (j b) ↔ M.mem a b := image_member_l j inj full
  have value {F i : M.Domain} {y : N.Domain} (iy : Rd_entry_d (j i) y (j F)) : ∃ z, Rd_entry_d i z F ∧ j z = y := by
    obtain ⟨p,pair,hp⟩ := iy
    obtain ⟨p₀,hp₀,rfl⟩ := (full F p).mp hp
    obtain ⟨i₀,z,pair₀,eq,yz⟩ := image_kpair_pull_l hM hN j inj full pair
    exact ⟨z,inj eq ▸ (⟨p₀,pair₀,hp₀⟩ : Rd_entry_d i₀ z F),yz⟩
  have empty o : (∀ y, ¬ M.mem y o) ↔ ∀ y, ¬ N.mem y (j o) :=
    ⟨fun h y hy => ((full o y).mp hy).elim fun z hz => h z hz.1,
      fun h y hy => h (j y) (member.mpr hy)⟩
  constructor
  · intro check o i k p b τ ho hi hk hz oi ok ib kτ op
    obtain ⟨o₀,ho₀,rfl⟩ := (full n o).mp ho
    obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
    obtain ⟨k₀,hk₀,rfl⟩ := (full n k).mp hk
    obtain ⟨p₀,op₀,rfl⟩ := value op
    obtain ⟨b₀,ib₀,rfl⟩ := value ib
    obtain ⟨τ₀,kτ₀,rfl⟩ := value kτ
    exact (image_qs_check_l j inj full hc).mp (check o₀ i₀ k₀ p₀ b₀ τ₀ ho₀ hi₀ hk₀ ((empty o₀).mpr hz)
      ((edge o₀ i₀ v).mpr oi) ((edge o₀ k₀ w).mpr ok) ib₀ kτ₀ op₀)
  · intro check o i k p b τ ho hi hk hz oi ok ib kτ op
    exact (image_qs_check_l j inj full hc).mpr (check (j o) (j i) (j k) (j p) (j b) (j τ)
      (member.mpr ho) (member.mpr hi) (member.mpr hk) ((empty o).mp hz)
      ((edge o i v).mp oi) ((edge o k w).mp ok) ((edge i b e).mp ib) ((edge k τ e).mp kτ) ((edge o p f).mp op))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原正负子树在强迫扩张中仍是同一节点集合

反向先从原名字树的旧节点取得全部坐标，再由投影唯一性识别目标坐标。
正负检查是固定源上的有界断言，故无需在目标另造一棵见证树。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN inj full

theorem image_qs_tree_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S σ a₀ S' : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω))
    {base : Nr_tree_d hM ω X Q T A F₀ A₀ de df Z W H a b c d l r Y dx dh F S}
    (tree : Qs_tree_d hM φ sign base σ a₀ S') :
    Qs_tree_d hN φ sign (image_nr_tree_l hM hN j inj full hw hw' base) (j σ) (j a₀) (j S') := by
  refine ⟨image_tree_l j inj full tree.tree,fun q => ?_⟩
  constructor
  · intro hq
    obtain ⟨q₀,hq₀,rfl⟩ := (full S' q).mp hq
    obtain ⟨old,n,x,h,t,z,s,u,v,w,e,f,hn,fq,cols,se,sf,check⟩ := (tree.nodes q₀).mp hq₀
    have fq := fn0_function_l (ZF.modelsKP hM) fq
    obtain ⟨_,_,fs,_,_,_⟩ := cols.functions_l hM base.letters fq
    exact ⟨(image_member_l j inj full).mpr old,j n,j x,j h,j t,j z,j s,j u,j v,j w,j e,j f,
      (image_member_l j inj full).mpr hn,fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full fq),
      image_nr_cols_l hM hN j inj full base.letters fq cols,image_fseq_recode_l hM hN j inj full base.enumeration fs se,
      image_fseq_recode_l hM hN j inj full base.conditions fs sf,(image_qs_at_l j inj full (ZF.modelsKP hM) hN.1 hc).mp check⟩
  · rintro ⟨old,n,x,h,t,z,s,u,v,w,e,f,_,fq,cols,se,sf,check⟩
    obtain ⟨q₀,hq₀,rfl⟩ := (full S q).mp old
    obtain ⟨m,x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,e₀,f₀,hm,fq₀,cols₀,_,se₀,sf₀,_⟩ := (base.nodes q₀).mp hq₀
    have fq₀ := fn0_function_l (ZF.modelsKP hM) fq₀
    have eqn := fq.domain_eq_l hN.1 (fn0_of_function_l (ZF.modelsKP hN) (image_function_l j inj full fq₀))
    subst n
    obtain ⟨ex,eh,et,ez,es,eu,ev,ew⟩ := (image_nr_cols_l hM hN j inj full base.letters fq₀ cols₀).unique_l hN cols
    subst x h t z s u v w
    obtain ⟨_,_,fs₀,_,_,_⟩ := cols₀.functions_l hM base.letters fq₀
    have ee := (image_fseq_recode_l hM hN j inj full base.enumeration fs₀ se₀).unique_l J hN.1 se
    subst e
    have ef := (image_fseq_recode_l hM hN j inj full base.conditions fs₀ sf₀).unique_l J hN.1 sf
    subst f
    exact (image_member_l j inj full).mpr ((tree.nodes q₀).mpr ⟨hq₀,m,x₀,h₀,t₀,z₀,s₀,u₀,v₀,w₀,e₀,f₀,hm,
      fn0_of_function_l (ZF.modelsKP hM) fq₀,cols₀,se₀,sf₀,(image_qs_at_l j inj full (ZF.modelsKP hM) hN.1 hc).mpr check⟩)

end YesMetaZFC.Model.Forcing.Internal
