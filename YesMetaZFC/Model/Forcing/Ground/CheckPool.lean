import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.Forcing.Names.CheckPools
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 成员满嵌入反射有序对、后继和条件序

旧有序对的两个坐标仍来自旧模型：先从其第二个无序对成员拉回两个值。
后继反射比较旧后继的规范像，因此不需要外部良基性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models KP) (hN : Extensional N)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
include hM hN inj full

theorem image_kpair_pull_l {p : M.Domain} {x y : N.Domain} (pair : KPair_d N (j p) x y) :
    ∃ a b, KPair_d M p a b ∧ j a = x ∧ j b = y := by
  have saved := pair
  obtain ⟨_,t,_,tp,pt⟩ := saved
  obtain ⟨t₀,_,eq⟩ := (full p t).mp ((pt t).mpr (Or.inr rfl))
  obtain ⟨a,_,ax⟩ := (full t₀ x).mp (eq.symm ▸ (tp x).mpr (Or.inl rfl))
  obtain ⟨b,_,by'⟩ := (full t₀ y).mp (eq.symm ▸ (tp y).mpr (Or.inr rfl))
  obtain ⟨q,qp⟩ := (kpair_interpretation_l M hM.1 (KP.exists_pair hM)).total a b
  have eq := inj (kpair_unique_l N hN (ax ▸ by' ▸ image_kpair_l j full qp) pair)
  exact ⟨a,b,eq ▸ qp,ax,by'⟩

theorem image_kpair_iff_l {p a b : M.Domain} :
    KPair_d M p a b ↔ KPair_d N (j p) (j a) (j b) := by
  refine ⟨image_kpair_l j full,fun pair => ?_⟩
  obtain ⟨x,y,xy,xa,yb⟩ := image_kpair_pull_l hM hN j inj full pair
  exact inj xa ▸ inj yb ▸ xy

/-- 原集合的关系条目必有原坐标；集合本身不必预先证明为关系。 -/
theorem image_entry_pull_l {F : M.Domain} {a b : N.Domain} (edge : Entry_d N a b (j F)) :
    ∃ x y, Entry_d M x y F ∧ j x = a ∧ j y = b := by
  obtain ⟨p,pair,hp⟩ := edge
  obtain ⟨q,hq,rfl⟩ := (full F p).mp hp
  obtain ⟨x,y,pair₀,ex,ey⟩ := image_kpair_pull_l hM hN j inj full pair
  exact ⟨x,y,⟨q,pair₀,hq⟩,ex,ey⟩

theorem image_successor_iff_l {a b : M.Domain} : M.SuccessorOf a b ↔ N.SuccessorOf (j a) (j b) := by
  refine ⟨image_successor_l (hEN := hN) j inj full hM.1,fun h => ?_⟩
  obtain ⟨c,succ⟩ := KP.exists_successor hM b
  have eq := inj ((image_successor_l (hEN := hN) j inj full hM.1 succ).eq hN h)
  exact eq ▸ succ

theorem image_cond_order_l {B R z : M.Domain} (O : Cond_order_d M B R z) :
    Cond_order_d N (j B) (j R) (j z) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair hM) hN
  constructor
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := (full B p).mp hp
    exact (entry a a R).mp (O.refl a ha)
  · intro p q r hp hq hr pq qr
    obtain ⟨a,ha,rfl⟩ := (full B p).mp hp
    obtain ⟨b,hb,rfl⟩ := (full B q).mp hq
    obtain ⟨c,hc,rfl⟩ := (full B r).mp hr
    exact (entry a c R).mp (O.trans a b c ha hb hc ((entry a b R).mpr pq) ((entry b c R).mpr qr))
  · intro p hp pz
    obtain ⟨a,ha,rfl⟩ := (full B p).mp hp
    exact congrArg j (O.zero a ha ((entry a z R).mpr pz))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范检查名字在成员满嵌入下的双向绝对性

正向直接搬运原集合递归图；反向比较源中实际构造的检查名字与目标
检查名字的唯一性。无需完整初等性，也不使用外部良基归纳。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
  (e : M.Domain → N.Domain) (inj : Function.Injective e)
  (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include inj full

theorem image_check_l (hM : M.Models KP) (hN : Extensional N) {b x t : M.Domain}
    (check : Check_d M b x t) : Check_d N (e b) (e x) (e t) := by
  obtain ⟨F,graph,xt⟩ := check
  have edge := image_entry_iff_l e inj full (KP.exists_pair hM) hN
  refine ⟨e F,⟨?_,?_⟩,(edge x t F).mp xt⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := (full F p).mp hp
    obtain ⟨a,s,pair⟩ := graph.1 q hq
    exact ⟨e a,e s,image_kpair_l e full pair⟩
  · intro x t xt
    obtain ⟨a,s,as,rfl,rfl⟩ := (image_entries_l e full graph.1 x t).mp xt
    obtain ⟨children,members⟩ := graph.2 a s as
    refine ⟨?_,fun p => ⟨?_,?_⟩⟩
    · intro y hy
      obtain ⟨c,hc,rfl⟩ := (full a y).mp hy
      obtain ⟨r,cr⟩ := children c hc
      exact ⟨e r,(edge c r F).mp cr⟩
    · intro hp
      obtain ⟨q,hq,rfl⟩ := (full s p).mp hp
      obtain ⟨c,r,hc,cr,pair⟩ := (members q).mp hq
      exact ⟨e c,e r,(image_member_l e inj full).mpr hc,(edge c r F).mp cr,image_kpair_l e full pair⟩
    · rintro ⟨y,r,hy,yr,pair⟩
      obtain ⟨c,hc,rfl⟩ := (full a y).mp hy
      obtain ⟨c',r₀,cr,eq,rfl⟩ := (image_entries_l e full graph.1 (e c) r).mp yr
      have eqc := inj eq
      subst c'
      obtain ⟨q,pair₀⟩ := (kpair_interpretation_l M hM.1 (KP.exists_pair hM)).total r₀ b
      exact (full s p).mpr ⟨q,(members q).mpr ⟨c,r₀,hc,cr,pair₀⟩,
        kpair_unique_l N hN (image_kpair_l e full pair₀) pair⟩

theorem image_check_iff_l (hM : M.Models ZF) (hN : N.Models ZF) (b x t : M.Domain) :
    Check_d M b x t ↔ Check_d N (e b) (e x) (e t) := by
  refine ⟨image_check_l e inj full (ZF.modelsKP hM) hN.1,fun check => ?_⟩
  obtain ⟨s,cs⟩ := check_exists_l M hM.1 (check_ind_l M hM) (check_ops_l M hM) b x
  have eq := inj (check_unique_l N hN.1 (check_ind_l N hN) (e b) (e x) (e s) (e t)
    (image_check_l e inj full (ZF.modelsKP hM) hN.1 cs) check)
  exact eq ▸ cs

end YesMetaZFC.Model.Forcing.Internal

/-! ## 大泛型沿成员满地包含回读为原泛型

原稠密集的每个条件及加强均仍在原条件域的像中，故直接回拉实际
滤子即可满足全部原稠密要求。无需原模型与背景具有相同幂集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem Generic_d.ground_pull_l (hM : M.Models KP) (hN : Extensional N)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z : M.Domain} {H : N.Domain → Prop}
    (generic : Generic_d N (e B) (e R) (e z) H) :
    Generic_d M B R z (H ∘ e) := by
  have edge := image_entry_iff_l e inj full (KP.exists_pair hM) hN
  have below a c : Below_d M B R z a c ↔ Below_d N (e B) (e R) (e z) (e a) (e c) :=
    and_congr (image_member_l e inj full).symm (and_congr (not_congr inj.eq_iff.symm) (edge a c R))
  refine ⟨fun p hp => ⟨(image_member_l e inj full).mp (generic.proper (e p) hp).1,
    fun eq => (generic.proper (e p) hp).2 (congrArg e eq)⟩,?_,?_,?_,?_⟩
  · obtain ⟨p,hp⟩ := generic.inhabited
    obtain ⟨q,_,rfl⟩ := (full B p).mp (generic.proper p hp).1
    exact ⟨q,hp⟩
  · intro p q hp hq pq
    exact generic.upward (e p) (e q) hp ((image_member_l e inj full).mpr hq) ((edge p q R).mp pq)
  · intro p q hp hq
    obtain ⟨r,hr,rp,rq⟩ := generic.directed (e p) (e q) hp hq
    obtain ⟨s,_,rfl⟩ := (full B r).mp (generic.proper r hr).1
    exact ⟨s,hr,(edge s p R).mpr rp,(edge s q R).mpr rq⟩
  · intro p hp D dense
    have dense' : Dense_d N (e B) (e R) (e z) (fun q => N.mem q (e D)) (e p) := by
      intro q hq
      obtain ⟨q₀,_,rfl⟩ := (full B q).mp hq.1
      obtain ⟨r,hr,rd⟩ := dense q₀ ((below q₀ p).mpr hq)
      exact ⟨e r,(below r q₀).mp hr,(image_member_l e inj full).mpr rd⟩
    obtain ⟨q,hq,qd⟩ := generic.meets (e p) hp (e D) dense'
    obtain ⟨r,_,rfl⟩ := (full B q).mp (generic.proper q hq).1
    exact ⟨r,hq,(image_member_l e inj full).mp qd⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 保持地参数的中间同构运输同一个第二步滤子

在目标中使用规范检查名字嵌入。中间同构与两个规范嵌入交换，
所以第二步泛型仍是原滤子的规范像，提升的同构仍保持原地模型参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}} (hM : M.Models ZF)
variable {B R z C S w P T v b : M.Domain} {H G K : M.Domain → Prop}
local notation "E" => extension_l M hM B R z H
local notation "D" => extension_l M hM C S w G

theorem Miso_over_d.check_step_l (O : Cond_order_d M B R z) (L : Cond_order_d M C S w)
    (U : Cond_order_d M P T v) (small : Generic_d M B R z H) (generic : Generic_d M C S w G)
    (iso : Miso_over_d E D (Gval_d M B R z H) (Gval_d M C S w G)) (hb : H b)
    (j : M.Domain → (E).Domain) (ji : Function.Injective j)
    (jf : ∀ a y, (E).mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    (checks : ∀ a t, Check_d M b a t → Qval_d M B R z H t (j a))
    (big : Generic_d E (j P) (j T) (j v) (Em_generic_d j K)) :
    ∃ c, G c ∧ ∃ k : M.Domain → (D).Domain, Function.Injective k ∧
      (∀ a y, (D).mem y (k a) ↔ ∃ x, M.mem x a ∧ k x = y) ∧
      (∀ a t, Check_d M c a t → Qval_d M C S w G t (k a)) ∧
      Generic_d D (k P) (k T) (k v) (Em_generic_d k K) ∧
      Miso_over_d (extension_l E (preserves_zf_l O hM small) (j P) (j T) (j v) (Em_generic_d j K))
        (extension_l D (preserves_zf_l L hM generic) (k P) (k T) (k v) (Em_generic_d k K))
        (fun a => Gval_d E (j P) (j T) (j v) (Em_generic_d j K) (j a))
        (fun a => Gval_d D (k P) (k T) (k v) (Em_generic_d k K) (k a)) := by
  obtain ⟨c,hc⟩ := generic.inhabited
  obtain ⟨k,kc,kf,ki⟩ := check_map_l L hM generic hc
  obtain ⟨f,fm,fi,fs,over⟩ := iso
  have square : Miso_over_d E D (fun x y => j x = y) (fun x y => k x = y) :=
    ⟨f,fm,fi,fs,fun x y => (gval_check_map_l O hM small hb j checks x y).symm.trans
      ((over x y).trans (gval_check_map_l L hM generic hc k kc x (f y)))⟩
  have hE := preserves_zf_l O hM small
  have hD := preserves_zf_l L hM generic
  have ord := image_cond_order_l (ZF.modelsKP hM) hE.1 j ji jf U
  exact ⟨c,hc,k,ki,kf,kc,square.iterate_l hE hD ord big⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原秩层的检查子集名字库覆盖全部背景名字

检查名字的绝对性识别每个直接子名字。任意背景候选名字的成员均落在
原名字库之并中，秩层的实际子集闭包因此把整个名字收回原模型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem image_ck_bound_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y) {B b D t : M.Domain} :
    Ck_bound_d B b D t ↔ Ck_bound_d (e B) (e b) (e D) (e t) := by
  constructor
  · intro bound v hv
    obtain ⟨q,hq,rfl⟩ := (full t v).mp hv
    obtain ⟨s,p,d,pair,hp,hd,check⟩ := bound q hq
    exact ⟨e s,e p,e d,image_kpair_l e full pair,(image_member_l e inj full).mpr hp,
      (image_member_l e inj full).mpr hd,image_check_l e inj full (ZF.modelsKP hM) hN.1 check⟩
  · intro bound v hv
    obtain ⟨s,p,d,pair,hp,hd,check⟩ := bound (e v) ((image_member_l e inj full).mpr hv)
    obtain ⟨s₀,p₀,pair₀,es,ep⟩ := image_kpair_pull_l (ZF.modelsKP hM) hN.1 e inj full pair
    obtain ⟨d₀,hd₀,rfl⟩ := (full D d).mp hd
    exact ⟨s₀,p₀,d₀,pair₀,(image_member_l e inj full).mp (ep.symm ▸ hp),hd₀,
      (image_check_iff_l e inj full hM hN b d₀ s₀).mpr (es.symm ▸ check)⟩

theorem Smem_d.check_pool_l (hZF : M.Models ZF) {c X R θ : M.Domain}
    (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (trans : M.TransitiveSet X)
    (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) θ X)
    (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Models ZF)
    {B b D W : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Domain}
    (pool : Ck_pool_d B b D W) : Ck_pool_d B.val b.val D.val W.val := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let L := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have member {a d : L.Domain} : M.mem a.val d.val ↔ L.mem a d := image_member_l (M := L) (N := M) Subtype.val inj full
  obtain ⟨Z,union⟩ := KP.exists_union (ZF.modelsKP native) W
  intro t
  constructor
  · intro ht
    obtain ⟨s,hs,rfl⟩ := (full W t).mp ht
    exact (image_ck_bound_l native hZF Subtype.val inj full).mp ((pool s).mp hs)
  · intro bound
    have sub : M.MemberSubset t Z.val := by
      intro v hv
      obtain ⟨s,p,d,pair,hp,hd,check⟩ := bound v hv
      obtain ⟨p₀,hp₀,rfl⟩ := (full B p).mp hp
      obtain ⟨d₀,hd₀,rfl⟩ := (full D d).mp hd
      obtain ⟨s₀,cs⟩ := check_exists_l L native.1 (check_ind_l L native) (check_ops_l L native) b d₀
      have es : s₀.val = s := check_unique_l M hZF.1 (check_ind_l M hZF) b.val d₀.val s₀.val s
        (image_check_l Subtype.val inj full (ZF.modelsKP native) hZF.1 cs) check
      obtain ⟨q,pair₀⟩ := (kp_pair_l (ZF.modelsKP native)).total s₀ p₀
      have eqv : q.val = v := kpair_unique_l M hZF.1 (es ▸ image_kpair_l Subtype.val full pair₀) pair
      obtain ⟨r,single⟩ := KP.exists_singleton (ZF.modelsKP native) q
      have small : Ck_bound_d B b D r := by
        intro y hy
        have eqy := (single y).mp hy
        subst y
        exact ⟨s₀,p₀,d₀,pair₀,hp₀,hd₀,cs⟩
      exact eqv ▸ member.mpr ((union q).mpr ⟨r,(pool r).mpr small,(single q).mpr rfl⟩)
    let t₀ : L.Domain := ⟨t,v_subset_mem_l I rank Z.property sub⟩
    exact member.mpr ((pool t₀).mpr ((image_ck_bound_l native hZF Subtype.val inj full).mpr bound))

end YesMetaZFC.Model.Forcing.Internal
