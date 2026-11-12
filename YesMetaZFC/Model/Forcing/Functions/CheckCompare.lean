import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Extension.Choice

/-! # 检查子集名字的逐成员求值

直接子名字都是检查名字，因此同一滤子在成员满地模型中的限制已经
确定整个值。这里不调用名字力迫关系的初等性或外部良基归纳。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem Ck_bound_d.value_l (hZF : M.Models ZF) {B R z b D τ : M.Domain}
    (bound : Ck_bound_d B b D τ) (O : Cond_order_d M B R z)
    {G : M.Domain → Prop} (g : Generic_d M B R z G)
    (j : M.Domain → (extension_l M hZF B R z G).Domain)
    (checks : ∀ d s, Check_d M b d s → Qval_d M B R z G s (j d))
    {y : (extension_l M hZF B R z G).Domain} (value : Qval_d M B R z G τ y)
    (x : (extension_l M hZF B R z G).Domain) :
    x ∈ y ↔ ∃ d s p, M.mem d D ∧ Check_d M b d s ∧ Entry_d M s p τ ∧ G p ∧ j d = x := by
  constructor
  · intro hx
    obtain ⟨s,p,⟨v,pair,hv⟩,hp,sx⟩ := (qval_mem_l O hZF g value).mp hx
    obtain ⟨s',p',d,pair',_,hd,check⟩ := bound v hv
    obtain ⟨es,ep⟩ := kpair_injective_l M pair' pair
    subst s' p'
    exact ⟨d,s,p,hd,check,⟨v,pair,hv⟩,hp,qval_unique_l (checks d s check) sx⟩
  · rintro ⟨d,s,p,_,check,entry,hp,rfl⟩
    exact (qval_mem_l O hZF g value).mpr ⟨s,p,entry,hp,checks d s check⟩

/-- 同一原名字的两个值逐成员对应；目标成员均来自原地集合 D。 -/
theorem Ck_bound_d.value_image_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z b D τ : M.Domain} (bound : Ck_bound_d B b D τ)
    (O : Cond_order_d M B R z) {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M B R z G) (h : Generic_d N (e B) (e R) (e z) H)
    (same : ∀ p, G p ↔ H (e p))
    (j : M.Domain → (extension_l M hM B R z G).Domain)
    (k : N.Domain → (extension_l N hN (e B) (e R) (e z) H).Domain)
    (jc : ∀ d s, Check_d M b d s → Qval_d M B R z G s (j d))
    (kc : ∀ d s, Check_d N (e b) d s → Qval_d N (e B) (e R) (e z) H s (k d))
    {x : (extension_l M hM B R z G).Domain}
    {y : (extension_l N hN (e B) (e R) (e z) H).Domain}
    (vx : Qval_d M B R z G τ x) (vy : Qval_d N (e B) (e R) (e z) H (e τ) y)
    (ji : Function.Injective j) (ki : Function.Injective k) :
    (∀ v, v ∈ x → ∃ d, M.mem d D ∧ j d = v) ∧
      ∀ d, j d ∈ x ↔ k (e d) ∈ y := by
  have O' := image_cond_order_l (ZF.modelsKP hM) hN.1 e inj full O
  have target := (image_ck_bound_l hM hN e inj full).mp bound
  have rel : ∀ v, M.mem v τ → ∃ s p, KPair_d M v s p := by
    intro v hv
    obtain ⟨s,p,_,pair,_⟩ := bound v hv
    exact ⟨s,p,pair⟩
  refine ⟨fun v hv => ?_,fun d => ⟨?_,?_⟩⟩
  · obtain ⟨d,_,_,hd,_,_,_,eq⟩ := (bound.value_l hM O g j jc vx v).mp hv
    exact ⟨d,hd,eq⟩
  · intro hd
    obtain ⟨a,s,p,ha,cs,sp,hp,eq⟩ := (bound.value_l hM O g j jc vx (j d)).mp hd
    have ad := ji eq
    subst a
    exact (target.value_l hN O' h k kc vy (k (e d))).mpr
      ⟨e d,e s,e p,(image_member_l e inj full).mpr ha,
        image_check_l e inj full (ZF.modelsKP hM) hN.1 cs,
        (image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1 s p τ).mp sp,
        (same p).mp hp,rfl⟩
  · intro hd
    obtain ⟨a,s,p,ha,cs,sp,hp,eq⟩ := (target.value_l hN O' h k kc vy (k (e d))).mp hd
    have ad := ki eq
    subst a
    obtain ⟨s₀,p₀,sp₀,es,ep⟩ := (image_entries_l e full rel s p).mp sp
    subst s p
    exact (bound.value_l hM O g j jc vx (j d)).mpr
      ⟨d,s₀,p₀,(image_member_l e inj full).mp ha,
        (image_check_iff_l e inj full hM hN b d s₀).mpr cs,sp₀,(same p₀).mpr hp,rfl⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一个检查子集名字的双向实数解释

两侧值的成员均来自同一地平方集，逐成员对应因而给出完整边对应。
全定义性及唯一性可向任一侧传递；整个论证不使用完整初等性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v w

private theorem ck_graph_pull_l {M : Structure.{u}} {E : Structure.{v}} {F : Structure.{w}}
    (hM : M.Models KP) (hE : E.Models KP) (hF : F.Models KP)
    (j : M.Domain → E.Domain) (ji : Function.Injective j)
    (jf : ∀ a y, E.mem y (j a) ↔ ∃ d, M.mem d a ∧ j d = y)
    (k : M.Domain → F.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, F.mem y (k a) ↔ ∃ d, M.mem d a ∧ k d = y)
    {D ω : M.Domain} (product : M.IsCartesianProduct (kp_pair_l hM) D ω ω)
    {x : E.Domain} {y : F.Domain}
    (covered : ∀ v, E.mem v x → ∃ d, M.mem d D ∧ j d = v)
    (members : ∀ d, E.mem (j d) x ↔ F.mem (k d) y)
    (real : Fn0_d (k ω) (k ω) y) : Fn0_d (j ω) (j ω) x ∧ Fn_read_d k j x y := by
  have edges a b : Entry_d E (j a) (j b) x ↔ Entry_d F (k a) (k b) y := by
    obtain ⟨d,pair⟩ := (kp_pair_l hM).total a b
    have left := image_kpair_l j jf pair
    have right := image_kpair_l k kf pair
    constructor
    · rintro ⟨v,pv,hv⟩
      exact ⟨k d,right,(members d).mp (kpair_unique_l E hE.1 pv left ▸ hv)⟩
    · rintro ⟨v,pv,hv⟩
      exact ⟨j d,left,(members d).mpr (kpair_unique_l F hF.1 pv right ▸ hv)⟩
  refine ⟨⟨?_,?_,?_⟩,fun a b => ⟨?_,?_⟩⟩
  · intro v hv
    obtain ⟨d,hd,rfl⟩ := covered v hv
    obtain ⟨a,ha,b,hb,pair⟩ := (product d).mp hd
    exact ⟨j a,(image_member_l j ji jf).mpr ha,j b,(image_member_l j ji jf).mpr hb,image_kpair_l j jf pair⟩
  · intro a ha
    obtain ⟨a₀,ha₀,rfl⟩ := (jf ω a).mp ha
    obtain ⟨b,hb,ab⟩ := real.2.1 (k a₀) ((image_member_l k ki kf).mpr ha₀)
    obtain ⟨b₀,hb₀,rfl⟩ := (kf ω b).mp hb
    exact ⟨j b₀,(image_member_l j ji jf).mpr hb₀,(edges a₀ b₀).mpr ab⟩
  · intro a ha b hb c hc ab ac
    obtain ⟨a₀,_,rfl⟩ := (jf ω a).mp ha
    obtain ⟨b₀,_,rfl⟩ := (jf ω b).mp hb
    obtain ⟨c₀,_,rfl⟩ := (jf ω c).mp hc
    exact congrArg j (ki ((fn0_function_l hF real).1.2 _ _ _ ((edges a₀ b₀).mp ab) ((edges a₀ c₀).mp ac)))
  · intro ab
    obtain ⟨a₀,_,rfl⟩ := (kf ω a).mp (real.bound_l ab).1
    obtain ⟨b₀,_,rfl⟩ := (kf ω b).mp (real.bound_l ab).2
    exact ⟨a₀,b₀,rfl,rfl,(edges a₀ b₀).mpr ab⟩
  · rintro ⟨a₀,b₀,rfl,rfl,ab⟩
    exact (edges a₀ b₀).mp ab

variable {M : Structure.{u}} {N : Structure.{v}}

theorem Ck_bound_d.real_compare_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R z b D ω τ : M.Domain} (bound : Ck_bound_d B b D τ)
    (product : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hM)) D ω ω)
    (O : Cond_order_d M B R z) {G : M.Domain → Prop} {H : N.Domain → Prop}
    (g : Generic_d M B R z G) (h : Generic_d N (e B) (e R) (e z) H) (same : ∀ p, G p ↔ H (e p))
    (j : M.Domain → (extension_l M hM B R z G).Domain)
    (k : N.Domain → (extension_l N hN (e B) (e R) (e z) H).Domain)
    (jc : ∀ a t, Check_d M b a t → Qval_d M B R z G t (j a))
    (kc : ∀ a t, Check_d N (e b) a t → Qval_d N (e B) (e R) (e z) H t (k a))
    (ji : Function.Injective j) (jf : ∀ a y, y ∈ j a ↔ ∃ d, M.mem d a ∧ j d = y)
    (ki : Function.Injective k) (kf : ∀ a y, y ∈ k a ↔ ∃ d, N.mem d a ∧ k d = y)
    {x : (extension_l M hM B R z G).Domain} {y : (extension_l N hN (e B) (e R) (e z) H).Domain}
    (vx : Qval_d M B R z G τ x) (vy : Qval_d N (e B) (e R) (e z) H (e τ) y) :
    (Fn0_d (j ω) (j ω) x ↔ Fn0_d (k (e ω)) (k (e ω)) y) ∧
      (Fn0_d (k (e ω)) (k (e ω)) y → Fn_read_d (k ∘ e) j x y) := by
  have O' := image_cond_order_l (ZF.modelsKP hM) hN.1 e inj full O
  have hE := ZF.modelsKP (preserves_zf_l O hM g)
  have hF := ZF.modelsKP (preserves_zf_l O' hN h)
  have composed a v : v ∈ k (e a) ↔ ∃ d, M.mem d a ∧ k (e d) = v := by
    constructor
    · intro hv
      obtain ⟨c,hc,rfl⟩ := (kf (e a) v).mp hv
      obtain ⟨d,hd,rfl⟩ := (full a c).mp hc
      exact ⟨d,hd,rfl⟩
    · rintro ⟨d,hd,rfl⟩
      exact (image_member_l k ki kf).mpr ((image_member_l e inj full).mpr hd)
  obtain ⟨cover,members⟩ := bound.value_image_l hM hN e inj full O g h same j k jc kc vx vy ji ki
  have target := (image_ck_bound_l hM hN e inj full).mp bound
  have cover' v (hv : v ∈ y) : ∃ d, M.mem d D ∧ k (e d) = v := by
    obtain ⟨a,_,_,ha,_,_,_,eq⟩ := (target.value_l hN O' h k kc vy v).mp hv
    obtain ⟨d,hd,rfl⟩ := (full D a).mp ha
    exact ⟨d,hd,eq⟩
  have pull := ck_graph_pull_l (ZF.modelsKP hM) hE hF j ji jf (k ∘ e) (ki.comp inj) composed product cover members
  have push := ck_graph_pull_l (ZF.modelsKP hM) hF hE (k ∘ e) (ki.comp inj) composed j ji jf product cover' (fun d => (members d).symm)
  exact ⟨⟨fun hx => (push hx).1,fun hy => (pull hy).1⟩,fun hy => (pull hy).2⟩

end YesMetaZFC.Model.Forcing.Internal
