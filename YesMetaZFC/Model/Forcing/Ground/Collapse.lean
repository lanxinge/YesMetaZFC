import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.Model.Forcing.Check.SupportBound
import YesMetaZFC.Model.Forcing.Extension.Isomorphism
import YesMetaZFC.SetTheory.PartialFunction
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Images.BinaryImage
import YesMetaZFC.SetTheory.Collapse.RelationExistence
import YesMetaZFC.SetTheory.InnerModel.HOD.Relative

/-! # 规范名称的地模型嵌入与有界结构保持

解释规范名称得到成员满覆盖的单射。以下传输只使用这个精确成员方程，
保持配对、函数图和序数；新子集上的良序最小元由扩张的基础公理提供。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u w
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

theorem check_map_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hU : Generic_d M B R z U) {b} (hb : U b) :
    ∃ e : M.Domain → (extension_l M hZF B R z U).Domain,
      (∀ a t, Check_d M b a t → Qval_d M B R z U t (e a)) ∧
      (∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y) ∧ Function.Injective e := by
  let E := extension_l M hZF B R z U
  have hbB := (hU.proper b hb).1
  have hall (a : M.Domain) : ∃ y : E.Domain, ∃ t, Check_d M b a t ∧ Qval_d M B R z U t y := by
    obtain ⟨t, ht, hn, _⟩ := zf_check_l M hZF hbB a
    obtain ⟨y, hy⟩ := name_value_l (R := R) (z := z) (U := U) hn
    exact ⟨y, t, ht, hy⟩
  obtain ⟨e, he⟩ := Classical.axiomOfChoice hall
  have hv a t (ht : Check_d M b a t) : Qval_d M B R z U t (e a) := by
    obtain ⟨s, hs, hv⟩ := he a
    exact check_unique_l M hZF.1 (check_ind_l M hZF) b a s t hs ht ▸ hv
  have hm a (y : E.Domain) : y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y := by
    obtain ⟨t, ht, hta⟩ := he a
    constructor
    · intro hy
      obtain ⟨c, s, hca, hcs, hsy⟩ := (check_val_mem_l O hZF hU ht hta hb).mp hy
      exact ⟨c, hca, qval_unique_l (hv c s hcs) hsy⟩
    · rintro ⟨c, hca, rfl⟩
      obtain ⟨s, hcs, hsc⟩ := he c
      exact (check_val_mem_l O hZF hU ht hta hb).mpr ⟨c, s, hca, hcs, hsc⟩
  refine ⟨e, hv, hm, fun a c heq => ?_⟩
  obtain ⟨s, hs, hsa⟩ := he a
  obtain ⟨t, ht, htc⟩ := he c
  obtain ⟨p, hp, hst⟩ := (qval_eq_l O hZF hU hsa htc).mpr heq
  obtain ⟨r, hr, hrp, hrb⟩ := hU.directed p b hp hb
  have hr' := hU.proper r hr
  exact check_force_reflect_l O hZF hbB hs ht ⟨hr'.1, hr'.2, hrb⟩
    (eq_force_lower_l O hZF (qval_name_l hsa) (qval_name_l htc) p r hst.1
      ⟨hr'.1, hr'.2, hrp⟩ hst)

variable {N : SetTheory.Structure.{w}} (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
include he

include hi in
theorem image_member_l {a b} : N.mem (e a) (e b) ↔ M.mem a b :=
  ⟨fun h => (he b (e a)).mp h |>.elim fun _ hc => hi hc.2 ▸ hc.1,
    fun h => (he b (e a)).mpr ⟨a, h, rfl⟩⟩

theorem image_pair_l {p a b} (hp : Pair_d M p a b) : Pair_d N (e p) (e a) (e b) := by
  intro y
  rw [he p y]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ((hp c).mp hc).elim (fun h => Or.inl (congrArg e h)) (fun h => Or.inr (congrArg e h))
  · rintro (rfl | rfl)
    · exact ⟨a, (hp a).mpr (Or.inl rfl), rfl⟩
    · exact ⟨b, (hp b).mpr (Or.inr rfl), rfl⟩

theorem image_kpair_l {p a b} (hp : KPair_d M p a b) : KPair_d N (e p) (e a) (e b) := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  refine ⟨e s, e t, ?_, image_pair_l e he ht, image_pair_l e he hp⟩
  intro y
  rw [he s y]
  exact ⟨fun ⟨c, hc, hy⟩ => hy.symm.trans (congrArg e ((hs c).mp hc)),
    fun hy => ⟨a, (hs a).mpr rfl, hy.symm⟩⟩

include hi in
/-- 任意旧集合中的关系条目双向绝对；无需该集合的所有成员都是有序对。 -/
theorem image_entry_iff_l (hP : ∀ a b, ∃ p, Pair_d M p a b) (hN : Extensional N)
    (a b F : M.Domain) : Entry_d M a b F ↔ Entry_d N (e a) (e b) (e F) := by
  constructor
  · rintro ⟨p, hp, hpF⟩
    exact ⟨e p, image_kpair_l e he hp, (he F (e p)).mpr ⟨p, hpF, rfl⟩⟩
  · rintro ⟨v, hv, hvF⟩
    obtain ⟨p, hpF, rfl⟩ := (he F v).mp hvF
    obtain ⟨s, hs⟩ := hP a a
    obtain ⟨t, ht⟩ := hP a b
    obtain ⟨q, hq⟩ := hP s t
    have hq : KPair_d M q a b := ⟨s, t, (fun x => (hs x).trans ⟨fun h => h.elim id id, Or.inl⟩), ht, hq⟩
    have hqp := hi (kpair_unique_l N hN (image_kpair_l e he hq) hv)
    exact ⟨q, hq, hqp.symm ▸ hpF⟩

theorem image_entries_l {f} (hf : ∀ p, M.mem p f → ∃ a b, KPair_d M p a b) (x y : N.Domain) :
    Entry_d N x y (e f) ↔ ∃ a b, Entry_d M a b f ∧ e a = x ∧ e b = y := by
  constructor
  · rintro ⟨q, hq, hqf⟩
    obtain ⟨p, hpf, rfl⟩ := (he f q).mp hqf
    obtain ⟨a, b, hp⟩ := hf p hpf
    obtain ⟨ha, hb⟩ := kpair_injective_l N (image_kpair_l e he hp) hq
    exact ⟨a, b, ⟨p, hp, hpf⟩, ha, hb⟩
  · rintro ⟨a, b, ⟨p, hp, hpf⟩, rfl, rfl⟩
    exact ⟨e p, image_kpair_l e he hp, (he f (e p)).mpr ⟨p, hpf, rfl⟩⟩

variable {hEM : Extensional M} {hPM : ∀ a b, ∃ p, Pair_d M p a b}
  {hEN : Extensional N} {hPN : ∀ a b, ∃ p, Pair_d N p a b}

include hi in
theorem image_product_l {P X Y}
    (hP : M.IsCartesianProduct (kpair_interpretation_l M hEM hPM) P X Y) :
    N.IsCartesianProduct (kpair_interpretation_l N hEN hPN) (e P) (e X) (e Y) := by
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := (he P p).mp hp
    obtain ⟨x, hx, y, hy, hq⟩ := (hP q).mp hq
    exact ⟨e x, (image_member_l e hi he).mpr hx, e y, (image_member_l e hi he).mpr hy, image_kpair_l e he hq⟩
  · rintro ⟨x, hx, y, hy, hp⟩
    obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
    obtain ⟨b, hb, rfl⟩ := (he Y y).mp hy
    obtain ⟨q, hq⟩ := (kpair_interpretation_l M hEM hPM).total a b
    exact (he P p).mpr ⟨q, (hP q).mpr ⟨a, ha, b, hb, hq⟩,
      kpair_unique_l N hEN (image_kpair_l e he hq) hp⟩

include hi in
theorem image_function_l {f X Y}
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hEM hPM) f X Y) :
    N.IsSetFunctionFromTo (kpair_interpretation_l N hEN hPN) (e f) (e X) (e Y) := by
  have hf' : ∀ p, M.mem p f → ∃ a b, KPair_d M p a b := hf.1.1
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := (he f q).mp hq
    obtain ⟨a, b, hab⟩ := hf' p hp
    exact ⟨e a, e b, image_kpair_l e he hab⟩
  · intro x y z hxy hxz
    obtain ⟨a, b, hab, hax, hby⟩ := (image_entries_l e he hf' x y).mp hxy
    obtain ⟨c, d, hcd, hcx, hdz⟩ := (image_entries_l e he hf' x z).mp hxz
    have hac := hi (hax.trans hcx.symm)
    subst c
    exact hby.symm.trans ((congrArg e (hf.1.2 a b d hab hcd)).trans hdz)
  · intro x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
      obtain ⟨b, hab⟩ := (hf.2.1 a).mp ha
      exact ⟨e b, (image_entries_l e he hf' (e a) (e b)).mpr ⟨a, b, hab, rfl, rfl⟩⟩
    · rintro ⟨y, hxy⟩
      obtain ⟨a, b, hab, rfl, _⟩ := (image_entries_l e he hf' x y).mp hxy
      exact (image_member_l e hi he).mpr (hf.input_mem_of_pairMember hab)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
    obtain ⟨b, hb, hab⟩ := hf.2.2 a ha
    exact ⟨e b, (image_member_l e hi he).mpr hb,
      (image_entries_l e he hf' (e a) (e b)).mpr ⟨a, b, hab, rfl, rfl⟩⟩

include hi in
theorem image_injection_l {f X Y}
    (hf : M.IsSetInjectionFromTo (kpair_interpretation_l M hEM hPM) f X Y) :
    N.IsSetInjectionFromTo (kpair_interpretation_l N hEN hPN) (e f) (e X) (e Y) := by
  refine ⟨image_function_l e hi he hf.1, fun x y z hx hy => ?_⟩
  obtain ⟨a, b, hab, rfl, hb⟩ := (image_entries_l e he hf.1.1.1 x z).mp hx
  obtain ⟨c, d, hcd, rfl, hd⟩ := (image_entries_l e he hf.1.1.1 y z).mp hy
  have hbd := hi (hb.trans hd.symm)
  subst d
  exact congrArg e (hf.2 a c b hab hcd)

include hi hEN in
theorem image_successor_l (hEM : Extensional M) {s a} (hs : M.SuccessorOf s a) :
    N.SuccessorOf (e s) (e a) := by
  intro y
  rw [he s y]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases (hs c).mp hc with hc | hc
    · exact Or.inl ((image_member_l e hi he).mpr hc)
    · have hc := hEM.eq_of_same_members c a hc
      exact Or.inr (hc ▸ fun _ => Iff.rfl)
  · rintro (hy | hy)
    · obtain ⟨c, hc, rfl⟩ := (he a y).mp hy
      exact ⟨c, (hs c).mpr (Or.inl hc), rfl⟩
    · have hy := hEN.eq_of_same_members y (e a) hy
      exact ⟨a, hs.predecessor_mem, hy.symm⟩

include hi in
theorem image_ordinal_l (hEM : Extensional M)
    (hF : ∀ X, (∃ x, N.mem x X) → ∃ x, N.mem x X ∧ ∀ y, N.mem y X → ¬ N.mem y x)
    {α} (hα : M.IsOrdinal α) : N.IsOrdinal (e α) := by
  have hl : N.MembershipLinearOrder (e α) := by
    constructor
    · intro x hx hxx
      obtain ⟨a, ha, rfl⟩ := (he α x).mp hx
      exact hα.wellOrder.linear.irrefl a ha ((image_member_l e hi he).mp hxx)
    · intro x hx y hy z hz hxy hyz
      obtain ⟨a, ha, rfl⟩ := (he α x).mp hx
      obtain ⟨b, hb, rfl⟩ := (he α y).mp hy
      obtain ⟨c, hc, rfl⟩ := (he α z).mp hz
      exact (image_member_l e hi he).mpr (hα.wellOrder.linear.trans a ha b hb c hc
        ((image_member_l e hi he).mp hxy) ((image_member_l e hi he).mp hyz))
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := (he α x).mp hx
      obtain ⟨b, hb, rfl⟩ := (he α y).mp hy
      rcases hα.wellOrder.linear.compare a ha b hb with hab | hab | hba
      · have hab := hEM.eq_of_same_members a b hab
        exact Or.inl (hab ▸ fun _ => Iff.rfl)
      · exact Or.inr (Or.inl ((image_member_l e hi he).mpr hab))
      · exact Or.inr (Or.inr ((image_member_l e hi he).mpr hba))
  refine ⟨?_, ⟨hl, ?_⟩⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (he α x).mp hx
    obtain ⟨b, hb, rfl⟩ := (he a y).mp hy
    exact (image_member_l e hi he).mpr (hα.transitive a ha b hb)
  · intro X hX hn
    obtain ⟨x, hx, hm⟩ := hF X hn
    refine ⟨x, hx, fun y hy => ?_⟩
    rcases hl.compare x (hX x hx) y (hX y hy) with heq | hxy | hyx
    · exact Or.inl heq
    · exact Or.inr hxy
    · exact False.elim (hm y hy hyx)

include hi hEN in
/-- 规范嵌入保留内部 ω；目标中的差集与基础公理排除新的归纳真子集。 -/
theorem image_omega_l (hZF : M.Models ZF)
    (hF : ∀ X, (∃ x, N.mem x X) → ∃ x, N.mem x X ∧ ∀ y, N.mem y X → ¬ N.mem y x)
    {ω} (hω : M.IsOmega ω)
    (hD : ∀ T, ∃ D, ∀ y, N.mem y D ↔ N.mem y (e ω) ∧ ¬ N.mem y T) : N.IsOmega (e ω) := by
  have hz a (ha : ∀ x, ¬ M.mem x a) : ∀ y, ¬ N.mem y (e a) := by
    intro y hy
    obtain ⟨x, hx, _⟩ := (he a y).mp hy
    exact ha x hx
  constructor
  · constructor
    · obtain ⟨a, ha, haω⟩ := hω.1.1
      exact ⟨e a, hz a ha, (image_member_l e hi he).mpr haω⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (he ω x).mp hx
      obtain ⟨s, hs, hsω⟩ := hω.1.2 a ha
      exact ⟨e s, image_successor_l (hEN := hEN) e hi he hZF.1 hs, (image_member_l e hi he).mpr hsω⟩
  · intro T hT y hy
    classical
    apply Classical.byContradiction
    intro hn
    obtain ⟨D, hD⟩ := hD T
    obtain ⟨x, hx, hm⟩ := hF D ⟨y, (hD y).mpr ⟨hy, hn⟩⟩
    obtain ⟨hxω, hxT⟩ := (hD x).mp hx
    obtain ⟨a, ha, rfl⟩ := (he ω x).mp hxω
    apply hxT
    by_cases hn : ∃ c, M.mem c a
    · obtain ⟨c, hcω, hac⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF ha hn
      have hcT : N.mem (e c) T := by
        apply Classical.byContradiction
        intro hnc
        exact hm (e c) ((hD (e c)).mpr ⟨(image_member_l e hi he).mpr hcω, hnc⟩)
          ((image_member_l e hi he).mpr hac.predecessor_mem)
      obtain ⟨s, hs, hsT⟩ := hT.2 (e c) hcT
      exact (Structure.SuccessorOf.eq hEN (image_successor_l (hEN := hEN) e hi he hZF.1 hac) hs).symm ▸ hsT
    · obtain ⟨s, hs, hsT⟩ := hT.1
      have ha0 := hz a (fun c hc => hn ⟨c, hc⟩)
      exact (hEN.eq_of_same_members (e a) s (fun y => iff_of_false (ha0 y) (hs y))).symm ▸ hsT

end YesMetaZFC.Model.Forcing.Internal

/-! ## 与基条件无关的地模型值

两个被泛型接受的基条件有共同加强，故它们的 check 名称给出同一个商值。
用这一关系记录同构对原模型对象的对应，而不固定额外的基条件选择。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

def Gval_d (M : Structure.{u}) (B R z : M.Domain) (U : M.Domain → Prop)
    (x : M.Domain) (a : Name_quot_l M B R z U) : Prop :=
  ∃ b t, U b ∧ Check_d M b x t ∧ Qval_d M B R z U t a

theorem Gval_d.unique_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (generic : Generic_d M B R z U) {x a d}
    (ha : Gval_d M B R z U x a) (hd : Gval_d M B R z U x d) : a = d := by
  obtain ⟨b,s,hb,hs,sa⟩ := ha
  obtain ⟨c,t,hc,ht,td⟩ := hd
  obtain ⟨p,hp,pb,pc⟩ := generic.directed b c hb hc
  exact (qval_eq_l O hZF generic sa td).mp ⟨p,hp,
    check_force_bases_l O hZF (generic.proper b hb).1 (generic.proper c hc).1 hs ht
      (generic.proper p hp).1 pb pc⟩

theorem gval_exists_l (hZF : M.Models ZF) (generic : Generic_d M B R z U) (x : M.Domain) :
    ∃ a, Gval_d M B R z U x a := by
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨t,ht,nt,_⟩ := zf_check_l M hZF (generic.proper b hb).1 x
  obtain ⟨a,ta⟩ := name_value_l (R := R) (z := z) (U := U) nt
  exact ⟨a,b,t,hb,ht,ta⟩

/-- 固定基条件的规范嵌入与基条件无关的关系完全一致。 -/
theorem gval_check_map_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (generic : Generic_d M B R z U) {b} (hb : U b)
    (j : M.Domain → (extension_l M hZF B R z U).Domain)
    (checks : ∀ x t, Check_d M b x t → Qval_d M B R z U t (j x)) (x a) :
    Gval_d M B R z U x a ↔ j x = a := by
  obtain ⟨t,ht,_,_⟩ := zf_check_l M hZF (generic.proper b hb).1 x
  have value : Gval_d M B R z U x (j x) := ⟨b,t,hb,ht,checks x t ht⟩
  exact ⟨fun ha => value.unique_l O hZF generic ha,fun eq => eq ▸ value⟩

/-- 被同一泛型接受的另一个基条件给出相同规范嵌入。 -/
theorem check_map_change_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (generic : Generic_d M B R z U) {b c} (hb : U b) (hc : U c)
    (j : M.Domain → (extension_l M hZF B R z U).Domain)
    (checks : ∀ x t, Check_d M b x t → Qval_d M B R z U t (j x)) :
    ∀ x t, Check_d M c x t → Qval_d M B R z U t (j x) := by
  intro x t check
  have name := check_name_l M (check_range_l M hZF) (generic.proper c hc).1 check
  obtain ⟨a,value⟩ := name_value_l (R := R) (z := z) (U := U) name
  have eq := (gval_check_map_l O hZF generic hb j checks x a).mp ⟨c,t,hc,check,value⟩
  exact eq.symm ▸ value

end YesMetaZFC.Model.Forcing.Internal

/-! ## 旧部分函数图的成员满嵌入保持 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem image_pfn_l {hM : Extensional M} {pairM : ∀ a b, ∃ p, Pair_d M p a b}
    {hN : Extensional N} {pairN : ∀ a b, ∃ p, Pair_d N p a b} (j : M.Domain → N.Domain)
    (inj : Function.Injective j) (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
    {X Y p : M.Domain} (h : Pfn_d (kpair_interpretation_l M hM pairM) X Y p) :
    Pfn_d (kpair_interpretation_l N hN pairN) (j X) (j Y) (j p) := by
  have entries := image_entries_l j full h.1.1
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro v hv
    obtain ⟨a,ha,rfl⟩ := (full p v).mp hv
    obtain ⟨x,y,pair⟩ := h.1.1 a ha
    exact ⟨j x,j y,image_kpair_l j full pair⟩
  · intro x y z xy xz
    obtain ⟨a,b,ab,ax,by'⟩ := (entries x y).mp xy
    obtain ⟨c,d,cd,cx,dz⟩ := (entries x z).mp xz
    have eq := inj (ax.trans cx.symm)
    subst c
    exact by'.symm.trans ((congrArg j (h.1.2 a b d ab cd)).trans dz)
  · intro x y xy
    obtain ⟨a,b,ab,rfl,rfl⟩ := (entries x y).mp xy
    exact ⟨(image_member_l j inj full).mpr (h.2 a b ab).1,(image_member_l j inj full).mpr (h.2 a b ab).2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 沿同一地参数识别的完整函数图解释

两个模型中的图通过同一地模型参数比较。每个输入都有同一个地输出时，
双向图方程确定背景中的唯一实际关系，不将不同模型的对象直接作类型相等。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v w
variable {N : Structure.{u}} {M : Structure.{v}} {E : Structure.{w}}

def Fn_read_d (k : N.Domain → M.Domain) (j : N.Domain → E.Domain) (F : E.Domain) (x : M.Domain) : Prop :=
  ∀ i y, Entry_d M i y x ↔ ∃ a b, k a = i ∧ k b = y ∧ Entry_d E (j a) (j b) F

/-- 两个已识别的地坐标上，完整图方程直接化为同一条边的双向对应。 -/
theorem Fn_read_d.entry_l {k : N.Domain → M.Domain} (ki : Function.Injective k)
    {j : N.Domain → E.Domain} {F : E.Domain} {x : M.Domain} (read : Fn_read_d k j F x)
    (a b : N.Domain) : Entry_d M (k a) (k b) x ↔ Entry_d E (j a) (j b) F := by
  constructor
  · intro ab
    obtain ⟨c,d,ec,ed,cd⟩ := (read (k a) (k b)).mp ab
    exact ki ec ▸ ki ed ▸ cd
  · exact fun ab => (read (k a) (k b)).mpr ⟨a,b,rfl,rfl,ab⟩

theorem Fn_read_d.unique_l (hM : M.Models KP) {k : N.Domain → M.Domain} {j : N.Domain → E.Domain}
    {F : E.Domain} {x y : M.Domain} (hx : Fn_read_d k j F x) (hy : Fn_read_d k j F y)
    (rx : M.IsSetRelation (kp_pair_l hM) x) (ry : M.IsSetRelation (kp_pair_l hM) y) : x = y :=
  rx.eq_of_pairMember_iff hM.1 ry (fun a b => (hx a b).trans (hy a b).symm)

/-- 成员满嵌入保留完整图读取；两侧地参数随同一个嵌入搬运。 -/
theorem Fn_read_d.image_l {D : Structure} (pair : ∀ a b, ∃ p, Pair_d E p a b) (hD : Extensional D)
    (e : E.Domain → D.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, D.mem y (e a) ↔ ∃ b, E.mem b a ∧ e b = y)
    {k : N.Domain → M.Domain} {j : N.Domain → E.Domain} {F : E.Domain} {x : M.Domain}
    (h : Fn_read_d k j F x) : Fn_read_d k (e ∘ j) (e F) x := by
  intro a b
  exact (h a b).trans (exists_congr fun c => exists_congr fun d =>
    and_congr_right fun _ => and_congr_right fun _ =>
      image_entry_iff_l e ei ef pair hD (j c) (j d) F)

/-- 背景图沿成员满包含搬运，原值及其名字保持不变。 -/
theorem Fn_read_d.background_image_l {D : Structure} (e : M.Domain → D.Domain)
    (full : ∀ a y, D.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {k : N.Domain → M.Domain} {j : N.Domain → E.Domain} {F : E.Domain} {x : M.Domain}
    (read : Fn_read_d k j F x) (rel : ∀ v, M.mem v x → ∃ a b, KPair_d M v a b) :
    Fn_read_d (e ∘ k) j F (e x) := by
  intro a b
  constructor
  · intro ab
    obtain ⟨a₀,b₀,edge,rfl,rfl⟩ := (image_entries_l e full rel a b).mp ab
    obtain ⟨a₁,b₁,ea,eb,old⟩ := (read a₀ b₀).mp edge
    exact ⟨a₁,b₁,congrArg e ea,congrArg e eb,old⟩
  · rintro ⟨a₀,b₀,rfl,rfl,old⟩
    exact (image_entries_l e full rel _ _).mpr ⟨k a₀,k b₀,(read _ _).mpr ⟨a₀,b₀,rfl,rfl,old⟩,rfl,rfl⟩

/-- 地参数覆盖函数源和目标时，同一背景图也唯一决定扩张中的函数。 -/
theorem Fn_read_d.value_unique_l (hE : Extensional E)
    {k : N.Domain → M.Domain} (ki : Function.Injective k) {j : N.Domain → E.Domain}
    (jf : ∀ a y, E.mem y (j a) ↔ ∃ b, N.mem b a ∧ j b = y)
    {D A : N.Domain} {F G : E.Domain} {x : M.Domain}
    (f : Fn0_d (j D) (j A) F) (g : Fn0_d (j D) (j A) G)
    (hx : Fn_read_d k j F x) (hy : Fn_read_d k j G x) : F = G := by
  have forward {F G} (f : Fn0_d (j D) (j A) F)
      (hx : Fn_read_d k j F x) (hy : Fn_read_d k j G x) {a b} (ab : Entry_d E a b F) : Entry_d E a b G := by
    obtain ⟨c,_,rfl⟩ := (jf D a).mp (f.bound_l ab).1
    obtain ⟨d,_,rfl⟩ := (jf A b).mp (f.bound_l ab).2
    obtain ⟨c',d',ec,ed,edge⟩ := (hy (k c) (k d)).mp ((hx (k c) (k d)).mpr ⟨c,d,rfl,rfl,ab⟩)
    exact ki ec ▸ ki ed ▸ edge
  have graph {F} (f : Fn0_d (j D) (j A) F) v (hv : E.mem v F) : ∃ a b, KPair_d E v a b := by
    obtain ⟨a,_,b,_,pair⟩ := f.1 v hv
    exact ⟨a,b,pair⟩
  exact entry_ext_l E hE (graph f) (graph g) (fun a b => ⟨forward f hx hy,forward g hy hx⟩)

/-- 完整图解释把目标函数的值域收紧到背景实数的同一地值域。 -/
theorem Fn_read_d.range_l (hM : M.Models KP) (hE : E.Models KP)
    {k : N.Domain → M.Domain} (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    {j : N.Domain → E.Domain} (ji : Function.Injective j)
    (jf : ∀ a y, E.mem y (j a) ↔ ∃ b, N.mem b a ∧ j b = y)
    {D A B : N.Domain} {F : E.Domain} {x : M.Domain}
    (fn : E.IsSetFunctionFromTo (kp_pair_l hE) F (j D) (j A))
    (fx : M.IsSetFunctionFromTo (kp_pair_l hM) x (k D) (k B))
    (read : Fn_read_d k j F x) : E.IsSetFunctionFromTo (kp_pair_l hE) F (j D) (j B) := by
  refine ⟨fn.1,fn.2.1,fun i hi => ?_⟩
  obtain ⟨a,_,rfl⟩ := (jf D i).mp hi
  obtain ⟨y,hy,ay⟩ := fn.2.2 (j a) hi
  obtain ⟨b,_,rfl⟩ := (jf A y).mp hy
  have edge := (read (k a) (k b)).mpr ⟨a,b,rfl,rfl,ay⟩
  exact ⟨j b,(image_member_l j ji jf).mpr ((image_member_l k ki kf).mp (fx.output_mem_of_pairMember edge)),ay⟩

theorem function_read_l (hM : M.Models KP) (hE : E.Models KP)
    (k : N.Domain → M.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    (j : N.Domain → E.Domain) (ji : Function.Injective j)
    (jf : ∀ a y, E.mem y (j a) ↔ ∃ b, N.mem b a ∧ j b = y)
    {D : N.Domain} {X x : M.Domain} {Y F : E.Domain}
    (fx : M.IsSetFunctionFromTo (kp_pair_l hM) x (k D) X)
    (fF : E.IsSetFunctionFromTo (kp_pair_l hE) F (j D) Y)
    (rows : ∀ a, N.mem a D → ∃ b, Entry_d M (k a) (k b) x ∧ Entry_d E (j a) (j b) F) :
    Fn_read_d k j F x ∧
      (∀ i y, Entry_d E i y F ↔ ∃ a b, j a = i ∧ j b = y ∧ Entry_d M (k a) (k b) x) ∧
      ∀ g, M.IsSetRelation (kp_pair_l hM) g → (Fn_read_d k j F g ↔ g = x) := by
  have forward a b (ab : Entry_d M (k a) (k b) x) : Entry_d E (j a) (j b) F := by
    have ha := (image_member_l k ki kf).mp (fx.input_mem_of_pairMember ab)
    obtain ⟨c,ac,ac'⟩ := rows a ha
    exact congrArg j (ki (fx.1.2 (k a) (k c) (k b) ac ab)) ▸ ac'
  have backward a b (ab : Entry_d E (j a) (j b) F) : Entry_d M (k a) (k b) x := by
    have ha := (image_member_l j ji jf).mp (fF.input_mem_of_pairMember ab)
    obtain ⟨c,ac,ac'⟩ := rows a ha
    exact congrArg k (ji (fF.1.2 (j a) (j c) (j b) ac' ab)) ▸ ac
  have read : Fn_read_d k j F x := by
    intro i y
    constructor
    · intro iy
      obtain ⟨a,ha,rfl⟩ := (kf D i).mp (fx.input_mem_of_pairMember iy)
      obtain ⟨b,ab,ab'⟩ := rows a ha
      exact ⟨a,b,rfl,fx.1.2 (k a) (k b) y ab iy,ab'⟩
    · rintro ⟨a,b,rfl,rfl,ab⟩
      exact backward a b ab
  refine ⟨read,?_,?_⟩
  · intro i y
    constructor
    · intro iy
      obtain ⟨a,ha,rfl⟩ := (jf D i).mp (fF.input_mem_of_pairMember iy)
      obtain ⟨b,ab,ab'⟩ := rows a ha
      exact ⟨a,b,rfl,fF.1.2 (j a) (j b) y ab' iy,ab⟩
    · rintro ⟨a,b,rfl,rfl,ab⟩
      exact forward a b ab
  · intro g rg
    exact ⟨fun h => h.unique_l hM read rg fx.1.1,fun eq => eq.symm ▸ read⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 两侧完整实数图解释保持规范二值解码

查询图和编码图通过同一个地模型的自然数比较。自然数方块在地模型中
实际构造，两侧满嵌入保持其证书；因此逐点图读取保持二值性和原规范解码。
这里不要求泛型扩张整体嵌入背景，也不要求两侧的全部实数相同。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u v w
variable {N : Structure.{u}} {M : Structure.{v}} {E : Structure.{w}}

private theorem bc_succ_image_l (hN : Extensional N) (hM : Extensional M)
    (e : N.Domain → M.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, M.mem y (e a) ↔ ∃ b, N.mem b a ∧ e b = y) (v k : N.Domain) :
    N.SuccessorOf v k ↔ M.SuccessorOf (e v) (e k) := by
  let ρ : Env N 2 := ⟨Fin.cases v (fun _ => k),fun _ => v⟩
  exact (KP.succ0_sat_l hN ρ (.bound 0) (.bound 1)).symm.trans
    ((delta0_image_l e ei ef (KP.succ0_delta_l ..) ρ).trans (KP.succ0_sat_l hM _ _ _))

/-- 自然数及规范编号属于地模型；新编码图只在其自然数坐标上读取。 -/
private theorem bc_entry_ground_l (hN : Extensional N) (hM : Extensional M)
    (e : N.Domain → M.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, M.mem y (e a) ↔ ∃ b, N.mem b a ∧ e b = y)
    (ω X F n y : N.Domain) (b : M.Domain) :
    Bc_entry_d (e ω) (e X) (e F) b (e n) (e y) ↔ N.mem n ω ∧ N.mem y ω ∧
      ∃ p, N.mem p X ∧ KPair_d N p n y ∧ ∃ k, N.mem k ω ∧ Rd_entry_d p k F ∧
        ∃ v, N.mem v ω ∧ N.SuccessorOf v k ∧ Entry_d M (e k) (e v) b := by
  have pair p : KPair_d N p n y ↔ KPair_d M (e p) (e n) (e y) := by
    let ρ : Env N 3 := ⟨fun i => [p,n,y].get i,fun _ => n⟩
    exact (kpair0_sat_l hN ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((delta0_image_l e ei ef (kpair0_delta_l ..) ρ).trans (kpair0_sat_l hM _ _ _ _))
  have edge p k : Rd_entry_d p k F ↔ Rd_entry_d (e p) (e k) (e F) := by
    let ρ : Env N 3 := ⟨fun i => [p,k,F].get i,fun _ => n⟩
    exact (rd_entry0_sat_l hN ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((delta0_image_l e ei ef (rd_entry0_delta_l ..) ρ).trans (rd_entry0_sat_l hM _ _ _ _))
  constructor
  · rintro ⟨hn,hy,p,hp,pair',k,hk,pk,v,hv,succ,kv⟩
    obtain ⟨p,hp₀,rfl⟩ := (ef X p).mp hp
    obtain ⟨k,hk₀,rfl⟩ := (ef ω k).mp hk
    obtain ⟨v,hv₀,rfl⟩ := (ef ω v).mp hv
    exact ⟨(image_member_l e ei ef).mp hn,(image_member_l e ei ef).mp hy,
      p,hp₀,(pair p).mpr pair',k,hk₀,(edge p k).mpr pk,v,hv₀,(bc_succ_image_l hN hM e ei ef v k).mpr succ,kv⟩
  · rintro ⟨hn,hy,p,hp,pair',k,hk,pk,v,hv,succ,kv⟩
    exact ⟨(image_member_l e ei ef).mpr hn,(image_member_l e ei ef).mpr hy,
      e p,(image_member_l e ei ef).mpr hp,(pair p).mp pair',e k,(image_member_l e ei ef).mpr hk,
      (edge p k).mp pk,e v,(image_member_l e ei ef).mpr hv,(bc_succ_image_l hN hM e ei ef v k).mp succ,kv⟩

/-- 扩张中的二值编码由完整背景图读取后，仍是同一原查询点的二值编码。 -/
theorem Fn_read_d.binary_decode_l (hN : N.Models ZF) (hM : M.Models ZF) (hE : E.Models ZF)
    (k : N.Domain → M.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    (j : N.Domain → E.Domain) (ji : Function.Injective j)
    (jf : ∀ a y, E.mem y (j a) ↔ ∃ b, N.mem b a ∧ j b = y)
    {ω : N.Domain} (hw : N.IsOrdinal ω) {b x : M.Domain} {B X : E.Domain}
    (fb : Fn0_d (k ω) (k ω) b) (fx : Fn0_d (k ω) (k ω) x)
    (code : Fn_read_d k j B b) (query : Fn_read_d k j X x)
    (binary : Bc_binary_d (j ω) B) (decoded : Bc_read_d (kp_pair_l (ZF.modelsKP hE)) (j ω) B X) :
    Bc_binary_d (k ω) b ∧ Bc_read_d (kp_pair_l (ZF.modelsKP hM)) (k ω) b x := by
  have bits : Bc_binary_d (k ω) b := by
    refine ⟨fb,fun n y ny => ?_⟩
    obtain ⟨a,_,rfl⟩ := (kf ω n).mp (fb.bound_l ny).1
    obtain ⟨v,_,rfl⟩ := (kf ω y).mp (fb.bound_l ny).2
    rcases binary.2 (j a) (j v) ((code.entry_l ki a v).mp ny) with empty | succ
    · refine Or.inl (fun t ht => ?_)
      obtain ⟨s,hs,_⟩ := (kf v t).mp ht
      exact empty (j s) ((image_member_l j ji jf).mpr hs)
    · exact Or.inr ((bc_succ_image_l hN.1 hM.1 k ki kf v a).mp
        ((bc_succ_image_l hN.1 hE.1 j ji jf v a).mpr succ))
  obtain ⟨Y,product⟩ := ZF.exists_cartesianProduct hN (kp_pair_l (ZF.modelsKP hN)) ω ω
  obtain ⟨η,F,square⟩ := oc_square_exists_l hN hw product
  have sqM := (oc_square_image_l k ki kf (ZF.modelsKP hN) (ZF.modelsKP hM)).mp square
  have sqE := (oc_square_image_l j ji jf (ZF.modelsKP hN) (ZF.modelsKP hE)).mp square
  have graph := (bc_graph_read_l hE sqE).mpr decoded
  refine ⟨bits,(bc_graph_read_l hM sqM).mp ⟨fx,fun n hn y hy => ?_⟩⟩
  obtain ⟨a,ha,rfl⟩ := (kf ω n).mp hn
  obtain ⟨v,hv,rfl⟩ := (kf ω y).mp hy
  have entries : Bc_entry_d (k ω) (k Y) (k F) b (k a) (k v) ↔
      Bc_entry_d (j ω) (j Y) (j F) B (j a) (j v) := by
    rw [bc_entry_ground_l hN.1 hM.1 k ki kf,bc_entry_ground_l hN.1 hE.1 j ji jf]
    simp only [code.entry_l ki]
  exact (query.entry_l ki a v).trans ((graph.2 (j a) ((image_member_l j ji jf).mpr ha)
    (j v) ((image_member_l j ji jf).mpr hv)).trans entries.symm)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地嵌入下的坍塌恢复

内部良基性向地模型回拉，实际坍塌图沿成员满嵌入向前保持。再用目标模型内部
的坍塌唯一性识别两个值；源图全部值的可定义性给出遗传可定义的地原像。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
  (hP : ∀ a b, ∃ p, Pair_d M p a b) (hN : Extensional N)
include hi he hP hN

omit hi hP hN in
theorem image_wf_reflect_l {X R} (h : Wf_rel_d (e X) (e R)) : Wf_rel_d X R := by
  intro Y hY hn
  obtain ⟨a, ha⟩ := hn
  obtain ⟨y, hy, hm⟩ := h (e Y) (fun x hx => by
    obtain ⟨b, hb, rfl⟩ := (he Y x).mp hx
    exact (he X (e b)).mpr ⟨b, hY b hb, rfl⟩) ⟨e a, (he Y (e a)).mpr ⟨a, ha, rfl⟩⟩
  obtain ⟨b, hb, rfl⟩ := (he Y y).mp hy
  exact ⟨b, hb, fun c hc ⟨p, hp, hpR⟩ => hm (e c) ((he Y (e c)).mpr ⟨c, hc, rfl⟩)
    ⟨e p, image_kpair_l e he hp, (he R (e p)).mpr ⟨p, hpR, rfl⟩⟩⟩

theorem image_collapse_graph_l {X R F} (h : Wc_graph_d X R F) : Wc_graph_d (e X) (e R) (e F) := by
  have entry a x := image_entry_iff_l e hi he hP hN a x F
  have rel a b := image_entry_iff_l e hi he hP hN a b R
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := (he F p).mp hp
    obtain ⟨a, x, hq⟩ := h.1 q hq
    exact ⟨e a, e x, image_kpair_l e he hq⟩
  · intro a x hax
    obtain ⟨b, y, hby, rfl, rfl⟩ := (image_entries_l e he h.1 a x).mp hax
    obtain ⟨hb, hs⟩ := h.2 b y hby
    refine ⟨(he X (e b)).mpr ⟨b, hb, rfl⟩, ?_, fun z => ?_⟩
    · intro c hc hcb
      obtain ⟨a, ha, rfl⟩ := (he X c).mp hc
      obtain ⟨w, haw⟩ := hs.1 a ha ((rel a b).mpr hcb)
      exact ⟨e w, (entry a w).mp haw⟩
    · constructor
      · intro hz
        obtain ⟨w, hw, rfl⟩ := (he y z).mp hz
        obtain ⟨a, ha, hab, haw⟩ := (hs.2 w).mp hw
        exact ⟨e a, (he X (e a)).mpr ⟨a, ha, rfl⟩, (rel a b).mp hab, (entry a w).mp haw⟩
      · rintro ⟨c, hc, hcb, hcz⟩
        obtain ⟨a, ha, rfl⟩ := (he X c).mp hc
        obtain ⟨a', w, haw, haa, hwz⟩ := (image_entries_l e he h.1 (e a) z).mp hcz
        have eq := hi haa
        subst a'
        exact (he y z).mpr ⟨w, (hs.2 w).mpr ⟨a, ha, (rel a b).mpr hcb, haw⟩, hwz⟩

omit hP hN in
/-- 恢复的代码载体和关系均为 OD[A] 时，总坍塌图的全部值形成遗传 OD[A] 容器。 -/
theorem collapse_hb_recover_l (hZF : M.Models ZF) (hZN : N.Models ZF) {A C R T F}
    (hC : Ob_d A C) (hR : Ob_d A R) (hc : ∀ a, M.mem a C → Ob_d A a)
    (fn : Fn0_d (e C) T F) (hg : Wc_graph_d (e C) (e R) F) {x : N.Domain}
    (hx : ∃ a, Rd_entry_d a x F) : ∃ y, Hb_d A y ∧ e y = x := by
  have hwN := wf_of_collapse_l hZN fn hg
  have hw := image_wf_reflect_l e he hwN
  obtain ⟨S, G, hf, hG, range, trans⟩ := wc_collapse_l hZF hw
  have hGI := image_collapse_graph_l e hi he (KP.exists_pair (ZF.modelsKP hZF)) hZN.1 hG
  have values a y (hay : Rd_entry_d a y G) : Ob_d A y := by
    let ρ : Env M 3 := ((⟨fun _ => C, fun _ => C⟩ : Env M 1).push R).push a
    let φ : UnarySchema 3 := { body := wc_value_m (.bound 3) (.bound 2) (.bound 1) .newest }
    have hy : Wc_value_d C R a y := ⟨G, hG, hay⟩
    exact ob_closed_l hZF A φ ρ (Fin.cases (hc a (hf.bound_l hay).1) (Fin.cases hR (fun _ => hC)))
      (fun z => (wc_value_sat_l hZF.1 (ρ.push z) _ _ _ _).trans
        ⟨fun hz => wc_value_unique_l hZF hw hz hy, fun he => he.symm ▸ hy⟩)
  obtain ⟨a, hax⟩ := hx
  obtain ⟨b, hb, hba⟩ := (he C a).mp (fn.bound_l hax).1
  obtain ⟨y, hy, hby⟩ := hf.2.1 b hb
  have hiy := (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hZF)) hZN.1 b y G).mp hby
  have eq := wc_value_unique_l hZN hwN ⟨e G, hGI, hba ▸ hiy⟩ ⟨F, hg, hax⟩
  exact ⟨y, ⟨S, trans, hy, fun z hz =>
    (range z).mp hz |>.elim fun a haz => oa_bracket_l.mpr (values a z haz)⟩, eq⟩

end YesMetaZFC.Model.Forcing.Internal
