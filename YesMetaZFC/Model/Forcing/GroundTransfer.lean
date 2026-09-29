import YesMetaZFC.Model.Forcing.InternalZFOperations
import YesMetaZFC.Model.Forcing.InternalCheckForcing

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
