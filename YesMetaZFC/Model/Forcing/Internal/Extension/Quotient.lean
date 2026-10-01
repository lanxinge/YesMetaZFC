import YesMetaZFC.Model.Forcing.Internal.Atomic.Equivalence
import YesMetaZFC.Model.Forcing.Internal.Atomic.Witness

/-! # 内部名称的泛型商

商载体与地模型处于同一 universe。等同来自被泛型接受的内部等号力迫，
隶属由原子力迫下降到商；不选择代表元，也不把模型折叠到外部良基集合。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

def Name_eq_d (M : SetTheory.Structure.{u}) (B R z : M.Domain) (U : M.Domain → Prop)
    (s t : {s // Name_d M B s}) : Prop := ∃ p, U p ∧ Eq_force_d M B R z p s.1 t.1

def Name_quot_l (M : SetTheory.Structure.{u}) (B R z : M.Domain) (U : M.Domain → Prop) : Type u :=
  Quot (Name_eq_d M B R z U)

def Qval_d (M : SetTheory.Structure.{u}) (B R z : M.Domain) (U : M.Domain → Prop)
    (t : M.Domain) (x : Name_quot_l M B R z U) : Prop :=
  ∃ ht : Name_d M B t, Quot.mk _ ⟨t, ht⟩ = x

/-- 关系在商类上的像；替换定理保证任意代表元都计算同一个隶属真值。 -/
def qmem_l (x y : Name_quot_l M B R z U) : Prop :=
  ∃ s t, Qval_d M B R z U s x ∧ Qval_d M B R z U t y ∧
    ∃ p, U p ∧ Mem_force_d M B R z p s t

instance name_quot_membership_l : Membership (Name_quot_l M B R z U) (Name_quot_l M B R z U) where
  mem y x := qmem_l x y

theorem qval_unique_l {t x y} (h : Qval_d M B R z U t x) (k : Qval_d M B R z U t y) : x = y := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := k
  rfl

theorem qval_name_l {t x} (h : Qval_d M B R z U t x) : Name_d M B t :=
  h.elim fun ht _ => ht

theorem name_value_l {t} (ht : Name_d M B t) : ∃ x : Name_quot_l M B R z U, Qval_d M B R z U t x :=
  ⟨Quot.mk _ ⟨t, ht⟩, ht, rfl⟩

theorem value_name_l (x : Name_quot_l M B R z U) : ∃ t, Name_d M B t ∧ Qval_d M B R z U t x := by
  induction x using Quot.inductionOn with
  | h t => exact ⟨t.1, t.2, t.2, rfl⟩

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
include O hZF hU

def name_setoid_l : Setoid {s // Name_d M B s} where
  r := Name_eq_d M B R z U
  iseqv := {
    refl := fun s => hU.inhabited.elim fun p hp => ⟨p, hp, eq_force_refl_l O hZF (hU.proper p hp).1 s.2⟩
    symm := fun {s t} h => h.elim fun p hp => ⟨p, hp.1, eq_force_symm_l hZF s.2 t.2 hp.2⟩
    trans := by
      rintro s t v ⟨p, hp, h⟩ ⟨q, hq, k⟩
      obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
      have hr' := hU.proper r hr
      exact ⟨r, hr, eq_force_trans_l O hZF s.2 t.2 v.2
        (eq_force_lower_l O hZF s.2 t.2 p r h.1 ⟨hr'.1, hr'.2, hrp⟩ h)
        (eq_force_lower_l O hZF t.2 v.2 q r k.1 ⟨hr'.1, hr'.2, hrq⟩ k)⟩ }

theorem qval_eq_l {s t x y} (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y) :
    (∃ p, U p ∧ Eq_force_d M B R z p s t) ↔ x = y := by
  obtain ⟨hs, rfl⟩ := hs
  obtain ⟨ht, rfl⟩ := ht
  exact ⟨fun h => Quot.sound (show Name_eq_d M B R z U ⟨s, hs⟩ ⟨t, ht⟩ from h),
    fun h => Quotient.exact (s := name_setoid_l O hZF hU) h⟩

private theorem mem_quot_congr_l {s t a b : {s // Name_d M B s}}
    (h : Name_eq_d M B R z U s a) (k : Name_eq_d M B R z U t b) :
    (∃ p, U p ∧ Mem_force_d M B R z p s.1 t.1) ↔ ∃ p, U p ∧ Mem_force_d M B R z p a.1 b.1 := by
  have forward {s t a b : {s // Name_d M B s}} (h : Name_eq_d M B R z U s a)
      (k : Name_eq_d M B R z U t b) :
      (∃ p, U p ∧ Mem_force_d M B R z p s.1 t.1) → ∃ p, U p ∧ Mem_force_d M B R z p a.1 b.1 := by
    rintro ⟨p, hp, hm⟩
    obtain ⟨q, hq, hs⟩ := h
    obtain ⟨r, hr, ht⟩ := k
    obtain ⟨v, hv, hvp, hvq⟩ := hU.directed p q hp hq
    obtain ⟨w, hw, hwv, hwr⟩ := hU.directed v r hv hr
    have hw' := hU.proper w hw
    have hwp := O.trans w v p hw'.1 (hU.proper v hv).1 hm.1 hwv hvp
    have hwq := O.trans w v q hw'.1 (hU.proper v hv).1 hs.1 hwv hvq
    have hm' : Mem_force_d M B R z w s.1 t.1 :=
      ⟨hw'.1, fun v hv => hm.2 v (below_trans_l O hm.1 hv ⟨hw'.1, hw'.2, hwp⟩)⟩
    exact ⟨w, hw, mem_force_right_l O hZF a.2 t.2 b.2
      (eq_force_lower_l O hZF t.2 b.2 r w ht.1 ⟨hw'.1, hw'.2, hwr⟩ ht)
      (mem_force_left_l O hZF s.2 a.2 t.2
        (eq_force_lower_l O hZF s.2 a.2 q w hs.1 ⟨hw'.1, hw'.2, hwq⟩ hs) hm')⟩
  exact ⟨forward h k, forward ((name_setoid_l O hZF hU).symm h) ((name_setoid_l O hZF hU).symm k)⟩

theorem qval_mem_forcing_l {s t x y} (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y) :
    (∃ p, U p ∧ Mem_force_d M B R z p s t) ↔ x ∈ y := by
  refine ⟨fun h => ⟨s, t, hs, ht, h⟩, ?_⟩
  rintro ⟨a, b, ha, hb, h⟩
  exact (mem_quot_congr_l O hZF hU
    (s := ⟨s, qval_name_l hs⟩) (t := ⟨t, qval_name_l ht⟩)
    (a := ⟨a, qval_name_l ha⟩) (b := ⟨b, qval_name_l hb⟩)
    ((qval_eq_l O hZF hU hs ha).mpr rfl) ((qval_eq_l O hZF hU ht hb).mpr rfl)).mpr h

theorem qval_mem_l {t x y} (ht : Qval_d M B R z U t x) : y ∈ x ↔
    ∃ s b, Entry_d M s b t ∧ U b ∧ Qval_d M B R z U s y := by
  constructor
  · intro h
    obtain ⟨a, ha, hay⟩ := value_name_l y
    obtain ⟨p, hp, hm⟩ := (qval_mem_forcing_l O hZF hU hay ht).mpr h
    obtain ⟨q, hq, s, b, hs, hqb, he⟩ := generic_pick_l hZF hU
      (wit_defined_l M hZF.1 false B R z a t) hp (fun q hq => by
        obtain ⟨r, s, b, hr, hs, hrb, he⟩ := hm.2 q hq
        exact ⟨r, hr, s, b, hs, hrb, he⟩)
    have hsN := (name_entry_l M (qval_name_l ht) hs).1
    obtain ⟨v, hv⟩ := name_value_l (R := R) (z := z) (U := U) hsN
    have hey := (qval_eq_l O hZF hU hay hv).mp ⟨q, hq, he⟩
    exact ⟨s, b, hs, hU.upward q b hq (name_entry_l M (qval_name_l ht) hs).2 hqb, hey.symm ▸ hv⟩
  · rintro ⟨s, b, hs, hb, hsv⟩
    have hbB := (hU.proper b hb).1
    exact (qval_mem_forcing_l O hZF hU hsv ht).mp
      ⟨b, hb, mem_force_entry_l O hZF hbB (qval_name_l hsv) hbB hs (O.refl b hbB)⟩

omit O hU in
theorem zf_name_exists_l : ∃ t, Name_d M B t := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact ⟨e, name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he⟩

abbrev extension_l (M : SetTheory.Structure.{u}) (hZF : M.Models ZF)
    (B R z : M.Domain) (U : M.Domain → Prop) : SetTheory.Structure.{u} where
  Domain := Name_quot_l M B R z U
  nonempty := (zf_name_exists_l (B := B) hZF).elim fun t ht => ⟨Quot.mk _ ⟨t, ht⟩⟩
  mem x y := x ∈ y

private theorem qwit_mem_l (k : Bool) {s t x y}
    (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y) :
    (∃ p, U p ∧ Wit_d M k B R z p s t) ↔ x ∈ y := by
  constructor
  · rintro ⟨p, hp, a, b, ha, hpb, he⟩
    have haN := (name_entry_l M (qval_name_l ht) ha).1
    obtain ⟨v, hv⟩ := name_value_l (R := R) (z := z) (U := U) haN
    have heq : x = v := by
      apply (qval_eq_l O hZF hU hs hv).mp
      refine ⟨p, hp, ?_⟩
      cases k
      · exact he
      · exact eq_force_symm_l hZF haN (qval_name_l hs) he
    exact (qval_mem_l O hZF hU ht).mpr ⟨a, b, ha,
      hU.upward p b hp (name_entry_l M (qval_name_l ht) ha).2 hpb, heq.symm ▸ hv⟩
  · intro h
    obtain ⟨p, hp, hm⟩ := (qval_mem_forcing_l O hZF hU hs ht).mpr h
    apply generic_pick_l hZF hU (wit_defined_l M hZF.1 k B R z s t) hp
    intro q hq
    obtain ⟨r, a, b, hr, ha, hrb, he⟩ := hm.2 q hq
    refine ⟨r, hr, a, b, ha, hrb, ?_⟩
    cases k
    · exact he
    · exact eq_force_symm_l hZF (qval_name_l hs) (name_entry_l M (qval_name_l ht) ha).1 he

/-- 原子等号的反例稠密集保证商中的外延性。 -/
theorem extension_ext_l : Extensional (extension_l M hZF B R z U) where
  eq_of_same_members := by
    intro x y hxy
    obtain ⟨s, hs, hsx⟩ := value_name_l x
    obtain ⟨t, ht, hty⟩ := value_name_l y
    apply (qval_eq_l O hZF hU hsx hty).mp
    apply Classical.byContradiction
    intro hn
    obtain ⟨p, hp, hn⟩ := (generic_decide_l O hZF hU (eq_force_defined_l M hZF.1 B R z s t)).elim
      (fun h => False.elim (hn h)) id
    obtain ⟨q, hq, hbad⟩ := generic_pick_l hZF hU (bad_defined_l M hZF.1 B R z s t) hp
      (neq_bad_dense_l M hZF hs ht hn)
    have no_wit (k : Bool) {d t} (hD : Name_d M B d) (hT : Name_d M B t)
        (hn : Neg_d M B R z (fun p => Wit_d M k B R z p d t) q)
        (hw : ∃ p, U p ∧ Wit_d M k B R z p d t) : False := by
      obtain ⟨p, hp, a, b, ha, hpb, he⟩ := hw
      obtain ⟨r, hr, hrq, hrp⟩ := hU.directed q p hq hp
      have hr' := hU.proper r hr
      apply hn r ⟨hr'.1, hr'.2, hrq⟩
      refine ⟨a, b, ha, O.trans r p b hr'.1 (hU.proper p hp).1
        (name_entry_l M hT ha).2 hrp hpb, ?_⟩
      cases k
      · exact eq_force_lower_l O hZF hD (name_entry_l M hT ha).1 p r
          (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ he
      · exact eq_force_lower_l O hZF (name_entry_l M hT ha).1 hD p r
          (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ he
    rcases hbad with ⟨d, b, hd, hqb, hn⟩ | ⟨d, b, hd, hqb, hn⟩
    · have hdN := (name_entry_l M hs hd).1
      obtain ⟨v, hv⟩ := name_value_l (R := R) (z := z) (U := U) hdN
      have hm := (qval_mem_l O hZF hU hsx).mpr
        ⟨d, b, hd, hU.upward q b hq (name_entry_l M hs hd).2 hqb, hv⟩
      exact no_wit false hdN ht hn ((qwit_mem_l O hZF hU false hv hty).mpr ((hxy v).mp hm))
    · have hdN := (name_entry_l M ht hd).1
      obtain ⟨v, hv⟩ := name_value_l (R := R) (z := z) (U := U) hdN
      have hm := (qval_mem_l O hZF hU hty).mpr
        ⟨d, b, hd, hU.upward q b hq (name_entry_l M ht hd).2 hqb, hv⟩
      exact no_wit true hdN hs hn ((qwit_mem_l O hZF hU true hv hsx).mpr ((hxy v).mpr hm))

end YesMetaZFC.Model.Forcing.Internal
