import YesMetaZFC.Model.Forcing.Atomic.Equivalence
import YesMetaZFC.Model.Forcing.Atomic.Truth
import YesMetaZFC.SetTheory.MembershipInduction

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

/-! ## 泛型商中的基础公理

把实际归纳公式加强到两层成员，便可沿 Kuratowski 名称条目的三条成员边归纳。
这给出模型内名称集合的条目极小元；在可定义的可能成员集合中选取该极小元，
再由泛型性取得扩张中的基础公理见证。模型内部的基础公理不被提升为外部良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

private def member_schema_m {n} (φ : UnarySchema n) : UnarySchema n where
  body := Formula.forallMem .newest (pred_m φ (fun i => .bound ⟨i.val + 2, by omega⟩) .newest)

private theorem member_schema_l {n} (φ : UnarySchema n) (ρ : Env M n) (x : M.Domain) :
    (member_schema_m φ).denote ρ x ↔ ∀ y, M.mem y x → φ.denote ρ y := by
  simp only [UnarySchema.denote, member_schema_m, Formula.satisfies_forallMem_iff,
    pred_sat_l M]
  rfl

/-- 将 P 加强为 P∧∀a∈x,P(a)∧∀a∈x,∀b∈a,P(b)，再消费原成员归纳模式。 -/
theorem entry_ind_l (hI : Mem_ind_d M) {n} (φ : UnarySchema n) (ρ : Env M n)
    (h : ∀ t, (∀ s b, Entry_d M s b t → φ.denote ρ s) → φ.denote ρ t) : ∀ t, φ.denote ρ t := by
  let ψ : UnarySchema n := {
    body := .conj φ.body (.conj (member_schema_m φ).body (member_schema_m (member_schema_m φ)).body) }
  have he t : ψ.denote ρ t ↔ φ.denote ρ t ∧
      (∀ a, M.mem a t → φ.denote ρ a) ∧ ∀ a, M.mem a t → ∀ b, M.mem b a → φ.denote ρ b := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_conj_iff]
    change (φ.denote ρ t ∧ (member_schema_m φ).denote ρ t ∧
      (member_schema_m (member_schema_m φ)).denote ρ t) ↔ _
    simp only [member_schema_l]
    rfl
  have hall := hI ψ ρ (fun t ih => (he t).mpr (by
    refine ⟨h t (fun s b ⟨p, hp, hpt⟩ => ?_), ?_, ?_⟩
    · obtain ⟨a, hap, hsa⟩ := (kpair_union_l M hp s).mpr (Or.inl rfl)
      exact ((he p).mp (ih p hpt)).2.2 a hap s hsa
    · exact fun a ha => ((he a).mp (ih a ha)).1
    · exact fun a ha b hb => ((he a).mp (ih a ha)).2.1 b hb))
  exact fun t => ((he t).mp (hall t)).1

/-- 模型内非空集合对条目关系有极小元，无须该关系在宿主中良基。 -/
theorem entry_min_l (hZF : M.Models ZF) {D : M.Domain} (hn : ∃ t, M.mem t D) :
    ∃ t, M.mem t D ∧ ∀ s b, Entry_d M s b t → ¬ M.mem s D := by
  classical
  apply Classical.byContradiction
  intro h
  let φ : UnarySchema 1 := { body := .neg (.mem .newest (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => D, fun _ => D⟩
  have he t : φ.denote ρ t ↔ ¬ M.mem t D := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
    rfl
  have hall := entry_ind_l (ZF.mem_ind_l M hZF
    (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)))) φ ρ
    (fun t ih => (he t).mpr (fun ht => h ⟨t, ht, fun s b hs => (he s).mp (ih s b hs)⟩))
  obtain ⟨t, ht⟩ := hn
  exact (he t).mp (hall t) ht

def Min_name_d (M : SetTheory.Structure.{u}) (B R z p a t : M.Domain) : Prop :=
  Name_d M B a ∧ Mem_force_d M B R z p a t ∧
    ∀ s b, Entry_d M s b a → Neg_d M B R z (fun q => Mem_force_d M B R z q s t) p

def min_name_m {n} (B R z p a t : Term n) : Formula 1 n :=
  .conj (name_m B a) (.conj (mem_force_m B R z p a t)
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest a.weaken.weaken)
      (.forallE (.imp (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
        .newest p.weaken.weaken.weaken) (.neg (mem_force_m B.weaken.weaken.weaken
          R.weaken.weaken.weaken z.weaken.weaken.weaken .newest (.bound 2) t.weaken.weaken.weaken))))))))
derive_free_closed min_name_m

theorem min_name_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z p a t : Term n) :
    Formula.satisfies ρ (min_name_m B R z p a t) ↔
      Min_name_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (a.eval ρ) (t.eval ρ) := by
  simp only [min_name_m, Min_name_d, Neg_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff,
    name_sat_l M hE, mem_force_sat_l M hE, entry_sat_l M hE, below_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

variable {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
include O hZF hU

/-- 极小可能成员的可定义稠密集给出商模型的基础公理。 -/
theorem internal_foundation_l (X : (extension_l M hZF B R z U).Domain)
    (hn : ∃ x, (extension_l M hZF B R z U).mem x X) :
    ∃ x, (extension_l M hZF B R z U).mem x X ∧
      ∀ y, (extension_l M hZF B R z U).mem y X → ¬ (extension_l M hZF B R z U).mem y x := by
  obtain ⟨t, ⟨S, htS, hS⟩, ht⟩ := value_name_l X
  obtain ⟨x, hx⟩ := hn
  obtain ⟨s, b, hs, hb, _⟩ := (qval_mem_l O hZF hU ht).mp hx
  let δ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push t
  let φ : UnarySchema 4 := {
    body := .existsE (min_name_m (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest (.bound 2)) }
  have hd : Defined_d M (fun p => ∃ a, Min_name_d M B R z p a t) := by
    refine ⟨4, φ, δ, fun p => ?_⟩
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, min_name_sat_l hZF.1]
    rfl
  obtain ⟨p, hp, a, ha, ham, hmin⟩ := generic_pick_l hZF hU hd hb (by
    intro q hq
    let ρ := δ.push q
    let ψ : UnarySchema 5 := {
      body := .existsE (.conj (below_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 2))
        (mem_force_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1) (.bound 3))) }
    obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF ψ ρ S
    have hd a : M.mem a D ↔ M.mem a S ∧ ∃ r, Below_d M B R z r q ∧ Mem_force_d M B R z r a t := by
      rw [hD a]
      simp only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        below_sat_l M hZF.1, mem_force_sat_l M hZF.1]
      rfl
    obtain ⟨a, ha, hmin⟩ := entry_min_l hZF ⟨s, (hd s).mpr
      ⟨(supp_entry_l M hS htS hs).1, q, below_refl_l O hq.1 hq.2.1,
        mem_force_entry_l O hZF hq.1 ⟨S, (supp_entry_l M hS htS hs).1, hS⟩
          (hU.proper b hb).1 hs hq.2.2⟩⟩
    obtain ⟨haS, r, hr, ham⟩ := (hd a).mp ha
    refine ⟨r, hr, a, ⟨S, haS, hS⟩, ham, fun c d hcd v hv hm => ?_⟩
    exact hmin c d hcd ((hd c).mpr ⟨(supp_entry_l M hS haS hcd).1,
      v, below_trans_l O hq.1 hv hr, hm⟩))
  obtain ⟨A, hA⟩ := name_value_l (R := R) (z := z) (U := U) ha
  refine ⟨A, (qval_mem_forcing_l O hZF hU hA ht).mp ⟨p, hp, ham⟩, fun y hy hya => ?_⟩
  obtain ⟨c, d, hcd, _, hcy⟩ := (qval_mem_l O hZF hU hA).mp hya
  obtain ⟨q, hq, hqt⟩ := (qval_mem_forcing_l O hZF hU hcy ht).mpr hy
  obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
  have hr' := hU.proper r hr
  exact hmin c d hcd r ⟨hr'.1, hr'.2, hrp⟩ ⟨hr'.1,
    fun v hv => hqt.2 v (below_trans_l O hqt.1 hv ⟨hr'.1, hr'.2, hrq⟩)⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 泛型扩张在地模型参数上的同构及合成 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v w k l

/-- 带指定参数关系的成员同构；双向对应使取逆和合成保留同一地模型。 -/
def Miso_over_d {A : Sort k} (M : Structure.{u}) (N : Structure.{v})
    (l : A → M.Domain → Prop) (r : A → N.Domain → Prop) : Prop :=
  ∃ f : M.Domain → N.Domain, (∀ a b, M.mem a b ↔ N.mem (f a) (f b)) ∧
    Function.Injective f ∧ Function.Surjective f ∧ ∀ x a, l x a ↔ r x (f a)

theorem Miso_over_d.symm_l {A : Sort k} {M : Structure.{u}} {N : Structure.{v}}
    {l : A → M.Domain → Prop} {r : A → N.Domain → Prop}
    (h : Miso_over_d M N l r) : Miso_over_d N M r l := by
  obtain ⟨f,mem,inj,onto,over⟩ := h
  obtain ⟨g,right⟩ := Classical.axiomOfChoice onto
  have left a : g (f a) = a := inj (right (f a))
  refine ⟨g,fun a b => ?_,fun a b eq => (right a).symm.trans ((congrArg f eq).trans (right b)),
    fun a => ⟨f a,left a⟩,fun x a => ?_⟩
  · exact ((mem (g a) (g b)).trans (by rw [right,right])).symm
  · exact ((over x (g a)).trans (by rw [right])).symm

theorem Miso_over_d.trans_l {A : Sort k} {M : Structure.{u}} {N : Structure.{v}} {K : Structure.{w}}
    {l : A → M.Domain → Prop} {r : A → N.Domain → Prop} {s : A → K.Domain → Prop}
    (h : Miso_over_d M N l r) (k : Miso_over_d N K r s) : Miso_over_d M K l s := by
  obtain ⟨f,hf,fi,fs,fr⟩ := h
  obtain ⟨g,hg,gi,gs,gr⟩ := k
  exact ⟨g ∘ f,fun a b => (hf a b).trans (hg (f a) (f b)),gi.comp fi,gs.comp fs,
    fun x a => (fr x a).trans (gr x (f a))⟩

/-- 同一参数族先经既有映射改指标，交换方程逐项保持。 -/
theorem Miso_over_d.comp_l {A : Sort k} {D : Sort l} {M : Structure.{u}} {N : Structure.{v}}
    {l : A → M.Domain → Prop} {r : A → N.Domain → Prop}
    (h : Miso_over_d M N l r) (j : D → A) :
    Miso_over_d M N (fun x => l (j x)) (fun x => r (j x)) := by
  obtain ⟨f,mem,inj,onto,over⟩ := h
  exact ⟨f,mem,inj,onto,fun x => over (j x)⟩

end YesMetaZFC.Model.Forcing.Internal
