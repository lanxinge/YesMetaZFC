import YesMetaZFC.Model.Forcing.Internal.Forcing.Formula

/-! # 内部正则真值的逻辑运算

逻辑运算只在非零条件上使用正则性。全称量词的反向真值由内部可定义的反例
稠密集推出；不存在假定量词已经具有真值对应的字段。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

def Regular_d (M : SetTheory.Structure.{u}) (B R z : M.Domain) (P : M.Domain → Prop) : Prop :=
  Lower_d M B R z P ∧ ∀ p, M.mem p B → p ≠ z → Dense_d M B R z P p → P p

def Eval_d (M : SetTheory.Structure.{u}) (B R z : M.Domain) (U : M.Domain → Prop)
    (P : M.Domain → Prop) (Q : Prop) : Prop := Regular_d M B R z P ∧ ((∃ p, U p ∧ P p) ↔ Q)

theorem eval_congr_l {P : M.Domain → Prop} {Q S : Prop} (h : Eval_d M B R z U P Q)
    (e : Q ↔ S) : Eval_d M B R z U P S := ⟨h.1, h.2.trans e⟩

variable (O : Cond_order_d M B R z)
include O

theorem regular_neg_l {P : M.Domain → Prop} (h : Lower_d M B R z P) :
    Regular_d M B R z (Neg_d M B R z P) := by
  refine ⟨neg_lower_l O P, fun p _ _ hd q hq hP => ?_⟩
  obtain ⟨r, hr, hn⟩ := hd q hq
  exact hn r (below_refl_l O hr.1 hr.2.1) (h q r hq.1 hr hP)

omit O in
theorem regular_conj_l {P Q : M.Domain → Prop}
    (hP : Regular_d M B R z P) (hQ : Regular_d M B R z Q) :
    Regular_d M B R z (fun p => P p ∧ Q p) := by
  refine ⟨fun p q hp hq h => ⟨hP.1 p q hp hq h.1, hQ.1 p q hp hq h.2⟩, fun p hp hn hd => ?_⟩
  exact ⟨hP.2 p hp hn (fun q hq => (hd q hq).elim fun r h => ⟨r, h.1, h.2.1⟩),
    hQ.2 p hp hn (fun q hq => (hd q hq).elim fun r h => ⟨r, h.1, h.2.2⟩)⟩

/-- 隶属力迫在稠密成立处成立；该原子规则只需要条件属于条件集。 -/
theorem mem_force_dense_l {s t p} (hp : M.mem p B)
    (hd : Dense_d M B R z (fun q => Mem_force_d M B R z q s t) p) : Mem_force_d M B R z p s t := by
  refine ⟨hp, fun q hq => ?_⟩
  obtain ⟨r, hr, _, h⟩ := hd q hq
  obtain ⟨v, a, b, hv, ha, hvb, he⟩ := h r (below_refl_l O hr.1 hr.2.1)
  exact ⟨v, a, b, below_trans_l O hq.1 hv hr, ha, hvb, he⟩

theorem regular_mem_l (s t : M.Domain) :
    Regular_d M B R z (fun p => Mem_force_d M B R z p s t) := by
  constructor
  · intro p q hp hq h
    refine ⟨hq.1, fun r hr => ?_⟩
    exact h.2 r (below_trans_l O hp hr hq)
  · exact fun _ hp _ hd => mem_force_dense_l O hp hd

theorem regular_eq_l (hZF : M.Models ZF) {s t} (hs : Name_d M B s) (ht : Name_d M B t) :
    Regular_d M B R z (fun p => Eq_force_d M B R z p s t) :=
  ⟨eq_force_lower_l O hZF hs ht, fun _ hp _ h => eq_force_dense_l O hZF hs ht hp h⟩

omit O in
/-- 正条件没有正则性质时，可加强到该性质的加强否定。 -/
theorem regular_neg_witness_l {P : M.Domain → Prop} (h : Regular_d M B R z P)
    {p} (hp : M.mem p B) (hz : p ≠ z) (hn : ¬ P p) :
    ∃ q, Below_d M B R z q p ∧ Neg_d M B R z P q := by
  classical
  apply Classical.byContradiction
  intro he
  apply hn (h.2 p hp hz ?_)
  intro q hq
  by_cases hq' : ∃ r, Below_d M B R z r q ∧ P r
  · exact hq'
  · exact False.elim (he ⟨q, hq, fun r hr hP => hq' ⟨r, hr, hP⟩⟩)

variable (hZF : M.Models ZF) (hU : Generic_d M B R z U)
include hZF hU

theorem eval_neg_l {P : M.Domain → Prop} {Q : Prop} (hD : Defined_d M P)
    (h : Eval_d M B R z U P Q) : Eval_d M B R z U (Neg_d M B R z P) (¬ Q) :=
  ⟨regular_neg_l O h.1.1, (generic_neg_l O hZF hU hD h.1.1).trans (not_congr h.2)⟩

omit O hZF in
theorem eval_conj_l {P Q : M.Domain → Prop} {A C : Prop}
    (h : Eval_d M B R z U P A) (k : Eval_d M B R z U Q C) :
    Eval_d M B R z U (fun p => P p ∧ Q p) (A ∧ C) := by
  refine ⟨regular_conj_l h.1 k.1, ?_⟩
  constructor
  · rintro ⟨p, hp, hP, hQ⟩
    exact ⟨h.2.mp ⟨p, hp, hP⟩, k.2.mp ⟨p, hp, hQ⟩⟩
  · rintro ⟨hA, hC⟩
    obtain ⟨p, hp, hP⟩ := h.2.mpr hA
    obtain ⟨q, hq, hQ⟩ := k.2.mpr hC
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
    have hr' := hU.proper r hr
    exact ⟨r, hr, h.1.1 p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hP,
      k.1.1 q r (hU.proper q hq).1 ⟨hr'.1, hr'.2, hrq⟩ hQ⟩

/-- 对可定义名称族的全称量词取真值；反例见证集也必须具有实际公式。 -/
theorem eval_all_l {P : M.Domain → M.Domain → Prop} {Q : M.Domain → Prop}
    (hD : Defined_d M (fun p => ∀ x, Name_d M B x → P x p))
    (hC : Defined_d M (fun p => ∃ x, Name_d M B x ∧ Neg_d M B R z (P x) p))
    (h : ∀ x, Name_d M B x → Eval_d M B R z U (P x) (Q x)) :
    Eval_d M B R z U (fun p => ∀ x, Name_d M B x → P x p) (∀ x, Name_d M B x → Q x) := by
  refine ⟨⟨fun p q hp hq hP x hx => (h x hx).1.1 p q hp hq (hP x hx), ?_⟩, ?_⟩
  · intro p hp hn hd x hx
    exact (h x hx).1.2 p hp hn (fun q hq => (hd q hq).elim fun r hr => ⟨r, hr.1, hr.2 x hx⟩)
  · constructor
    · rintro ⟨p, hp, hP⟩ x hx
      exact (h x hx).2.mp ⟨p, hp, hP x hx⟩
    · intro hQ
      apply Classical.byContradiction
      intro hn
      obtain ⟨p, hp, hnP⟩ := (generic_decide_l O hZF hU hD).elim (fun h => False.elim (hn h)) id
      obtain ⟨q, hq, x, hx, hnX⟩ := generic_pick_l hZF hU hC hp (by
        intro q hq
        apply Classical.byContradiction
        intro hnC
        apply hnP q hq
        intro x hx
        apply (h x hx).1.2 q hq.1 hq.2.1
        intro r hr
        apply Classical.byContradiction
        intro hnX
        exact hnC ⟨r, hr, x, hx, fun s hs hP => hnX ⟨s, hs, hP⟩⟩)
      obtain ⟨r, hr, hP⟩ := (h x hx).2.mpr (hQ x hx)
      obtain ⟨s, hs, hsq, hsr⟩ := hU.directed q r hq hr
      have hs' := hU.proper s hs
      exact hnX s ⟨hs'.1, hs'.2, hsq⟩
        ((h x hx).1.1 r s (hU.proper r hr).1 ⟨hs'.1, hs'.2, hsr⟩ hP)

end YesMetaZFC.Model.Forcing.Internal
