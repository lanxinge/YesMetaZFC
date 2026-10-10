import YesMetaZFC.Model.Forcing.Order.Basic

/-! # 稠密性与保持不相容的稠密映射

稠密性要求实际加强，预稠密性只要求相容。映射不预设单射或反射原顺序，
从而允许分离商的规范映射。此层的集合族是宿主谓词，尚未断言地模型泛型性。
-/

namespace YesMetaZFC.Model.Forcing
universe u v w

namespace PO_pre
variable {P : Type u} (R : PO_pre P)

def Dense_below_l (D : P → Prop) (p : P) : Prop :=
  ∀ q, R.le q p → ∃ r, R.le r q ∧ D r

def Dense_l (D : P → Prop) : Prop := ∀ p, ∃ q, R.le q p ∧ D q

def Predense_below_l (D : P → Prop) (p : P) : Prop :=
  ∀ q, R.le q p → ∃ r, D r ∧ R.Cmp_l q r

def Predense_l (D : P → Prop) : Prop := ∀ p, ∃ q, D q ∧ R.Cmp_l p q

theorem dense_below_mono_l {D : P → Prop} {p q : P}
    (h : R.Dense_below_l D p) (k : R.le q p) : R.Dense_below_l D q :=
  fun r hr => h r (R.le_trans hr k)

theorem dense_iff_below_l (D : P → Prop) :
    R.Dense_l D ↔ ∀ p, R.Dense_below_l D p :=
  ⟨fun h _ q _ => h q, fun h p => h p p (R.le_refl p)⟩

/-- 预稠密的精确内容是向下闭包稠密；不附加开性。 -/
theorem predense_below_iff_l (D : P → Prop) (p : P) :
    R.Predense_below_l D p ↔ R.Dense_below_l (R.down_l D) p := by
  constructor
  · intro h q hq
    obtain ⟨r, hr, s, hs, ks⟩ := h q hq
    exact ⟨s, hs, r, hr, ks⟩
  · intro h q hq
    obtain ⟨r, hr, s, hs, ks⟩ := h q hq
    exact ⟨s, hs, r, hr, ks⟩

theorem predense_iff_l (D : P → Prop) :
    R.Predense_l D ↔ R.Dense_l (R.down_l D) := by
  constructor
  · intro h p
    obtain ⟨q, hq, r, hr, kr⟩ := h p
    exact ⟨r, hr, q, hq, kr⟩
  · intro h p
    obtain ⟨q, hq, r, hr, kr⟩ := h p
    exact ⟨r, hr, q, hq, kr⟩

theorem dense_inter_l {D E : P → Prop} (hD : R.Dense_l D)
    (hE : R.Dense_l E) (h : R.Lower_l D) : R.Dense_l (fun p => D p ∧ E p) := by
  intro p
  obtain ⟨q, hq, kq⟩ := hD p
  obtain ⟨r, hr, kr⟩ := hE q
  exact ⟨r, R.le_trans hr hq, h hr kq, kr⟩

/-- 有限初段的稠密开集可同时满足，用于可数多重下标的逐阶段调度。 -/
theorem dense_bounded_l (D : Nat → P → Prop) (hD : ∀ i, R.Dense_l (D i))
    (hO : ∀ i, R.Lower_l (D i)) (n : Nat) :
    R.Dense_l (fun p => ∀ i, i ≤ n → D i p) := by
  induction n with
  | zero =>
    intro p
    obtain ⟨q, hq, kq⟩ := hD 0 p
    exact ⟨q, hq, fun i hi => Nat.eq_zero_of_le_zero hi ▸ kq⟩
  | succ n ih =>
    intro p
    obtain ⟨q, hq, kq, lq⟩ := R.dense_inter_l ih (hD (n+1))
      (fun h k i hi => hO i h (k i hi)) p
    refine ⟨q, hq, fun i hi => ?_⟩
    rcases Nat.eq_or_lt_of_le hi with e | e
    · exact e ▸ lq
    · exact kq i (Nat.le_of_lt_succ e)

end PO_pre

structure PO_hom {P : Type u} {Q : Type v} (R : PO_pre P) (S : PO_pre Q) where
  map : P → Q
  mono : ∀ {p q}, R.le p q → S.le (map p) (map q)

structure PO_compat {P : Type u} {Q : Type v} (R : PO_pre P) (S : PO_pre Q)
    extends PO_hom R S where
  incompat : ∀ {p q}, R.Inc_l p q → S.Inc_l (map p) (map q)

structure PO_dense {P : Type u} {Q : Type v} (R : PO_pre P) (S : PO_pre Q)
    extends PO_compat R S where
  dense : ∀ q, ∃ p, S.le (map p) q

namespace PO_hom
variable {P : Type u} {Q : Type v} {R : PO_pre P} {S : PO_pre Q}

theorem cmp_map_l (e : PO_hom R S) {p q : P} :
    R.Cmp_l p q → S.Cmp_l (e.map p) (e.map q) :=
  fun ⟨r, h, k⟩ => ⟨e.map r, e.mono h, e.mono k⟩

theorem lower_preimage_l (e : PO_hom R S) {D : Q → Prop} (h : S.Lower_l D) :
    R.Lower_l (fun p => D (e.map p)) := fun k => h (e.mono k)

end PO_hom

namespace PO_compat
variable {P : Type u} {Q : Type v} {R : PO_pre P} {S : PO_pre Q}

/-- 相容性反射只消费不相容保持，不要求像稠密。 -/
theorem cmp_iff_l (e : PO_compat R S) (p q : P) :
    S.Cmp_l (e.map p) (e.map q) ↔ R.Cmp_l p q :=
  ⟨fun h => Classical.byContradiction (fun k => e.incompat k h), e.toPO_hom.cmp_map_l⟩

end PO_compat

namespace PO_dense
variable {P : Type u} {Q : Type v} {T : Type w}
  {R : PO_pre P} {S : PO_pre Q} {U : PO_pre T}

def id_l (R : PO_pre P) : PO_dense R R where
  map := id
  mono h := h
  incompat h := h
  dense p := ⟨p, R.le_refl p⟩

def comp_l (f : PO_dense S U) (e : PO_dense R S) : PO_dense R U where
  map p := f.map (e.map p)
  mono h := f.mono (e.mono h)
  incompat h := f.incompat (e.incompat h)
  dense r := by
    obtain ⟨q, hq⟩ := f.dense r
    obtain ⟨p, hp⟩ := e.dense q
    exact ⟨p, U.le_trans (f.mono hp) hq⟩

/-- 稠密开集可沿稠密映射回拉；只需一侧的向下封闭。 -/
theorem dense_preimage_l (e : PO_dense R S) {D : Q → Prop}
    (hD : S.Dense_l D) (h : S.Lower_l D) : R.Dense_l (fun p => D (e.map p)) := by
  intro p
  obtain ⟨q, hq, kq⟩ := hD (e.map p)
  obtain ⟨r, hr⟩ := e.dense q
  have hc : R.Cmp_l r p := (e.toPO_compat.cmp_iff_l r p).mp
    (S.cmp_of_le_l (S.le_trans hr hq))
  obtain ⟨s, hs, ks⟩ := hc
  exact ⟨s, ks, h (S.le_trans (e.mono hs) hr) kq⟩

/-- 先取像中的加强，再传送不相容分裂，故无原子性沿稠密映射保持。 -/
theorem atomless_l (e : PO_dense R S) (h : R.Atomless_l) : S.Atomless_l := by
  intro q
  obtain ⟨p, hp⟩ := e.dense q
  obtain ⟨r, s, hr, hs, k⟩ := h p
  exact ⟨e.map r, e.map s, S.le_trans (e.mono hr) hp,
    S.le_trans (e.mono hs) hp, e.incompat k⟩

end PO_dense
end YesMetaZFC.Model.Forcing
