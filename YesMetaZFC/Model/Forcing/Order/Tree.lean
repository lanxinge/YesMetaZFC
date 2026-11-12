import Init.Classical
import Init.Data.List.Sublist

/-! # 力迫条件的预序

`R.le p q` 表示 `p` 加强 `q`。基本层只要求自反和传递；非空性、最大条件、
反对称性及分离性各自独立。条件域保持原 universe，不选取任何代表元。
-/

namespace YesMetaZFC.Model.Forcing
universe u v

structure PO_pre (P : Type u) where
  le : P → P → Prop
  le_refl : ∀ p, le p p
  le_trans : ∀ {p q r}, le p q → le q r → le p r

structure PO_ord (P : Type u) extends PO_pre P where
  le_antisymm : ∀ {p q}, le p q → le q p → p = q

namespace PO_pre
variable {P : Type u} (R : PO_pre P)

/-- 相容恰指具有共同加强，不要求交运算。 -/
def Cmp_l (p q : P) : Prop := ∃ r, R.le r p ∧ R.le r q

def Inc_l (p q : P) : Prop := ¬ R.Cmp_l p q

def Lower_l (D : P → Prop) : Prop := ∀ {p q}, R.le p q → D q → D p

/-- 集合的向下闭包；后续预稠密与稠密的比较直接消费它。 -/
def down_l (D : P → Prop) (p : P) : Prop := ∃ q, D q ∧ R.le p q

def Antichain_l (A : P → Prop) : Prop :=
  ∀ {p q}, A p → A q → R.Cmp_l p q → p = q

def Atomless_l : Prop := ∀ p, ∃ q r, R.le q p ∧ R.le r p ∧ R.Inc_l q r

def Separative_l : Prop := ∀ p q, ¬ R.le p q → ∃ r, R.le r p ∧ R.Inc_l r q

@[simp] theorem cmp_refl_l (p : P) : R.Cmp_l p p := ⟨p, R.le_refl p, R.le_refl p⟩

theorem cmp_symm_l {p q : P} : R.Cmp_l p q → R.Cmp_l q p :=
  fun ⟨r, h, k⟩ => ⟨r, k, h⟩

theorem cmp_of_le_l {p q : P} (h : R.le p q) : R.Cmp_l p q :=
  ⟨p, R.le_refl p, h⟩

theorem cmp_mono_l {p q r s : P} (h : R.le p r) (k : R.le q s) :
    R.Cmp_l p q → R.Cmp_l r s :=
  fun ⟨t, ht, kt⟩ => ⟨t, R.le_trans ht h, R.le_trans kt k⟩

theorem inc_mono_l {p q r s : P} (h : R.le p r) (k : R.le q s)
    (i : R.Inc_l r s) : R.Inc_l p q := fun c => i (R.cmp_mono_l h k c)

theorem down_lower_l (D : P → Prop) : R.Lower_l (R.down_l D) :=
  fun h ⟨r, hr, k⟩ => ⟨r, hr, R.le_trans h k⟩

theorem mem_down_l {D : P → Prop} {p : P} (h : D p) : R.down_l D p :=
  ⟨p, h, R.le_refl p⟩

theorem down_iff_l {D : P → Prop} (h : R.Lower_l D) (p : P) :
    R.down_l D p ↔ D p :=
  ⟨fun ⟨_, k, hq⟩ => h hq k, R.mem_down_l⟩

/-- 限制到一个条件以下，保留原来的加强关系。 -/
def below_l (p : P) : PO_pre {q : P // R.le q p} where
  le q r := R.le q.1 r.1
  le_refl q := R.le_refl q.1
  le_trans := R.le_trans

end PO_pre
end YesMetaZFC.Model.Forcing

/-! ## 稠密性与保持不相容的稠密映射

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

/-! ## 相容性所确定的分离商

先按相容条件的包含比较原条件，再对双向比较取商。商的顺序、规范映射、
稠密性及相容性保持全部实际构造；分离性的经典论证只位于 Prop。
-/

namespace YesMetaZFC.Model.Forcing.PO_pre
universe u
variable {P : Type u} (R : PO_pre P)

def Sep_le_l (p q : P) : Prop := ∀ r, R.Cmp_l r p → R.Cmp_l r q

theorem sep_refl_l (p : P) : R.Sep_le_l p p := fun _ h => h

theorem sep_trans_l {p q r : P} (h : R.Sep_le_l p q) (k : R.Sep_le_l q r) :
    R.Sep_le_l p r := fun s hs => k s (h s hs)

theorem sep_of_le_l {p q : P} (h : R.le p q) : R.Sep_le_l p q :=
  fun r k => R.cmp_mono_l (R.le_refl r) h k

/-- 分离预序也可由每个加强仍与目标相容来判定。 -/
theorem sep_le_iff_l (p q : P) :
    R.Sep_le_l p q ↔ ∀ r, R.le r p → R.Cmp_l r q := by
  constructor
  · exact fun h r hr => h r (R.cmp_of_le_l hr)
  · intro h r ⟨s, hs, ks⟩
    exact R.cmp_mono_l hs (R.le_refl q) (h s ks)

def sep_pre_l : PO_pre P where
  le := R.Sep_le_l
  le_refl := R.sep_refl_l
  le_trans := R.sep_trans_l

theorem sep_pre_cmp_l (p q : P) : R.sep_pre_l.Cmp_l p q ↔ R.Cmp_l p q := by
  constructor
  · rintro ⟨r, h, k⟩
    exact R.cmp_symm_l (h q (R.cmp_symm_l (k r (R.cmp_refl_l r))))
  · rintro ⟨r, h, k⟩
    exact ⟨r, R.sep_of_le_l h, R.sep_of_le_l k⟩

theorem separative_iff_l :
    R.Separative_l ↔ ∀ p q, R.Sep_le_l p q → R.le p q := by
  constructor
  · intro h p q k
    apply Classical.byContradiction
    intro n
    obtain ⟨r, hr, kr⟩ := h p q n
    exact kr (k r (R.cmp_of_le_l hr))
  · intro h p q n
    apply Classical.byContradiction
    intro k
    apply n (h p q ((R.sep_le_iff_l p q).mpr ?_))
    intro r hr
    exact Classical.byContradiction (fun kr => k ⟨r, hr, kr⟩)

def sep_setoid_l : Setoid P where
  r p q := R.Sep_le_l p q ∧ R.Sep_le_l q p
  iseqv := ⟨fun p => ⟨R.sep_refl_l p, R.sep_refl_l p⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h k => ⟨R.sep_trans_l h.1 k.1, R.sep_trans_l k.2 h.2⟩⟩

abbrev Sep_l := Quotient R.sep_setoid_l

def sep_mk_l (p : P) : R.Sep_l := Quotient.mk R.sep_setoid_l p

/-- 商比较直接消去两个商参数，不选择代表元函数。 -/
def sep_order_l : PO_ord R.Sep_l where
  le := Quotient.lift₂ R.Sep_le_l (fun _ _ _ _ h k => propext
    ⟨fun t => R.sep_trans_l h.2 (R.sep_trans_l t k.1),
     fun t => R.sep_trans_l h.1 (R.sep_trans_l t k.2)⟩)
  le_refl p := Quotient.inductionOn p (R.sep_refl_l)
  le_trans := by
    intro p q r
    refine Quotient.inductionOn₃ p q r ?_
    exact fun _ _ _ h k => R.sep_trans_l h k
  le_antisymm := by
    intro p q
    refine Quotient.inductionOn₂ p q ?_
    exact fun _ _ h k => Quotient.sound ⟨h, k⟩

@[simp] theorem sep_mk_le_l (p q : P) :
    R.sep_order_l.le (R.sep_mk_l p) (R.sep_mk_l q) ↔ R.Sep_le_l p q := Iff.rfl

@[simp] theorem sep_mk_cmp_l (p q : P) :
    R.sep_order_l.toPO_pre.Cmp_l (R.sep_mk_l p) (R.sep_mk_l q) ↔ R.Cmp_l p q := by
  constructor
  · rintro ⟨r, h, k⟩
    induction r using Quotient.inductionOn with
    | _ r => exact (R.sep_pre_cmp_l p q).mp ⟨r, h, k⟩
  · rintro ⟨r, h, k⟩
    exact ⟨R.sep_mk_l r, R.sep_of_le_l h, R.sep_of_le_l k⟩

theorem sep_separative_l : R.sep_order_l.toPO_pre.Separative_l := by
  apply R.sep_order_l.toPO_pre.separative_iff_l.mpr
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro p q h r hr
  exact (R.sep_mk_cmp_l r q).mp (h (R.sep_mk_l r) ((R.sep_mk_cmp_l r p).mpr hr))

/-- 原预序到分离偏序的实际稠密映射；不要求原预序分离或反对称。 -/
def sep_map_l : PO_dense R R.sep_order_l.toPO_pre where
  map := R.sep_mk_l
  mono := R.sep_of_le_l
  incompat h k := h ((R.sep_mk_cmp_l _ _).mp k)
  dense q := Quotient.inductionOn q (fun p => ⟨p, R.sep_refl_l p⟩)

end YesMetaZFC.Model.Forcing.PO_pre

/-! ## 有限序列条件

任意字母表上的有限序列按延长排序；二元情形是添加一个 Cohen 实数的条件树。
本层实际证明树的相容性、任意长度的稠密性及二元树的无原子性，尚未构造泛型实数。
-/

namespace YesMetaZFC.Model.Forcing
universe u

def tree_order_l (A : Type u) : PO_ord (List A) where
  le p q := q <+: p
  le_refl := List.prefix_refl
  le_trans h k := k.trans h
  le_antisymm h k := k.eq_of_length_le h.length_le

@[simp] theorem tree_cmp_l {A : Type u} (p q : List A) :
    (tree_order_l A).toPO_pre.Cmp_l p q ↔ p <+: q ∨ q <+: p := by
  constructor
  · rintro ⟨r, h, k⟩
    exact List.prefix_or_prefix_of_prefix h k
  · rintro (h | h)
    · exact ⟨q, h, List.prefix_refl q⟩
    · exact ⟨p, List.prefix_refl p, h⟩

/-- 延长到任意给定有限长度，只需给定一个实际字母。 -/
theorem tree_length_dense_l {A : Type u} (a : A) (n : Nat) :
    (tree_order_l A).toPO_pre.Dense_l (fun p => n ≤ p.length) := by
  intro p
  refine ⟨p ++ List.replicate n a, List.prefix_append _ _, ?_⟩
  simp only [List.length_append, List.length_replicate]
  exact Nat.le_add_left _ _

theorem binary_split_l (p : List Bool) :
    (tree_order_l Bool).toPO_pre.Inc_l (p ++ [false]) (p ++ [true]) := by
  intro h
  have hn : (p ++ [false]).length = (p ++ [true]).length := by simp
  have he : p ++ [false] = p ++ [true] :=
    ((tree_cmp_l _ _).mp h).elim (fun k => k.eq_of_length hn)
      (fun k => (k.eq_of_length hn.symm).symm)
  have k : [false] = [true] := List.append_cancel_left he
  cases k

theorem binary_atomless_l : (tree_order_l Bool).toPO_pre.Atomless_l :=
  fun p => ⟨p ++ [false], p ++ [true], List.prefix_append _ _, List.prefix_append _ _,
    binary_split_l p⟩

theorem binary_antichain_l (p : List Bool) :
    (tree_order_l Bool).toPO_pre.Antichain_l
      (fun q => q = p ++ [false] ∨ q = p ++ [true]) := by
  intro q r h k c
  rcases h with rfl | rfl <;> rcases k with rfl | rfl
  · rfl
  · exact False.elim (binary_split_l p c)
  · exact False.elim (binary_split_l p ((tree_order_l Bool).toPO_pre.cmp_symm_l c))
  · rfl

end YesMetaZFC.Model.Forcing
