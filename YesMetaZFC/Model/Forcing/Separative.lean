import YesMetaZFC.Model.Forcing.Density

/-! # 相容性所确定的分离商

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
