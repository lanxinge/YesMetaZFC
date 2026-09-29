import YesMetaZFC.Model.Forcing.Density
import YesMetaZFC.Model.Boolean.Algebra

/-! # 预序上的正则开完备布尔代数

向下集的伪补表示其下没有成员的条件；正则性由双重伪补的不动点刻画。
交与蕴含直接按谓词定义，上确界正则化集合并。所有运算及代数律均不使用选择；
载体 `RO_l` 与原条件域处于同一 universe，也不要求条件域非空或分离。
-/

namespace YesMetaZFC.Model.Forcing.PO_pre
open Boolean
universe u
variable {P : Type u} (R : PO_pre P)

def ro_neg_l (D : P → Prop) (p : P) : Prop := ∀ q, R.le q p → ¬ D q

def ro_reg_l (D : P → Prop) : P → Prop := R.ro_neg_l (R.ro_neg_l D)

theorem ro_neg_lower_l (D : P → Prop) : R.Lower_l (R.ro_neg_l D) :=
  fun h k r hr => k r (R.le_trans hr h)

theorem ro_neg_antitone_l {D E : P → Prop} (h : ∀ p, D p → E p) :
    ∀ p, R.ro_neg_l E p → R.ro_neg_l D p :=
  fun _ k q hq hd => k q hq (h q hd)

theorem ro_reg_mono_l {D E : P → Prop} (h : ∀ p, D p → E p) :
    ∀ p, R.ro_reg_l D p → R.ro_reg_l E p :=
  R.ro_neg_antitone_l (R.ro_neg_antitone_l h)

theorem ro_reg_lower_l (D : P → Prop) : R.Lower_l (R.ro_reg_l D) :=
  R.ro_neg_lower_l (R.ro_neg_l D)

/-- 正则化扩张向下集；对任意谓词不作这一断言。 -/
theorem ro_reg_intro_l {D : P → Prop} (hD : R.Lower_l D) {p : P} (h : D p) :
    R.ro_reg_l D p := fun q hq k => k q (R.le_refl q) (hD hq h)

theorem ro_reg_idem_l (D : P → Prop) (p : P) :
    R.ro_reg_l (R.ro_reg_l D) p ↔ R.ro_reg_l D p :=
  ⟨fun h q hq k => h q hq (R.ro_reg_intro_l (R.ro_neg_lower_l D) k),
   R.ro_reg_intro_l (R.ro_reg_lower_l D)⟩

structure RO_l where
  mem : P → Prop
  lower : R.Lower_l mem
  regular : ∀ p, R.ro_reg_l mem p → mem p

theorem RO_l.ext_l {U V : R.RO_l} (h : ∀ p, U.mem p ↔ V.mem p) : U = V := by
  cases U; cases V
  congr
  exact funext (fun p => propext (h p))

@[simp] theorem ro_regular_iff_l (U : R.RO_l) (p : P) :
    R.ro_reg_l U.mem p ↔ U.mem p :=
  ⟨U.regular p, R.ro_reg_intro_l U.lower⟩

def ro_regularize_l (D : P → Prop) : R.RO_l where
  mem := R.ro_reg_l D
  lower := R.ro_reg_lower_l D
  regular p := (R.ro_reg_idem_l D p).mp

/-- 包含原谓词的正则开集也包含其正则化。 -/
theorem ro_regularize_le_l {D : P → Prop} (U : R.RO_l) (h : ∀ p, D p → U.mem p) :
    ∀ p, (R.ro_regularize_l D).mem p → U.mem p :=
  fun p k => U.regular p (R.ro_reg_mono_l h p k)

def ro_bot_l : R.RO_l where
  mem _ := False
  lower _ h := h
  regular p h := h p (R.le_refl p) (fun _ _ k => k)

def ro_meet_l (U V : R.RO_l) : R.RO_l where
  mem p := U.mem p ∧ V.mem p
  lower h k := ⟨U.lower h k.1, V.lower h k.2⟩
  regular p h :=
    ⟨U.regular p (R.ro_reg_mono_l (fun _ k => k.1) p h),
     V.regular p (R.ro_reg_mono_l (fun _ k => k.2) p h)⟩

/-- 剩余运算沿所有加强解释；目标正则性保证结果正则。 -/
def ro_imp_l (U V : R.RO_l) : R.RO_l where
  mem p := ∀ q, R.le q p → U.mem q → V.mem q
  lower h k r hr := k r (R.le_trans hr h)
  regular _ h q hq hu := V.regular q (fun r hr n =>
    h r (R.le_trans hr hq) (fun s hs hi =>
      n s hs (hi s (R.le_refl s) (U.lower (R.le_trans hs hr) hu))))

def ro_sup_l (S : R.RO_l → Prop) : R.RO_l :=
  R.ro_regularize_l (fun p => ∃ U, S U ∧ U.mem p)

theorem ro_sup_le_iff_l (S : R.RO_l → Prop) (U : R.RO_l) :
    (∀ p, (R.ro_sup_l S).mem p → U.mem p) ↔
      ∀ V, S V → ∀ p, V.mem p → U.mem p := by
  constructor
  · intro h V hV p hp
    apply h p
    exact R.ro_reg_intro_l
      (fun k ⟨W, hW, hw⟩ => ⟨W, hW, W.lower k hw⟩) ⟨V, hV, hp⟩
  · intro h
    exact R.ro_regularize_le_l U (fun p ⟨V, hV, hp⟩ => h V hV p hp)

/-- 任意预序的正则开完备布尔代数；所有字段由上面的实际运算与证明填充。 -/
def ro_algebra_l : CB_alg R.RO_l where
  le U V := ∀ p, U.mem p → V.mem p
  bot := R.ro_bot_l
  le_refl _ _ := id
  le_trans h k p hp := k p (h p hp)
  le_antisymm h k := RO_l.ext_l R (fun p => ⟨h p, k p⟩)
  bot_le _ _ h := False.elim h
  meet := R.ro_meet_l
  imp := R.ro_imp_l
  le_meet_iff _ _ _ := ⟨fun h => ⟨fun p hp => (h p hp).1,
    fun p hp => (h p hp).2⟩, fun ⟨h, k⟩ p hp => ⟨h p hp, k p hp⟩⟩
  le_imp_iff U _ _ := ⟨fun h p hp => h p hp.1 p (R.le_refl p) hp.2,
    fun h _ hp q hq k => h q ⟨U.lower hq hp, k⟩⟩
  double_neg U := RO_l.ext_l R (fun p => R.ro_regular_iff_l U p)
  sup := R.ro_sup_l
  sup_le_iff := R.ro_sup_le_iff_l

/-- 与已有正向稠密量词的对应；经典反证仅用于命题中的见证存在性。 -/
theorem ro_reg_dense_iff_l (D : P → Prop) (p : P) :
    R.ro_reg_l D p ↔ R.Dense_below_l D p := by
  constructor
  · intro h q hq
    apply Classical.byContradiction
    intro n
    exact h q hq (fun r hr hd => n ⟨r, hr, hd⟩)
  · intro h q hq n
    obtain ⟨r, hr, hd⟩ := h q hq
    exact n r hr hd

end YesMetaZFC.Model.Forcing.PO_pre
