import YesMetaZFC.Model.Forcing.Separative
import YesMetaZFC.Model.Boolean.Algebra

/-! # 布尔代数的非零条件

任意实际布尔代数给出分离偏序；相容性恰是交非零。这里只消费有限布尔运算，
不要求完备性，也不把零元放入条件域。`prop_algebra` 等已有代数可直接作为输入。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean
universe u
variable {B : Type u} (𝔹 : BA_alg B)

abbrev Pos_l := {b : B // b ≠ 𝔹.bot}

def positive_order_l : PO_ord (Pos_l 𝔹) where
  le p q := 𝔹.le p.1 q.1
  le_refl p := 𝔹.le_refl p.1
  le_trans := 𝔹.le_trans
  le_antisymm h k := Subtype.ext (𝔹.le_antisymm h k)

/-- 非零条件域非空恰要求代数非平凡，序论构造本身无需这一假设。 -/
theorem positive_nonempty_l : Nonempty (Pos_l 𝔹) ↔ 𝔹.bot ≠ 𝔹.top := by
  constructor
  · rintro ⟨p⟩ h
    have hp := 𝔹.le_top p.1
    rw [← h] at hp
    exact p.2 (𝔹.le_antisymm hp (𝔹.bot_le _))
  · intro h
    exact ⟨⟨𝔹.top, fun k => h k.symm⟩⟩

@[simp] theorem positive_cmp_l (p q : Pos_l 𝔹) :
    (positive_order_l 𝔹).toPO_pre.Cmp_l p q ↔ 𝔹.meet p.1 q.1 ≠ 𝔹.bot := by
  constructor
  · rintro ⟨r, h, k⟩ e
    have hz := 𝔹.le_meet h k
    rw [e] at hz
    exact r.2 (𝔹.le_antisymm hz (𝔹.bot_le r.1))
  · intro h
    exact ⟨⟨𝔹.meet p.1 q.1, h⟩, 𝔹.meet_le_left _ _, 𝔹.meet_le_right _ _⟩

/-- 不满足 `p ≤ q` 时，差 `p ∧ ¬q` 直接给出非零的不相容加强。 -/
theorem positive_separative_l : (positive_order_l 𝔹).toPO_pre.Separative_l := by
  intro p q h
  have hz : 𝔹.meet p.1 (𝔹.neg q.1) ≠ 𝔹.bot := by
    intro k
    apply h ((𝔹.le_iff_meet_neg _ _).mpr ?_)
    rw [k]
    exact 𝔹.le_refl _
  refine ⟨⟨𝔹.meet p.1 (𝔹.neg q.1), hz⟩, 𝔹.meet_le_left _ _, ?_⟩
  rintro ⟨r, hr, kr⟩
  have hn := 𝔹.le_trans hr (𝔹.meet_le_right p.1 (𝔹.neg q.1))
  have hb := 𝔹.le_meet kr hn
  rw [𝔹.meet_neg] at hb
  exact r.2 (𝔹.le_antisymm hb (𝔹.bot_le _))

end YesMetaZFC.Model.Forcing
