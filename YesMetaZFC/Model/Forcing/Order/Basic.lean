import Init.Classical

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
