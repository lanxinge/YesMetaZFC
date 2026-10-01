import YesMetaZFC.Model.Forcing.Boolean.RegularOpen
import YesMetaZFC.Model.Forcing.Boolean.Conditions

/-! # 条件到正则开代数的规范稠密映射

条件映为其主向下集的正则化。包含关系精确恢复分离预序，相容性由非零交识别。
映射和非零性直接构造；像稠密的经典证明只在 Prop 内从非空谓词取得存在见证。
-/

namespace YesMetaZFC.Model.Forcing
namespace PO_pre
universe u
variable {P : Type u} (R : PO_pre P)

def ro_principal_l (p : P) : R.RO_l := R.ro_regularize_l (fun q => R.le q p)

theorem ro_principal_self_l (p : P) : (R.ro_principal_l p).mem p :=
  R.ro_reg_intro_l (fun h k => R.le_trans h k) (R.le_refl p)

/-- 主正则开集以下的比较归结为一个条件的成员判断。 -/
@[simp] theorem ro_principal_le_iff_l (p : P) (U : R.RO_l) :
    R.ro_algebra_l.le (R.ro_principal_l p) U ↔ U.mem p :=
  ⟨fun h => h p (R.ro_principal_self_l p),
   fun h => R.ro_regularize_le_l U (fun _ k => U.lower k h)⟩

theorem ro_principal_mono_l {p q : P} (h : R.le p q) :
    R.ro_algebra_l.le (R.ro_principal_l p) (R.ro_principal_l q) :=
  R.ro_reg_mono_l (fun _ k => R.le_trans k h)

theorem ro_principal_mem_l (p q : P) :
    (R.ro_principal_l p).mem q ↔ R.Sep_le_l q p :=
  (R.ro_reg_dense_iff_l _ _).trans (R.sep_le_iff_l q p).symm

theorem ro_principal_order_l (p q : P) :
    R.ro_algebra_l.le (R.ro_principal_l p) (R.ro_principal_l q) ↔ R.Sep_le_l p q :=
  (R.ro_principal_le_iff_l p _).trans (R.ro_principal_mem_l q p)

theorem ro_order_iff_l (h : R.Separative_l) (p q : P) :
    R.ro_algebra_l.le (R.ro_principal_l p) (R.ro_principal_l q) ↔ R.le p q :=
  (R.ro_principal_order_l p q).trans
    ⟨(R.separative_iff_l.mp h) p q, R.sep_of_le_l⟩

theorem ro_principal_ne_bot_l (p : P) : R.ro_principal_l p ≠ R.ro_algebra_l.bot := by
  intro h
  have k := R.ro_principal_self_l p
  rw [h] at k
  exact k

/-- 两个不相容主向下集的正则化仍不相交；此方向不使用排中律。 -/
theorem ro_meet_eq_bot_l {p q : P} (h : R.Inc_l p q) :
    R.ro_algebra_l.meet (R.ro_principal_l p) (R.ro_principal_l q) =
      R.ro_algebra_l.bot := by
  apply RO_l.ext_l R
  intro r
  constructor
  · rintro ⟨hp, hq⟩
    exact hp r (R.le_refl r) (fun s hs hsp =>
      hq s hs (fun t ht htq => h ⟨t, R.le_trans ht hsp, htq⟩))
  · exact False.elim

def ro_condition_l (p : P) : Pos_l R.ro_algebra_l.toBA_alg :=
  ⟨R.ro_principal_l p, R.ro_principal_ne_bot_l p⟩

def ro_map_l : PO_compat R (positive_order_l R.ro_algebra_l.toBA_alg).toPO_pre where
  map := R.ro_condition_l
  mono := R.ro_principal_mono_l
  incompat h k := ((positive_cmp_l R.ro_algebra_l.toBA_alg _ _).mp k)
    (R.ro_meet_eq_bot_l h)

/-- 非零正则开集含有某个主正则开集；见证只在存在命题中取得。 -/
def ro_dense_l : PO_dense R (positive_order_l R.ro_algebra_l.toBA_alg).toPO_pre where
  toPO_compat := R.ro_map_l
  dense U := by
    have he : ∃ p, U.1.mem p := by
      apply Classical.byContradiction
      intro n
      apply U.2
      exact RO_l.ext_l R (fun p => ⟨fun h => n ⟨p, h⟩, False.elim⟩)
    obtain ⟨p, hp⟩ := he
    exact ⟨p, (R.ro_principal_le_iff_l p U.1).mpr hp⟩

theorem ro_cmp_iff_l (p q : P) :
    R.ro_algebra_l.meet (R.ro_principal_l p) (R.ro_principal_l q) ≠
      R.ro_algebra_l.bot ↔ R.Cmp_l p q :=
  (positive_cmp_l R.ro_algebra_l.toBA_alg _ _).symm.trans (R.ro_map_l.cmp_iff_l p q)

theorem ro_nontrivial_l : R.ro_algebra_l.bot ≠ R.ro_algebra_l.top ↔ Nonempty P := by
  constructor
  · intro h
    obtain ⟨U⟩ := (positive_nonempty_l R.ro_algebra_l.toBA_alg).mpr h
    obtain ⟨p, _⟩ := R.ro_dense_l.dense U
    exact ⟨p⟩
  · rintro ⟨p⟩ h
    have hp := R.ro_algebra_l.le_top (R.ro_principal_l p)
    rw [← h] at hp
    exact R.ro_principal_ne_bot_l p
      (R.ro_algebra_l.le_antisymm hp (R.ro_algebra_l.bot_le _))

end PO_pre

/-- 只有需要单射性时，才同时消费分离性与原偏序的反对称性。 -/
theorem PO_ord.ro_injective_l {P : Type u} (R : PO_ord P)
    (h : R.toPO_pre.Separative_l) {p q : P}
    (e : R.toPO_pre.ro_principal_l p = R.toPO_pre.ro_principal_l q) : p = q := by
  apply R.le_antisymm
  · apply (R.toPO_pre.ro_order_iff_l h p q).mp
    rw [e]
    exact R.toPO_pre.ro_algebra_l.le_refl _
  · apply (R.toPO_pre.ro_order_iff_l h q p).mp
    rw [e]
    exact R.toPO_pre.ro_algebra_l.le_refl _

end YesMetaZFC.Model.Forcing
