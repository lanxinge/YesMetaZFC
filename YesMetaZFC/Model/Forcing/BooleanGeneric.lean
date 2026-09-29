import YesMetaZFC.Model.Forcing.Boolean
import YesMetaZFC.Model.Forcing.Generic
import YesMetaZFC.Model.Boolean.Ultrafilter

/-! # 布尔滤子的局部泛型性

上确界见证稠密集由布尔运算直接给出。遇到这一稠密集，才可从被滤子接受的
无限析取中取出一项；普通超滤子的二择性质本身不保证这一点。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean
universe u v
variable {B : Type u}

def BF_meets_l {𝔹 : BA_alg B} (U : Filter_l 𝔹) (D : Pos_l 𝔹 → Prop) : Prop :=
  ∃ p, U.mem p.1 ∧ D p

/-- 非零条件滤子的布尔向上闭包，构造不选取任何条件。 -/
def boolean_filter_l (𝔹 : BA_alg B) (G : PO_filter (positive_order_l 𝔹).toPO_pre) :
    Filter_l 𝔹 where
  mem b := ∃ p, G.mem p ∧ 𝔹.le p.1 b
  top_mem := G.inhabited.elim fun p h => ⟨p, h, 𝔹.le_top _⟩
  upward := fun ⟨p, h, k⟩ l => ⟨p, h, 𝔹.le_trans k l⟩
  meet_mem := by
    rintro a b ⟨p, hp, h⟩ ⟨q, hq, k⟩
    obtain ⟨r, hr, rp, rq⟩ := G.directed hp hq
    exact ⟨r, hr, 𝔹.le_meet (𝔹.le_trans rp h) (𝔹.le_trans rq k)⟩

theorem boolean_filter_proper_l (𝔹 : BA_alg B)
    (G : PO_filter (positive_order_l 𝔹).toPO_pre) : (boolean_filter_l 𝔹 G).Proper_l :=
  fun ⟨p, _, h⟩ => p.2 (𝔹.le_antisymm h (𝔹.bot_le _))

/-- 可数稠密族的滤子再作极大扩张，原先遇到的每个稠密集仍有同一见证。 -/
theorem generic_ultrafilter_countable_l (𝔹 : BA_alg B)
    (D : Nat → Pos_l 𝔹 → Prop) (h : ∀ n, (positive_order_l 𝔹).toPO_pre.Dense_l (D n))
    (p : Pos_l 𝔹) : ∃ U : Filter_l 𝔹,
      U.Maximal_l ∧ U.mem p.1 ∧ ∀ n, BF_meets_l U (D n) := by
  obtain ⟨G, hp, hG⟩ := generic_countable_l (positive_order_l 𝔹).toPO_pre D h p
  obtain ⟨U, hU, k⟩ := (boolean_filter_l 𝔹 G).tarski_extension_l
    (boolean_filter_proper_l 𝔹 G)
  refine ⟨U, hU, k _ ⟨p, hp, 𝔹.le_refl _⟩, fun n => ?_⟩
  obtain ⟨q, hq, hd⟩ := hG n
  exact ⟨q, k _ ⟨q, hq, 𝔹.le_refl _⟩, hd⟩

/-- 条件要么否定整族析取，要么已经蕴含其中一项。 -/
def sup_dense_l (𝔹 : CB_alg B) {ι : Sort v} (f : ι → B) (p : Pos_l 𝔹.toBA_alg) : Prop :=
  𝔹.le p.1 (𝔹.neg (𝔹.iSup f)) ∨ ∃ i, 𝔹.le p.1 (f i)

theorem sup_dense_lower_l (𝔹 : CB_alg B) {ι : Sort v} (f : ι → B) :
    (positive_order_l 𝔹.toBA_alg).toPO_pre.Lower_l (sup_dense_l 𝔹 f) :=
  fun h k => k.elim (fun l => Or.inl (𝔹.le_trans h l))
    (fun ⟨i, l⟩ => Or.inr ⟨i, 𝔹.le_trans h l⟩)

theorem sup_dense_dense_l (𝔹 : CB_alg B) {ι : Sort v} (f : ι → B) :
    (positive_order_l 𝔹.toBA_alg).toPO_pre.Dense_l (sup_dense_l 𝔹 f) := by
  classical
  intro p
  by_cases h : ∃ i, 𝔹.meet p.1 (f i) ≠ 𝔹.bot
  · obtain ⟨i, hi⟩ := h
    exact ⟨⟨𝔹.meet p.1 (f i), hi⟩, 𝔹.meet_le_left _ _,
      Or.inr ⟨i, 𝔹.meet_le_right _ _⟩⟩
  · refine ⟨p, 𝔹.le_refl _, Or.inl ((𝔹.le_imp_iff _ _ _).mpr ?_)⟩
    rw [𝔹.meet_iSup, 𝔹.iSup_le_iff]
    intro i
    have hi : 𝔹.meet p.1 (f i) = 𝔹.bot := Classical.not_not.mp (fun k => h ⟨i, k⟩)
    rw [hi]
    exact 𝔹.le_refl _

theorem sup_mem_iff_l (𝔹 : CB_alg B) (U : Filter_l 𝔹.toBA_alg) (h : U.Proper_l)
    {ι : Sort v} (f : ι → B) (k : BF_meets_l U (sup_dense_l 𝔹 f)) :
    U.mem (𝔹.iSup f) ↔ ∃ i, U.mem (f i) := by
  constructor
  · intro ha
    obtain ⟨p, hp, hd | ⟨i, hi⟩⟩ := k
    · exact False.elim (U.not_neg_l h ha (U.upward hp hd))
    · exact ⟨i, U.upward hp hi⟩
  · rintro ⟨i, hi⟩
    exact U.upward hi (𝔹.le_iSup f i)

/-- 无限合取只消费其否定各项的见证稠密集，不假设滤子具有无限交闭性。 -/
theorem inf_mem_iff_l (𝔹 : CB_alg B) (U : Filter_l 𝔹.toBA_alg) (h : U.Proper_l)
    {ι : Sort v} (f : ι → B) (k : BF_meets_l U (sup_dense_l 𝔹 (fun i => 𝔹.neg (f i)))) :
    U.mem (𝔹.iInf f) ↔ ∀ i, U.mem (f i) := by
  refine ⟨fun ha i => U.upward ha (𝔹.iInf_le f i), fun ha => ?_⟩
  obtain ⟨p, hp, hd | ⟨i, hi⟩⟩ := k
  · apply U.upward hp ((𝔹.le_iInf_iff f _).mpr fun i => ?_)
    have hn := 𝔹.neg_antitone (𝔹.le_iSup (fun j => 𝔹.neg (f j)) i)
    rw [𝔹.neg_neg] at hn
    exact 𝔹.le_trans hd hn
  · exact False.elim (U.not_neg_l h (ha i) (U.upward hp hi))

theorem meet_mem_iff_l {𝔹 : BA_alg B} (U : Filter_l 𝔹) (a b : B) :
    U.mem (𝔹.meet a b) ↔ U.mem a ∧ U.mem b :=
  ⟨fun h => ⟨U.upward h (𝔹.meet_le_left _ _), U.upward h (𝔹.meet_le_right _ _)⟩,
    fun h => U.meet_mem h.1 h.2⟩

theorem imp_mem_iff_l {𝔹 : BA_alg B} (U : Filter_l 𝔹) (h : U.Maximal_l) (a b : B) :
    U.mem (𝔹.imp a b) ↔ (U.mem a → U.mem b) := by
  refine ⟨fun k ha => U.upward (U.meet_mem k ha) (𝔹.imp_elim _ _), fun k => ?_⟩
  rcases (U.maximal_iff_l.mp h).2 a with ha | ha
  · exact U.upward (k ha) ((𝔹.le_imp_iff _ _ _).mpr (𝔹.meet_le_left _ _))
  · exact U.upward ha ((𝔹.le_imp_iff _ _ _).mpr
      (𝔹.le_trans (𝔹.imp_elim _ _) (𝔹.bot_le _)))

/-- 每阶段满足有限方阵，避免另选二维下标的编码或枚举。 -/
theorem generic_ultrafilter_grid_l (𝔹 : BA_alg B) (D : Nat → Nat → Pos_l 𝔹 → Prop)
    (h : ∀ i j, (positive_order_l 𝔹).toPO_pre.Dense_l (D i j))
    (k : ∀ i j, (positive_order_l 𝔹).toPO_pre.Lower_l (D i j)) (p : Pos_l 𝔹) :
    ∃ U : Filter_l 𝔹, U.Maximal_l ∧ U.mem p.1 ∧ ∀ i j, BF_meets_l U (D i j) := by
  let R := (positive_order_l 𝔹).toPO_pre
  let E n q := ∀ i, i ≤ n → ∀ j, j ≤ n → D i j q
  have he n : R.Dense_l (E n) := R.dense_bounded_l _
    (fun i => R.dense_bounded_l (D i) (h i) (k i) n)
    (fun i {_ _} h₁ h₂ j hj => k i j h₁ (h₂ j hj)) n
  obtain ⟨U, hU, hp, hu⟩ := generic_ultrafilter_countable_l 𝔹 E he p
  refine ⟨U, hU, hp, fun i j => ?_⟩
  obtain ⟨q, hq, hd⟩ := hu (max i j)
  exact ⟨q, hq, hd i (Nat.le_max_left _ _) j (Nat.le_max_right _ _)⟩

end YesMetaZFC.Model.Forcing
