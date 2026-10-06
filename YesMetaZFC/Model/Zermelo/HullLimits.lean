import YesMetaZFC.Model.Zermelo.HullProof

/-! # Z 闭包之间仍不保持全部旧真值
考察原公式：存在集合 w，包含参数 p，且 w 的每个成员都属于 w 的另一个成员。
取 p 为第一个闭包的种子。有限阶段内不能容纳这种向上的成员链，
但整个第一个闭包在第二个闭包中就是见证。两个范围均满足完整 Z，参数保持不变。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory
universe u
attribute [local implicit_reducible] SetTheory.signature

/-- 在有限层界内，向上封闭的成员族只能留在最初的层界内。 -/
theorem hl_up_bound (d a : V.{u}) (h : Sl_trans d) (n : Nat) (ha : V.sub a (sl_stage d n))
    (k : ∀ x, x ∈ a → ¬¬∃ y, y ∈ a ∧ x ∈ y) : V.sub a d := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    apply ih
    intro x hx
    exact st_use (k x hx) (fun ⟨y, hy, hxy⟩ =>
      sl_next_sub _ (sl_stage_trans d h n) (ha y hy) x hxy)

/-- p 是唯一自由变量；正文中的量词均由原隶属式限定。 -/
def hl_up_form : OpenFormula ℒ [.set] := .existsE .set (.conj
  (.rel .membership (.cons (.fvar .here) (.cons (.bvar .here) .nil)))
  (.forallE .set (.imp
    (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))
    (.existsE .set (.conj
      (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there (.there .here))) .nil)))
      (.rel .membership (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil))))))))

theorem hl_seed_in (d : V.{u}) : hl_seed d ∈ hl_range d :=
  hl_stage d 1 _ (sl_self_next _)

/-- 在第一个闭包内为假：任何候选 w 都有某个有限层界。 -/
theorem hl_up_false (d : V.{u}) (h : Sl_trans d) :
    ¬ sc_sat hl_up_form (hl_range d) (FirstOrder.Env.empty.pushFree (hl_seed d)) := by
  intro p
  apply st_use p
  intro ⟨a, ha, hp, k⟩
  apply st_use ((hl_mem d a).mp ha)
  intro ⟨n, hn⟩
  have hb := hl_up_bound (hl_seed d) a (hl_seed_trans d h) n
    (sl_stage_trans _ (hl_seed_trans d h) n a hn) (fun x hx =>
      st_use (k x (hl_trans d h a ha x hx) hx) (fun ⟨y, _, hy, hxy⟩ => nn_in ⟨y, hy, hxy⟩))
  exact sl_irrefl (hl_seed d) (hb _ hp)

/-- 在第二个闭包内为真：第一个闭包本身提供见证，成员容器使用实际配对。 -/
theorem hl_up_true (d : V.{u}) :
    sc_sat hl_up_form (hl_range (hl_range d)) (FirstOrder.Env.empty.pushFree (hl_seed d)) :=
  nn_in ⟨hl_range d, hl_self _, hl_seed_in d, fun x _ hx =>
    nn_in ⟨V.pair x x, hl_sub _ _ (hl_pair d hx hx), hl_pair d hx hx,
      (V.pair_mem _ _ _).mpr (nn_in (.inl (V.eq_refl x)))⟩⟩

/-- 两边的参数均在相应范围内；真值改变不是由越界自由参数造成的。 -/
theorem hl_truth_change (d : V.{u}) (h : Sl_trans d) :
    let ρ : Env.{u} [] [.set] := FirstOrder.Env.empty.pushFree (hl_seed d)
    Sc_free (hl_range d) ρ ∧ Sc_free (hl_range (hl_range d)) ρ ∧
      sc_sat (.neg hl_up_form) (hl_range d) ρ ∧ sc_sat hl_up_form (hl_range (hl_range d)) ρ :=
  ⟨(fun i => match i with | .here => hl_seed_in d | .there i => nomatch i),
    (fun i => match i with | .here => hl_sub _ _ (hl_seed_in d) | .there i => nomatch i),
    hl_up_false d h, hl_up_true d⟩

/-- info: 'YesMetaZFC.Model.Zermelo.hl_truth_change' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_truth_change
end YesMetaZFC.Model.Zermelo
