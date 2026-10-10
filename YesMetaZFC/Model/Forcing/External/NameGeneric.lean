import YesMetaZFC.Model.Forcing.External.Truth

/-! # 可数名称族的同时泛型化

第 n 阶段处理前 n 幅图、各图前 n 个节点之间的全部原子要求，再处理指定的
第 n 个稠密集。直接使用有限初段调度，节点枚举由调用者的实际图提供。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean
universe u v
variable {B : Type v} (𝔹 : CB_alg B)

/-- 同一个滤子同时解释整个可数名称族，并遇到额外给定的稠密族。 -/
theorem name_family_generic_l (F : Nat → BV_graph.{u, v} B)
    (e : ∀ i, Nat → (F i).Domain) (he : ∀ i a, ∃ n, e i n = a)
    (D : Nat → Pos_l 𝔹.toBA_alg → Prop)
    (hD : ∀ n, (positive_order_l 𝔹.toBA_alg).toPO_pre.Dense_l (D n))
    (p : Pos_l 𝔹.toBA_alg) : ∃ U : Filter_l 𝔹.toBA_alg,
      U.Maximal_l ∧ U.mem p.1 ∧ (∀ n, BF_meets_l U (D n)) ∧
      ∀ i j, Name_generic_l 𝔹 U (F i) (F j) := by
  let R := (positive_order_l 𝔹.toBA_alg).toPO_pre
  let A i j a b := name_dense_l 𝔹 (F i) (F j) (e i a) (e j b)
  have hd i j a b : R.Dense_l (A i j a b) := name_dense_dense_l 𝔹 _ _ _ _
  have ho i j a b : R.Lower_l (A i j a b) := name_dense_lower_l 𝔹 _ _ _ _
  let Q n q := ∀ i, i ≤ n → ∀ j, j ≤ n → ∀ a, a ≤ n → ∀ b, b ≤ n → A i j a b q
  have hq n : R.Dense_l (Q n) :=
    R.dense_bounded_l _ (fun i =>
      R.dense_bounded_l _ (fun j =>
        R.dense_bounded_l _ (fun a => R.dense_bounded_l _ (hd i j a) (ho i j a) n)
          (fun a {_ _} h k b hb => ho i j a b h (k b hb)) n)
        (fun j {_ _} h k a ha b hb => ho i j a b h (k a ha b hb)) n)
      (fun i {_ _} h k j hj a ha b hb => ho i j a b h (k j hj a ha b hb)) n
  have hE n := R.dense_inter_l (hq n) (hD n)
    (fun h k i hi j hj a ha b hb => ho i j a b h (k i hi j hj a ha b hb))
  obtain ⟨U, hU, hp, h⟩ := generic_ultrafilter_countable_l 𝔹.toBA_alg
    (fun n q => Q n q ∧ D n q) hE p
  refine ⟨U, hU, hp, fun n => ?_, fun i j => ?_⟩
  · obtain ⟨q, hu, _, hd⟩ := h n
    exact ⟨q, hu, hd⟩
  · apply name_generic_of_meets_l 𝔹 U (F i) (F j)
    intro a b
    obtain ⟨k, rfl⟩ := he i a
    obtain ⟨l, rfl⟩ := he j b
    obtain ⟨q, hu, hq, _⟩ := h (max (max i j) (max k l))
    exact ⟨q, hu, hq
      i (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      j (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      k (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      l (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩

end YesMetaZFC.Model.Forcing
