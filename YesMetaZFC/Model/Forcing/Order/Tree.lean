import YesMetaZFC.Model.Forcing.Order.Density
import Init.Data.List.Sublist

/-! # 有限序列条件

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
