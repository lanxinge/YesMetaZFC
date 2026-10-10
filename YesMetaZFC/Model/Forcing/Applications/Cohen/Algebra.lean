import YesMetaZFC.Model.Forcing.Boolean.Completion
import YesMetaZFC.Model.Forcing.Order.Tree

/-! # 一个 Cohen 实数的布尔条件代数

直接对已有二元有限序列偏序作正则开完备化，得到非平凡、无原子的完备布尔代数。
这里只构造代数及其条件性质；泛型实数和名称语义由后续层处理。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean

abbrev Cohen_l := (tree_order_l Bool).toPO_pre.RO_l

def cohen_algebra_l : CB_alg Cohen_l := (tree_order_l Bool).toPO_pre.ro_algebra_l

theorem cohen_nontrivial_l : cohen_algebra_l.bot ≠ cohen_algebra_l.top :=
  (tree_order_l Bool).toPO_pre.ro_nontrivial_l.mpr ⟨[]⟩

theorem cohen_atomless_l : (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre.Atomless_l :=
  (tree_order_l Bool).toPO_pre.ro_dense_l.atomless_l binary_atomless_l

end YesMetaZFC.Model.Forcing
