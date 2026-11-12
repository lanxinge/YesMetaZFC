import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor

/-! # 已选共同图与两条原根图的交换

只在固定原根切片的成员载体上比较实际求值。每次复合保留原来的
共同图见证，既不使用外部良基性，也不把不同选择的共同图视为唯一。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_root_square_d (D p q g : M.Domain) : Prop :=
  ∀ a, M.mem a D → ∀ x, Rd_entry_d a x p → ∀ y,
    Rd_entry_d x y g ↔ Rd_entry_d a y q

/-- 两个实际复合方程逐点保持同一原根方块。 -/
theorem Tg_root_square_d.comp_l {D p q q' g g' j : M.Domain}
    (square : Tg_root_square_d D p q g)
    (common : It_comp_d g j g') (root : It_comp_d q j q') :
    Tg_root_square_d D p q' g' := by
  intro a ha x ax y
  exact (common.2 x y).trans ((exists_congr fun z =>
    and_congr (square a ha x ax z) Iff.rfl).trans (root.2 a y).symm)

end YesMetaZFC.SetTheory.LargeCardinal
