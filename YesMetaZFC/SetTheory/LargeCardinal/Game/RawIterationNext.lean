import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationState
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchiveEdge

/-! # 六十六项原生状态的精确后继几何

新档案位于两条实际原边之间。重置记录自己的原空集；继续记录所选
旧档案沿第一边的精确三图延伸。第二边搬运控制数据与同一个外部前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 父行由真实档案索引选择，原边上的几何仍读取两端保存码。 -/
def Tg_raw_iteration_parent_d (v : Fin 20 → M.Domain) (a : Fin 46 → M.Domain)
    (k G : M.Domain) (row : Tg_raw_archive_row_d M.Domain) : Prop :=
  ∃ j, It_map_d G k (v 6) j ∧
    ((a 23 = a 1 ∧ k = v 7 ∧ Tg_raw_archive_reset_d I row (a 7) j) ∨
      (a 23 ≠ a 1 ∧ ∃ l r, ∃ old : Tg_raw_archive_row_d M.Domain,
        M.mem l (v 18) ∧ M.PairMember I l (a 22) (v 3) ∧ M.PairMember I l r (v 13) ∧
          Rt_tuple_d old.values_d r ∧ old.i = k ∧ Tg_raw_archive_step_d I old row j))

/-- 两次原树延伸、严格历史增长与恰一次原字母追加共用这一组对象。 -/
def Tg_raw_iteration_next_d (ω c₀ A x : M.Domain) (v w : Fin 20 → M.Domain)
    (a b : Fin 46 → M.Domain) : Prop :=
  ∃ k T Q G E j,
    It_tree_d hZF ω c₀ (w 7) T Q G E ∧
    It_extension_d (v 6) (v 7) k (v 8) (v 9) (v 10) (v 11) (w 7) T Q G E ∧
    It_extension_d (w 7) (v 6) (v 7) T Q G E (w 6) (w 8) (w 9) (w 10) (w 11) ∧
    It_map_d (w 10) (v 7) (w 7) j ∧
    (∀ i : Fin 19, M.PairMember I (a (i.castAdd 27)) (b (i.castAdd 27)) j) ∧
    (∃ h, M.PairMember I (a 20) h j ∧ h ≠ b 20 ∧
      ∀ y, Rd_entry_d y h (w 1) → Rd_entry_d y (b 20) (w 1)) ∧
    M.SuccessorOf (w 18) (v 18) ∧
    ∃ y, M.mem y A ∧ Fseq_end_d I ω (w 19) (v 19) y ∧
      (Descriptive.Gm_even_d I ω (v 18) → y = x) ∧
    ∃ row : Tg_raw_archive_row_d M.Domain, ∃ r,
      row.i = v 6 ∧ Rt_tuple_d row.values_d r ∧ Tg_raw_iteration_parent_d hZF v a k G row ∧
      (∀ i z, M.PairMember I i z (w 13) ↔ M.PairMember I i z (v 13) ∨ i = v 18 ∧ z = r)

end YesMetaZFC.SetTheory.LargeCardinal
