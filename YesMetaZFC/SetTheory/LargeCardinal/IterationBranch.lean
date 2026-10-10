import YesMetaZFC.SetTheory.LargeCardinal.IterationOrder
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Basic

/-! # 共尾树枝及其实际指标序

树枝是旧树序中向下封闭的链；共尾性针对时间长度。指标序由原树序限制
得到，其定向性只使用链条件，不假定极限模型已经存在。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure It_branch_d (α T B : M.Domain) : Prop where
  subset : M.MemberSubset B α
  chain : ∀ i j, M.mem i B → M.mem j B → Rd_entry_d i j T ∨ Rd_entry_d j i T
  down : ∀ i j, Rd_entry_d i j T → M.mem j B → M.mem i B
  cofinal : ∀ i, M.mem i α → ∃ j, M.mem j B ∧ (i = j ∨ M.mem i j)

theorem It_branch_d.order_l (hKP : M.Models KP) {α T B : M.Domain}
    (h : It_order_d α T) (b : It_branch_d α T B) : ∃ L, Di_order_d B L ∧
      ∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T := by
  let φ : Delta0BinarySchema 1 := {
    body := rd_entry0_m (.bound 1) .newest (.bound 2), delta0 := rd_entry0_delta_l .. }
  let ρ : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  obtain ⟨L, ls⟩ := rw_rel_exists_l hKP φ ρ B
  have read i j : Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T :=
    (ls.entry_l hKP).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry0_sat_l hKP.1 ..)
  refine ⟨L, ⟨fun i hi => (read i i).mpr ⟨hi, hi, h.refl i (b.subset i hi)⟩,
    fun i j k hij hjk => (read i k).mpr ⟨((read i j).mp hij).1, ((read j k).mp hjk).2.1,
      h.trans i j k ((read i j).mp hij).2.2 ((read j k).mp hjk).2.2⟩,
    fun i j hij => ⟨((read i j).mp hij).1, ((read i j).mp hij).2.1⟩, ?_⟩, read⟩
  intro i j hi hj
  rcases b.chain i j hi hj with hij | hji
  · exact ⟨j, hj, (read i j).mpr ⟨hi, hj, hij⟩, (read j j).mpr ⟨hj, hj, h.refl j (b.subset j hj)⟩⟩
  · exact ⟨i, hi, (read i i).mpr ⟨hi, hi, h.refl i (b.subset i hi)⟩, (read j i).mpr ⟨hj, hi, hji⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
