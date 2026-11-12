import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover
import YesMetaZFC.SetTheory.Collapse.RegularRank

/-! # 反例的实际联合尝试树与正则下降秩

公共可数载体先给出规范枚举，随后构造全部有限尝试和内部良基秩。
正则化直接作用于这张秩图；初等复制同一图时，就是论文中的逐结点正则高度替换。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_failure_l {ω T Q G E Y W z π c₀ X₀ V₀ d η : M.Domain}
    (tree : It_tree_d hZF ω c₀ ω T Q G E) (mx : Smdl_d I c₀ X₀ V₀) (cx : M.CardinalLessOrEqual I X₀ ω)
    (hz : ∀ x, ¬ M.mem x z) (my : Smem_d I d Y W) (pi : Fn0_d X₀ Y π)
    (ho : M.IsOrdinal η) (bad : ¬ It_return_d hZF ω z T Q G d Y π) :
    ∃ U A R F, Ja_enum_d I ω ω Q U ∧ Ja_space_d I ω T Q G U Y W z π A R ∧ Rr_d I A R η F := by
  obtain ⟨Z, ι, inj, cover⟩ := it_countable_cover_l hZFC tree mx cx
  obtain ⟨U, en⟩ := ja_enum_l hZF tree.omega tree.diagram inj cover
  have root := tree.root z hz
  obtain ⟨A, R, _, F, space, _, _, rank⟩ := ja_counterexample_rank_l hZF tree.omega (ZFC.dc_l I hZFC tree.omega)
    tree.diagram en hz root mx (tree.sources z c₀ root) my pi bad
  obtain ⟨H, hh⟩ := wr_regular_l hZFC tree.omega ho rank
  exact ⟨U, A, R, H, en, space, hh⟩

end YesMetaZFC.SetTheory.LargeCardinal
