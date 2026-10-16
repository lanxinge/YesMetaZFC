import YesMetaZFC.Model.Forcing.Internal.Ground.Arithmetic
import YesMetaZFC.Model.Forcing.Internal.Ground.FiniteSequence
import YesMetaZFC.SetTheory.Descriptive.TreeRank

/-! # 地面树秩在传递外模型中的保持

秩证书是有界公式；成员满覆盖的嵌入逐式保持证书。无限分支在目标模型
中重新量化，由实际秩排除，不要求两模型具有相同的实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
include hi he

theorem image_tree_l {F T : M.Domain} (tree : Tree_d F T) : Tree_d (e F) (e T) := by
  refine ⟨(image_subset_iff_l e hi he).mpr tree.1, ?_⟩
  intro s hs t ht sub
  obtain ⟨a, ha, rfl⟩ := (he T s).mp hs
  obtain ⟨b, hb, rfl⟩ := (he F t).mp ht
  exact (image_member_l e hi he).mpr (tree.2 a ha b hb ((image_subset_iff_l e hi he).mp sub))

include hM hN in
theorem image_tree_rank_l {ω X T α H : M.Domain} (rank : Cg_rank_d ω X T α H) :
    Cg_rank_d (e ω) (e X) (e T) (e α) (e H) := by
  let ρ : Env M 5 := ⟨fun i => [H, α, T, X, ω].get i, fun _ => ω⟩
  exact (cg_rank0_sat_l (ZF.modelsKP hN) (image_env_l e ρ) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).mp
    ((delta0_image_l e hi he (cg_rank0_delta_l (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ρ).mp
      ((cg_rank0_sat_l (ZF.modelsKP hM) ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).mpr rank))

end YesMetaZFC.Model.Forcing.Internal
