import YesMetaZFC.SetTheory.HereditaryCover
import YesMetaZFC.SetTheory.RankImage

/-! # 任意集合的正规秩层包络

先取实际正则 H(δ) 包络，再用传递闭包的大小界进入 Vδ。
-/
namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC

include hZFC in
theorem v_regular_cover_l {ω : M.Domain} (hω : M.IsOmega ω) (x : M.Domain) :
    ∃ δ V, M.IsRegularCardinal I δ ∧ M.mem ω δ ∧ V_d I δ V ∧ M.mem x V := by
  obtain ⟨δ, H, regular, above, rank, hx⟩ := h_cover_l I hZFC hω x
  obtain ⟨T, μ, tc, hμ, size⟩ := (rank x).mp hx
  obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF regular.isCardinal.1
  exact ⟨δ, V, regular, above, hV,
    ZF.rk_transitive_bound_l I hZF tc.1 regular.isCardinal hμ size hV x tc.2.1⟩

end YesMetaZFC.SetTheory.ZFC
