import YesMetaZFC.SetTheory.FlatPairing.Functions
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 后继秩层中的实际平坦结构码

平坦配对和图坐标均在当前层中绝对，故载体、关系和隶属结构完整双向读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

theorem rt_fp_smdl_l (c A R : (N).Domain) : Smdl_d J c A R ↔ Smdl_d K c.val A.val R.val := by
  have trans := v_transitive_l I hW
  have entry := rt_fp_entry_l I hZF hω hW hωY
  refine and_congr (fp_fixed_l hZF.1 hω).symm (and_congr ?_ ?_)
  · exact ⟨fun ⟨x, hx⟩ => ⟨x.val, hx⟩, fun ⟨x, hx⟩ => ⟨⟨x, trans A.val A.property x hx⟩, hx⟩⟩
  · refine and_congr (rt_fp_relation_l I hZF hω hW hωY R) ?_
    constructor
    · intro h x y he
      have xy := rt_fp_coordinates_l I hZF hω hW R.property he
      exact h ⟨x, xy.1⟩ ⟨y, xy.2⟩ ((entry _ _ R).mpr he)
    · intro h x y he
      exact h x.val y.val ((entry x y R).mp he)

theorem rt_fp_smem_l (c A R : (N).Domain) : Smem_d J c A R ↔ Smem_d K c.val A.val R.val := by
  have trans := v_transitive_l I hW
  have entry := rt_fp_entry_l I hZF hω hW hωY
  refine and_congr (rt_fp_smdl_l I hZF hω hW hωY c A R) ?_
  constructor
  · intro h x y
    constructor
    · intro he
      have xy := rt_fp_coordinates_l I hZF hω hW R.property he
      exact (h ⟨x, xy.1⟩ ⟨y, xy.2⟩).mp ((entry _ _ R).mpr he)
    · intro he
      exact (entry _ _ R).mp ((h ⟨x, trans A.val A.property x he.1⟩
        ⟨y, trans A.val A.property y he.2.1⟩).mpr he)
  · intro h x y
    exact (entry x y R).trans (h x.val y.val)

end YesMetaZFC.SetTheory.Internal
