import YesMetaZFC.SetTheory.HereditaryAlgebra
import YesMetaZFC.Model.Forcing.Internal.Maximum.Pool

/-! # 遗传小名称族的加权装配界

将加权名称看成名称族与条件集乘积的子集。配对与乘积封闭复用集合论层，
小族闭性只在正则基数处使用，不引入强极限假设。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ) (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
include hω hχ hωχ hH

/-- 遗传小名称族及遗传小条件集上的任意加权子图仍遗传小。 -/
theorem h_name_bound_l {B A t} (hA : M.mem A H) (hB : M.mem B H) (ht : Name_bound_d M B A t) : M.mem t H := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I A B
  apply ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (ZFC.h_product_l hZFC hω hχ hωχ hH hA hB hP) t
  intro p hp
  obtain ⟨a, b, hp, ha, hb⟩ := ht p hp
  exact (hP p).mpr ⟨a, ha, b, hb, hp⟩

end YesMetaZFC.Model.Forcing.Internal
