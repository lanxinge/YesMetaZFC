import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Separation
import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.PowerSet

/-! # 任意 ZF 模型中的 Jensen 内模型

沿用同一个 J 隶属结构。新增的全分离、全收集和内部幂集逐项满足原 ZF 公理，
再接上已经完成的内部层级识别，得到 ZF + V=L 的实际模型。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem l_model_zf_l (hZF : M.Models ZF) : (l_model_l (ZF.models_kpi_l hZF)).Models ZF := by
  have hKP := l_model_kp_l (ZF.models_kpi_l hZF)
  refine ⟨hKP.1, fun s hs => ?_⟩
  cases hs with
  | extensionality => exact hKP.2 _ .extensionality
  | emptySet => exact hKP.2 _ .emptySet
  | pairing => exact hKP.2 _ .pairing
  | union => exact hKP.2 _ .union
  | infinity => exact hKP.2 _ .infinity
  | foundation => exact hKP.2 _ .foundation
  | powerSet =>
    rw [Structure.satisfiesSentence_iff]
    exact fun f => (Axioms.satisfies_powerSet_iff f).mpr (l_model_power_l hZF)
  | separation φ =>
    rw [Structure.satisfiesSentence_iff]
    intro f
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.separationCore φ)).mpr
    intro b
    exact (Axioms.Schema.separation_sat_iff_d ⟨b, f⟩ φ).mpr (l_model_full_separation_l hZF φ ⟨b, f⟩)
  | collection φ =>
    rw [Structure.satisfiesSentence_iff]
    intro f
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.collectionCore φ)).mpr
    intro b
    exact (Axioms.Schema.collection_sat_iff_d ⟨b, f⟩ φ).mpr (l_model_full_collection_l hZF φ ⟨b, f⟩)

/-- 模型允许外部非标准、非良基；序数、量词和构造历史仍由各自模型内部解释。 -/
theorem l_model_zfl_l (hZF : M.Models ZF) : (l_model_l (ZF.models_kpi_l hZF)).Models ZFL := by
  refine ⟨(l_model_zf_l hZF).1, fun s hs => ?_⟩
  cases hs with
  | zf hs => exact (l_model_zf_l hZF).2 s hs
  | constructible => exact l_model_vl_l (ZF.models_kpi_l hZF)

end YesMetaZFC.SetTheory.InnerModel
