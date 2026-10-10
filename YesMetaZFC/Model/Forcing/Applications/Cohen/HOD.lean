import YesMetaZFC.Model.Forcing.Applications.Cohen.OrdinalSubsets
import YesMetaZFC.Model.Forcing.Internal.Homogeneous.HOD

/-! # Cohen 扩张的 HOD 比较实例

输入实际 Cohen 呈现、序数添加量与泛型。呈现的 OD 性、弱齐性、地嵌入及坍塌
全部由已实现构造提供；不另要求模型外部良基或背景选择公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cohen_hod_comparison_l {κ B R} {U : M.Domain → Prop}
    (hκ : M.IsOrdinal κ) (h : Cohen_spec_d I κ B R) (hU : Generic_d M B R B U) :
    ∃ e : M.Domain → (extension_l M hZF B R B U).Domain, Function.Injective e ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧
      (∀ x, (extension_l M hZF B R B U).IsOrdinal x ↔ ∃ α, M.IsOrdinal α ∧ e α = x) ∧
      ∀ x : (extension_l M hZF B R B U).Domain, Hod_d x → ∃ y, Hod_d y ∧ e y = x := by
  obtain ⟨hB, hR⟩ := cohen_presentation_od_l hZF hκ h
  exact whom_hod_comparison_l (cohen_cond_order_l hZF h) hZF hU (cohen_whom_l hZF h) hB hR hB

end YesMetaZFC.Model.Forcing.Internal
