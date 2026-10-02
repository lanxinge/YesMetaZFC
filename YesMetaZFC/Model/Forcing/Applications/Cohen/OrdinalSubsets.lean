import YesMetaZFC.Model.Forcing.Applications.Cohen.Homogeneous
import YesMetaZFC.Model.Forcing.Internal.Homogeneous.OrdinalSubsets

/-! # Cohen 扩张的 OD 序数子集比较

参数化 Cohen 呈现由添加量唯一决定。添加量为序数时，条件集与完整序图均为 OD；
结合已构造的弱齐性实例，一次取得不增加序数及 OD 序数子集恢复的实际地嵌入。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem cohen_presentation_od_l {κ B R} (hκ : M.IsOrdinal κ) (h : Cohen_spec_d I κ B R) :
    Od_d B ∧ Od_d R := by
  let ρ : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  let φ : UnarySchema 1 := { body := .existsE (cohen_m (.bound 2) (.bound 1) .newest) }
  let ψ : UnarySchema 1 := { body := .existsE (cohen_m (.bound 2) .newest (.bound 1)) }
  have hφ X : φ.denote ρ X ↔ X = B := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, cohen_sat_l I hZF.1]
    exact ⟨fun ⟨T, ht⟩ => (cohen_spec_unique_l I hZF.1 ht h).1, fun he => he.symm ▸ ⟨R, h⟩⟩
  have hψ T : ψ.denote ρ T ↔ T = R := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_exists_iff, cohen_sat_l I hZF.1]
    exact ⟨fun ⟨X, hx⟩ => (cohen_spec_unique_l I hZF.1 hx h).2, fun he => he.symm ▸ ⟨B, h⟩⟩
  exact ⟨od_of_unique_l hZF φ ρ (fun _ => hκ) hφ, od_of_unique_l hZF ψ ρ (fun _ => hκ) hψ⟩

/-- 从实际 Cohen 呈现与泛型出发，不另要求自同构、OD 证书或地嵌入。 -/
theorem cohen_od_recovery_l {κ B R} {U : M.Domain → Prop}
    (hκ : M.IsOrdinal κ) (h : Cohen_spec_d I κ B R) (hU : Generic_d M B R B U) :
    ∃ e : M.Domain → (extension_l M hZF B R B U).Domain, Function.Injective e ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧
      (∀ x, (extension_l M hZF B R B U).IsOrdinal x ↔ ∃ α, M.IsOrdinal α ∧ e α = x) ∧
      ∀ X : (extension_l M hZF B R B U).Domain, Od_d X →
        (∀ x, x ∈ X → (extension_l M hZF B R B U).IsOrdinal x) →
        ∃ Y, Od_d Y ∧ e Y = X := by
  let O := cohen_cond_order_l hZF h
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi, ho⟩ := check_map_ordinals_l O hZF hU hb
  obtain ⟨hB, hR⟩ := cohen_presentation_od_l hZF hκ h
  exact ⟨e, hi, he, ho, fun _ hX hOrd =>
    whom_od_ordinal_subset_l O hZF hU hb e hv he hi (cohen_whom_l hZF h) hB hR hB hX hOrd⟩

end YesMetaZFC.Model.Forcing.Internal
