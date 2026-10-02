import YesMetaZFC.SetTheory.InnerModel.Order.Uniform
import YesMetaZFC.SetTheory.InnerModel.Jensen.Constructibility

/-! # 有序微层级在 Jensen 内模型中的识别

内部 KPi 实例产生真实状态证书；Σ₁ 向上绝对性和背景唯一性识别内外状态。
由此证明每个有序微层及其关系表均属于 L，而不预设微层的可构造性。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_l_state_up_l (hM : M.Models KPi) {a p : (l_model_l hM).Domain}
    (h : Js_state_d (M := l_model_l hM) a p) : Js_state_d (M := M) a.val p.val := by
  let ρ := js_env_l a
  have h' := l_sigma1_up_l hM (rc_value_s rw_op_s) ρ h
  exact (js_state_env_l (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) a.val p.val).mp h'

theorem l_kpair_iff_l (hM : M.Models KPi) (p x y : (l_model_l hM).Domain) :
    KPair_d (l_model_l hM) p x y ↔ KPair_d M p.val x.val y.val := by
  let ρ := (((js_env_l p).push y).push x).push p
  exact (kpair0_sat_l (l_model_ext_l hM) ρ .newest (.bound 1) (.bound 2)).symm.trans
    ((l_model_delta_l hM (kpair0_delta_l .newest (.bound 1) (.bound 2)) ρ).trans
      (kpair0_sat_l (KPi.models_iff_l.mp hM).1.1 _ .newest (.bound 1) (.bound 2)))

theorem js_l_value_up_l (hM : M.Models KPi) {a U R : (l_model_l hM).Domain}
    (h : Js_value_d (M := l_model_l hM) a U R) : Js_value_d (M := M) a.val U.val R.val := by
  obtain ⟨p, hp, hpair⟩ := h
  exact ⟨p.val, js_l_state_up_l hM hp, (l_kpair_iff_l hM p U R).mp hpair⟩

theorem js_l_value_iff_l (hM : M.Models KPi) (a U R : (l_model_l hM).Domain) :
    Js_value_d (M := l_model_l hM) a U R ↔ Js_value_d (M := M) a.val U.val R.val := by
  refine ⟨js_l_value_up_l hM, fun h => ?_⟩
  obtain ⟨V, S, hv⟩ := js_value_exists_l (l_model_kpi_l hM) a
  obtain ⟨hu, hr⟩ := js_value_unique_l hM h (js_l_value_up_l hM hv)
  have hu : U = V := Subtype.ext hu
  have hr : R = S := Subtype.ext hr
  subst U; subst R
  exact hv

theorem js_value_constructible_l (hM : M.Models KPi) {a U R : M.Domain}
    (ha : M.IsOrdinal a) (h : Js_value_d a U R) : L_d U ∧ L_d R := by
  let b : (l_model_l hM).Domain := ⟨a, l_ordinal_l hM ha⟩
  obtain ⟨V, S, hv⟩ := js_value_exists_l (l_model_kpi_l hM) b
  obtain ⟨hu, hr⟩ := js_value_unique_l hM (js_l_value_up_l hM hv) h
  exact ⟨hu ▸ V.property, hr ▸ S.property⟩

/-- 有序微层的并类恰是原 J 并类。 -/
theorem js_covered_iff_l (hM : M.Models KPi) (x : M.Domain) :
    (∃ a U R, M.IsOrdinal a ∧ Js_value_d a U R ∧ M.mem x U) ↔ L_d x := by
  constructor
  · rintro ⟨a, U, R, ha, hu, hx⟩
    exact l_transitive_l hM (js_value_constructible_l hM ha hu).1 hx
  · rintro ⟨a, U, ha, hx⟩
    obtain ⟨b, R, hb, hr⟩ := jh_order_rep_l hM ha.1 ha.2
    exact ⟨b, U, R, hb, hr, hx⟩

end YesMetaZFC.SetTheory.InnerModel
