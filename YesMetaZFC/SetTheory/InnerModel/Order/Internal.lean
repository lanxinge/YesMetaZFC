import YesMetaZFC.SetTheory.InnerModel.Order.Global

/-! # Jensen 序及初段函数的模型内部化

比较的向上绝对性来自真实 Σ₁ 证书，反向由内部三歧性确定。初段图的反向
绝对性用内部实际初段及背景唯一性，不在 J 中假定新的正确性或反射公理。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_l_absolute_l (hM : M.Models KPi) (x y : (l_model_l hM).Domain) :
    Js_lt_d (M := l_model_l hM) x y ↔ Js_lt_d (M := M) x.val y.val := by
  have up (x y : (l_model_l hM).Domain) (h : Js_lt_d (M := l_model_l hM) x y) : Js_lt_d (M := M) x.val y.val :=
    (js_less_sat_l (KPi.models_iff_l.mp hM).1 _ x.val y.val).mp
      (l_sigma1_up_l hM js_less_s (js_env_l x) ((js_less_sat_l (l_model_kp_l hM) _ x y).mpr h))
  refine ⟨up x y, fun h => ?_⟩
  rcases js_compare_l (l_model_kpi_l hM) (l_internal_constructible_l hM x) (l_internal_constructible_l hM y) with he | he | he
  · subst y; exact (js_irrefl_l hM x.val h).elim
  · exact he
  · exact (js_irrefl_l hM x.val (js_trans_l hM h (up y x he))).elim

theorem js_initial_l_absolute_l (hM : M.Models KPi) (x I : (l_model_l hM).Domain) :
    Js_initial_d (M := l_model_l hM) x I ↔ Js_initial_d (M := M) x.val I.val := by
  have up (I : (l_model_l hM).Domain) (h : Js_initial_d (M := l_model_l hM) x I) : Js_initial_d (M := M) x.val I.val :=
    (js_initial_sat_l hM _ x.val I.val).mp
      (l_sigma1_up_l hM js_initial_s (js_env_l x) ((js_initial_sat_l (l_model_kpi_l hM) _ x I).mpr h))
  refine ⟨up I, fun hi => ?_⟩
  obtain ⟨K, _, hk⟩ := js_initial_exists_l (l_model_kpi_l hM) (l_internal_constructible_l hM x)
  have eq : I = K := Subtype.ext (js_initial_unique_l (KPi.models_iff_l.mp hM).1.1 hi (up K hk))
  subst I
  exact hk

def js_initial_m {n} (x I : Term n) : Formula 1 n := binary_pred_m js_initial_s.schema Fin.elim0 x I
derive_free_closed js_initial_m
theorem js_initial_formula_l (hM : M.Models KPi) {n} (ρ : Env M n) (x I : Term n) :
    Formula.satisfies ρ (js_initial_m x I) ↔ Js_initial_d (x.eval ρ) (I.eval ρ) := by
  rw [js_initial_m, binary_pred_sat_l, js_initial_sat_l hM]

theorem js_rel_sat_l (hM : M.Models KPi) {n} (ρ : Env (l_model_l hM) n) (x y : Term n) :
    Formula.satisfies (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) (l_rel_m (js_less_m x y)) ↔
      Js_lt_d (M := M) (x.eval ρ).val (y.eval ρ).val :=
  (l_rel_sat_l hM (js_less_m x y) ρ).symm.trans
    ((js_less_formula_l (l_model_kp_l hM) ρ x y).trans (js_l_absolute_l hM (x.eval ρ) (y.eval ρ)))

theorem js_initial_rel_sat_l (hM : M.Models KPi) {n} (ρ : Env (l_model_l hM) n) (x I : Term n) :
    Formula.satisfies (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) (l_rel_m (js_initial_m x I)) ↔
      Js_initial_d (M := M) (x.eval ρ).val (I.eval ρ).val :=
  (l_rel_sat_l hM (js_initial_m x I) ρ).symm.trans
    ((js_initial_formula_l (l_model_kpi_l hM) ρ x I).trans (js_initial_l_absolute_l hM (x.eval ρ) (I.eval ρ)))

end YesMetaZFC.SetTheory.InnerModel
