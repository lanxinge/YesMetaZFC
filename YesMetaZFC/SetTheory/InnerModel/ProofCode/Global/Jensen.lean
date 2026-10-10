import YesMetaZFC.SetTheory.InnerModel.ProofCode.Global.Table
import YesMetaZFC.SetTheory.InnerModel.Jensen.Constructibility

/-! # Jensen 内模型中的目标良序与绝对性

同一 Σ₁ 公式在 J 内定义全局良序及其初段函数。向上绝对性由既有的 Σ₁
解释定理提供；反方向由内部三歧性和背景不可反性推出。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem lo_l_compare_l (hM : M.Models KPi) (x y : (l_model_l hM).Domain) :
    x = y ∨ Lo_lt_d (M := l_model_l hM) x y ∨ Lo_lt_d (M := l_model_l hM) y x :=
  lo_compare_l (l_model_kpi_l hM) (l_internal_constructible_l hM x) (l_internal_constructible_l hM y)

theorem lo_l_absolute_l (hM : M.Models KPi) (x y : (l_model_l hM).Domain) :
    Lo_lt_d (M := l_model_l hM) x y ↔ Lo_lt_d (M := M) x.val y.val := by
  have up (x y : (l_model_l hM).Domain) (h : Lo_lt_d (M := l_model_l hM) x y) : Lo_lt_d (M := M) x.val y.val := by
    let ρ : Env (l_model_l hM) 0 := jh_env_l x
    exact (lo_lt_sat_l hM _ x.val y.val).mp
      (l_sigma1_up_l hM lo_lt_s ρ ((lo_lt_sat_l (l_model_kpi_l hM) ρ x y).mpr h))
  refine ⟨up x y, fun h => ?_⟩
  rcases lo_l_compare_l hM x y with he | he | he
  · subst y; exact (lo_irrefl_l hM x.val h).elim
  · exact he
  · exact (lo_irrefl_l hM x.val (lo_trans_l hM h (up y x he))).elim

/-- 背景中的精确对象初段本身属于 L。 -/
theorem lo_initial_in_l_l (hM : M.Models KPi) {x : M.Domain} (hx : L_d x) : ∃ Y, L_d Y ∧ Lo_initial_d x Y := by
  let a : (l_model_l hM).Domain := ⟨x, hx⟩
  obtain ⟨Y, hy⟩ := lo_initial_exists_l (l_model_kpi_l hM) (l_internal_constructible_l hM a)
  let ρ : Env (l_model_l hM) 0 := jh_env_l a
  exact ⟨Y.val, Y.property, (lo_initial_sat_l hM _ x Y.val).mp
    (l_sigma1_up_l hM lo_initial_s ρ ((lo_initial_sat_l (l_model_kpi_l hM) ρ a Y).mpr hy))⟩

/-- J 内任意集合自动获得由统一公式定义的实际良序关系表。 -/
theorem lo_l_order_table_l (hM : M.Models KPi) (X : (l_model_l hM).Domain) :
    ∃ R, Lo_table_d (M := l_model_l hM) X R ∧
      (l_model_l hM).IsSetCodedWellOrder (kp_pair_l (l_model_kp_l hM)) R X :=
  lo_order_table_l (l_model_kpi_l hM) (fun x _ => l_internal_constructible_l hM x)

theorem lo_l_delta1_l (hM : M.Models KPi) (ρ : Env (l_model_l hM) 0) (x y : (l_model_l hM).Domain) :
    lo_lt_s.schema.denote ρ x y ↔ ¬ lo_not_lt_s.schema.denote ρ x y :=
  lo_delta1_l (l_model_kpi_l hM) (l_internal_constructible_l hM x) (l_internal_constructible_l hM y) ρ

end YesMetaZFC.SetTheory.InnerModel
