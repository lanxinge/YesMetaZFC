import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Model
import YesMetaZFC.SetTheory.InnerModel.Order.Statement
import YesMetaZFC.SetTheory.GlobalChoice

/-! # ZF 背景下 Jensen 内模型的选择公理 -/
namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem js_zfc_l (hZF : M.Models ZF) (hVL : M.SatisfiesSentence Axioms.vl_axiom) : M.Models ZFC :=
  ZF.gw_zfc_l hZF js_less_s.schema (js_universe_l (ZF.models_kpi_l hZF) hVL)

/-- 外部只假设 ZF；内部选择来自已经构造的 Jensen 全局良序。 -/
theorem l_model_zfc_l (hZF : M.Models ZF) : (l_model_l (ZF.models_kpi_l hZF)).Models ZFC :=
  js_zfc_l (l_model_zf_l hZF) (l_model_vl_l (ZF.models_kpi_l hZF))

end YesMetaZFC.SetTheory.InnerModel
