import YesMetaZFC.SetTheory.InnerModel.ProofCode.Global.Jensen
import YesMetaZFC.SetTheory.Definitional.Project.GlobalOrder

/-! # 原对象语言中的目标全局良序句子

固定的原 Project 句子同时表达严格线序、每个非空集合的最小元以及所有严格
初段的集合性。它是已有理论的结论，不作为新公理加入任何理论。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def lo_universe_s : Sentence := gw_sentence_s lo_lt_s.schema

theorem lo_universe_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) : M.SatisfiesSentence lo_universe_s := by
  rw [Structure.satisfiesSentence_iff]
  intro f
  have all : ∀ x : M.Domain, L_d x := (vl_sat_l (KPi.models_iff_l.mp hM).1 f).mp
    ((Structure.satisfiesSentence_iff M Axioms.vl_axiom).mp hVL f)
  apply (gw_sentence_sat_l (KPi.models_iff_l.mp hM).1.1 lo_lt_s.schema ⟨Fin.elim0, f⟩).mpr
  simp only [Gw_order_d, lo_lt_sat_l hM]
  exact ⟨lo_irrefl_l hM, (fun _ _ _ h g => lo_trans_l hM h g),
    (fun x y => lo_compare_l hM (all x) (all y)), (fun X hn => lo_min_l hM (fun x _ => all x) hn),
    fun x => (lo_initial_exists_l hM (all x)).imp (fun _ h => h.2)⟩

/-- Jensen 模型满足已固定的原对象语言全局良序句子。 -/
theorem lo_l_model_l (hM : M.Models KPi) : (l_model_l hM).SatisfiesSentence lo_universe_s :=
  lo_universe_l (l_model_kpi_l hM) (l_model_vl_l hM)

/-- 将比较公式相对化到 J 后，所得关系与背景模型在 L 上的比较完全一致。 -/
theorem lo_rel_sat_l (hM : M.Models KPi) {n} (ρ : Env (l_model_l hM) n) (x y : Term n) :
    Formula.satisfies (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) (l_rel_m (lo_lt_m x y)) ↔
      Lo_lt_d (M := M) (x.eval ρ).val (y.eval ρ).val :=
  (l_rel_sat_l hM (lo_lt_m x y) ρ).symm.trans
    ((lo_lt_formula_l (l_model_kpi_l hM) ρ x y).trans (lo_l_absolute_l hM (x.eval ρ) (y.eval ρ)))

end YesMetaZFC.SetTheory.InnerModel
