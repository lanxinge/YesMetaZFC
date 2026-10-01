import YesMetaZFC.SetTheory.InnerModel.ProofCode.Global.Jensen

/-! # 原对象语言中的目标全局良序句子

固定的原 Project 句子同时表达严格线序、每个非空集合的最小元以及所有严格
初段的集合性。它是已有理论的结论，不作为新公理加入任何理论。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def lo_universe_s : Sentence := Sentence.ofFormula
  (.conj (.forallE (.neg (lo_lt_m .newest .newest))) <|
    .conj (.forallE (.forallE (.forallE (.imp
      (.conj (lo_lt_m (.bound 2) (.bound 1)) (lo_lt_m (.bound 1) .newest)) (lo_lt_m (.bound 2) .newest))))) <|
      .conj (.forallE (.forallE (.disj (Formula.extensionalEq (.bound 1) .newest)
        (.disj (lo_lt_m (.bound 1) .newest) (lo_lt_m .newest (.bound 1)))))) <|
        .conj (.forallE (.imp (Formula.existsMem .newest .truth)
          (Formula.existsMem .newest (Formula.forallMem (.bound 1)
            (.disj (Formula.extensionalEq (.bound 1) .newest) (lo_lt_m (.bound 1) .newest))))))
          (.forallE (.existsE (.forallE (.iff (.mem .newest (.bound 1)) (lo_lt_m .newest (.bound 2)))))))
  (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])

theorem lo_universe_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) : M.SatisfiesSentence lo_universe_s := by
  rw [Structure.satisfiesSentence_iff]
  intro f
  have all : ∀ x : M.Domain, L_d x := (vl_sat_l (KPi.models_iff_l.mp hM).1 f).mp
    ((Structure.satisfiesSentence_iff M Axioms.vl_axiom).mp hVL f)
  simp only [lo_universe_s, Sentence.ofFormula, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_neg_iff, lo_lt_formula_l hM, Formula.satisfies_imp_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq (KPi.models_iff_l.mp hM).1.1, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_truth_iff, and_true, Formula.satisfies_exists_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff]
  exact ⟨lo_irrefl_l hM, (fun _ _ _ h => lo_trans_l hM h.1 h.2),
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
