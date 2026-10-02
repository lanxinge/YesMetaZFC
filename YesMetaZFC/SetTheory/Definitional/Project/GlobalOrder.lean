import YesMetaZFC.SetTheory.Definitional.Project.Predicate
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv

/-! # 由二元公式实例化的全局良序句子

句子同时表达严格线序、每个非空集合的最小元和所有严格初段的集合性。
模板不依赖任何内模型或良序构造；语义展开仅需外延性。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Gw_order_d (r : M.Domain → M.Domain → Prop) : Prop :=
  (∀ x, ¬ r x x) ∧ (∀ x y z, r x y → r y z → r x z) ∧
  (∀ x y, x = y ∨ r x y ∨ r y x) ∧
  (∀ X, (∃ x, M.mem x X) → ∃ x, M.mem x X ∧ ∀ y, M.mem y X → x = y ∨ r x y) ∧
  ∀ x, ∃ I, ∀ y, M.mem y I ↔ r y x

def gw_pred_m {n} (φ : BinarySchema 0) (x y : Term n) : Formula 1 n := binary_pred_m φ Fin.elim0 x y
derive_free_closed gw_pred_m
theorem gw_pred_sat_l (φ : BinarySchema 0) (ρ : Env M 0) {n} (η : Env M n) (x y : Term n) :
    Formula.satisfies η (gw_pred_m φ x y) ↔ φ.denote ρ (x.eval η) (y.eval η) := by
  rw [gw_pred_m, binary_pred_sat_l]
  exact Formula.closed_env_l _ φ.freeClosed (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))

def gw_sentence_s (φ : BinarySchema 0) : Sentence := Sentence.ofFormula
  (.conj (.forallE (.neg (gw_pred_m φ .newest .newest))) <|
    .conj (.forallE (.forallE (.forallE (.imp
      (.conj (gw_pred_m φ (.bound 2) (.bound 1)) (gw_pred_m φ (.bound 1) .newest)) (gw_pred_m φ (.bound 2) .newest))))) <|
      .conj (.forallE (.forallE (.disj (Formula.extensionalEq (.bound 1) .newest)
        (.disj (gw_pred_m φ (.bound 1) .newest) (gw_pred_m φ .newest (.bound 1)))))) <|
        .conj (.forallE (.imp (Formula.existsMem .newest .truth)
          (Formula.existsMem .newest (Formula.forallMem (.bound 1)
            (.disj (Formula.extensionalEq (.bound 1) .newest) (gw_pred_m φ (.bound 1) .newest))))))
          (.forallE (.existsE (.forallE (.iff (.mem .newest (.bound 1)) (gw_pred_m φ .newest (.bound 2)))))))
  (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])

theorem gw_sentence_sat_l (hE : Extensional M) (φ : BinarySchema 0) (ρ : Env M 0) :
    Formula.satisfies ρ (gw_sentence_s φ).formula ↔ Gw_order_d (φ.denote ρ) := by
  simp only [gw_sentence_s, Sentence.ofFormula, Gw_order_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, gw_pred_sat_l φ ρ,
    Formula.satisfies_imp_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_truth_iff,
    and_true, and_imp, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff]
  rfl

end YesMetaZFC.SetTheory.Definitional.Project
