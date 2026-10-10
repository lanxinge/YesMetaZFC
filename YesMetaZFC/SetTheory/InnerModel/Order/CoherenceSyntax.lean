import YesMetaZFC.SetTheory.InnerModel.Order.Hierarchy
import YesMetaZFC.SetTheory.InnerModel.Order.JoinOrder

/-! # 有序微层级归纳所用的原公式

同时归纳当前层的良序性及所有前层微后继到当前层的端延拓。
这是背景 KPi 的实际公式归纳实例，索引不作外部良基递归。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def js_value_m {n} (a U R : Term n) : Formula 1 n := .existsE
  (.conj (js_state_m a.weaken .newest) (kpair0_m .newest U.weaken R.weaken))
derive_free_closed js_value_m
theorem js_value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (a U R : Term n) :
    Formula.satisfies ρ (js_value_m a U R) ↔ Js_value_d (a.eval ρ) (U.eval ρ) (R.eval ρ) := by
  simp only [js_value_m, Js_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    js_state_sat_l, kpair0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def rw_successor_m {n} (U R V S : Term n) : Formula 1 n :=
  binary_pred_m rw_successor_s.schema (Fin.cases R (fun _ => S)) U V
@[simp] theorem rw_successor_closed_l {n} (U R V S : Term n)
    (hU : U.freeSupport = []) (hR : R.freeSupport = []) (hV : V.freeSupport = []) (hS : S.freeSupport = []) :
    (rw_successor_m U R V S).FreeClosed := binary_pred_closed_l _ _ _ _ (Fin.cases hR (fun _ => hS)) hU hV
theorem rw_successor_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (U R V S : Term n) :
    Formula.satisfies ρ (rw_successor_m U R V S) ↔ Rw_successor_d (U.eval ρ) (R.eval ρ) (V.eval ρ) (S.eval ρ) := by
  rw [rw_successor_m, binary_pred_sat_l, rw_successor_sat_l hKP]
  rfl

def rw_end_m {n} (U R V S : Term n) : Formula 1 n := .conj (Formula.subset U V)
  (.forallE (.forallE (.imp (.mem .newest U.weaken.weaken)
    (.iff (rd_entry0_m (.bound 1) .newest S.weaken.weaken)
      (.conj (.mem (.bound 1) U.weaken.weaken) (rd_entry0_m (.bound 1) .newest R.weaken.weaken))))))
derive_free_closed rw_end_m
theorem rw_end_sat_l (hE : Extensional M) {n} (ρ : Env M n) (U R V S : Term n) :
    Formula.satisfies ρ (rw_end_m U R V S) ↔ Rw_end_d (U.eval ρ) (R.eval ρ) (V.eval ρ) (S.eval ρ) := by
  simp only [rw_end_m, Rw_end_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def js_coherence_s : UnarySchema 0 where
  body := .imp (KP.ord0_m .newest) (.forallE (.forallE
    (.imp (js_value_m (.bound 2) (.bound 1) .newest)
      (.conj (Formula.isTransitive (.bound 1))
        (.conj (Formula.isSetCodedWellOrder kpair_convention_l .newest (.bound 1))
          (Formula.forallMem (.bound 2) (.forallE (.forallE (.forallE (.forallE
            (.imp (js_value_m (.bound 4) (.bound 3) (.bound 2))
              (.imp (rw_successor_m (.bound 3) (.bound 2) (.bound 1) .newest)
                (rw_end_m (.bound 1) .newest (.bound 6) (.bound 5))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem js_coherence_sat_l (hKP : M.Models KP) (ρ : Env M 0) (a : M.Domain) :
    js_coherence_s.denote ρ a ↔ (M.IsOrdinal a → ∀ U R, Js_value_d a U R → M.TransitiveSet U ∧
      M.IsSetCodedWellOrder (kp_pair_l hKP) R U ∧ ∀ b, M.mem b a → ∀ A S V T,
        Js_value_d b A S → Rw_successor_d A S V T → Rw_end_d V T U R) := by
  simp only [UnarySchema.denote, js_coherence_s, Formula.satisfies_imp_iff, KP.ord0_sat_l hKP,
    Formula.satisfies_forall_iff, js_value_sat_l hKP.1, Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_isSetCodedWellOrder_iff (kp_pair_l hKP),
    Formula.satisfies_forallMem_iff, rw_successor_formula_l hKP, rw_end_sat_l hKP.1]; rfl

end YesMetaZFC.SetTheory.InnerModel
