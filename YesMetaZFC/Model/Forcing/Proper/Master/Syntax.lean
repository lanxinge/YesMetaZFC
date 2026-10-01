import YesMetaZFC.Model.Forcing.CCC.Basic

/-! # 内部主条件的原公式

N 是地模型中的实际集合。主条件要求 N 中每个稠密集与 N 的交在该条件以下
预稠密；它不要求 N 的全部元素本身成为滤子。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Dense_set_d (B R z D : M.Domain) : Prop :=
  (∀ p, M.mem p D → M.mem p B ∧ p ≠ z) ∧
  ∀ p, M.mem p B → p ≠ z → ∃ q, Below_d M B R z q p ∧ M.mem q D

def Mstr_d (B R z N q : M.Domain) : Prop :=
  M.mem q B ∧ q ≠ z ∧ ∀ D, M.mem D N → Dense_set_d M B R z D →
    ∀ r, Below_d M B R z r q → ∃ s, M.mem s D ∧ M.mem s N ∧ Cmp_d M B R z r s

def dense_set_m {n} (B R z D : Term n) : Formula 1 n :=
  .conj (Formula.forallMem D (.conj (.mem .newest B.weaken) (.neg (Formula.extensionalEq .newest z.weaken))))
    (Formula.forallMem B (.imp (.neg (Formula.extensionalEq .newest z.weaken))
      (.existsE (.conj (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest (.bound 1))
        (.mem .newest D.weaken.weaken)))))
derive_free_closed dense_set_m

def mstr_m {n} (B R z N q : Term n) : Formula 1 n :=
  .conj (.mem q B) (.conj (.neg (Formula.extensionalEq q z))
    (Formula.forallMem N (.imp (dense_set_m B.weaken R.weaken z.weaken .newest)
      (.forallE (.imp (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest q.weaken.weaken)
        (.existsE (.conj (.mem .newest (.bound 2)) (.conj (.mem .newest N.weaken.weaken.weaken)
          (cmp_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken (.bound 1) .newest)))))))))
derive_free_closed mstr_m

theorem dense_set_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z D : Term n) :
    Formula.satisfies ρ (dense_set_m B R z D) ↔ Dense_set_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (D.eval ρ) := by
  simp only [dense_set_m, Dense_set_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, below_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push]
  rfl

theorem mstr_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z N q : Term n) :
    Formula.satisfies ρ (mstr_m B R z N q) ↔ Mstr_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (N.eval ρ) (q.eval ρ) := by
  simp only [mstr_m, Mstr_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    dense_set_sat_l M hE, below_sat_l M hE, cmp_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

end YesMetaZFC.Model.Forcing.Internal
