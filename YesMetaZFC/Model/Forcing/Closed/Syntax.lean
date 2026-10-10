import YesMetaZFC.Model.Forcing.Closed.Basic

/-! # 内部可数闭性的原公式

下降链与下界都由模型内部集合编码，闭性可直接置于名称力迫及内部归纳中。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def chain_m {n} (B R z ω f : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo kpair_convention_l f ω B)
    (.conj (.forallE (.forallE (.imp (entry_m (.bound 1) .newest f.weaken.weaken)
      (.neg (Formula.extensionalEq .newest z.weaken.weaken)))))
      (.forallE (.forallE (.forallE (.forallE
        (.imp (Formula.isSuccessor (.bound 2) (.bound 3))
          (.imp (entry_m (.bound 3) (.bound 1) f.weaken.weaken.weaken.weaken)
            (.imp (entry_m (.bound 2) .newest f.weaken.weaken.weaken.weaken)
              (entry_m .newest (.bound 1) R.weaken.weaken.weaken.weaken)))))))))
derive_free_closed chain_m

def chain_bound_m {n} (B R z f q : Term n) : Formula 1 n :=
  .conj (.mem q B) (.conj (.neg (Formula.extensionalEq q z))
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest f.weaken.weaken)
      (entry_m q.weaken.weaken .newest R.weaken.weaken)))))
derive_free_closed chain_bound_m

def closed_m {n} (B R z ω : Term n) : Formula 1 n :=
  .forallE (.imp (chain_m B.weaken R.weaken z.weaken ω.weaken .newest)
    (.existsE (chain_bound_m B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1) .newest)))
derive_free_closed closed_m

theorem chain_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z ω f : Term n) : Formula.satisfies ρ (chain_m B R z ω f) ↔
      Chain_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (ω.eval ρ) (f.eval ρ) := by
  simp only [chain_m, Chain_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, entry_m, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]
  rfl

theorem chain_bound_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z f q : Term n) :
    Formula.satisfies ρ (chain_bound_m B R z f q) ↔ M.mem (q.eval ρ) (B.eval ρ) ∧ q.eval ρ ≠ z.eval ρ ∧
      ∀ i p, M.PairMember I i p (f.eval ρ) → M.PairMember I (q.eval ρ) p (R.eval ρ) := by
  simp only [chain_bound_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_m, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem closed_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z ω : Term n) : Formula.satisfies ρ (closed_m B R z ω) ↔
      Closed_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (ω.eval ρ) := by
  simp only [closed_m, Closed_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, chain_sat_l I hE, chain_bound_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
