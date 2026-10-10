import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.Tail

/-! # 有限尾支撑反链计数的内部归纳公式 -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_bounded_ccc_d (I : kpair_convention_l.Interpretation M) (δ F H P V ω n : M.Domain) : Prop :=
  ∀ α B R A, M.mem α δ → Entry_d M α B F → Entry_d M α R H → Antichain_d M P V P A →
    (∀ p, M.mem p A → Row_tail_bound_d I α p n) → M.CardinalLessOrEqual I A ω

def row_bounded_ccc_m {n} (δ F H P V ω k : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 3) δ.weaken.weaken.weaken.weaken)
      (.imp (entry_m (.bound 3) (.bound 2) F.weaken.weaken.weaken.weaken)
        (.imp (entry_m (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken)
          (.imp (antichain_m P.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken
            P.weaken.weaken.weaken.weaken .newest)
            (.imp (Formula.forallMem .newest (row_tail_bound_m (.bound 4) .newest k.weaken.weaken.weaken.weaken.weaken))
              (Formula.cardinalLessOrEqual kpair_convention_l .newest ω.weaken.weaken.weaken.weaken)))))))))
derive_free_closed row_bounded_ccc_m

theorem row_bounded_ccc_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (δ F H P V ω k : Term n) : Formula.satisfies ρ (row_bounded_ccc_m δ F H P V ω k) ↔
      Row_bounded_ccc_d I (δ.eval ρ) (F.eval ρ) (H.eval ρ) (P.eval ρ) (V.eval ρ) (ω.eval ρ) (k.eval ρ) := by
  simp only [row_bounded_ccc_m, Row_bounded_ccc_d, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, entry_sat_l M hE, antichain_sat_l M hE,
    Formula.satisfies_forallMem_iff, row_tail_bound_sat_l I hE,
    Formula.satisfies_cardinalLessOrEqual_iff I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
