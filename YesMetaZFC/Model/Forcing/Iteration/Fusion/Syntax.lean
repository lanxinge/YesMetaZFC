import YesMetaZFC.Model.Forcing.Iteration.Limit.Basic
import YesMetaZFC.Model.Forcing.Iteration.Fusion.Countable

/-! # 可数支撑融合的内部前缀族

指标和条件族都是模型内集合。较早条件严格等于较晚条件的限制；融合时取这些
条件图的并，而不是对外部自然数序列假设模型内收集。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

structure Row_fusion_d (I : kpair_convention_l.Interpretation M) (δ F J Q : M.Domain) : Prop where
  function : M.IsSetFunction I Q
  domain : M.IsDomainOf I J Q
  subset : M.MemberSubset J δ
  cofinal : ∀ i, M.mem i δ → ∃ α, M.mem α J ∧ M.mem i α
  conditions : ∀ α p, Entry_d M α p Q → ∃ B, Entry_d M α B F ∧ M.mem p B
  coherent : ∀ α β p q, Entry_d M α p Q → Entry_d M β q Q → M.MemberSubset α β → M.IsRestrictionOf I p q α

def row_fusion_m {n} (δ F J Q : Term n) : Formula 1 n :=
  .conj (Formula.isFunction kpair_convention_l Q)
    (.conj (Formula.isDomain kpair_convention_l J Q) (.conj (Formula.subset J δ)
      (.conj (Formula.forallMem δ (.existsE (.conj (.mem .newest J.weaken.weaken) (.mem (.bound 1) .newest))))
        (.conj (.forallE (.forallE (.imp (entry_m (.bound 1) .newest Q.weaken.weaken)
          (.existsE (.conj (entry_m (.bound 2) .newest F.weaken.weaken.weaken) (.mem (.bound 1) .newest))))))
          (.forallE (.forallE (.forallE (.forallE
            (.imp (entry_m (.bound 3) (.bound 1) Q.weaken.weaken.weaken.weaken)
              (.imp (entry_m (.bound 2) .newest Q.weaken.weaken.weaken.weaken)
                (.imp (Formula.subset (.bound 3) (.bound 2))
                  (Formula.isRestriction kpair_convention_l (.bound 1) .newest (.bound 3)))))))))))))
derive_free_closed row_fusion_m

theorem row_fusion_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (δ F J Q : Term n) : Formula.satisfies ρ (row_fusion_m δ F J Q) ↔
      Row_fusion_d I (δ.eval ρ) (F.eval ρ) (J.eval ρ) (Q.eval ρ) := by
  simp only [row_fusion_m, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hE, Formula.satisfies_isRestriction_iff I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h => ⟨h.function, h.domain, h.subset, h.cofinal, h.conditions, h.coherent⟩⟩

end YesMetaZFC.Model.Forcing.Internal
