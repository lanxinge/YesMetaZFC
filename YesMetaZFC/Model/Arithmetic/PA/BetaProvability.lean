import YesMetaZFC.Model.Arithmetic.Completeness
import YesMetaZFC.Model.Arithmetic.PA.BetaSequence
import YesMetaZFC.Model.Arithmetic.Sequence

/-! # β 读取总性与唯一性的对象推导 -/
namespace YesMetaZFC.Model.Arithmetic.PA.Beta.Provability
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false

variable {T : Theory signature_m} (hPA : Theory.Extends T Logic.Arithmetic.PA.theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem total_m (b c i : Term signature_m [] Δ .num) :
    Derives T Γ (Logic.Arithmetic.Beta.domain_m b c i) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  exact (domain_sat_m η b c i).mpr (Beta.total_m hℳ _ _ _)

theorem unique_m (b c i a d : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (Logic.Arithmetic.Beta.graph_m b c i a)
      (.imp (Logic.Arithmetic.Beta.graph_m b c i d) (.equal a d))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, graph_sat_m]
  exact fun ha hd => Beta.unique_m hℳ ha hd

theorem sequence_m (φ : OpenFormula signature_m (.num :: .num :: Δ)) (n : Term signature_m [] Δ .num) :
    Derives T Γ ((Formula.imp (Logic.Arithmetic.FiniteRange.segment_m φ lt_m)
      (Logic.Arithmetic.Sequence.code_m φ lt_m Logic.Arithmetic.Beta.graph_m)).instantiateFreeTop n) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  rw [Formula.satisfies_instantiateFreeTop]
  simp only [Formula.satisfies, FiniteRange.segment_sat_m _ _ _ lt_m lt_l lt_sat_m,
    Sequence.code_sat_m _ _ _ lt_m Logic.Arithmetic.Beta.graph_m lt_l graph_l lt_sat_m graph_sat_m]
  exact Beta.sequence_m hℳ φ η (n.eval η)

end YesMetaZFC.Model.Arithmetic.PA.Beta.Provability
