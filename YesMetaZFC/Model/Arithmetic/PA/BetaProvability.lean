import YesMetaZFC.Model.Arithmetic.Completeness
import YesMetaZFC.Model.Arithmetic.PA.Beta

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

end YesMetaZFC.Model.Arithmetic.PA.Beta.Provability
