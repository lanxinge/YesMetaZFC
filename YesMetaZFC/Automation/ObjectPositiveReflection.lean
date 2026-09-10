import YesMetaZFC.Automation.ObjectNumeralReflection

/-! # 原查询成立时的统一数码实例可证明性 -/
namespace YesMetaZFC.Automation.ObjectPositiveReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def onNaturals (graph : ProofT.Delta0ProofGraph) (body : SetOpenFormula [.set]) : SetSentence :=
  ((((.fvar .here : SetOpenTerm [.set]) ∈ₘ ωₘ) ∧ₘ body) ⟶ₘ
    ObjectNumeralReflection.atNumber graph body (.fvar .here)).forallFreeTop SetSort.set

end YesMetaZFC.Automation.ObjectPositiveReflection
