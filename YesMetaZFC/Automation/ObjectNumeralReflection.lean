import YesMetaZFC.Automation.ObjectCodeInstantiation
import YesMetaZFC.Automation.ObjectNumeralSyntaxSpecifications
import YesMetaZFC.Automation.NaturalProofPresentation

/-! # 数码实例可证明性的实际对象公式

性质由给定证明图解释，不新增公理。构造码的项只遍历固定公式骨架。
-/
namespace YesMetaZFC.Automation.ObjectNumeralReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def instanceCode {bound free : SetContext} (body : SetOpenFormula [.set])
    (named : SetTerm bound free) : SetTerm bound free :=
  ObjectCodeInstantiation.formula ProofT.IntrinsicQuotation.node (fun _ => named) body

/-- 所有合法数码输出都具有该固定公式实例的内部证明。 -/
def atNumber {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (body : SetOpenFormula [.set]) (input : SetTerm bound free) : SetFormula bound free :=
  let named : SetTerm bound (.set :: free) := .fvar .here
  (((named ∈ₘ ωₘ) ∧ₘ ObjectNumeralSyntax.condition (input.weakenFree SetSort.set) named) ⟶ₘ
    (NaturalProofPresentation.graph graph).provability (instanceCode body named)).forallFreeTop SetSort.set

/-- 以自然数为输入域的统一数码实例可证明性句子。 -/
def onNaturals (graph : ProofT.Delta0ProofGraph) (body : SetOpenFormula [.set]) : SetSentence :=
  (((.fvar .here : SetOpenTerm [.set]) ∈ₘ ωₘ) ⟶ₘ
    atNumber graph body (.fvar .here)).forallFreeTop SetSort.set

end YesMetaZFC.Automation.ObjectNumeralReflection
