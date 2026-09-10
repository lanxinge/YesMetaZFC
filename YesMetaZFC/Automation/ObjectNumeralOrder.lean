import YesMetaZFC.Automation.ObjectNumeralQuantifiers

/-! # 自然数严格序正负反射的实际对象公式 -/
namespace YesMetaZFC.Automation.ObjectNumeralOrder
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectNumeralReflection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def body : SetOpenFormula [.set,.set] := (.fvar .here) ∈ₘ (.fvar (.there .here))

def atPair {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (left right : SetTerm bound free) : SetFormula bound free :=
  let values := ObjectCodeInstantiation.prepend
    (.fvar (.there .here) : SetTerm bound (.set :: .set :: free)) (fun _ => .fvar .here)
  let code := ObjectCodeInstantiation.formula ProofT.IntrinsicQuotation.node values body
  let truth := (left.weakenFree SetSort.set).weakenFree SetSort.set ∈ₘ
    (right.weakenFree SetSort.set).weakenFree SetSort.set
  forallNumeral left (forallNumeral (right.weakenFree SetSort.set)
    (signed graph truth code))

def atRight {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (right : SetTerm bound free) : SetFormula bound free :=
  forallNatural (atPair graph (.fvar .here) (right.weakenFree SetSort.set))

end YesMetaZFC.Automation.ObjectNumeralOrder
