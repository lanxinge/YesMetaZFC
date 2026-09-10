import YesMetaZFC.Automation.ObjectNumeralQuantifiers

/-! # 二元算术项数码求值的公共归纳公式 -/
namespace YesMetaZFC.Automation.ObjectNumeralEvaluation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectNumeralReflection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

abbrev BinaryTerm := SetOpenTerm [.set,.set]

def termAt {bound free : SetContext} (operation : BinaryTerm) (left right : SetTerm bound free) : SetTerm bound free :=
  operation.substituteMapped VariableSubstitution.empty
    (VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty))

def body (operation : BinaryTerm) : SetOpenFormula [.set,.set,.set] :=
  operation.weakenFree SetSort.set ≐ₘ (.fvar .here)

def atPair {bound free : SetContext} (graph : ProofT.Delta0ProofGraph) (operation : BinaryTerm)
    (left right : SetTerm bound free) : SetFormula bound free :=
  let l := (left.weakenFree SetSort.set).weakenFree SetSort.set
  let r := (right.weakenFree SetSort.set).weakenFree SetSort.set
  let values := ObjectCodeInstantiation.prepend (.fvar .here : SetTerm bound (.set :: .set :: .set :: free))
    (ObjectCodeInstantiation.prepend (.fvar (.there (.there .here))) (fun _ => .fvar (.there .here)))
  forallNumeral left (forallNumeral (right.weakenFree SetSort.set)
    (forallNumeral (termAt operation l r)
      ((NaturalProofPresentation.graph graph).provability
        (ObjectCodeInstantiation.formula ProofT.IntrinsicQuotation.node values (body operation)))))

def atRight {bound free : SetContext} (graph : ProofT.Delta0ProofGraph) (operation : BinaryTerm)
    (right : SetTerm bound free) : SetFormula bound free :=
  forallNatural (atPair graph operation (.fvar .here) (right.weakenFree SetSort.set))

end YesMetaZFC.Automation.ObjectNumeralEvaluation
