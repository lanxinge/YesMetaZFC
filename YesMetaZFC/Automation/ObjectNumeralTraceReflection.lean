import YesMetaZFC.Automation.ObjectNumeralQuantifiers

/-! # 数码递归图自身反射的可分离公式 -/
namespace YesMetaZFC.Automation.ObjectNumeralTraceReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectNumeralReflection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def template : ProofT.FormulaTemplate.Binary :=
  ⟨ObjectNumeralSyntax.condition (.fvar .here) (.fvar (.there .here))⟩

theorem template_apply {bound free : SetContext} (input output : SetTerm bound free) :
    template input output = ObjectNumeralSyntax.condition input output := by
  unfold template ProofT.FormulaTemplate.apply_two ProofT.FormulaTemplate.instantiate
  dsimp only
  rw [ObjectNumeralSyntax.condition_substituteMapped]
  rfl

def nextTerm {bound free : SetContext} (output : SetTerm bound free) : SetTerm bound free :=
  ProofT.IntrinsicQuotation.node 2 [numₘ(ObjectNumeralSyntax.successorSymbol), output]

/-- 图真值、数码命名与内部可证明性都使用既有原公式。 -/
def atInput {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (input : SetTerm bound free) : SetFormula bound free :=
  forallNatural
    (ObjectNumeralSyntax.condition (input.weakenFree SetSort.set) (.fvar .here) ⟶ₘ
      forallNumeral (input.weakenFree SetSort.set)
        (forallNumeral (.fvar (.there .here))
          ((NaturalProofPresentation.graph graph).provability
            (ObjectCodeInstantiation.formula ProofT.IntrinsicQuotation.node
              (ObjectCodeInstantiation.prepend (.fvar (.there .here)) (fun _ => .fvar .here)) template.body))))

end YesMetaZFC.Automation.ObjectNumeralTraceReflection
