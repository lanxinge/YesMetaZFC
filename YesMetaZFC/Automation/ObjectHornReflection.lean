import YesMetaZFC.Automation.ObjectNumeralQuantifiers
import YesMetaZFC.Automation.ObjectProjection

/-! # Horn 图反射的公共公式骨架 -/
namespace YesMetaZFC.Automation.ObjectHornReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectNumeralReflection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 第二槽不参与图，供公共双参数同余接口使用。 -/
def template (rules : List ObjectHorn.Rule) : ProofT.FormulaTemplate.Binary :=
  ⟨ObjectHorn.condition rules (.fvar .here)⟩

theorem template_apply (rules : List ObjectHorn.Rule) {bound free : SetContext} (row other : SetTerm bound free) :
    template rules row other = ObjectHorn.condition rules row := by
  unfold template ProofT.FormulaTemplate.apply_two ProofT.FormulaTemplate.instantiate
  dsimp only
  simp only [ObjectHorn.condition, ObjectTrace.condition_substituteMapped, Term.substituteMapped]
  rfl

def atRow {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (rules : List ObjectHorn.Rule) (row : SetTerm bound free) : SetFormula bound free :=
  forallNumeral row ((NaturalProofPresentation.graph graph).provability
    (ObjectCodeInstantiation.formula ProofT.IntrinsicQuotation.node (fun _ => .fvar .here) (template rules).body))

def onNaturals (graph : ProofT.Delta0ProofGraph) (rules : List ObjectHorn.Rule) : SetSentence :=
  forallNatural (ObjectHorn.condition rules (.fvar .here) ⟶ₘ atRow graph rules (.fvar .here))

def naturals {free : SetContext} {n : Nat} (inputs : Fin n → SetOpenTerm free) : SetOpenFormula free :=
  ObjectHorn.allOf (List.ofFn (fun i => inputs i ∈ₘ ωₘ))
def bounds {free : SetContext} (rule : ObjectHorn.Rule) (inputs : Fin rule.arity → SetOpenTerm free) : SetOpenFormula free :=
  ObjectHorn.allOf (List.ofFn (fun i => inputs i ∈ₘ Sₘ(rule.head.term inputs)))

def guards {free : SetContext} (rule : ObjectHorn.Rule) (inputs : Fin rule.arity → SetOpenTerm free) : SetOpenFormula free :=
  ObjectHorn.allOf (rule.guards.map (fun guard => guard.1.term inputs ∈ₘ guard.2.term inputs))
def premises {free : SetContext} (rules : List ObjectHorn.Rule) (rule : ObjectHorn.Rule)
    (inputs : Fin rule.arity → SetOpenTerm free) : SetOpenFormula free :=
  ObjectHorn.allOf (rule.premises.map (fun premise => ObjectHorn.condition rules (premise.term inputs)))

def getAt {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (index : SetTerm bound free) : SetFormula bound free :=
  let row := ProofT.IntrinsicQuotation.node 1 [(.fvar (.there .here)),
    (index.weakenFree SetSort.set).weakenFree SetSort.set, .fvar .here]
  forallNatural (forallNatural (ObjectHorn.condition ObjectProjection.rules row ⟶ₘ atRow graph ObjectProjection.rules row))

end YesMetaZFC.Automation.ObjectHornReflection
