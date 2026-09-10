import YesMetaZFC.Automation.ObjectNumeralQuantifiers

/-! # 自然数有界全称的码骨架与证明组合性质 -/
namespace YesMetaZFC.Automation.ObjectBoundedReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectNumeralReflection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def allAt {free : SetContext} (body : SetFormula [.set] free) (limit : SetOpenTerm free) : SetOpenFormula free :=
  .forallE .set ((.bvar .here ∈ₘ limit.weakenBound SetSort.set) ⟶ₘ body)

def existsAt {free : SetContext} (body : SetFormula [.set] free) (limit : SetOpenTerm free) : SetOpenFormula free :=
  .existsE .set ((.bvar .here ∈ₘ limit.weakenBound SetSort.set) ∧ₘ body)

def allBody {free : SetContext} (body : SetOpenFormula (.set :: free)) : SetOpenFormula (.set :: free) :=
  allAt (body.abstractFreeTop.weakenFree SetSort.set) (.fvar .here)

def existsBody {free : SetContext} (body : SetOpenFormula (.set :: free)) : SetOpenFormula (.set :: free) :=
  existsAt (body.abstractFreeTop.weakenFree SetSort.set) (.fvar .here)

def nextBody {free : SetContext} (body : SetOpenFormula (.set :: free)) : SetOpenFormula (.set :: free) :=
  allAt (body.abstractFreeTop.weakenFree SetSort.set) (Sₘ(.fvar .here))

def zeroBody {free : SetContext} (body : SetOpenFormula (.set :: free)) : SetOpenFormula free :=
  allAt body.abstractFreeTop ∅ₘ

def counterGuard {free : SetContext} : SetOpenFormula (.set :: .set :: free) :=
  .fvar (.there .here) ∈ₘ .fvar .here

def counterResult {free : SetContext} (body : SetOpenFormula (.set :: free)) : SetOpenFormula (.set :: .set :: free) :=
  allAt ((body.abstractFreeTop.weakenFree SetSort.set).weakenFree SetSort.set) (.fvar .here)

universe u
def allCode {α : Type u} (node : Nat → List α → α) (body limit : α) : α :=
  node 9 [node 7 [(node 2 [(node RelationSymbol.membership.ctorIdx []), (node 0 [node 0 []]), limit]), body]]

/-- 归纳性质只涉及实际数码图与证明图，不把任意外部性质用于分离。 -/
def bundleAt {parameters free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (body : SetOpenFormula (.set :: free)) (values : Nat → SetOpenTerm parameters)
    (limit : SetOpenTerm parameters) : SetOpenFormula parameters :=
  let inputs := forallNatural
    (((.fvar .here) ∈ₘ limit.weakenFree SetSort.set) ⟶ₘ
      forallNumeral (.fvar .here)
        ((NaturalProofPresentation.graph graph).provability
          (ObjectCodeInstantiation.formula ProofT.IntrinsicQuotation.node
            (ObjectCodeInstantiation.prepend (.fvar .here)
              (fun i => ((values i).weakenFree SetSort.set).weakenFree SetSort.set)) body)))
  let output := forallNumeral limit
    ((NaturalProofPresentation.graph graph).provability
      (ObjectCodeInstantiation.formula ProofT.IntrinsicQuotation.node
        (ObjectCodeInstantiation.prepend (.fvar .here) (fun i => (values i).weakenFree SetSort.set)) (allBody body)))
  inputs ⟶ₘ output

end YesMetaZFC.Automation.ObjectBoundedReflection
