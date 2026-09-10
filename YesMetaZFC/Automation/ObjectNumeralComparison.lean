import YesMetaZFC.Automation.ObjectNumeralReflection

/-! # 两个内部数码不等式反射的归纳公式

数值不等是对象公式的前提，结论为原证明图接受的不等式证明码。
-/
namespace YesMetaZFC.Automation.ObjectNumeralComparison
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def unequalAt {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (left right : SetTerm bound free) : SetFormula bound free :=
  let first : SetTerm bound (.set :: .set :: free) := .fvar (.there .here)
  let second : SetTerm bound (.set :: .set :: free) := .fvar .here
  let l := (left.weakenFree SetSort.set).weakenFree SetSort.set
  let r := (right.weakenFree SetSort.set).weakenFree SetSort.set
  (((first ∈ₘ ωₘ) ∧ₘ ((second ∈ₘ ωₘ) ∧ₘ
    (ObjectNumeralSyntax.condition l first ∧ₘ (ObjectNumeralSyntax.condition r second ∧ₘ (¬ₘ (l ≐ₘ r)))))) ⟶ₘ
      (NaturalProofPresentation.graph graph).provability (ProofT.IntrinsicQuotation.node 4
        [ProofT.IntrinsicQuotation.node 3 [first, second]])).forallFreeTop SetSort.set |>.forallFreeTop SetSort.set

def unequalAll {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (left : SetTerm bound free) : SetFormula bound free :=
  (((.fvar .here : SetTerm bound (.set :: free)) ∈ₘ ωₘ) ⟶ₘ
    unequalAt graph (left.weakenFree SetSort.set) (.fvar .here)).forallFreeTop SetSort.set

end YesMetaZFC.Automation.ObjectNumeralComparison
