import YesMetaZFC.Automation.ObjectNumeralReflection

/-! # 数码反射共用的受限量词

每次只增加一个数码槽位；序关系与算术复用相同的绑定和语义接口。
-/
namespace YesMetaZFC.Automation.ObjectNumeralReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

universe u v

theorem map_prepend {α : Type u} {β : Type v} (f : α → β) (first : α) (rest : Nat → α) :
    (fun i => f (ObjectCodeInstantiation.prepend first rest i)) =
      ObjectCodeInstantiation.prepend (f first) (fun i => f (rest i)) := by
  funext i; cases i <;> rfl

def signed {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (truth : SetFormula bound free) (code : SetTerm bound free) : SetFormula bound free :=
  (truth ⟶ₘ (NaturalProofPresentation.graph graph).provability code) ∧ₘ
    ((¬ₘ truth) ⟶ₘ (NaturalProofPresentation.graph graph).provability (ProofT.IntrinsicQuotation.node 4 [code]))

def forallNumeral {bound free : SetContext} (input : SetTerm bound free)
    (body : SetFormula bound (.set :: free)) : SetFormula bound free :=
  ((((.fvar .here : SetTerm bound (.set :: free)) ∈ₘ ωₘ) ∧ₘ
    ObjectNumeralSyntax.condition (input.weakenFree SetSort.set) (.fvar .here)) ⟶ₘ body).forallFreeTop SetSort.set

def forallNatural {bound free : SetContext}
    (body : SetFormula bound (.set :: free)) : SetFormula bound free :=
  (((.fvar .here : SetTerm bound (.set :: free)) ∈ₘ ωₘ) ⟶ₘ body).forallFreeTop SetSort.set

end YesMetaZFC.Automation.ObjectNumeralReflection
