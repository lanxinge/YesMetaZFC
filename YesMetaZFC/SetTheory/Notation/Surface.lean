import Lean.Elab.Term
import Init.Meta
import YesMetaZFC.SetTheory.Ord.Notation
import YesMetaZFC.SetTheory.Definitional.Project.Class
import YesMetaZFC.SetTheory.Definitional.Project.FlatPairing
import YesMetaZFC.SetTheory.Definitional.Project.Ord.Syntax

/-!
# 纯集合论纸面语法编译器

具名 binder 只存在于 elaboration 期间。编译器直接生成 intrinsically scoped 的
`Term depth` / `Formula depth`，不会经过自由变量占位符，也不会产生捕获风险。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Surface

open Lean
open Lean.Elab.Term

private structure Binder where
  name : Name
  term : Syntax

private def binderName (identifier : Syntax) : Name :=
  identifier.getId.eraseMacroScopes

private def findBinder? (binders : List Binder) (identifier : Syntax) : Option Binder :=
  binders.find? (·.name == binderName identifier)

private def asTerm (node : Syntax) : TSyntax `term :=
  ⟨node⟩

private def weakenTermSyntax (node : Syntax) : TermElabM Syntax := do
  let term : TSyntax `term := ⟨node⟩
  `(SetTheory.Definitional.Project.Term.weaken $term)

private def weakenFormulaSyntax (node : Syntax) : TermElabM Syntax := do
  let formula : TSyntax `term := ⟨node⟩
  `(SetTheory.Definitional.Project.Formula.weaken $formula)

private def weakenTermN (count : Nat) (node : Syntax) : TermElabM Syntax := do
  let mut result := node
  for _ in [:count] do
    result ← weakenTermSyntax result
  pure result

private def weakenFormulaN (count : Nat) (node : Syntax) : TermElabM Syntax := do
  let mut result := node
  for _ in [:count] do
    result ← weakenFormulaSyntax result
  pure result

private def liftBinders (binders : List Binder) : TermElabM (List Binder) :=
  binders.mapM fun binder => do
    pure {
      binder with
      term := ← weakenTermSyntax binder.term
    }

private partial def compileTerm (binders : List Binder) (binderDepth : Nat)
    (termSyntax : Syntax) : TermElabM Syntax := do
  match termSyntax with
  | `(setTerm| ($term:setTerm)) =>
      compileTerm binders binderDepth term
  | `(setTerm| #ᶠ[$id:num]) =>
      `(SetTheory.Definitional.Project.Term.free $id)
  | `(setTerm| ⌜$term:term⌝ₛ) =>
      weakenTermN binderDepth term.raw
  | `(setTerm| $identifier:ident) =>
      match findBinder? binders identifier with
      | some binder =>
          pure binder.term
      | none =>
          throwErrorAt identifier
            "未绑定的集合变量；请使用量词绑定，或用 `⌜term⌝ₛ` / `#ᶠ[id]` 显式注入"
  | _ =>
      throwErrorAt termSyntax "不支持的纯集合论项语法"

mutual

private partial def compileFormula (binders : List Binder) (binderDepth : Nat)
    (formulaSyntax : Syntax) : TermElabM Syntax := do
  let expanded ← Lean.Elab.liftMacroM <| Lean.expandMacros formulaSyntax
  match expanded with
  | `(setFormula| ⊥) =>
      `(SetTheory.Definitional.Formula.falsum)
  | `(setFormula| ⊤) =>
      `(SetTheory.Definitional.Formula.truth)
  | `(setFormula| ⌜$formula:term⌝ₚ) =>
      weakenFormulaN binderDepth formula.raw
  | `(setFormula| ($formula:setFormula)) =>
      compileFormula binders binderDepth formula
  | `(setFormula| $element:setTerm ∈ ⋃ $family:setTerm) =>
      let element ← compileTerm binders binderDepth element
      let family ← compileTerm binders binderDepth family
      `(SetTheory.Definitional.Project.Formula.existsMem $(asTerm family)
          (SetTheory.Definitional.Formula.mem
            (SetTheory.Definitional.Project.Term.weaken $(asTerm element))
            SetTheory.Definitional.Project.Term.newest))
  | `(setFormula| $subset:setTerm ∈ 𝒫($set:setTerm)) =>
      let subset ← compileTerm binders binderDepth subset
      let set ← compileTerm binders binderDepth set
      `(SetTheory.Definitional.Project.Formula.subset $(asTerm subset) $(asTerm set))
  | `(setFormula| $element:setTerm ∈
      ($left:setTerm ∩ $right:setTerm)) =>
      let element ← compileTerm binders binderDepth element
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Formula.conj
          (SetTheory.Definitional.Formula.mem $(asTerm element) $(asTerm left))
          (SetTheory.Definitional.Formula.mem $(asTerm element) $(asTerm right)))
  | `(setFormula| $element:setTerm ∈
      ($left:setTerm ∖ $right:setTerm)) =>
      let element ← compileTerm binders binderDepth element
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Formula.conj
          (SetTheory.Definitional.Formula.mem $(asTerm element) $(asTerm left))
          (SetTheory.Definitional.Formula.neg
            (SetTheory.Definitional.Formula.mem $(asTerm element) $(asTerm right))))
  | `(setFormula| ⟨$left:setTerm, $right:setTerm⟩
      ∈ $relation:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      let relation ← compileTerm binders binderDepth relation
      `(SetTheory.Definitional.Project.Formula.orderedPairMem
          SetTheory.Definitional.Project.FlatPairing.convention
          $(asTerm left) $(asTerm right) $(asTerm relation))
  | `(setFormula| ⟨$left:setTerm, $right:setTerm⟩[
      $convention:term] ∈ $relation:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      let relation ← compileTerm binders binderDepth relation
      `(SetTheory.Definitional.Project.Formula.orderedPairMem $convention
          $(asTerm left) $(asTerm right) $(asTerm relation))
  | `(setFormula| Rel($relation:setTerm)) =>
      let relation ← compileTerm binders binderDepth relation
      `(SetTheory.Definitional.Project.Formula.isRelation SetTheory.Definitional.Project.FlatPairing.convention
          $(asTerm relation))
  | `(setFormula| Rel[$convention:term]($relation:setTerm)) =>
      let relation ← compileTerm binders binderDepth relation
      `(SetTheory.Definitional.Project.Formula.isRelation $convention $(asTerm relation))
  | `(setFormula| Fun($function:setTerm)) =>
      let function ← compileTerm binders binderDepth function
      `(SetTheory.Definitional.Project.Formula.isFunction SetTheory.Definitional.Project.FlatPairing.convention
          $(asTerm function))
  | `(setFormula| Fun[$convention:term]($function:setTerm)) =>
      let function ← compileTerm binders binderDepth function
      `(SetTheory.Definitional.Project.Formula.isFunction $convention $(asTerm function))
  | `(setFormula| $function:setTerm :
      $source:setTerm ⟶ $target:setTerm) =>
      let function ← compileTerm binders binderDepth function
      let source ← compileTerm binders binderDepth source
      let target ← compileTerm binders binderDepth target
      `(SetTheory.Definitional.Project.Formula.isFunctionFromTo
          SetTheory.Definitional.Project.FlatPairing.convention
          $(asTerm function) $(asTerm source) $(asTerm target))
  | `(setFormula| $function:setTerm :[$convention:term]
      $source:setTerm ⟶ $target:setTerm) =>
      let function ← compileTerm binders binderDepth function
      let source ← compileTerm binders binderDepth source
      let target ← compileTerm binders binderDepth target
      `(SetTheory.Definitional.Project.Formula.isFunctionFromTo $convention
          $(asTerm function) $(asTerm source) $(asTerm target))
  | `(setFormula| Inj($function:setTerm)) =>
      let function ← compileTerm binders binderDepth function
      `(SetTheory.Definitional.Project.Formula.isInjective SetTheory.Definitional.Project.FlatPairing.convention
          $(asTerm function))
  | `(setFormula| Inj[$convention:term]($function:setTerm)) =>
      let function ← compileTerm binders binderDepth function
      `(SetTheory.Definitional.Project.Formula.isInjective $convention $(asTerm function))
  | `(setFormula| Trans($set:setTerm)) =>
      let set ← compileTerm binders binderDepth set
      `(SetTheory.Definitional.Project.Formula.isTransitive $(asTerm set))
  | `(setFormula| Ord($ordinal:setTerm)) =>
      let ordinal ← compileTerm binders binderDepth ordinal
      `(SetTheory.Definitional.Project.Formula.isOrdinal $(asTerm ordinal))
  | `(setFormula| $left:setTerm <ₒ $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Formula.mem $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setTerm ≤ₒ $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Project.Formula.subset $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setTerm ∈ $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Formula.mem $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setTerm ∉ $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Formula.neg
          (SetTheory.Definitional.Formula.mem $(asTerm left) $(asTerm right)))
  | `(setFormula| $left:setTerm = $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Project.Formula.extensionalEq $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setTerm ≠ $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Project.Formula.extensionalNe $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setTerm ⊆ $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Project.Formula.subset $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setTerm ⊊ $right:setTerm) =>
      let left ← compileTerm binders binderDepth left
      let right ← compileTerm binders binderDepth right
      `(SetTheory.Definitional.Project.Formula.properSubset $(asTerm left) $(asTerm right))
  | `(setFormula| ¬ $formula:setFormula) =>
      let formula ← compileFormula binders binderDepth formula
      `(SetTheory.Definitional.Formula.neg $(asTerm formula))
  | `(setFormula| $left:setFormula ∧ $right:setFormula) =>
      let left ← compileFormula binders binderDepth left
      let right ← compileFormula binders binderDepth right
      `(SetTheory.Definitional.Formula.conj $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setFormula ∨ $right:setFormula) =>
      let left ← compileFormula binders binderDepth left
      let right ← compileFormula binders binderDepth right
      `(SetTheory.Definitional.Formula.disj $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setFormula → $right:setFormula) =>
      let left ← compileFormula binders binderDepth left
      let right ← compileFormula binders binderDepth right
      `(SetTheory.Definitional.Formula.imp $(asTerm left) $(asTerm right))
  | `(setFormula| $left:setFormula ↔ $right:setFormula) =>
      let left ← compileFormula binders binderDepth left
      let right ← compileFormula binders binderDepth right
      `(SetTheory.Definitional.Formula.iff $(asTerm left) $(asTerm right))
  | `(setFormula| ∀ $identifiers:ident* , $body:setFormula) =>
      compileQuantifier true binders binderDepth
        (identifiers.toList.map (·.raw)) body
  | `(setFormula| ∃ $identifiers:ident* , $body:setFormula) =>
      compileQuantifier false binders binderDepth
        (identifiers.toList.map (·.raw)) body
  | `(setFormula| ∀ $identifier:ident ∈ $set:setTerm, $body:setFormula) =>
      let set ← compileTerm binders binderDepth set
      let compiledBody ← compileUnderBinder binders binderDepth identifier body
      `(SetTheory.Definitional.Project.Formula.forallMem $(asTerm set) $(asTerm compiledBody))
  | `(setFormula| ∃ $identifier:ident ∈ $set:setTerm, $body:setFormula) =>
      let set ← compileTerm binders binderDepth set
      let compiledBody ← compileUnderBinder binders binderDepth identifier body
      `(SetTheory.Definitional.Project.Formula.existsMem $(asTerm set) $(asTerm compiledBody))
  | _ =>
      throwErrorAt expanded "不支持的纯集合论公式语法"

private partial def compileUnderBinder (binders : List Binder) (binderDepth : Nat)
    (identifier : Syntax) (body : Syntax) : TermElabM Syntax := do
  let lifted ← liftBinders binders
  let newest ← `(SetTheory.Definitional.Project.Term.newest)
  let binder : Binder := {
    name := binderName identifier
    term := newest
  }
  compileFormula (binder :: lifted) (binderDepth + 1) body

private partial def compileQuantifier (universal : Bool) (binders : List Binder)
    (binderDepth : Nat) (identifiers : List Syntax) (body : Syntax) :
    TermElabM Syntax := do
  match identifiers with
  | [] =>
      compileFormula binders binderDepth body
  | identifier :: rest =>
      let lifted ← liftBinders binders
      let newest ← `(SetTheory.Definitional.Project.Term.newest)
      let binder : Binder := {
        name := binderName identifier
        term := newest
      }
      let compiled ←
        compileQuantifier universal (binder :: lifted) (binderDepth + 1) rest body
      let compiledTerm := asTerm compiled
      if universal then
        `(SetTheory.Definitional.Formula.forallE $compiledTerm)
      else
        `(SetTheory.Definitional.Formula.existsE $compiledTerm)

end

private def elaborateFormula (depth : Syntax) (formula : Syntax) : TermElabM Expr := do
  let compiled ← compileFormula [] 0 formula
  let compiledTerm : TSyntax `term := ⟨compiled⟩
  let depthTerm : TSyntax `term := ⟨depth⟩
  let result ← `(($compiledTerm : SetTheory.Definitional.Project.Formula 1 $depthTerm))
  elabTerm result none

elab (name := elaborateSetTheoryFormula)
    "set[" depth:term "]" " ⟪" formula:setFormula "⟫" : term =>
  elaborateFormula depth.raw formula.raw

elab (name := elaborateClosedSetTheoryFormula)
    "set!" " ⟪" formula:setFormula "⟫" : term =>
  elaborateFormula (Syntax.mkNumLit "0") formula.raw

elab (name := elaborateSetTheorySentence)
    "sentence!" " ⟪" formula:setFormula "⟫" : term => do
  let compiled ← compileFormula [] 0 formula.raw
  let compiledTerm : TSyntax `term := ⟨compiled⟩
  let result ←
    `((SetTheory.Definitional.Project.Sentence.ofFormula
        ($compiledTerm : SetTheory.Definitional.Project.OpenFormula)
        (by native_decide) : SetTheory.Definitional.Project.Sentence))
  elabTerm result none

private def elaborateClass (depth : Syntax) (identifier : Syntax)
    (body : Syntax) : TermElabM Expr := do
  let compiled ← compileUnderBinder [] 0 identifier body
  let compiledTerm : TSyntax `term := ⟨compiled⟩
  let depthTerm : TSyntax `term := ⟨depth⟩
  let result ← `(($compiledTerm : SetTheory.Definitional.Project.DefinableClass $depthTerm))
  elabTerm result none

elab (name := elaborateSetTheoryClass)
    "class[" depth:term "]" " ⟪" identifier:ident " | "
      body:setFormula "⟫" : term =>
  elaborateClass depth.raw identifier.raw body.raw

elab (name := elaborateClosedSetTheoryClass)
    "class!" " ⟪" identifier:ident " | " body:setFormula "⟫" : term =>
  elaborateClass (Syntax.mkNumLit "0") identifier.raw body.raw

end Surface
end SetTheory
end YesMetaZFC
