import Lean.Elab.Term
import Init.Meta
import YesMetaZFC.Logic.Notation.Relation

/-!
# 一阶逻辑数学 DSL 编译器

具名 binder 只存在于宏展开期间。编译器为 binder 分配临时 free id，展开 body 后
调用核心 `Formula.closeFreeAt`，最后得到普通的 sorted locally nameless AST。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Surface

open Lean
open Lean.Elab.Term

/-- 带参数数目检查的函数应用；定义透明归约为核心构造子。 -/
def checkedApp {σ : Signature} (function : σ.FuncSymbol) (arguments : List (Term σ))
    (_arity : arguments.length = σ.funcArity function := by decide) : Term σ :=
  .app function arguments

/-- 带参数数目检查的关系应用；定义透明归约为核心构造子。 -/
def checkedRel {σ : Signature} (relation : σ.RelSymbol) (arguments : List (Term σ))
    (_arity : arguments.length = σ.relArity relation := by decide) : Formula σ :=
  .rel relation arguments

private structure Binder where
  name : Name
  sort : TSyntax `term
  id : Nat

private abbrev CompileM := StateT Nat TermElabM

private def freshFreeId : CompileM Nat := do
  let next ← get
  set (next + 1)
  pure next

private def binderName (identifier : Syntax) : Name :=
  identifier.getId.eraseMacroScopes

private def findBinder? (binders : List Binder) (identifier : Syntax) : Option Binder :=
  binders.find? (·.name == binderName identifier)

private def asTerm (rawSyntax : Syntax) : TSyntax `term :=
  ⟨rawSyntax⟩

private def mkTermList (termNodes : Array Syntax) : TermElabM Syntax := do
  let mut result ← `(List.nil)
  for termNode in termNodes.reverse do
    let node : TSyntax `term := ⟨termNode⟩
    let tail : TSyntax `term := ⟨result⟩
    result ← `(List.cons $node $tail)
  pure result

private partial def compileTerm (binders : List Binder) (termSyntax : Syntax) :
    CompileM Syntax := do
  match termSyntax with
  | `(foTerm| ($term:foTerm)) =>
      compileTerm binders term
  | `(foTerm| #ᶠ[$sort:term, $id:num]) =>
      `(FirstOrder.Term.var (FirstOrder.Var.fvar $sort $id))
  | `(foTerm| ⌜$term:term⌝ₜ) =>
      pure term
  | `(foTerm| 𝒇[$function:term]($arguments:foTerm,*)) =>
      let compiled ← arguments.getElems.mapM (compileTerm binders)
      let list ← StateT.lift <| mkTermList compiled
      let listTerm : TSyntax `term := ⟨list⟩
      `(Surface.checkedApp $function $listTerm)
  | `(foTerm| $function:ident($arguments:foTerm,*)) =>
      let compiled ← arguments.getElems.mapM (compileTerm binders)
      let list ← StateT.lift <| mkTermList compiled
      let listTerm : TSyntax `term := ⟨list⟩
      `(Surface.checkedApp $function $listTerm)
  | `(foTerm| $identifier:ident) =>
      match findBinder? binders identifier with
      | some binder =>
          `(FirstOrder.Term.var
              (FirstOrder.Var.fvar $(binder.sort) $(quote binder.id)))
      | none =>
          throwErrorAt identifier
            "未绑定的一阶变量；free 变量请写成 `#ᶠ[sort, id]`，常量函数请写成 `c()`"
  | _ =>
      throwErrorAt termSyntax "不支持的一阶项语法"

private def closeBinder (quantifier : Syntax) (binder : Binder) (body : Syntax) :
    TermElabM Syntax := do
  let bodyTerm : TSyntax `term := ⟨body⟩
  let closed ← `(FirstOrder.Formula.closeFreeAt $binder.sort $(quote binder.id) 0 $bodyTerm)
  if quantifier.isToken "∀" then
    `(FirstOrder.Formula.forallE $binder.sort $closed)
  else
    `(FirstOrder.Formula.existsE $binder.sort $closed)

private partial def compileFormula (binders : List Binder) (formulaSyntax : Syntax) :
    CompileM Syntax := do
  let expanded ← StateT.lift <| Lean.Elab.liftMacroM <| Lean.expandMacros formulaSyntax
  let formulaSyntax := expanded
  match formulaSyntax with
  | `(foFormula| ⊥) =>
      `(FirstOrder.Formula.falsum)
  | `(foFormula| ⊤) =>
      `(FirstOrder.Formula.truth)
  | `(foFormula| ⌜$formula:term⌝ₚ) =>
      pure formula
  | `(foFormula| ($formula:foFormula)) =>
      compileFormula binders formula
  | `(foFormula| ℛ[$relation:term]($arguments:foTerm,*)) =>
      let compiled ← arguments.getElems.mapM (compileTerm binders)
      let list ← StateT.lift <| mkTermList compiled
      let listTerm : TSyntax `term := ⟨list⟩
      `(Surface.checkedRel $relation $listTerm)
  | `(foFormula| $left:foTerm = $right:foTerm) =>
      let left ← compileTerm binders left
      let right ← compileTerm binders right
      `(FirstOrder.Formula.equal $(asTerm left) $(asTerm right))
  | `(foFormula| ¬ $formula:foFormula) =>
      let formula ← compileFormula binders formula
      `(FirstOrder.Formula.neg $(asTerm formula))
  | `(foFormula| $left:foFormula ∧ $right:foFormula) =>
      let left ← compileFormula binders left
      let right ← compileFormula binders right
      `(FirstOrder.Formula.conj $(asTerm left) $(asTerm right))
  | `(foFormula| $left:foFormula ∨ $right:foFormula) =>
      let left ← compileFormula binders left
      let right ← compileFormula binders right
      `(FirstOrder.Formula.disj $(asTerm left) $(asTerm right))
  | `(foFormula| $left:foFormula → $right:foFormula) =>
      let left ← compileFormula binders left
      let right ← compileFormula binders right
      `(FirstOrder.Formula.imp $(asTerm left) $(asTerm right))
  | `(foFormula| $left:foFormula ↔ $right:foFormula) =>
      let left ← compileFormula binders left
      let right ← compileFormula binders right
      `(FirstOrder.Formula.iff $(asTerm left) $(asTerm right))
  | stx@`(foFormula| ∀ $identifiers:ident* : $sort:term, $formulaBody:foFormula) =>
      let newBinders ← identifiers.mapM fun identifier => do
        pure {
          name := binderName identifier
          sort
          id := ← freshFreeId
        }
      let compiledBody ← compileFormula (newBinders.toList.reverse ++ binders) formulaBody
      StateT.lift <| newBinders.foldrM (closeBinder stx[0]) compiledBody
  | stx@`(foFormula| ∃ $identifiers:ident* : $sort:term, $formulaBody:foFormula) =>
      let newBinders ← identifiers.mapM fun identifier => do
        pure {
          name := binderName identifier
          sort
          id := ← freshFreeId
        }
      let compiledBody ← compileFormula (newBinders.toList.reverse ++ binders) formulaBody
      StateT.lift <| newBinders.foldrM (closeBinder stx[0]) compiledBody
  | _ =>
      throwErrorAt formulaSyntax "不支持的一阶公式语法"

elab (name := elaborateFirstOrderSurface)
    "fo[" signature:term "]" " ⟪" formula:foFormula "⟫" : term => do
  let compiled ← (compileFormula [] formula.raw).run' 0
  let compiledTerm : TSyntax `term := ⟨compiled⟩
  let result : TSyntax `term ← `(($compiledTerm : FirstOrder.Formula $signature))
  elabTerm result.raw none

end Surface
end FirstOrder
end Logic
end YesMetaZFC
