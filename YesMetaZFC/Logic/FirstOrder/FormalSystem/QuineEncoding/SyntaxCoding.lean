import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormalSystem

/-!
# FormalSystem 内在语法的 Quine 结构码

宿主侧 checked replay 直接比较与语法树同形的有限代数码，不再把每个节点递归压入
指数增长的自然数配数。对象语言 quotation 仍由 `Numbered.Code` 给出；本层只负责
宿主计算，因此保留构造子边界即可获得快速 `DecidableEq` 与结构单射性。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace QuineEncoding
namespace SyntaxCoding

open Nonlogical.BasicSetTheory

mutual

/-- 项的宿主 Quine 结构码。 -/
inductive TermCode where
  | bound_variable (index : Nat)
  | free_variable (index : Nat)
  | application (symbol : Nat) (arguments : ArgumentsCode)
  deriving DecidableEq, Repr

/-- 参数列的宿主 Quine 结构码。 -/
inductive ArgumentsCode where
  | nil
  | cons (head : TermCode) (tail : ArgumentsCode)
  deriving DecidableEq, Repr

end

/-- 公式的宿主 Quine 结构码。 -/
inductive FormulaCode where
  | falsum
  | truth
  | relation (symbol : Nat) (arguments : ArgumentsCode)
  | equality (left right : TermCode)
  | negation (body : FormulaCode)
  | conjunction (left right : FormulaCode)
  | disjunction (left right : FormulaCode)
  | implication (left right : FormulaCode)
  | equivalence (left right : FormulaCode)
  | universal (body : FormulaCode)
  | existential (body : FormulaCode)
  deriving DecidableEq, Repr

private theorem variable_index_injective {S : Type}
    {context : List S} {sort : S} :
    Function.Injective (@Variable.index S context sort) := by
  intro left right hIndex
  induction left with
  | here =>
      cases right with
      | here => rfl
      | there previous => cases hIndex
  | there previous ih =>
      cases right with
      | here => cases hIndex
      | there previous' =>
          apply congrArg Variable.there
          apply ih
          exact Nat.succ.inj hIndex

def function_symbol_code (symbol : FunctionSymbol) : Nat :=
  symbol.ctorIdx

theorem function_symbol_code_injective :
    Function.Injective function_symbol_code :=
  fs_quotation_numbering.function_number_injective

def relation_symbol_code (symbol : RelationSymbol) : Nat :=
  symbol.ctorIdx

theorem relation_symbol_code_injective :
    Function.Injective relation_symbol_code :=
  fs_quotation_numbering.relation_number_injective

mutual

/-- 内在项到宿主 Quine 结构码的总编码。 -/
def term_code {bound free : SetContext} {sort : SetSort} :
    Term signature bound free sort → TermCode
  | .bvar entry => .bound_variable entry.index
  | .fvar entry => .free_variable entry.index
  | .app function arguments =>
      .application (function_symbol_code function) (arguments_code arguments)

/-- 内在异质参数列到普通结构码列表的总编码。 -/
def arguments_code {bound free : SetContext}
    {sorts : List SetSort} :
    Arguments signature bound free sorts → ArgumentsCode
  | .nil => .nil
  | .cons term rest => .cons (term_code term) (arguments_code rest)

end

mutual

private theorem term_code_eq_core {bound free : SetContext} :
    (sort : SetSort) →
      (left right : Term signature bound free sort) →
      term_code left = term_code right → left = right
  | .set, .bvar leftEntry, .bvar rightEntry, hCode => by
      injection hCode with hIndex
      cases variable_index_injective hIndex
      rfl
  | .set, .bvar leftEntry, .fvar rightEntry, hCode => by
      cases hCode
  | .set, .bvar leftEntry, .app rightFunction rightArguments, hCode => by
      cases hCode
  | .set, .fvar leftEntry, .bvar rightEntry, hCode => by
      cases hCode
  | .set, .fvar leftEntry, .fvar rightEntry, hCode => by
      injection hCode with hIndex
      cases variable_index_injective hIndex
      rfl
  | .set, .fvar leftEntry, .app rightFunction rightArguments, hCode => by
      cases hCode
  | .set, .app leftFunction leftArguments,
      .bvar rightEntry, hCode => by
      cases hCode
  | .set, .app leftFunction leftArguments,
      .fvar rightEntry, hCode => by
      cases hCode
  | .set, .app leftFunction leftArguments,
      .app rightFunction rightArguments, hCode => by
      injection hCode with hFunction hArguments
      cases function_symbol_code_injective hFunction
      cases arguments_code_eq_core _ leftArguments rightArguments hArguments
      rfl

private theorem arguments_code_eq_core {bound free : SetContext} :
    (sorts : List SetSort) →
      (left right : Arguments signature bound free sorts) →
      arguments_code left = arguments_code right → left = right
  | .nil, .nil, .nil, _ => rfl
  | .cons sort sorts, .cons leftHead leftTail,
      .cons rightHead rightTail, hCode => by
      injection hCode with hHead hTail
      cases term_code_eq_core sort leftHead rightHead hHead
      cases arguments_code_eq_core sorts leftTail rightTail hTail
      rfl

end

theorem term_code_eq {bound free : SetContext}
    {sort : SetSort}
    {left right : Term signature bound free sort}
    (hCode : term_code left = term_code right) :
    left = right :=
  term_code_eq_core sort left right hCode

theorem arguments_code_eq {bound free : SetContext}
    {sorts : List SetSort}
    {left right : Arguments signature bound free sorts}
    (hCode : arguments_code left = arguments_code right) :
    left = right :=
  arguments_code_eq_core sorts left right hCode

theorem term_code_injective {bound free : SetContext} :
    Function.Injective (@term_code bound free SetSort.set) :=
  fun _ _ => term_code_eq

theorem arguments_code_injective {bound free : SetContext}
    {sorts : List SetSort} :
    Function.Injective (@arguments_code bound free sorts) :=
  fun _ _ => arguments_code_eq

/-- 内在公式到宿主 Quine 结构码的总编码。 -/
def formula_code {bound free : SetContext} :
    SetFormula bound free → FormulaCode
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments =>
      .relation (relation_symbol_code relation) (arguments_code arguments)
  | .equal left right => .equality (term_code left) (term_code right)
  | .neg body => .negation (formula_code body)
  | .conj left right => .conjunction (formula_code left) (formula_code right)
  | .disj left right => .disjunction (formula_code left) (formula_code right)
  | .imp left right => .implication (formula_code left) (formula_code right)
  | .iff left right => .equivalence (formula_code left) (formula_code right)
  | .forallE _ body => .universal (formula_code body)
  | .existsE _ body => .existential (formula_code body)

private theorem equality_formula_eq_of_codes {bound free : SetContext}
    {leftSort rightSort : SetSort}
    {left₁ left₂ : Term signature bound free leftSort}
    {right₁ right₂ : Term signature bound free rightSort}
    (hLeft : term_code left₁ = term_code right₁)
    (hRight : term_code left₂ = term_code right₂) :
    Formula.equal left₁ left₂ = Formula.equal right₁ right₂ := by
  cases leftSort
  cases rightSort
  cases term_code_eq hLeft
  cases term_code_eq hRight
  rfl

theorem formula_code_injective {bound free : SetContext} :
    Function.Injective (@formula_code bound free) := by
  intro left
  induction left with
  | falsum =>
      intro right hCode
      cases right <;> cases hCode
      rfl
  | truth =>
      intro right hCode
      cases right <;> cases hCode
      rfl
  | rel relation arguments =>
      intro right hCode
      cases right with
      | rel relation' arguments' =>
          injection hCode with hRelation hArguments
          cases relation_symbol_code_injective hRelation
          cases arguments_code_eq hArguments
          rfl
      | _ => cases hCode
  | equal left right =>
      intro target hCode
      cases target with
      | equal left' right' =>
          injection hCode with hLeft hRight
          exact equality_formula_eq_of_codes hLeft hRight
      | _ => cases hCode
  | neg body ih =>
      intro right hCode
      cases right with
      | neg body' =>
          injection hCode with hBody
          cases ih hBody
          rfl
      | _ => cases hCode
  | conj left right ihLeft ihRight =>
      intro target hCode
      cases target with
      | conj left' right' =>
          injection hCode with hLeft hRight
          cases ihLeft hLeft
          cases ihRight hRight
          rfl
      | _ => cases hCode
  | disj left right ihLeft ihRight =>
      intro target hCode
      cases target with
      | disj left' right' =>
          injection hCode with hLeft hRight
          cases ihLeft hLeft
          cases ihRight hRight
          rfl
      | _ => cases hCode
  | imp left right ihLeft ihRight =>
      intro target hCode
      cases target with
      | imp left' right' =>
          injection hCode with hLeft hRight
          cases ihLeft hLeft
          cases ihRight hRight
          rfl
      | _ => cases hCode
  | iff left right ihLeft ihRight =>
      intro target hCode
      cases target with
      | iff left' right' =>
          injection hCode with hLeft hRight
          cases ihLeft hLeft
          cases ihRight hRight
          rfl
      | _ => cases hCode
  | forallE sort body ih =>
      intro right hCode
      cases right with
      | forallE sort' body' =>
          cases sort
          cases sort'
          injection hCode with hBody
          cases ih hBody
          rfl
      | _ => cases hCode
  | existsE sort body ih =>
      intro right hCode
      cases right with
      | existsE sort' body' =>
          cases sort
          cases sort'
          injection hCode with hBody
          cases ih hBody
          rfl
      | _ => cases hCode

end SyntaxCoding
end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
