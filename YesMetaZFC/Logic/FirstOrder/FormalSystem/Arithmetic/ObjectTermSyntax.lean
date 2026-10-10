import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteJoin
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeBounds
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxCanonical

/-! # 完整内核项及参数证书的固定识别图

行标签依次表示项、定长参数列、嵌套 indexed 项证书及上下文外壳。
作用域长度和元数均作为对象数码输入，函数表来自实际解码器的全部符号。
-/
namespace YesMetaZFC.Automation.ObjectTermSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields
def cons {n : Nat} (head tail : Expr n) : Expr n := .succ (.pair (.literal 1) (.pair head tail))
def rawNode {n : Nat} (tag : Nat) (fields : Expr n) : Expr n := .succ (.pair (.literal tag) fields)

def variableRule (isFree : Bool) : Rule where
  arity := 3
  head := node 0 [.var 0, .var 1, node (if isFree then 1 else 0) [rawNodeVar]]
  guards := [(.var 2, .var (if isFree then 1 else 0))]
where rawNodeVar : Expr 3 := .node (.var 2) []

def applicationRule (symbol : FunctionSymbol) : Rule where
  arity := 3
  head := node 0 [.var 0, .var 1, rawNode 2 (cons (node symbol.ctorIdx []) (.var 2))]
  premises := [node 1 [.var 0, .var 1, .literal (signature.funcDomain symbol).length, .var 2]]

def nilRule : Rule where
  arity := 2
  head := node 1 [.var 0, .var 1, .literal 0, .list []]

def consRule : Rule where
  arity := 5
  head := node 1 [.var 0, .var 1, .succ (.var 2), cons (.var 3) (.var 4)]
  premises := [node 0 [.var 0, .var 1, .var 3] , node 1 [.var 0, .var 1, .var 2, .var 4]]

def parameterNilRule : Rule where
  arity := 1
  head := node 2 [.var 0, .literal 0, node 0 []]

def parameterConsRule : Rule where
  arity := 4
  head := node 2 [.var 0, .succ (.var 1), node 0 [.var 2, .var 3]]
  premises := [node 0 [.literal 0, .var 0, .var 2] , node 2 [.var 0, .var 1, .var 3]]

def envelopeRule : Rule where
  arity := 3
  head := node 3 [.var 0, node 0 [.node (.var 1) [] , .var 2]]
  premises := [node 2 [.var 1, .var 0, .var 2]]

def termRules : List Rule := [variableRule false, variableRule true] ++
  SyntaxDecode.functionSymbols.toList.map applicationRule
def argumentRules : List Rule := [nilRule, consRule]
def parameterRules : List Rule := [parameterNilRule, parameterConsRule, envelopeRule]
def rules : List Rule := termRules ++ argumentRules ++ parameterRules

theorem symbol_mem (symbol : FunctionSymbol) : symbol ∈ SyntaxDecode.functionSymbols.toList := by
  cases symbol <;> simp [SyntaxDecode.functionSymbols]

theorem heads_tagged (rule : Rule) (h : rule ∈ rules) : rule.head.tag?.isSome := by
  simp only [rules, termRules, argumentRules, parameterRules, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | rfl) | h) | rfl | rfl) | rfl | rfl | rfl
  all_goals try rfl
  obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp h
  rfl

theorem head_variables (rule : Rule) (h : rule ∈ rules) : ∀ i, i ∈ rule.head.variables := by
  simp only [rules, termRules, argumentRules, parameterRules, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | rfl) | h) | rfl | rfl) | rfl | rfl | rfl
  all_goals try decide
  obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp h
  intro i
  change Fin 3 at i
  change i ∈ ([0, 1, 2] : List (Fin 3))
  have hi : i.val < 3 := i.isLt
  have hCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> decide

theorem accept_rule (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) :=
  Acceptance.of_rule rule hRule values
    (fun i => rule.head.variable_le values (head_variables rule hRule i)) hGuards hPremises

theorem rulesFor_zero : rulesFor rules 0 = termRules := by
  simp [rulesFor, rules, termRules, argumentRules, parameterRules, variableRule,
    applicationRule, nilRule, consRule, parameterNilRule, parameterConsRule, envelopeRule,
    node, Expr.node, Expr.tag?]

theorem rulesFor_one : rulesFor rules 1 = argumentRules := by
  simp [rulesFor, rules, termRules, argumentRules, parameterRules, variableRule,
    applicationRule, nilRule, consRule, parameterNilRule, parameterConsRule, envelopeRule,
    node, Expr.node, Expr.tag?]

theorem rulesFor_two : rulesFor rules 2 = [parameterNilRule, parameterConsRule] := by
  simp [rulesFor, rules, termRules, argumentRules, parameterRules, variableRule,
    applicationRule, nilRule, consRule, parameterNilRule, parameterConsRule, envelopeRule,
    node, Expr.node, Expr.tag?]

theorem rulesFor_three : rulesFor rules 3 = [envelopeRule] := by
  simp [rulesFor, rules, termRules, argumentRules, parameterRules, variableRule,
    applicationRule, nilRule, consRule, parameterNilRule, parameterConsRule, envelopeRule,
    node, Expr.node, Expr.tag?]

def termCondition {bound free : SetContext} (boundCount freeCount input : SetTerm bound free) :
    SetFormula bound free := ObjectHorn.condition rules (IntrinsicQuotation.node 0 [boundCount, freeCount, input])

def parameterCondition {bound free : SetContext} (count input : SetTerm bound free) :
    SetFormula bound free := ObjectHorn.condition rules (IntrinsicQuotation.node 3 [count, input])

theorem term_delta0 {bound free : SetContext} (boundCount freeCount input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (termCondition boundCount freeCount input) := ObjectHorn.condition_delta0 _ _

theorem parameter_delta0 {bound free : SetContext} (count input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (parameterCondition count input) := ObjectHorn.condition_delta0 _ _

end YesMetaZFC.Automation.ObjectTermSyntax
