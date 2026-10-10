import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeBounds

/-! # Project 树到内在语法树的固定转换图

成员关系和子集关系增加内核的关系符号字段；等号、连接词和量词保持独立构造子。
原子项原样传输，其合法性由前级正文识别器负责。本模块只编译这一结构转换。
-/
namespace YesMetaZFC.Automation.ObjectProjectQuotation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation ProofCode
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 原子的目标形状；关系符号编号来自当前类型安全内核。 -/
def atom (tag : Nat) (children : List Tree) : Tree :=
  if tag = 2 then .node 2 (leaf RelationSymbol.membership.ctorIdx :: children)
  else if tag = 11 then .node 2 (leaf RelationSymbol.subset.ctorIdx :: children)
  else .node tag children

def run (input : Tree) : Option Tree :=
  match input with
  | .node 0 [] => some (leaf 0)
  | .node 1 [] => some (leaf 1)
  | .node 2 children => some (atom 2 children)
  | .node 3 children => some (atom 3 children)
  | .node 4 [body] => do return .node 4 [← run body]
  | .node 5 [left, right] => do return .node 5 [← run left, ← run right]
  | .node 6 [left, right] => do return .node 6 [← run left, ← run right]
  | .node 7 [left, right] => do return .node 7 [← run left, ← run right]
  | .node 8 [left, right] => do return .node 8 [← run left, ← run right]
  | .node 9 [body] => do return .node 9 [← run body]
  | .node 10 [body] => do return .node 10 [← run body]
  | .node 11 children => some (atom 11 children)
  | _ => none
termination_by sizeOf input

def node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields

def rawNode {n : Nat} (tag : Nat) (fields : Expr n) : Expr n := .succ (.pair (.literal tag) fields)

def atomExpr {n : Nat} (tag : Nat) (fields : Expr n) : Expr n :=
  if tag = 2 then rawNode 2 (.succ (.pair (.literal 1) (.pair (node RelationSymbol.membership.ctorIdx []) fields)))
  else if tag = 11 then rawNode 2 (.succ (.pair (.literal 1) (.pair (node RelationSymbol.subset.ctorIdx []) fields)))
  else rawNode tag fields

@[simp] theorem atom_value (tag : Nat) (children : List Tree) :
    treeValue (atom tag children) = (atomExpr tag (.var (0 : Fin 1))).eval
      (fun _ => listValue (children.map treeValue)) := by
  by_cases h2 : tag = 2
  · simp [atom, atomExpr, h2, rawNode, node, Expr.eval, listValue, nodeValue, leaf]
  · by_cases h11 : tag = 11 <;> simp [atom, atomExpr, h2, h11, rawNode, node, Expr.eval, listValue, nodeValue, leaf]

def constantRule (tag : Nat) : Rule where
  arity := 0
  head := node 0 [node tag [] , node tag []]

def atomRule (tag : Nat) : Rule where
  arity := 1
  head := node 0 [rawNode tag (.var 0), atomExpr tag (.var 0)]

def unaryRule (tag : Nat) : Rule where
  arity := 2
  head := node 0 [node tag [.var 0] , node tag [.var 1]]
  premises := [node 0 [.var 0, .var 1]]

def binaryRule (tag : Nat) : Rule where
  arity := 4
  head := node 0 [node tag [.var 0, .var 1] , node tag [.var 2, .var 3]]
  premises := [node 0 [.var 0, .var 2] , node 0 [.var 1, .var 3]]

def rules : List Rule := [constantRule 0, constantRule 1, atomRule 2, atomRule 3,
  unaryRule 4, binaryRule 5, binaryRule 6, binaryRule 7, binaryRule 8,
  unaryRule 9, unaryRule 10, atomRule 11]

theorem heads_tagged (rule : Rule) (h : rule ∈ rules) : rule.head.tag?.isSome := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rulesFor_zero : rulesFor rules 0 = rules := rfl

theorem head_variables (rule : Rule) (h : rule ∈ rules) : ∀ i, i ∈ rule.head.variables := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem accept_rule (rule : Rule) (h : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) :=
  Acceptance.of_rule rule h values (fun i => rule.head.variable_le values (head_variables rule h i))
    (by
      intro guard hGuard
      have hEmpty : rule.guards = [] := by
        simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      rw [hEmpty] at hGuard
      cases hGuard) hPremises

def condition {bound free : SetContext} (input output : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 0 [input, output])

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (input output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition input output).substituteMapped bs fs =
      condition (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition, ObjectHorn.condition, IntrinsicQuotation.node, structural_list_code_term,
    structural_raw_node_code_term, structural_code_tag, Term.substituteMapped, Arguments.substituteMapped]

def template : FormulaTemplate.Binary where
  body := condition (.fvar .here) (.fvar (.there .here))

@[simp] theorem template_apply {bound free : SetContext} (input output : SetTerm bound free) :
    template input output = condition input output := by
  simp [template, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem condition_delta0 {bound free : SetContext} (input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition input output) := ObjectHorn.condition_delta0 _ _

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _

end YesMetaZFC.Automation.ObjectProjectQuotation
