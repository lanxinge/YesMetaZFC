import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornCheck
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeProjection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectTermSyntax

/-! # 完整类型安全内核公式的固定识别图

复用全部函数符号和定长项列，补齐全部关系符号及十一个公式构造子。
bound 与 free 的长度分别记录；进入对象量词只增加 bound 长度。
递归秩只读取输入语法码，因此量词下增加上下文不会破坏下降。
-/
namespace YesMetaZFC.Automation.ObjectFormulaSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation
open ObjectHorn ObjectTermSyntax
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def constantRule (tag : Nat) : Rule where
  arity := 2
  head := node 4 [.var 0, .var 1, node tag []]

def relationRule (symbol : RelationSymbol) : Rule where
  arity := 3
  head := node 4 [.var 0, .var 1, rawNode 2 (cons (node symbol.ctorIdx []) (.var 2))]
  premises := [node 1 [.var 0, .var 1, .literal (signature.relDomain symbol).length, .var 2]]

def equalityRule : Rule where
  arity := 4
  head := node 4 [.var 0, .var 1, node 3 [.var 2, .var 3]]
  premises := [node 0 [.var 0, .var 1, .var 2] , node 0 [.var 0, .var 1, .var 3]]

def unaryRule (tag : Nat) (binder : Bool) : Rule where
  arity := 3
  head := node 4 [.var 0, .var 1, node tag [.var 2]]
  premises := [node 4 [if binder then .succ (.var 0) else .var 0, .var 1, .var 2]]

def binaryRule (tag : Nat) : Rule where
  arity := 4
  head := node 4 [.var 0, .var 1, node tag [.var 2, .var 3]]
  premises := [node 4 [.var 0, .var 1, .var 2] , node 4 [.var 0, .var 1, .var 3]]

def formulaRules : List Rule :=
  [constantRule 0, constantRule 1] ++ SyntaxDecode.relationSymbols.toList.map relationRule ++
  [equalityRule, unaryRule 4 false, binaryRule 5, binaryRule 6, binaryRule 7, binaryRule 8,
    unaryRule 9 true, unaryRule 10 true]

def rules : List Rule := termRules ++ argumentRules ++ formulaRules

def rank (row : Nat) : Nat :=
  ObjectCodeProjection.field row (if ObjectCodeProjection.tag row = 1 then 3 else 2)

@[simp] theorem rank_term (bound free input : Nat) : rank (nodeValue 0 [bound, free, input]) = input := by
  simp [rank]

@[simp] theorem rank_arguments (bound free count input : Nat) :
    rank (nodeValue 1 [bound, free, count, input]) = input := by simp [rank]

@[simp] theorem rank_formula (bound free input : Nat) : rank (nodeValue 4 [bound, free, input]) = input := by
  simp [rank]

set_option maxHeartbeats 1000000 in
theorem descending : Descending rules rank := by
  intro rule hRule values _ _ premise hPremise
  simp only [rules, termRules, argumentRules, formulaRules, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with (((rfl | rfl) | hRule) | rfl | rfl) |
    ((rfl | rfl) | hRule) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp hRule
  all_goals dsimp only [variableRule, applicationRule, nilRule, consRule,
    constantRule, relationRule, equalityRule, unaryRule, binaryRule] at values premise hPremise ⊢
  all_goals first
    | exact False.elim (List.not_mem_nil hPremise)
    | have h := List.mem_cons.mp hPremise
      rcases h with rfl | hTail
  all_goals try exact False.elim (List.not_mem_nil hTail)
  all_goals try obtain rfl := List.mem_singleton.mp hTail
  all_goals simp [ObjectTermSyntax.node, rawNode, cons, Expr.node_eval,
    List.map_cons, List.map_nil, Expr.eval, Bool.false_eq_true,
    rank, ObjectCodeProjection.field, ObjectCodeProjection.tag, ObjectCodeProjection.payload,
    ObjectCodeProjection.get, ObjectCodeProjection.head, ObjectCodeProjection.tail,
    nodeValue, listValue, ProofCode.godel_unpair_value_pair]
  all_goals first
    | exact Nat.lt_trans (ObjectCodeProjection.tail_lt_cons _ _)
        (Nat.lt_succ_of_le (ProofCode.right_le_godel_pair_value _ _))
    | exact ObjectCodeProjection.head_lt_cons _ _
    | exact ObjectCodeProjection.tail_lt_cons _ _
    | exact ObjectCodeProjection.node_field_lt _ [values 2] _ List.mem_cons_self
    | exact ObjectCodeProjection.node_field_lt _ [values 2, values 3] _ List.mem_cons_self
    | exact ObjectCodeProjection.node_field_lt _ [values 2, values 3] _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- 检查器覆盖所有自然数，包括不编码任何语法树的输入。 -/
def checked (bound free input : Nat) : Bool := ObjectHorn.check rules rank (nodeValue 4 [bound, free, input])

def condition {bound free : SetContext} (b f input : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 4 [b, f, input])

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (b f input : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition b f input).substituteMapped bs fs =
      condition (b.substituteMapped bs fs) (f.substituteMapped bs fs) (input.substituteMapped bs fs) := by
  simp [condition]

def template : FormulaTemplate.Ternary where
  body := condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

@[simp] theorem template_apply {bound free : SetContext} (b f input : SetTerm bound free) :
    template b f input = condition b f input := by
  simp [template, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem delta0 {bound free : SetContext} (b f input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition b f input) := ObjectHorn.condition_delta0 _ _

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (bound free input : Nat) (h : checked bound free input = true) :
    Derives T [] (condition (numₘ(bound)) (numₘ(free)) (numₘ(input) : Code)) :=
  ObjectHorn.transport rules (FirstOrder.Derives.eq_symm (node_evaluate C 4 [bound, free, input]))
    (check_positive C S hPower hInfinity rules rank descending _ h)

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (bound free input : Nat) (h : checked bound free input = false) :
    Derives T [] (¬ₘ condition (numₘ(bound)) (numₘ(free)) (numₘ(input) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm (node_evaluate C 4 [bound, free, input]))
    (check_negative C A rules rank descending _ h)

end YesMetaZFC.Automation.ObjectFormulaSyntax
