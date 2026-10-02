import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornCheck
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeProjection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteJoin
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxTransform

/-! # 量词、加强、实例化和自由代入的共用对象图

同一有限规则表通过模式、量词深度和参数码表达四种语法变换。
函数及关系符号原样传递；排序和作用域由独立的完整公式识别图负责。
-/
namespace YesMetaZFC.Automation.ObjectSyntaxTransform
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding IntrinsicQuotation
open ObjectHorn ObjectCodeProjection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

abbrev node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields
abbrev cons {n : Nat} (first rest : Expr n) : Expr n := .succ (.pair (.literal 1) (.pair first rest))
abbrev rawNode {n : Nat} (tag : Nat) (fields : Expr n) : Expr n := .succ (.pair (.literal tag) fields)
abbrev varCode {n : Nat} (free : Bool) (index : Expr n) : Expr n := node (if free then 1 else 0) [.node index []]
abbrev row {n : Nat} (kind : Nat) (mode depth parameter input output : Expr n) : Expr n :=
  node kind [mode, depth, parameter, input, output]

abbrev lookupHead : Rule where
  arity := 2
  head := node 0 [cons (.var 0) (.var 1), .literal 0, .var 0]
abbrev lookupTail : Rule where
  arity := 4
  head := node 0 [cons (.var 0) (.var 1), .succ (.var 2), .var 3]
  premises := [node 0 [.var 1, .var 2, .var 3]]

abbrev boundIdentity (mode : Nat) (below : Bool := false) : Rule where
  arity := 3
  head := row 1 (.literal mode) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))
  guards := if below then [(.var 2, .var 0)] else []
abbrev boundAbstract : Rule where
  arity := 3
  head := row 1 (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.succ (.var 2)))
  guards := [(.var 0, .succ (.var 2))]
abbrev boundPoint : Rule where
  arity := 2
  head := row 1 (.literal 2) (.var 0) (.var 1) (varCode false (.var 0)) (.var 1)
abbrev boundPredecessor : Rule where
  arity := 3
  head := row 1 (.literal 2) (.var 0) (.var 1) (varCode false (.succ (.var 2))) (varCode false (.var 2))
  guards := [(.var 0, .succ (.var 2))]
abbrev freeWeaken : Rule where
  arity := 3
  head := row 1 (.literal 0) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.succ (.var 2)))
abbrev freeAbstractHead : Rule where
  arity := 2
  head := row 1 (.literal 1) (.var 0) (.var 1) (varCode true (.literal 0)) (varCode false (.var 0))
abbrev freeAbstractTail : Rule where
  arity := 3
  head := row 1 (.literal 1) (.var 0) (.var 1) (varCode true (.succ (.var 2))) (varCode true (.var 2))
abbrev freeIdentity : Rule where
  arity := 3
  head := row 1 (.literal 2) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.var 2))
abbrev freeReplace : Rule where
  arity := 4
  head := row 1 (.literal 3) (.var 0) (.var 1) (varCode true (.var 2)) (.var 3)
  premises := [node 0 [.var 1, .var 2, .var 3]]

abbrev application (kind : Nat) : Rule where
  arity := 6
  head := row kind (.var 0) (.var 1) (.var 2)
    (rawNode 2 (cons (.node (.var 3) []) (.var 4)))
    (rawNode 2 (cons (.node (.var 3) []) (.var 5)))
  premises := [row 2 (.var 0) (.var 1) (.var 2) (.var 4) (.var 5)]
abbrev nilArguments : Rule where
  arity := 3
  head := row 2 (.var 0) (.var 1) (.var 2) (.list []) (.list [])
  guards := [(.var 0, .literal 4)]
abbrev consArguments : Rule where
  arity := 7
  head := row 2 (.var 0) (.var 1) (.var 2) (cons (.var 3) (.var 4)) (cons (.var 5) (.var 6))
  premises := [row 1 (.var 0) (.var 1) (.var 2) (.var 3) (.var 5),
    row 2 (.var 0) (.var 1) (.var 2) (.var 4) (.var 6)]
abbrev constant (tag : Nat) : Rule where
  arity := 3
  head := row 3 (.var 0) (.var 1) (.var 2) (node tag []) (node tag [])
  guards := [(.var 0, .literal 4)]
abbrev binary (tag childKind : Nat) : Rule where
  arity := 7
  head := row 3 (.var 0) (.var 1) (.var 2) (node tag [.var 3, .var 4]) (node tag [.var 5, .var 6])
  premises := [row childKind (.var 0) (.var 1) (.var 2) (.var 3) (.var 5),
    row childKind (.var 0) (.var 1) (.var 2) (.var 4) (.var 6)]
abbrev unary (tag : Nat) (binder : Bool) : Rule where
  arity := 5
  head := row 3 (.var 0) (.var 1) (.var 2) (node tag [.var 3]) (node tag [.var 4])
  premises := [row 3 (.var 0) (if binder then .succ (.var 1) else .var 1) (.var 2) (.var 3) (.var 4)]

def rules : List Rule :=
  [lookupHead, lookupTail,
    boundIdentity 0, boundIdentity 3, boundIdentity 1 true, boundAbstract,
    boundIdentity 2 true, boundPoint, boundPredecessor,
    freeWeaken, freeAbstractHead, freeAbstractTail, freeIdentity, freeReplace,
    application 1, nilArguments, consArguments,
    constant 0, constant 1, application 3, binary 3 1, unary 4 false,
    binary 5 3, binary 6 3, binary 7 3, binary 8 3, unary 9 true, unary 10 true]

/-- 查表按表码下降；语法递归按输入码下降，参数码为查表转移提供余量。 -/
def rank (code : Nat) : Nat := if tag code = 0 then field code 0 else field code 2 + field code 3

@[simp] theorem rank_lookup (table index output : Nat) : rank (nodeValue 0 [table, index, output]) = table := by
  simp [rank]
@[simp] theorem rank_term (mode depth parameter input output : Nat) :
    rank (nodeValue 1 [mode, depth, parameter, input, output]) = parameter + input := by simp [rank]
@[simp] theorem rank_arguments (mode depth parameter input output : Nat) :
    rank (nodeValue 2 [mode, depth, parameter, input, output]) = parameter + input := by simp [rank]
@[simp] theorem rank_formula (mode depth parameter input output : Nat) :
    rank (nodeValue 3 [mode, depth, parameter, input, output]) = parameter + input := by simp [rank]

set_option maxHeartbeats 1000000 in
theorem descending : Descending rules rank := by
  intro rule hRule values _ _ premise hPremise
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [lookupHead, lookupTail, boundIdentity, boundAbstract,
    boundPoint, boundPredecessor, freeWeaken, freeAbstractHead, freeAbstractTail,
    freeIdentity, freeReplace, application, nilArguments, consArguments,
    constant, binary, unary] at values premise hPremise ⊢
  all_goals first
    | exact False.elim (List.not_mem_nil hPremise)
    | obtain rfl | hTail := List.mem_cons.mp hPremise
  all_goals try exact False.elim (List.not_mem_nil hTail)
  all_goals try obtain rfl := List.mem_singleton.mp hTail
  all_goals simp [Expr.eval]
  all_goals first
    | exact tail_lt_cons _ _
    | have h : 0 < nodeValue 1 [nodeValue (values 2) []] := Nat.zero_lt_succ _
      omega
    | first
      | exact Nat.lt_trans (tail_lt_cons _ _)
          (Nat.lt_succ_of_le (ProofCode.right_le_godel_pair_value _ _))
      | exact head_lt_cons _ _
      | exact tail_lt_cons _ _
      | exact node_field_lt _ [values 3] _ List.mem_cons_self
      | exact node_field_lt _ [values 3, values 4] _ List.mem_cons_self
      | exact node_field_lt _ [values 3, values 4] _ (List.mem_cons_of_mem _ List.mem_cons_self)

def checked (mode depth parameter input output : Nat) : Bool :=
  check rules rank (nodeValue 3 [mode, depth, parameter, input, output])

def condition {bound free : SetContext} (mode depth parameter input output : SetTerm bound free) :
    SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 3 [mode, depth, parameter, input, output])

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext}
    (mode depth parameter input output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition mode depth parameter input output).substituteMapped bs fs =
      condition (mode.substituteMapped bs fs) (depth.substituteMapped bs fs)
        (parameter.substituteMapped bs fs) (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition]

theorem delta0 {bound free : SetContext} (mode depth parameter input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition mode depth parameter input output) :=
  ObjectHorn.condition_delta0 _ _

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (mode depth parameter input output : Nat) (h : checked mode depth parameter input output = true) :
    Derives T [] (condition (numₘ(mode)) (numₘ(depth)) (numₘ(parameter)) (numₘ(input)) (numₘ(output) : Code)) :=
  ObjectHorn.transport rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 3 [mode, depth, parameter, input, output]))
    (check_positive C S hPower hInfinity rules rank descending _ h)

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (mode depth parameter input output : Nat) (h : checked mode depth parameter input output = false) :
    Derives T [] (¬ₘ condition (numₘ(mode)) (numₘ(depth)) (numₘ(parameter)) (numₘ(input)) (numₘ(output) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 3 [mode, depth, parameter, input, output]))
    (check_negative C A rules rank descending _ h)

end YesMetaZFC.Automation.ObjectSyntaxTransform
