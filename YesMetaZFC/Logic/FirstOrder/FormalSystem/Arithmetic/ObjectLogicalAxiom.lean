import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLocalDecision
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFormulaSound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectSyntaxTransformConcrete
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.LogicalAxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxCodeRenaming

/-! # 二十七类逻辑公理的局部对象模式

公理正文使用当前类型安全 AST 的全部构造子。参数良构性与四种变换分别
调用已经精确表示的固定图；模式表不限制公式大小或自由变量个数。
-/
namespace YesMetaZFC.Automation.ObjectLogicalAxiom
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn
set_option autoImplicit false

abbrev node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields
abbrev imp {n : Nat} (a b : Expr n) : Expr n := node 7 [a, b]
abbrev neg {n : Nat} (a : Expr n) : Expr n := node 4 [a]
abbrev conj {n : Nat} (a b : Expr n) : Expr n := node 5 [a, b]
abbrev disj {n : Nat} (a b : Expr n) : Expr n := node 6 [a, b]
abbrev iffE {n : Nat} (a b : Expr n) : Expr n := node 8 [a, b]
abbrev allE {n : Nat} (a : Expr n) : Expr n := node 9 [a]
abbrev exE {n : Nat} (a : Expr n) : Expr n := node 10 [a]
abbrev eqE {n : Nat} (a b : Expr n) : Expr n := node 3 [a, b]

@[simp] theorem abstract_imp {bound free : SetContext} (left right : SetFormula bound (SetSort.set :: free)) :
    SyntaxEncode.formula ((Formula.imp left right).abstractFreeTop) =
      .node 7 [SyntaxEncode.formula left.abstractFreeTop, SyntaxEncode.formula right.abstractFreeTop] := rfl

/-- 查询标签 false 为完整语法图，true 为共用变换图。 -/
structure Shape where
  arity : Nat
  head : Expr arity
  queries : List (Bool × Expr arity)

abbrev grammar {n : Nat} (isTerm : Bool) (bound free input : Expr n) : Bool × Expr n :=
  (false, node (if isTerm then 0 else 4) [bound, free, input])
abbrev transform {n : Nat} (mode : Nat) (parameter input output : Expr n) : Bool × Expr n :=
  (true, node 3 [.literal mode, .literal 0, parameter, input, output])
abbrev head {n : Nat} (tag : Nat) (free : Expr n) (parameters : List (Expr n)) (output : Expr n) : Expr n :=
  node 0 [free, node tag parameters, output]

abbrev prop (tag count : Nat) (output : Expr (count + 1)) : Shape where
  arity := count + 1
  head := head tag (.var 0) ((List.finRange count).map (fun i => .var i.succ)) output
  queries := (List.finRange count).map (fun i => grammar false (.literal 0) (.var 0) (.var i.succ))

abbrev rule0 : Shape := prop 0 3 (imp (imp (.var 1) (imp (.var 2) (.var 3))) (imp (imp (.var 1) (.var 2)) (imp (.var 1) (.var 3))))
abbrev rule1 : Shape := prop 1 1 (imp (.var 1) (imp (.var 1) (.var 1)))
abbrev rule2 : Shape := prop 2 2 (imp (.var 1) (imp (.var 2) (.var 1)))
abbrev rule3 : Shape := prop 3 2 (imp (.var 1) (imp (neg (.var 1)) (.var 2)))
abbrev rule4 : Shape := prop 4 1 (imp (imp (neg (.var 1)) (.var 1)) (.var 1))
abbrev rule5 : Shape := prop 5 2 (imp (neg (.var 1)) (imp (.var 1) (.var 2)))
abbrev rule6 : Shape := prop 6 2 (imp (imp (.var 1) (.var 2)) (imp (imp (neg (.var 1)) (.var 2)) (.var 2)))
abbrev rule7 : Shape := prop 7 0 (node 1 [])
abbrev rule8 : Shape := prop 8 1 (imp (node 0 []) (.var 1))
abbrev rule9 : Shape := prop 9 1 (imp (imp (.var 1) (node 0 [])) (neg (.var 1)))
abbrev rule10 : Shape := prop 10 1 (imp (.var 1) (imp (neg (.var 1)) (node 0 [])))
abbrev rule11 : Shape := prop 11 2 (imp (.var 1) (imp (.var 2) (conj (.var 1) (.var 2))))
abbrev rule12 : Shape := prop 12 2 (imp (conj (.var 1) (.var 2)) (.var 1))
abbrev rule13 : Shape := prop 13 2 (imp (conj (.var 1) (.var 2)) (.var 2))
abbrev rule14 : Shape := prop 14 2 (imp (.var 1) (disj (.var 1) (.var 2)))
abbrev rule15 : Shape := prop 15 2 (imp (.var 2) (disj (.var 1) (.var 2)))
abbrev rule16 : Shape := prop 16 3 (imp (imp (.var 1) (.var 3)) (imp (imp (.var 2) (.var 3)) (imp (disj (.var 1) (.var 2)) (.var 3))))
abbrev rule17 : Shape := prop 17 2 (imp (imp (.var 1) (.var 2)) (imp (imp (.var 2) (.var 1)) (iffE (.var 1) (.var 2))))
abbrev rule18 : Shape := prop 18 2 (imp (iffE (.var 1) (.var 2)) (imp (.var 1) (.var 2)))
abbrev rule19 : Shape := prop 19 2 (imp (iffE (.var 1) (.var 2)) (imp (.var 2) (.var 1)))

abbrev rule20 : Shape where
  arity := 4
  head := head 20 (.var 0) [.var 1, .var 2] (imp (allE (.var 1)) (.var 3))
  queries := [grammar false (.literal 1) (.var 0) (.var 1), grammar true (.literal 0) (.var 0) (.var 2),
    transform 2 (.var 2) (.var 1) (.var 3)]
abbrev rule21 : Shape where
  arity := 5
  head := head 21 (.var 0) [.var 1, .var 2]
    (imp (allE (imp (.var 3) (.var 4))) (imp (allE (.var 3)) (allE (.var 4))))
  queries := [grammar false (.literal 0) (.succ (.var 0)) (.var 1), grammar false (.literal 0) (.succ (.var 0)) (.var 2),
    transform 1 (.literal 0) (.var 1) (.var 3), transform 1 (.literal 0) (.var 2) (.var 4)]
abbrev rule22 : Shape where
  arity := 2
  head := head 22 (.var 0) [.var 1] (imp (.var 1) (allE (.var 1)))
  queries := [grammar false (.literal 0) (.var 0) (.var 1)]
abbrev rule23 : Shape where
  arity := 4
  head := head 23 (.var 0) [.var 1, .var 2] (imp (.var 3) (exE (.var 1)))
  queries := [grammar false (.literal 1) (.var 0) (.var 1), grammar true (.literal 0) (.var 0) (.var 2),
    transform 2 (.var 2) (.var 1) (.var 3)]
abbrev rule24 : Shape where
  arity := 4
  head := head 24 (.var 0) [.var 1, .var 2]
    (imp (allE (imp (.var 3) (.var 2))) (imp (exE (.var 3)) (.var 2)))
  queries := [grammar false (.literal 0) (.succ (.var 0)) (.var 1), grammar false (.literal 0) (.var 0) (.var 2),
    transform 1 (.literal 0) (.var 1) (.var 3)]
abbrev rule25 : Shape where
  arity := 6
  head := head 25 (.var 0) [.var 1, .var 2, .var 3]
    (imp (eqE (.var 1) (.var 2)) (imp (.var 4) (.var 5)))
  queries := [grammar true (.literal 0) (.var 0) (.var 1), grammar true (.literal 0) (.var 0) (.var 2),
    grammar false (.literal 1) (.var 0) (.var 3),
    transform 2 (.var 1) (.var 3) (.var 4), transform 2 (.var 2) (.var 3) (.var 5)]
abbrev rule26 : Shape where
  arity := 2
  head := head 26 (.var 0) [.var 1] (eqE (.var 1) (.var 1))
  queries := [grammar true (.literal 0) (.var 0) (.var 1)]

def shapes : List Shape :=
  [rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11, rule12, rule13, rule14, rule15, rule16, rule17, rule18, rule19, rule20, rule21, rule22, rule23, rule24, rule25, rule26]

set_option maxHeartbeats 1000000 in
/-- 每个见证都出现在公理码或结论码里，因此由根行给出统一有限界。 -/
theorem head_variables (shape : Shape) (h : shape ∈ shapes) : ∀ i, i ∈ shape.head.variables := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def Shape.compile {T : SetTheory} (shape : Shape)
    (syntaxTest transformTest : ObjectCheckedTrace.LocalTest T) : ObjectLocalDecision.Rule T where
  arity := shape.arity
  head := shape.head
  queries := shape.queries.map (fun query => (if query.1 then transformTest else syntaxTest, query.2))

def queryChecked (kind : Bool) (code : Nat) : Bool :=
  if kind then check ObjectSyntaxTransform.rules ObjectSyntaxTransform.rank code
  else check ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank code

def checked (root : Nat) : Bool :=
  shapes.any fun shape => (environments root shape.arity).any fun values =>
    (root == shape.head.eval values) && shape.queries.all (fun q => queryChecked q.1 (q.2.eval values))

theorem checked_iff (root : Nat) : checked root = true ↔
    ∃ shape, shape ∈ shapes ∧ ∃ values : Fin shape.arity → Nat,
      (∀ i, values i ≤ root) ∧ root = shape.head.eval values ∧
      ∀ query, query ∈ shape.queries → queryChecked query.1 (query.2.eval values) = true := by
  simp [checked, List.any_eq_true, mem_environments, List.all_eq_true]

/-- 模式表只消费两项已具体完成的对象测试。 -/
def localTest {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ) : ObjectCheckedTrace.LocalTest T :=
  ObjectLocalDecision.localTest C hSuccessor (shapes.map (fun shape => shape.compile
    (ObjectHorn.localTest C S hPower hInfinity ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank ObjectFormulaSyntax.descending)
    (ObjectSyntaxTransform.localTest C S hPower hInfinity)))


theorem localTest_checked {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ) :
    (localTest C S hSuccessor hPower hInfinity).checked = checked := by
  funext root
  simp only [localTest, ObjectLocalDecision.localTest, ObjectLocalDecision.checked, List.any_map,
    Function.comp_def, ObjectLocalDecision.Rule.checked, Shape.compile, List.all_map]
  apply List.any_congr rfl
  intro shape
  apply List.any_congr rfl
  intro values
  congr 1
  apply List.all_congr rfl
  intro query
  cases query.1 <;> rfl

end YesMetaZFC.Automation.ObjectLogicalAxiom
