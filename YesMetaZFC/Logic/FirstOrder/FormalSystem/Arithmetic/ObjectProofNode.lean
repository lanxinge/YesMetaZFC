import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLogicalAxiomSpec
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjection

/-! # 六类证明节点的固定局部对象模式

外壳与递归证明图共用规范编码。子证明在本层只读取头部；其有效性由递归图
负责。中间公式码由子头部或本节点结论给界，不量化无界语法对象。
-/
namespace YesMetaZFC.Automation.ObjectProofNode
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation ObjectHorn
set_option autoImplicit false

inductive Kind where
  | projection | syntax | transform | logical | axiom
  deriving DecidableEq
structure Shape where
  arity : Nat
  head : Expr arity
  queries : List (Kind × Expr arity)

abbrev node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields
abbrev projection {n : Nat} (input : Expr n) (index : Nat) (output : Expr n) : Kind × Expr n :=
  (.projection, node 2 [input, .literal index, output])
abbrev formula {n : Nat} (free input : Expr n) : Kind × Expr n :=
  (.syntax, node 4 [.literal 0, free, input])
abbrev transform {n : Nat} (mode : Nat) (parameter input output : Expr n) : Kind × Expr n :=
  (.transform, node 3 [.literal mode, .literal 0, parameter, input, output])

abbrev logicalShape : Shape where
  arity := 3
  head := node 0 [.var 0, .var 1, .var 2]
  queries := [(.logical, node 0 [.var 0, .var 2, .var 1])]
abbrev theoryShape : Shape where
  arity := 3
  head := node 1 [.var 0, .var 1, .var 2]
  queries := [formula (.var 0) (.var 1), (.axiom, node 0 [.var 2, .var 1])]
abbrev mpShape : Shape where
  arity := 5
  head := node 2 [.var 0, .var 1, .var 2, .var 3]
  queries := [formula (.var 0) (.var 1), formula (.var 0) (.var 4),
    projection (.var 2) 0 (.var 0), projection (.var 2) 1 (.var 4),
    projection (.var 3) 0 (.var 0), projection (.var 3) 1 (node 7 [.var 4, .var 1])]
abbrev forallShape : Shape where
  arity := 4
  head := node 3 [.var 0, node 9 [.var 1] , .var 2]
  queries := [formula (.succ (.var 0)) (.var 3),
    projection (.var 2) 0 (.succ (.var 0)), projection (.var 2) 1 (.var 3),
    transform 1 (.literal 0) (.var 3) (.var 1)]
abbrev strengtheningShape : Shape where
  arity := 4
  head := node 4 [.var 0, .var 1, .var 2]
  queries := [formula (.var 0) (.var 1),
    projection (.var 2) 0 (.succ (.var 0)), projection (.var 2) 1 (.var 3),
    transform 0 (.literal 0) (.var 1) (.var 3)]
abbrev substitutionShape : Shape where
  arity := 6
  head := node 5 [.var 0, .var 1, .var 2, .var 3, .var 4]
  queries := [formula (.var 2) (.var 5),
    (.syntax, node 1 [.literal 0, .var 0, .var 2, .var 3]),
    projection (.var 4) 0 (.var 2), projection (.var 4) 1 (.var 5),
    transform 3 (.var 3) (.var 5) (.var 1)]

def shapes : List Shape := [logicalShape, theoryShape, mpShape, forallShape, strengtheningShape, substitutionShape]

def queryChecked (axiomChecked : Nat → Bool) : Kind → Nat → Bool
  | .projection => check ObjectProjection.rules ObjectProjection.rank
  | .syntax => check ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank
  | .transform => check ObjectSyntaxTransform.rules ObjectSyntaxTransform.rank
  | .logical => ObjectLogicalAxiom.checked
  | .axiom => axiomChecked

def checked (axiomChecked : Nat → Bool) (root : Nat) : Bool :=
  shapes.any fun shape => (environments root shape.arity).any fun values =>
    (root == shape.head.eval values) && shape.queries.all (fun query => queryChecked axiomChecked query.1 (query.2.eval values))

theorem checked_iff (axiomChecked : Nat → Bool) (root : Nat) : checked axiomChecked root = true ↔
    ∃ shape, shape ∈ shapes ∧ ∃ values : Fin shape.arity → Nat,
      (∀ i, values i ≤ root) ∧ root = shape.head.eval values ∧
      ∀ query, query ∈ shape.queries → queryChecked axiomChecked query.1 (query.2.eval values) = true := by
  simp [checked, List.any_eq_true, mem_environments, List.all_eq_true]

def queryTest {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (axiomTest : ObjectCheckedTrace.LocalTest T) : Kind → ObjectCheckedTrace.LocalTest T
  | .projection => ObjectProjection.localTest C S hPower hInfinity
  | .syntax => ObjectHorn.localTest C S hPower hInfinity ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank ObjectFormulaSyntax.descending
  | .transform => ObjectSyntaxTransform.localTest C S hPower hInfinity
  | .logical => ObjectLogicalAxiom.localTest C S hSuccessor hPower hInfinity
  | .axiom => axiomTest

def localTest {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (axiomTest : ObjectCheckedTrace.LocalTest T) : ObjectCheckedTrace.LocalTest T :=
  ObjectLocalDecision.localTest C hSuccessor (shapes.map fun shape =>
    ⟨shape.arity, shape.head, shape.queries.map fun query => (queryTest C S hSuccessor hPower hInfinity axiomTest query.1, query.2)⟩)

theorem localTest_checked {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (axiomTest : ObjectCheckedTrace.LocalTest T) :
    (localTest C S hSuccessor hPower hInfinity axiomTest).checked = checked axiomTest.checked := by
  funext root
  simp only [localTest, ObjectLocalDecision.localTest, ObjectLocalDecision.checked, List.any_map, checked]
  apply List.any_congr rfl
  intro shape
  simp only [ObjectLocalDecision.Rule.checked]
  apply List.any_congr rfl
  intro values
  congr 1
  simp only [List.all_map]
  apply List.all_congr rfl
  intro query
  rcases query with ⟨kind, expr⟩
  dsimp only [Function.comp_def]
  cases kind <;> simp only [queryTest, queryChecked, ObjectProjection.localTest, ObjectSyntaxTransform.localTest,
    ObjectHorn.localTest, ObjectLogicalAxiom.localTest_checked]

end YesMetaZFC.Automation.ObjectProofNode
