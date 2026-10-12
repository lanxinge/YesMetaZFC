import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotationEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-!
# 有限码模式的统一有界对象图

模式只使用原有 numeral、后继和配数，不添加解释符号或公理。
两个空位由有限界中的任意对象见证填充；拒绝证明通过有限穷尽处理这些见证，
不将宿主解析成功作为对象见证的前提。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.CodePattern
open Nonlogical.BasicSetTheory QuineEncoding ProofCode
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false

inductive Pattern where
  | literal (value : Nat)
  | first
  | second
  | successor (body : Pattern)
  | pairing (left right : Pattern)
  deriving Repr

def Pattern.eval (pattern : Pattern) (first second : Nat) : Nat :=
  match pattern with
  | .literal value => value
  | .first => first
  | .second => second
  | .successor body => body.eval first second + 1
  | .pairing left right => godel_pair_value (left.eval first second) (right.eval first second)

def Pattern.term {bound free : SetContext} (pattern : Pattern)
    (first second : SetTerm bound free) : SetTerm bound free :=
  match pattern with
  | .literal value => numₘ(value)
  | .first => first
  | .second => second
  | .successor body => Sₘ(body.term first second)
  | .pairing left right => godel_pairₘ(left.term first second, right.term first second)

@[simp] theorem Pattern.term_substituteMapped (pattern : Pattern)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (first second : SetTerm sourceBound sourceFree)
    (bs : VariableSubstitution signature sourceBound targetBound targetFree)
    (fs : VariableSubstitution signature sourceFree targetBound targetFree) :
    (pattern.term first second).substituteMapped bs fs =
      pattern.term (first.substituteMapped bs fs) (second.substituteMapped bs fs) := by
  induction pattern with
  | literal value => exact finite_numeral_term_substituteMapped bs fs value
  | first => rfl
  | second => rfl
  | successor _ ih => exact congrArg successor_term ih
  | pairing _ _ ihLeft ihRight =>
      exact congr (congrArg (fun left right => godel_pairₘ(left, right)) ihLeft) ihRight

@[simp] theorem Pattern.term_instantiateTop (pattern : Pattern)
    {bound free : SetContext} (first second : SetTerm (SetSort.set :: bound) free)
    (witness : SetTerm bound free) :
    (pattern.term first second).instantiateTop witness =
      pattern.term (first.instantiateTop witness) (second.instantiateTop witness) := by
  exact pattern.term_substituteMapped first second _ _

theorem Pattern.evaluate {T : SetTheory} (C : CertificateCore T)
    (pattern : Pattern) (first second : Nat) :
    Derives T [] (pattern.term (numₘ(first) : Code) (numₘ(second)) ≐ₘ numₘ(pattern.eval first second)) := by
  induction pattern with
  | literal value => exact Metatheory.Derives.equality_refl _
  | first => exact Metatheory.Derives.equality_refl _
  | second => exact Metatheory.Derives.equality_refl _
  | successor body ih => exact successor_term_congr_of_equality _ _ ih
  | pairing left right ihLeft ihRight =>
      exact Metatheory.Derives.equality_trans
        (IntrinsicPairing.pair_congr_of_equalities _ _ _ _ ihLeft ihRight)
        (C.pair_value _ _)

def inner {bound free : SetContext} (pattern : Pattern)
    (raw first : SetTerm bound free) : SetFormula bound free :=
  Formula.LevyBound.boundedExists set_levy_bound (Sₘ(raw))
    (.equal (raw.weakenBound SetSort.set)
      (pattern.term (first.weakenBound SetSort.set) (.bvar .here)))

/-- 输入码本身界定两个见证；模式是固定的有限表达式。 -/
def graph {bound free : SetContext} (pattern : Pattern)
    (raw : SetTerm bound free) : SetFormula bound free :=
  Formula.LevyBound.boundedExists set_levy_bound (Sₘ(raw))
    (inner pattern (raw.weakenBound SetSort.set) (.bvar .here))

theorem graph_delta0 {bound free : SetContext} (pattern : Pattern)
    (raw : SetTerm bound free) : Formula.IsDelta0 set_levy_bound (graph pattern raw) :=
  Formula.IsDelta0.bounded_exists _
    (Formula.IsDelta0.bounded_exists _ (Formula.IsDelta0.equal _ _))

@[simp] theorem inner_instantiateTop {free : SetContext} (pattern : Pattern)
    (raw witness : SetOpenTerm free) :
    (inner pattern (raw.weakenBound SetSort.set) (.bvar .here)).instantiateTop witness =
      inner pattern raw witness := by
  simp [inner, Formula.LevyBound.boundedExists, set_levy_bound,
    Formula.LevyBound.membership, Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftBound,
    VariableSubstitution.instantiateTop]

theorem positive {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (pattern : Pattern) (raw first second : Nat)
    (hFirst : first ≤ raw) (hSecond : second ≤ raw)
    (hValue : raw = pattern.eval first second) :
    Derives T [] (graph pattern (numₘ(raw) : Code)) := by
  apply bounded_exists_intro _ _ (numₘ(first))
    (numeral_mem_of_lt hSuccessor (Nat.lt_succ_of_le hFirst))
  rw [inner_instantiateTop]
  apply bounded_exists_intro _ _ (numₘ(second))
    (numeral_mem_of_lt hSuccessor (Nat.lt_succ_of_le hSecond))
  simp only [Formula.instantiateTop_equal, Term.instantiateTop_weakenBound,
    Pattern.term_instantiateTop]
  rw [hValue]
  exact Metatheory.Derives.equality_symm (pattern.evaluate C first second)

theorem negative {T : SetTheory} (C : CertificateCore T)
    (pattern : Pattern) (raw : Nat)
    (hReject : ∀ first, first ≤ raw → ∀ second, second ≤ raw →
      raw ≠ pattern.eval first second) :
    Derives T [] (¬ₘ graph pattern (numₘ(raw) : Code)) := by
  apply bounded_exists_numeral_neg C.toFiniteCore (raw + 1)
  intro first hFirst
  rw [inner_instantiateTop]
  apply bounded_exists_numeral_neg C.toFiniteCore (raw + 1)
  intro second hSecond
  simp only [Formula.instantiateTop_equal, Term.instantiateTop_weakenBound,
    Pattern.term_instantiateTop]
  apply FirstOrder.Derives.neg_intro
  have hEq := FirstOrder.Derives.assumption (T := T) (Γ := [
    (numₘ(raw) : Code) ≐ₘ pattern.term (numₘ(first)) (numₘ(second))]) List.mem_cons_self
  have hEvaluation := FirstOrder.Derives.context_weaken_cons
    (assumption := (numₘ(raw) : Code) ≐ₘ pattern.term (numₘ(first)) (numₘ(second)))
    (pattern.evaluate C first second)
  exact FirstOrder.Derives.neg_elim
    (Metatheory.Derives.equality_trans hEq hEvaluation)
    (FirstOrder.Derives.context_weaken_cons
      (C.numeral_ne (hReject first (Nat.le_of_lt_succ hFirst) second (Nat.le_of_lt_succ hSecond))))

@[simp] theorem graph_instantiateTop (pattern : Pattern) (witness : Code) :
    (graph pattern (.bvar .here : SetTerm [SetSort.set] [])).instantiateTop witness =
      graph pattern witness := by
  simp [graph, inner, Formula.LevyBound.boundedExists, set_levy_bound,
    Formula.LevyBound.membership, Formula.instantiateTop, Formula.substitute,
    Substitution.instantiateTop, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftBound,
    VariableSubstitution.instantiateTop]

/-- 已求值的紧凑码项可直接进入同一个图，不要求把码实际展开为一元 numeral。 -/
theorem transport {T : SetTheory} (pattern : Pattern) {left right : Code}
    (hEq : Derives T [] (left ≐ₘ right))
    (hGraph : Derives T [] (graph pattern left)) :
    Derives T [] (graph pattern right) := by
  have h := FirstOrder.Derives.eq_subst
    (body := graph pattern (.bvar .here : SetTerm [SetSort.set] [])) hEq
    (by rw [graph_instantiateTop pattern left]; exact hGraph)
  rw [graph_instantiateTop pattern right] at h
  exact h

theorem transport_neg {T : SetTheory} (pattern : Pattern) {left right : Code}
    (hEq : Derives T [] (left ≐ₘ right))
    (hGraph : Derives T [] (¬ₘ graph pattern left)) :
    Derives T [] (¬ₘ graph pattern right) := by
  have h := FirstOrder.Derives.eq_subst
    (body := .neg (graph pattern (.bvar .here : SetTerm [SetSort.set] []))) hEq
    (by rw [Formula.instantiateTop_neg, graph_instantiateTop pattern left]; exact hGraph)
  rw [Formula.instantiateTop_neg, graph_instantiateTop pattern right] at h
  exact h

/-- 单孔模式由调用方指定作用域；另一个孔固定为零。 -/
def unaryGraph {bound free : SetContext} (pattern : Pattern)
    (scope raw : SetTerm bound free) : SetFormula bound free :=
  Formula.LevyBound.boundedExists set_levy_bound scope
    (.equal (raw.weakenBound SetSort.set)
      (pattern.term (.bvar .here) (numₘ(0))))

theorem unaryGraph_delta0 {bound free : SetContext} (pattern : Pattern)
    (scope raw : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (unaryGraph pattern scope raw) :=
  Formula.IsDelta0.bounded_exists _ (Formula.IsDelta0.equal _ _)

theorem unary_positive {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (pattern : Pattern) (scope raw index : Nat)
    (hIndex : index < scope) (hValue : raw = pattern.eval index 0) :
    Derives T [] (unaryGraph pattern (numₘ(scope)) (numₘ(raw) : Code)) := by
  apply bounded_exists_intro _ _ (numₘ(index)) (numeral_mem_of_lt hSuccessor hIndex)
  simp only [Formula.instantiateTop_equal, Term.instantiateTop_weakenBound,
    Pattern.term_instantiateTop]
  rw [hValue]
  exact Metatheory.Derives.equality_symm (pattern.evaluate C index 0)

theorem unary_negative {T : SetTheory} (C : CertificateCore T)
    (pattern : Pattern) (scope raw : Nat)
    (hReject : ∀ index, index < scope → raw ≠ pattern.eval index 0) :
    Derives T [] (¬ₘ unaryGraph pattern (numₘ(scope)) (numₘ(raw) : Code)) := by
  apply bounded_exists_numeral_neg C.toFiniteCore scope
  intro index hIndex
  simp only [Formula.instantiateTop_equal, Term.instantiateTop_weakenBound,
    Pattern.term_instantiateTop]
  apply FirstOrder.Derives.neg_intro
  have hEq := FirstOrder.Derives.assumption (T := T) (Γ := [
    (numₘ(raw) : Code) ≐ₘ pattern.term (numₘ(index)) (numₘ(0))]) List.mem_cons_self
  have hEvaluation := FirstOrder.Derives.context_weaken_cons
    (assumption := (numₘ(raw) : Code) ≐ₘ pattern.term (numₘ(index)) (numₘ(0)))
    (pattern.evaluate C index 0)
  exact FirstOrder.Derives.neg_elim
    (Metatheory.Derives.equality_trans hEq hEvaluation)
    (FirstOrder.Derives.context_weaken_cons (C.numeral_ne (hReject index hIndex)))

@[simp] theorem unaryGraph_instantiateTop (pattern : Pattern) (scope witness : Code) :
    (unaryGraph pattern (scope.weakenBound SetSort.set)
      (.bvar .here : SetTerm [SetSort.set] [])).instantiateTop witness =
      unaryGraph pattern scope witness := by
  simp [unaryGraph, Formula.LevyBound.boundedExists, set_levy_bound,
    Formula.LevyBound.membership, Formula.instantiateTop, Formula.substitute,
    Substitution.instantiateTop, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftBound,
    VariableSubstitution.instantiateTop]

theorem unary_transport {T : SetTheory} (pattern : Pattern) (scope : Code) {left right : Code}
    (hEq : Derives T [] (left ≐ₘ right))
    (hGraph : Derives T [] (unaryGraph pattern scope left)) :
    Derives T [] (unaryGraph pattern scope right) := by
  have h := FirstOrder.Derives.eq_subst
    (body := unaryGraph pattern (scope.weakenBound SetSort.set)
      (.bvar .here : SetTerm [SetSort.set] [])) hEq
    (by rw [unaryGraph_instantiateTop pattern scope left]; exact hGraph)
  rw [unaryGraph_instantiateTop pattern scope right] at h
  exact h

theorem unary_transport_neg {T : SetTheory} (pattern : Pattern) (scope : Code) {left right : Code}
    (hEq : Derives T [] (left ≐ₘ right))
    (hGraph : Derives T [] (¬ₘ unaryGraph pattern scope left)) :
    Derives T [] (¬ₘ unaryGraph pattern scope right) := by
  have h := FirstOrder.Derives.eq_subst
    (body := .neg (unaryGraph pattern (scope.weakenBound SetSort.set)
      (.bvar .here : SetTerm [SetSort.set] []))) hEq
    (by rw [Formula.instantiateTop_neg, unaryGraph_instantiateTop pattern scope left]; exact hGraph)
  rw [Formula.instantiateTop_neg, unaryGraph_instantiateTop pattern scope right] at h
  exact h

def listPattern : List Pattern → Pattern
  | [] => .successor (.pairing (.literal 0) (.literal 0))
  | head :: tail => .successor (.pairing (.literal 1) (.pairing head (listPattern tail)))

def nodePattern (tag : Pattern) (fields : List Pattern) : Pattern :=
  .successor (.pairing tag (listPattern fields))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.CodePattern
