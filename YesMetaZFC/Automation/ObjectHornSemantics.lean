import YesMetaZFC.Automation.ObjectLocalDecision
import YesMetaZFC.Automation.ObjectBinaryTest
import YesMetaZFC.Automation.NaturalRosserSemantics
import YesMetaZFC.Model.FirstOrder.LevyAbsoluteness

/-! # 有界规则的任意模型语义

规则参数是模型对象，不先解码成宿主 Nat。固定长度的见证块、表达式和局部查询
分别解释，供模型间的逐构造对应复用。
-/
namespace YesMetaZFC.Automation.ObjectHornSemantics
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding ObjectHorn
open RelationalTranslation NaturalRosserSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def boundEnv {free : SetContext} (env : Env 𝒩 [] free) :
    (count : Nat) → (Fin count → 𝒩.Carrier .set) → Env 𝒩 (project_bound_context count) free
  | 0, _ => env
  | count + 1, values => (boundEnv env count (fun i => values i.succ)).pushBound (values 0)

@[simp] theorem boundEnv_variable {free : SetContext} (env : Env 𝒩 [] free)
    {count : Nat} (values : Fin count → 𝒩.Carrier .set) (i : Fin count) :
    (boundEnv env count values).boundVal (project_bound_variable i) = values i := by
  induction count with
  | zero => exact Fin.elim0 i
  | succ count ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih (fun j => values j.succ) i

@[simp] theorem boundEnv_free {free : SetContext} (env : Env 𝒩 [] free)
    {count : Nat} (values : Fin count → 𝒩.Carrier .set) {sort : SetSort} (entry : Variable free sort) :
    (boundEnv env count values).freeVal entry = env.freeVal entry := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih (fun i => values i.succ)

@[simp] theorem boundEnv_term {free : SetContext} (env : Env 𝒩 [] free)
    {count : Nat} (values : Fin count → 𝒩.Carrier .set) (term : SetOpenTerm free) :
    (term.embedBoundClosed (project_bound_context count)).eval (boundEnv env count values) = term.eval env := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [project_bound_context, List.replicate_succ, Term.embedBoundClosed,
      boundEnv, Term.eval_weakenBound] using ih (fun i => values i.succ)

theorem quantify_satisfies {free : SetContext} (env : Env 𝒩 [] free)
    (count : Nat) (limit : SetOpenTerm free) (body : SetFormula (project_bound_context count) free) :
    (quantify count limit body).satisfies env ↔
      ∃ values : Fin count → 𝒩.Carrier .set,
        (∀ i, mem 𝒩 (values i) (limit.eval env)) ∧ body.satisfies (boundEnv env count values) := by
  induction count with
  | zero =>
    constructor
    · intro h; exact ⟨Fin.elim0, fun i => Fin.elim0 i, h⟩
    · rintro ⟨values, _, h⟩; exact h
  | succ count ih =>
    rw [quantify, ih]
    simp only [Formula.LevyBound.satisfies_boundedExists, boundEnv_term]
    constructor
    · rintro ⟨tail, hTail, head, hHead, hBody⟩
      refine ⟨(Fin.cases head tail : Fin (count + 1) → 𝒩.Carrier .set), ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => exact hHead
        | succ i => exact hTail i
      · exact hBody
    · rintro ⟨values, hValues, hBody⟩
      exact ⟨(fun i => values i.succ), (fun i => hValues i.succ), values 0, hValues 0, hBody⟩

@[simp] theorem allOf_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (formulas : List (SetFormula bound free)) :
    (allOf formulas).satisfies env ↔ ∀ formula ∈ formulas, formula.satisfies env := by
  induction formulas with
  | nil => simp [allOf, Formula.satisfies]
  | cons head tail ih => simp [allOf, Formula.satisfies, ih]

@[simp] theorem anyOf_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (formulas : List (SetFormula bound free)) :
    (anyOf formulas).satisfies env ↔ ∃ formula ∈ formulas, formula.satisfies env := by
  induction formulas with
  | nil => simp [anyOf, Formula.satisfies]
  | cons head tail ih => simp [anyOf, Formula.satisfies, ih]

def exprValue {n : Nat} (𝒩 : Structure.{0,0,0,x} signature) (values : Fin n → 𝒩.Carrier .set) : Expr n → 𝒩.Carrier .set
  | .literal number => (finite_numeral_term number : SetTerm [] []).eval (Env.empty : Env 𝒩 [] [])
  | .var i => values i
  | .succ body => 𝒩.funcInterp .successor (.cons (exprValue 𝒩 values body) .nil)
  | .pair left right => 𝒩.funcInterp .godelPairing (.cons (exprValue 𝒩 values left) (.cons (exprValue 𝒩 values right) .nil))

theorem numeral_eval {bound free : SetContext} (env : Env 𝒩 bound free) (number : Nat) :
    (finite_numeral_term number : SetTerm bound free).eval env =
      (finite_numeral_term number : SetTerm [] []).eval (Env.empty : Env 𝒩 [] []) := by
  induction number with
  | zero => rfl
  | succ number ih => exact congrArg (fun value => 𝒩.funcInterp .successor (.cons value .nil)) ih

theorem expr_eval {bound free : SetContext} (env : Env 𝒩 bound free) {n : Nat}
    (terms : Fin n → SetTerm bound free) (expr : Expr n) :
    (expr.term terms).eval env = exprValue 𝒩 (fun i => (terms i).eval env) expr := by
  induction expr with
  | literal number => exact numeral_eval env number
  | var i => rfl
  | succ body ih => exact congrArg (fun value => 𝒩.funcInterp .successor (.cons value .nil)) ih
  | pair left right ihLeft ihRight =>
    change 𝒩.funcInterp .godelPairing (.cons ((left.term terms).eval env) (.cons ((right.term terms).eval env) .nil)) = _
    rw [ihLeft, ihRight]; rfl

theorem rule_satisfies (rule : ObjectHorn.Rule) (row trace : 𝒩.Carrier .set) :
    rule.template.body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) ↔
      ∃ values : Fin rule.arity → 𝒩.Carrier .set,
        (∀ i, mem 𝒩 (values i) (𝒩.funcInterp .successor (.cons row .nil))) ∧
        row = exprValue 𝒩 values rule.head ∧
        (∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2)) ∧
        ∀ premise ∈ rule.premises, mem 𝒩 (exprValue 𝒩 values premise) trace := by
  simp only [Rule.template, quantify_satisfies, Rule.matrix, Formula.satisfies,
    allOf_satisfies, List.forall_mem_map, Arguments.eval, expr_eval, Term.eval,
    boundEnv_variable, boundEnv_free]
  rfl

theorem step_satisfies (rules : List ObjectHorn.Rule) (row trace : 𝒩.Carrier .set) :
    (ObjectHorn.step rules).body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) ↔
      ∃ rule ∈ rules, rule.template.body.satisfies
        (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) := by
  rw [ObjectHorn.step, anyOf_satisfies]
  constructor
  · rintro ⟨formula, hFormula, h⟩
    obtain ⟨rule, hRule, rfl⟩ := List.mem_map.mp hFormula
    exact ⟨rule, hRule, h⟩
  · rintro ⟨rule, hRule, h⟩
    exact ⟨_, List.mem_map.mpr ⟨rule, hRule, rfl⟩, h⟩

theorem local_rule_satisfies {T : SetTheory} (rule : ObjectLocalDecision.Rule T) (row : 𝒩.Carrier .set) :
    rule.template.body.satisfies (templateEnv (.cons row .nil) : Env 𝒩 [] [.set]) ↔
      ∃ values : Fin rule.arity → 𝒩.Carrier .set,
        (∀ i, mem 𝒩 (values i) (𝒩.funcInterp .successor (.cons row .nil))) ∧
        row = exprValue 𝒩 values rule.head ∧ ∀ query ∈ rule.queries,
          query.1.condition.body.satisfies (templateEnv (.cons (exprValue 𝒩 values query.2) .nil) : Env 𝒩 [] [.set]) := by
  simp only [ObjectLocalDecision.Rule.template, quantify_satisfies, ObjectLocalDecision.Rule.matrix,
    Formula.satisfies, allOf_satisfies, List.forall_mem_map, unary_satisfies,
    expr_eval, Term.eval, boundEnv_variable, boundEnv_free]
  rfl

end YesMetaZFC.Automation.ObjectHornSemantics
