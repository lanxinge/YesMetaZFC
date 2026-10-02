import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodePattern
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.Project

/-!
# 自然数行码的有限规则编译

规则只使用变量、常数、后继和配数。每条规则的见证均由当前行码给出的有限界
约束；递归前提表现为同一个轨迹集合的成员关系，规则表本身与输入无关。
-/
namespace YesMetaZFC.Automation.ObjectHorn
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

inductive Expr (arity : Nat) where
  | literal (value : Nat)
  | var (index : Fin arity)
  | succ (body : Expr arity)
  | pair (left right : Expr arity)
  deriving Repr

def Expr.eval {n : Nat} (env : Fin n → Nat) : Expr n → Nat
  | .literal value => value
  | .var index => env index
  | .succ body => body.eval env + 1
  | .pair left right => ProofCode.godel_pair_value (left.eval env) (right.eval env)

def Expr.term {n : Nat} {bound free : SetContext} (env : Fin n → SetTerm bound free) :
    Expr n → SetTerm bound free
  | .literal value => numₘ(value)
  | .var index => env index
  | .succ body => Sₘ(body.term env)
  | .pair left right => godel_pairₘ(left.term env, right.term env)

def Expr.list {n : Nat} : List (Expr n) → Expr n
  | [] => .succ (.pair (.literal 0) (.literal 0))
  | head :: tail => .succ (.pair (.literal 1) (.pair head (.list tail)))

def Expr.node {n : Nat} (tag : Expr n) (fields : List (Expr n)) : Expr n :=
  .succ (.pair tag (.list fields))

def Expr.variables {n : Nat} : Expr n → List (Fin n)
  | .literal _ => []
  | .var index => [index]
  | .succ body => body.variables
  | .pair left right => left.variables ++ right.variables

theorem Expr.variable_le {n : Nat} (expr : Expr n) (env : Fin n → Nat)
    {index : Fin n} (h : index ∈ expr.variables) : env index ≤ expr.eval env := by
  induction expr with
  | literal _ => simp [variables] at h
  | var value =>
    have : index = value := List.mem_singleton.mp h
    subst index
    exact Nat.le_refl _
  | succ body ih => exact Nat.le_trans (ih h) (Nat.le_succ _)
  | pair left right ihLeft ihRight =>
    rcases List.mem_append.mp h with h | h
    · exact Nat.le_trans (ihLeft h) (ProofCode.left_le_godel_pair_value _ _)
    · exact Nat.le_trans (ihRight h) (ProofCode.right_le_godel_pair_value _ _)

@[simp] theorem Expr.term_substituteMapped {n : Nat} (expr : Expr n)
    {sb sf tb tf : SetContext} (env : Fin n → SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (expr.term env).substituteMapped bs fs =
      expr.term (fun index => (env index).substituteMapped bs fs) := by
  induction expr <;> simp_all [Expr.term, Term.substituteMapped, Arguments.substituteMapped]

@[simp] theorem Expr.term_renameMapped {n : Nat} (expr : Expr n)
    {sb sf tb tf : SetContext} (env : Fin n → SetTerm sb sf)
    (bs : VariableRenaming sb tb) (fs : VariableRenaming sf tf) :
    (expr.term env).renameMapped bs fs =
      expr.term (fun index => (env index).renameMapped bs fs) := by
  induction expr <;> simp_all [Expr.term, Term.renameMapped, Arguments.renameMapped]

theorem Expr.evaluate {T : SetTheory} (C : CertificateCore T)
    {n : Nat} (expr : Expr n) (env : Fin n → Nat) :
    Derives T [] ((expr.term (fun index => numₘ(env index)) : Code) ≐ₘ numₘ(expr.eval env)) := by
  induction expr with
  | literal _ | var _ => exact Metatheory.Derives.equality_refl _
  | succ body ih => exact successor_term_congr_of_equality _ _ ih
  | pair left right ihLeft ihRight =>
      exact Metatheory.Derives.equality_trans
        (IntrinsicPairing.pair_congr_of_equalities _ _ _ _ ihLeft ihRight) (C.pair_value _ _)

def allOf {bound free : SetContext} : List (SetFormula bound free) → SetFormula bound free
  | [] => .truth
  | head :: tail => .conj head (allOf tail)

def anyOf {bound free : SetContext} : List (SetFormula bound free) → SetFormula bound free
  | [] => .falsum
  | head :: tail => .disj head (anyOf tail)

@[simp] theorem allOf_substituteMapped {sb sf tb tf : SetContext} (formulas : List (SetFormula sb sf))
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (allOf formulas).substituteMapped bs fs =
      allOf (formulas.map (fun φ => φ.substituteMapped bs fs)) := by
  induction formulas <;> simp_all [allOf, Formula.substituteMapped]

@[simp] theorem anyOf_substituteMapped {sb sf tb tf : SetContext} (formulas : List (SetFormula sb sf))
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (anyOf formulas).substituteMapped bs fs =
      anyOf (formulas.map (fun φ => φ.substituteMapped bs fs)) := by
  induction formulas <;> simp_all [anyOf, Formula.substituteMapped]

theorem allOf_delta0 {bound free : SetContext} (formulas : List (SetFormula bound free))
    (h : ∀ φ, φ ∈ formulas → Formula.IsDelta0 set_levy_bound φ) :
    Formula.IsDelta0 set_levy_bound (allOf formulas) := by
  induction formulas with
  | nil => exact .truth
  | cons head tail ih =>
      exact .conj (h head List.mem_cons_self) (ih (fun φ hφ => h φ (List.mem_cons_of_mem head hφ)))

theorem anyOf_delta0 {bound free : SetContext} (formulas : List (SetFormula bound free))
    (h : ∀ φ, φ ∈ formulas → Formula.IsDelta0 set_levy_bound φ) :
    Formula.IsDelta0 set_levy_bound (anyOf formulas) := by
  induction formulas with
  | nil => exact .falsum
  | cons head tail ih =>
      exact .disj (h head List.mem_cons_self) (ih (fun φ hφ => h φ (List.mem_cons_of_mem head hφ)))

/-- 同一个有限界量化全部参数；界只取决于行码，参数个数由固定规则决定。 -/
def quantify {free : SetContext} (count : Nat) (bound : SetOpenTerm free) :
    SetFormula (project_bound_context count) free → SetOpenFormula free :=
  match count with
  | 0 => fun body => body
  | n + 1 => fun body => quantify n bound
      (Formula.LevyBound.boundedExists set_levy_bound
        (bound.embedBoundClosed (project_bound_context n)) body)

theorem quantify_delta0 {free : SetContext} (count : Nat) (bound : SetOpenTerm free)
    (body : SetFormula (project_bound_context count) free)
    (h : Formula.IsDelta0 set_levy_bound body) :
    Formula.IsDelta0 set_levy_bound (quantify count bound body) := by
  induction count with
  | zero => exact h
  | succ n ih => exact ih _ (Formula.IsDelta0.bounded_exists _ h)

structure Rule where
  arity : Nat
  head : Expr arity
  /-- 每对表达式表示严格小于守卫。 -/
  guards : List (Expr arity × Expr arity) := []
  premises : List (Expr arity) := []

def Rule.matrix (rule : Rule) {bound free : SetContext}
    (env : Fin rule.arity → SetTerm bound free) (row trace : SetTerm bound free) :
    SetFormula bound free :=
  (row ≐ₘ rule.head.term env) ∧ₘ
    (allOf (rule.guards.map (fun guard => guard.1.term env ∈ₘ guard.2.term env)) ∧ₘ
      allOf (rule.premises.map (fun premise => premise.term env ∈ₘ trace)))

def Rule.template (rule : Rule) : FormulaTemplate.Binary where
  body := quantify rule.arity (Sₘ(.fvar .here))
    (rule.matrix (fun index => .bvar (project_bound_variable index))
      (.fvar .here) (.fvar (.there .here)))

@[simp] theorem Rule.matrix_substituteMapped (rule : Rule) {sb sf tb tf : SetContext}
    (env : Fin rule.arity → SetTerm sb sf) (row trace : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (rule.matrix env row trace).substituteMapped bs fs =
      rule.matrix (fun index => (env index).substituteMapped bs fs)
        (row.substituteMapped bs fs) (trace.substituteMapped bs fs) := by
  simp [Rule.matrix, Formula.substituteMapped, Arguments.substituteMapped, Function.comp_def]

theorem Rule.matrix_delta0 (rule : Rule) {bound free : SetContext}
    (env : Fin rule.arity → SetTerm bound free) (row trace : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (rule.matrix env row trace) := by
  apply Formula.IsDelta0.conj (.equal _ _) (Formula.IsDelta0.conj ?_ ?_)
  all_goals
    apply allOf_delta0
    intro φ hφ
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hφ
    exact .rel _ _

theorem Rule.template_delta0 (rule : Rule) :
    Formula.IsDelta0 set_levy_bound rule.template.body :=
  quantify_delta0 _ _ _ (rule.matrix_delta0 _ _ _)

def step (rules : List Rule) : FormulaTemplate.Binary where
  body := anyOf (rules.map (fun rule => rule.template.body))

@[simp] theorem step_apply (rules : List Rule) {bound free : SetContext}
    (row trace : SetTerm bound free) :
    step rules row trace = anyOf (rules.map (fun rule => rule.template row trace)) := by
  simp [step, FormulaTemplate.apply_two, FormulaTemplate.instantiate, Function.comp_def]

theorem step_delta0 (rules : List Rule) : Formula.IsDelta0 set_levy_bound (step rules).body := by
  apply anyOf_delta0
  intro φ hφ
  obtain ⟨rule, _, rfl⟩ := List.mem_map.mp hφ
  exact rule.template_delta0

def condition (rules : List Rule) {bound free : SetContext} (row : SetTerm bound free) :
    SetFormula bound free := ObjectTrace.condition (step rules) ωₘ row

theorem condition_delta0 (rules : List Rule) {bound free : SetContext} (row : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition rules row) :=
  ObjectTrace.condition_delta0 _ (step_delta0 rules) _ _

end YesMetaZFC.Automation.ObjectHorn
