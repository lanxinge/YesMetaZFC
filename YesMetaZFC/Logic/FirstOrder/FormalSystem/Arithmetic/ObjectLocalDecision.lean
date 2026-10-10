import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCheckedTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteJoin

/-! # 有限局部模式与已表示判定的连接

模式的所有中间参数在当前行码内有界。每个查询复用已证明正负表示的固定
一元公式；有限存在连接的否定由数码有界穷尽定理导出，而不加入反射公理。
-/
namespace YesMetaZFC.Automation.ObjectLocalDecision
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

private theorem transport {T : SetTheory} (condition : FormulaTemplate.Unary)
    {free : SetContext} {Γ : Context signature free} {left right : SetOpenTerm free}
    (hEq : Derives T Γ (left ≐ₘ right)) (h : Derives T Γ (condition left)) :
    Derives T Γ (condition right) := by
  have result := FirstOrder.Derives.eq_subst (body := condition (.bvar .here)) hEq
    (by rw [FormulaTemplate.apply_one_instantiateTop_bvar]; exact h)
  rwa [FormulaTemplate.apply_one_instantiateTop_bvar] at result

private theorem transport_negative {T : SetTheory} (condition : FormulaTemplate.Unary)
    {free : SetContext} {Γ : Context signature free} {left right : SetOpenTerm free}
    (hEq : Derives T Γ (left ≐ₘ right)) (h : Derives T Γ (¬ₘ condition left)) :
    Derives T Γ (¬ₘ condition right) := by
  have result := FirstOrder.Derives.eq_subst (body := .neg (condition (.bvar .here))) hEq
    (by rw [Formula.instantiateTop_neg, FormulaTemplate.apply_one_instantiateTop_bvar]; exact h)
  rwa [Formula.instantiateTop_neg, FormulaTemplate.apply_one_instantiateTop_bvar] at result

structure Rule (T : SetTheory) where
  arity : Nat
  head : Expr arity
  queries : List (ObjectCheckedTrace.LocalTest T × Expr arity)

namespace Rule

def checked {T : SetTheory} (rule : Rule T) (root : Nat) : Bool :=
  (environments root rule.arity).any fun values =>
    (root == rule.head.eval values) &&
      rule.queries.all (fun query => query.1.checked (query.2.eval values))

theorem checked_iff {T : SetTheory} (rule : Rule T) (root : Nat) :
    rule.checked root = true ↔ ∃ values : Fin rule.arity → Nat,
      (∀ i, values i ≤ root) ∧ root = rule.head.eval values ∧
      ∀ query, query ∈ rule.queries → query.1.checked (query.2.eval values) = true := by
  simp [checked, List.any_eq_true, mem_environments, List.all_eq_true]

def matrix {T : SetTheory} (rule : Rule T) {bound free : SetContext}
    (env : Fin rule.arity → SetTerm bound free) (root : SetTerm bound free) : SetFormula bound free :=
  (root ≐ₘ rule.head.term env) ∧ₘ allOf (rule.queries.map (fun query => query.1.condition (query.2.term env)))

@[simp] theorem matrix_substituteMapped {T : SetTheory} (rule : Rule T) {sb sf tb tf : SetContext}
    (env : Fin rule.arity → SetTerm sb sf) (root : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (rule.matrix env root).substituteMapped bs fs =
      rule.matrix (fun i => (env i).substituteMapped bs fs) (root.substituteMapped bs fs) := by
  simp [matrix, Formula.substituteMapped, Function.comp_def]

def template {T : SetTheory} (rule : Rule T) : FormulaTemplate.Unary where
  body := quantify rule.arity (Sₘ(.fvar .here))
    (rule.matrix (fun i => .bvar (project_bound_variable i)) (.fvar .here))

theorem delta0 {T : SetTheory} (rule : Rule T) :
    Formula.IsDelta0 set_levy_bound rule.template.body := by
  apply quantify_delta0
  apply Formula.IsDelta0.conj (.equal _ _)
  apply allOf_delta0
  intro φ hφ
  obtain ⟨query, _, rfl⟩ := List.mem_map.mp hφ
  exact query.1.condition.instantiate_delta0 query.1.delta0 _

theorem positive {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (rule : Rule T) (root : Nat) (h : rule.checked root = true) :
    Derives T [] (rule.template (numₘ(root) : Code)) := by
  obtain ⟨values, hBound, hHead, hQueries⟩ := (rule.checked_iff root).mp h
  have hMatrix : Derives T [] (rule.matrix (fun i => (numₘ(values i) : Code)) (numₘ(root))) := by
    apply FirstOrder.Derives.conj_intro
    · rw [hHead]
      exact FirstOrder.Derives.eq_symm (rule.head.evaluate C values)
    · apply allOf_intro
      intro φ hφ
      obtain ⟨query, hQuery, rfl⟩ := List.mem_map.mp hφ
      exact transport query.1.condition (FirstOrder.Derives.eq_symm (query.2.evaluate C values))
        (query.1.positive _ (hQueries query hQuery))
  unfold template FormulaTemplate.apply_one FormulaTemplate.instantiate
  apply quantify_positive (values := values)
  · intro i
    simpa [Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons, finite_numeral_term]
      using numeral_mem_of_lt hSuccessor (Nat.lt_succ_of_le (hBound i))
  · simpa [matrix_substituteMapped, Term.substituteMapped, VariableSubstitution.cons] using hMatrix

theorem negative {T : SetTheory} (C : CertificateCore T)
    (rule : Rule T) (root : Nat) (h : rule.checked root = false) :
    Derives T [] (¬ₘ rule.template (numₘ(root) : Code)) := by
  classical
  have hMatrix : ∀ values : Fin rule.arity → Nat, (∀ i, values i ≤ root) →
      Derives T [] (¬ₘ rule.matrix (fun i => (numₘ(values i) : Code)) (numₘ(root))) := by
    intro values hBound
    apply FirstOrder.Derives.neg_intro
    let body := rule.matrix (fun i => (numₘ(values i) : Code)) (numₘ(root))
    have hBody : Derives T [body] body := FirstOrder.Derives.assumption List.mem_cons_self
    by_cases hHead : root = rule.head.eval values
    · have hFailure : ∃ query, query ∈ rule.queries ∧ query.1.checked (query.2.eval values) = false := by
        apply Classical.byContradiction
        intro hNo
        have hQueries : ∀ query, query ∈ rule.queries → query.1.checked (query.2.eval values) = true := by
          intro query hQuery
          cases hQueryResult : query.1.checked (query.2.eval values) with
          | false => exact False.elim (hNo ⟨query, hQuery, hQueryResult⟩)
          | true => rfl
        have hTrue := (rule.checked_iff root).mpr ⟨values, hBound, hHead, hQueries⟩
        rw [h] at hTrue
        cases hTrue
      obtain ⟨query, hQuery, hFalse⟩ := hFailure
      have hMember := allOf_elim (FirstOrder.Derives.conj_elim_right hBody)
        (List.mem_map.mpr ⟨query, hQuery, rfl⟩)
      have hNeg := transport_negative query.1.condition
        (FirstOrder.Derives.eq_symm (query.2.evaluate C values)) (query.1.negative _ hFalse)
      exact FirstOrder.Derives.neg_elim hMember (FirstOrder.Derives.context_weaken_cons hNeg)
    · exact FirstOrder.Derives.neg_elim
        (Metatheory.Derives.equality_trans (FirstOrder.Derives.conj_elim_left hBody)
          (rule.head.evaluate_open C values))
        (FirstOrder.Derives.context_weaken_cons (C.numeral_ne hHead))
  unfold template FormulaTemplate.apply_one FormulaTemplate.instantiate
  apply quantify_negative C.toFiniteCore (limit := root + 1)
  · rfl
  · intro values hValues
    simpa [matrix_substituteMapped, Term.substituteMapped, VariableSubstitution.cons]
      using hMatrix values (fun i => Nat.le_of_lt_succ (hValues i))

end Rule

/-- 有限模式表的总检查；所有分支共享同一个一元对象公式。 -/
def checked {T : SetTheory} (rules : List (Rule T)) (root : Nat) : Bool :=
  rules.any (fun rule => rule.checked root)

def template {T : SetTheory} (rules : List (Rule T)) : FormulaTemplate.Unary where
  body := anyOf (rules.map (fun rule => rule.template.body))

@[simp] theorem template_apply {T : SetTheory} (rules : List (Rule T)) {bound free : SetContext}
    (root : SetTerm bound free) : template rules root = anyOf (rules.map (fun rule => rule.template root)) := by
  simp [template, FormulaTemplate.apply_one, FormulaTemplate.instantiate, Function.comp_def]

/-- 有限存在连接保留普通推导的正负表示。 -/
def localTest {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ) (rules : List (Rule T)) :
    ObjectCheckedTrace.LocalTest T where
  condition := template rules
  delta0 := by
    apply anyOf_delta0
    intro φ hφ
    obtain ⟨rule, _, rfl⟩ := List.mem_map.mp hφ
    exact rule.delta0
  checked := checked rules
  positive root h := by
    obtain ⟨rule, hRule, h⟩ := List.any_eq_true.mp h
    rw [template_apply]
    exact anyOf_intro (List.mem_map.mpr ⟨rule, hRule, rfl⟩) (rule.positive C hSuccessor root h)
  negative root h := by
    rw [template_apply]
    apply anyOf_negative
    intro φ hφ
    obtain ⟨rule, hRule, rfl⟩ := List.mem_map.mp hφ
    exact rule.negative C root (Bool.eq_false_iff.mpr (List.any_eq_false.mp h rule hRule))

end YesMetaZFC.Automation.ObjectLocalDecision
