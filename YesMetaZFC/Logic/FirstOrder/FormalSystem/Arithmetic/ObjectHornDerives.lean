import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHorn
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxTransport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchema

/-!
# 有限规则的对象推导编译

量词消去使用有限 numeral 的成员反演，因而不要求对象见证预先具有宿主值。
-/
namespace YesMetaZFC.Automation.ObjectHorn
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem Expr.evaluate_open {T : SetTheory} (C : CertificateCore T)
    {free : SetContext} {Γ : Context signature free}
    {n : Nat} (expr : Expr n) (env : Fin n → Nat) :
    Derives T Γ (expr.term (fun i => numₘ(env i)) ≐ₘ numₘ(expr.eval env)) := by
  have h := FirstOrder.Derives.free_renaming
    (ρ := (VariableRenaming.empty : VariableRenaming [] free)) (expr.evaluate C env)
  apply FirstOrder.Derives.context_weaken (Γ := []) (by simp)
  simpa [Formula.renameFree, Formula.rename, Renaming.free, Formula.renameMapped] using h

theorem allOf_intro {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (formulas : List (SetOpenFormula free))
    (h : ∀ φ, φ ∈ formulas → Derives T Γ φ) : Derives T Γ (allOf formulas) := by
  induction formulas with
  | nil => exact FirstOrder.Derives.truth_intro
  | cons head tail ih =>
    exact FirstOrder.Derives.conj_intro (h head List.mem_cons_self)
      (ih (fun φ hφ => h φ (List.mem_cons_of_mem head hφ)))

theorem allOf_elim {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    {formulas : List (SetOpenFormula free)} {φ : SetOpenFormula free}
    (h : Derives T Γ (allOf formulas)) (hφ : φ ∈ formulas) : Derives T Γ φ := by
  induction formulas with
  | nil => simp at hφ
  | cons head tail ih =>
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact FirstOrder.Derives.conj_elim_left h
    · exact ih (FirstOrder.Derives.conj_elim_right h) hφ

theorem anyOf_intro {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    {formulas : List (SetOpenFormula free)} {φ : SetOpenFormula free}
    (hφ : φ ∈ formulas) (h : Derives T Γ φ) : Derives T Γ (anyOf formulas) := by
  induction formulas with
  | nil => simp at hφ
  | cons head tail ih =>
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact FirstOrder.Derives.disj_intro_left h
    · exact FirstOrder.Derives.disj_intro_right (ih hφ)

theorem anyOf_negative {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (formulas : List (SetOpenFormula free))
    (h : ∀ φ, φ ∈ formulas → Derives T Γ (¬ₘ φ)) : Derives T Γ (¬ₘ anyOf formulas) := by
  induction formulas with
  | nil => exact FirstOrder.Derives.neg_intro (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head tail ih =>
    exact IntrinsicSchema.disj_neg (h head List.mem_cons_self)
      (ih (fun φ hφ => h φ (List.mem_cons_of_mem head hφ)))

def numeralSubstitution {n : Nat} {free : SetContext} (values : Fin n → Nat) :
    VariableSubstitution signature (project_bound_context n) [] free :=
  fun {sort} entry => by
    cases sort
    exact numₘ(values (project_bound_index entry))

@[simp] theorem numeralSubstitution_variable {n : Nat} {free : SetContext}
    (values : Fin n → Nat) (index : Fin n) :
    @numeralSubstitution n free values (sort := SetSort.set) (project_bound_variable index) =
      numₘ(values index) := by simp [numeralSubstitution]

theorem numeralSubstitution_cons {n : Nat} {free : SetContext} (values : Fin (n + 1) → Nat) :
    @numeralSubstitution (n + 1) free values =
      (fun {sort} entry => VariableSubstitution.cons (numₘ(values 0))
        (@numeralSubstitution n free (fun i => values i.succ)) (sort := sort) entry) := by
  funext sort entry
  cases entry <;> rfl

@[simp] theorem numeralSubstitution_zero {free : SetContext} (values : Fin 0 → Nat) :
    @numeralSubstitution 0 free values = (fun {sort} entry => VariableSubstitution.empty (sort := sort) entry) := by
  funext sort entry
  cases entry

theorem quantify_positive {T : SetTheory} {sourceFree free : SetContext}
    {Γ : Context signature free} (n : Nat) (bound : SetOpenTerm sourceFree)
    (body : SetFormula (project_bound_context n) sourceFree)
    (fs : VariableSubstitution signature sourceFree [] free) (values : Fin n → Nat)
    (hBound : ∀ i, Derives T Γ
      ((numₘ(values i)) ∈ₘ bound.substituteMapped VariableSubstitution.empty fs))
    (hBody : Derives T Γ (body.substituteMapped (numeralSubstitution values) fs)) :
    Derives T Γ ((quantify n bound body).substituteMapped VariableSubstitution.empty fs) := by
  induction n with
  | zero => simpa only [quantify, numeralSubstitution_zero] using hBody
  | succ n ih =>
    apply ih _ (fun i => values i.succ) (fun i => hBound i.succ)
    let inner := body.substituteMapped
      (VariableSubstitution.liftBound SetSort.set (numeralSubstitution (fun i => values i.succ)))
      (VariableSubstitution.weakenBound SetSort.set fs)
    have hInstance : Derives T Γ (inner.instantiateTop (numₘ(values 0))) := by
      simp only [inner, Formula.substituteMapped_liftBound_instantiateTop]
      rw [← numeralSubstitution_cons]
      exact hBody
    have hExists := bounded_exists_intro
      (bound.substituteMapped VariableSubstitution.empty fs) inner (numₘ(values 0))
      (hBound 0) hInstance
    simpa only [Formula.LevyBound.boundedExists, Formula.substituteMapped,
      Formula.LevyBound.membership_substituteMapped, Term.substituteMapped_weakenBound,
      Term.embedBoundClosed_substituteMapped, inner] using! hExists

theorem quantify_negative {T : SetTheory} (C : FiniteCore T)
    {sourceFree free : SetContext} {Γ : Context signature free}
    (n : Nat) (bound : SetOpenTerm sourceFree)
    (body : SetFormula (project_bound_context n) sourceFree)
    (fs : VariableSubstitution signature sourceFree [] free) (limit : Nat)
    (hBound : bound.substituteMapped VariableSubstitution.empty fs = numₘ(limit))
    (hBody : ∀ values : Fin n → Nat, (∀ i, values i < limit) →
      Derives T Γ (¬ₘ body.substituteMapped (numeralSubstitution values) fs)) :
    Derives T Γ (¬ₘ (quantify n bound body).substituteMapped VariableSubstitution.empty fs) := by
  induction n with
  | zero =>
    simpa only [quantify, numeralSubstitution_zero] using
      hBody Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
    apply ih
    intro tail hTail
    let inner := body.substituteMapped
      (VariableSubstitution.liftBound SetSort.set (numeralSubstitution tail))
      (VariableSubstitution.weakenBound SetSort.set fs)
    have hReject := bounded_exists_numeral_neg C limit inner (fun value hValue => by
      simp only [inner, Formula.substituteMapped_liftBound_instantiateTop]
      have h := hBody (Fin.cases value tail) (Fin.cases hValue hTail)
      rw [numeralSubstitution_cons] at h
      exact h)
    simpa only [Formula.LevyBound.boundedExists, Formula.substituteMapped,
      Formula.LevyBound.membership_substituteMapped, Term.substituteMapped_weakenBound,
      Term.embedBoundClosed_substituteMapped, hBound, inner] using! hReject

theorem Rule.positive_matrix {T : SetTheory}
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    {free : SetContext} {Γ : Context signature free}
    (rule : Rule) (root : Nat) (trace : SetOpenTerm free) (values : Fin rule.arity → Nat)
    (hBound : ∀ i, values i ≤ root)
    (hMatrix : Derives T Γ (rule.matrix (fun i => numₘ(values i)) (numₘ(root)) trace)) :
    Derives T Γ (rule.template (numₘ(root)) trace) := by
  unfold Rule.template FormulaTemplate.apply_two FormulaTemplate.instantiate
  apply quantify_positive (values := values)
  · intro i
    simpa [Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons,
      finite_numeral_term] using
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
        (numeral_mem_of_lt hSuccessor (Nat.lt_succ_of_le (hBound i)))
  · simpa [Rule.matrix_substituteMapped, Term.substituteMapped, VariableSubstitution.cons] using hMatrix

theorem Rule.negative_matrix {T : SetTheory} (C : FiniteCore T)
    {free : SetContext} {Γ : Context signature free}
    (rule : Rule) (root : Nat) (trace : SetOpenTerm free)
    (hMatrix : ∀ values : Fin rule.arity → Nat, (∀ i, values i ≤ root) →
      Derives T Γ (¬ₘ rule.matrix (fun i => numₘ(values i)) (numₘ(root)) trace)) :
    Derives T Γ (¬ₘ rule.template (numₘ(root)) trace) := by
  unfold Rule.template FormulaTemplate.apply_two FormulaTemplate.instantiate
  apply quantify_negative C (limit := root + 1)
  · rfl
  · intro values hValues
    simpa [Rule.matrix_substituteMapped, Term.substituteMapped, VariableSubstitution.cons] using
      hMatrix values (fun i => Nat.le_of_lt_succ (hValues i))

private theorem numeral_ne_open {T : SetTheory} (C : NumeralArithmetic T)
    {free : SetContext} {Γ : Context signature free} {left right : Nat} (h : left ≠ right) :
    Derives T Γ (¬ₘ ((numₘ(left)) ≐ₘ numₘ(right))) := by
  have h := FirstOrder.Derives.free_renaming
    (ρ := (VariableRenaming.empty : VariableRenaming [] free)) (C.numeral_ne h)
  apply FirstOrder.Derives.context_weaken (Γ := []) (by simp)
  simpa [Formula.renameFree, Formula.rename, Renaming.free, Formula.renameMapped] using h

private theorem numeral_not_mem_open {T : SetTheory} (A : ArithmeticSupport T)
    {free : SetContext} {Γ : Context signature free} {left right : Nat} (h : ¬ left < right) :
    Derives T Γ (¬ₘ ((numₘ(left)) ∈ₘ numₘ(right))) := by
  have h := FirstOrder.Derives.free_renaming
    (ρ := (VariableRenaming.empty : VariableRenaming [] free))
    (numeral_not_mem_of_not_lt A.contains_empty_set A.contains_membership_irreflexive
      A.contains_successor h)
  apply FirstOrder.Derives.context_weaken (Γ := []) (by simp)
  simpa [Formula.renameFree, Formula.rename, Renaming.free, Formula.renameMapped,
    Arguments.renameMapped] using h

theorem Rule.positive {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    {free : SetContext} {Γ : Context signature free}
    (rule : Rule) (root : Nat) (trace : SetOpenTerm free) (values : Fin rule.arity → Nat)
    (hBound : ∀ i, values i ≤ root) (hHead : root = rule.head.eval values)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises →
      Derives T Γ (numₘ(premise.eval values) ∈ₘ trace)) :
    Derives T Γ (rule.template (numₘ(root)) trace) := by
  apply rule.positive_matrix hSuccessor root trace values hBound
  apply FirstOrder.Derives.conj_intro
  · rw [hHead]
    exact FirstOrder.Derives.eq_symm (rule.head.evaluate_open C values)
  · apply FirstOrder.Derives.conj_intro
    · apply allOf_intro
      intro φ hφ
      obtain ⟨guard, hGuard, rfl⟩ := List.mem_map.mp hφ
      apply FirstOrder.Derives.iff_elim_right
        (membership_left_iff_of_equality _ _ _ (guard.1.evaluate_open C values))
      apply FirstOrder.Derives.iff_elim_right
        (membership_right_iff_of_equality _ _ _ (guard.2.evaluate_open C values))
      exact FirstOrder.Derives.context_weaken (Γ := []) (by simp)
        (numeral_mem_of_lt hSuccessor (hGuards guard hGuard))
    · apply allOf_intro
      intro φ hφ
      obtain ⟨premise, hPremise, rfl⟩ := List.mem_map.mp hφ
      exact FirstOrder.Derives.iff_elim_right
        (membership_left_iff_of_equality _ _ _ (premise.evaluate_open C values))
        (hPremises premise hPremise)

/-- 头码和守卫的有限判定自动消去；调用方只负责真正递归的失败前提。 -/
theorem Rule.negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    {free : SetContext} {Γ : Context signature free}
    (rule : Rule) (root : Nat) (trace : SetOpenTerm free)
    (hReject : ∀ values : Fin rule.arity → Nat, (∀ i, values i ≤ root) →
      root = rule.head.eval values →
      (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
      ∃ premise, premise ∈ rule.premises ∧ Derives T Γ (¬ₘ (numₘ(premise.eval values) ∈ₘ trace))) :
    Derives T Γ (¬ₘ rule.template (numₘ(root)) trace) := by
  classical
  apply rule.negative_matrix C.toFiniteCore root trace
  intro values hValues
  apply FirstOrder.Derives.neg_intro
  let matrix := rule.matrix (fun i => numₘ(values i)) (numₘ(root)) trace
  have hMatrix : Derives T (matrix :: Γ) matrix :=
    FirstOrder.Derives.assumption List.mem_cons_self
  by_cases hHead : root = rule.head.eval values
  · by_cases hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values
    · obtain ⟨premise, hPremise, hNeg⟩ := hReject values hValues hHead hGuards
      have hMember := allOf_elim
        (FirstOrder.Derives.conj_elim_right (FirstOrder.Derives.conj_elim_right hMatrix))
        (List.mem_map.mpr ⟨premise, hPremise, rfl⟩)
      exact FirstOrder.Derives.neg_elim
        (FirstOrder.Derives.iff_elim_left
          (membership_left_iff_of_equality _ _ _ (premise.evaluate_open C values)) hMember)
        (FirstOrder.Derives.context_weaken_cons hNeg)
    · obtain ⟨guard, hGuard, hNotLt⟩ : ∃ guard, guard ∈ rule.guards ∧
          ¬ guard.1.eval values < guard.2.eval values := by simpa using hGuards
      have hMember := allOf_elim
        (FirstOrder.Derives.conj_elim_left (FirstOrder.Derives.conj_elim_right hMatrix))
        (List.mem_map.mpr ⟨guard, hGuard, rfl⟩)
      have hLeft := FirstOrder.Derives.iff_elim_left
        (membership_left_iff_of_equality _ _ _ (guard.1.evaluate_open C values)) hMember
      have hBoth := FirstOrder.Derives.iff_elim_left
        (membership_right_iff_of_equality _ _ _ (guard.2.evaluate_open C values)) hLeft
      exact FirstOrder.Derives.neg_elim hBoth (numeral_not_mem_open A hNotLt)
  · exact FirstOrder.Derives.neg_elim
      (Metatheory.Derives.equality_trans (FirstOrder.Derives.conj_elim_left hMatrix)
        (rule.head.evaluate_open C values))
      (numeral_ne_open C.toNumeralArithmetic hHead)

end YesMetaZFC.Automation.ObjectHorn
