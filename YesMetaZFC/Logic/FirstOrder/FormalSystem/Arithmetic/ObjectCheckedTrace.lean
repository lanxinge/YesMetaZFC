import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornCheck

/-! # 带局部检查的完整递归轨迹

公理、语法和单步连接的对象测试可以在行处复用已有表示。
本模块实际构造递归布尔检查、固定 Delta0 轨迹公式及其正负推导。
局部测试自身的正负表示必须已证明；这里不以新增公理代替它们。
-/
namespace YesMetaZFC.Automation.ObjectCheckedTrace
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

structure LocalTest (T : SetTheory) where
  condition : FormulaTemplate.Unary
  delta0 : Formula.IsDelta0 set_levy_bound condition.body
  checked : Nat → Bool
  positive : ∀ n, checked n = true → Derives T [] (condition (numₘ(n) : Code))
  negative : ∀ n, checked n = false → Derives T [] (¬ₘ condition (numₘ(n) : Code))

def check (localCheck : Nat → Bool) (rules : List Rule) (rank : Nat → Nat) (root : Nat) : Bool :=
  localCheck root && rules.any fun rule => (environments root rule.arity).any fun values =>
    (root == rule.head.eval values) &&
    rule.guards.all (fun guard => decide (guard.1.eval values < guard.2.eval values)) &&
    rule.premises.all (fun premise =>
      if _h : rank (premise.eval values) < rank root then
        check localCheck rules rank (premise.eval values)
      else false)
termination_by rank root

theorem check_eq_true_iff (localCheck : Nat → Bool) (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (root : Nat) :
    check localCheck rules rank root = true ↔ localCheck root = true ∧
      ∃ rule, rule ∈ rules ∧ ∃ values : Fin rule.arity → Nat,
        (∀ i, values i ≤ root) ∧ root = rule.head.eval values ∧
        (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) ∧
        (∀ premise, premise ∈ rule.premises → check localCheck rules rank (premise.eval values) = true) := by
  rw [check]
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq, mem_environments]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨rule, hRule, values, hBound, ⟨hHead, hGuards⟩, hPremises⟩
    refine ⟨rule, hRule, values, hBound, hHead, hGuards, ?_⟩
    intro premise hPremise
    have h := hPremises premise hPremise
    split at h
    · exact h
    · cases h
  · rintro ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩
    refine ⟨rule, hRule, values, hBound, ⟨hHead, hGuards⟩, ?_⟩
    intro premise hPremise
    have hRank : rank (premise.eval values) < rank root := by
      rw [hHead]
      exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise
    simp only [dif_pos hRank]
    exact hPremises premise hPremise

def step (rules : List Rule) (localCondition : FormulaTemplate.Unary) : FormulaTemplate.Binary where
  body := (ObjectHorn.step rules).body ∧ₘ
    localCondition (.fvar .here)

@[simp] theorem step_apply (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    {bound free : SetContext} (row trace : SetTerm bound free) :
    step rules localCondition row trace = (ObjectHorn.step rules row trace) ∧ₘ localCondition row := by
  change Formula.substituteMapped _ _ (_ ∧ₘ _) = _
  simp only [Formula.substituteMapped, FormulaTemplate.apply_one_substituteMapped]
  rfl

def condition (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    {bound free : SetContext} (root : SetTerm bound free) : SetFormula bound free :=
  ObjectTrace.condition (step rules localCondition) ωₘ root

@[simp] theorem condition_instantiateTop (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    {free : SetContext} (point : SetOpenTerm free) :
    (condition rules localCondition (.bvar .here : SetTerm [SetSort.set] free)).instantiateTop point =
      condition rules localCondition point := by
  simp [condition, Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.instantiateTop]

theorem transport {T : SetTheory} (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    {free : SetContext} {Γ : Context signature free} {left right : SetOpenTerm free}
    (hEq : Derives T Γ (left ≐ₘ right))
    (h : Derives T Γ (condition rules localCondition left)) : Derives T Γ (condition rules localCondition right) := by
  have h := FirstOrder.Derives.eq_subst (body := condition rules localCondition (.bvar .here)) hEq
    (by rw [condition_instantiateTop]; exact h)
  rwa [condition_instantiateTop] at h

theorem transport_negative {T : SetTheory} (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    {free : SetContext} {Γ : Context signature free} {left right : SetOpenTerm free}
    (hEq : Derives T Γ (left ≐ₘ right))
    (h : Derives T Γ (¬ₘ condition rules localCondition left)) :
    Derives T Γ (¬ₘ condition rules localCondition right) := by
  have h := FirstOrder.Derives.eq_subst (body := .neg (condition rules localCondition (.bvar .here))) hEq
    (by rw [Formula.instantiateTop_neg, condition_instantiateTop]; exact h)
  rwa [Formula.instantiateTop_neg, condition_instantiateTop] at h

theorem delta0 (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    (hLocal : Formula.IsDelta0 set_levy_bound localCondition.body)
    {bound free : SetContext} (root : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition rules localCondition root) := by
  apply ObjectTrace.condition_delta0
  exact .conj (ObjectHorn.step_delta0 rules) (localCondition.instantiate_delta0 hLocal _)

/-- 实际接受的递归检查给出所有行都通过局部测试的有限闭合轨迹。 -/
theorem accepted_rows (localCheck : Nat → Bool) (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (root : Nat)
    (h : check localCheck rules rank root = true) :
    ∃ rows, root ∈ rows ∧ ClosedRows rules rows ∧ ∀ row, row ∈ rows → localCheck row = true := by
  classical
  obtain ⟨hLocal, rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ :=
    (check_eq_true_iff localCheck rules rank descending root).mp h
  have children : ∀ premise, premise ∈ rule.premises → ∃ rows,
      premise.eval values ∈ rows ∧ ClosedRows rules rows ∧ ∀ row, row ∈ rows → localCheck row = true := by
    intro premise hPremise
    exact accepted_rows localCheck rules rank descending (premise.eval values) (hPremises premise hPremise)
  let parts := rule.premises.attach.map (fun p => (children p.1 p.2).choose)
  have hParts : ∀ part, part ∈ parts → ClosedRows rules part ∧ ∀ row, row ∈ part → localCheck row = true := by
    intro part hPart
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hPart
    exact (children p.1 p.2).choose_spec.2
  have hMembers : ∀ premise, premise ∈ rule.premises → premise.eval values ∈ parts.flatten := by
    intro premise hPremise
    exact List.mem_flatten.mpr ⟨(children premise hPremise).choose,
      List.mem_map.mpr ⟨⟨premise, hPremise⟩, List.mem_attach _ _, rfl⟩,
      (children premise hPremise).choose_spec.1⟩
  refine ⟨root :: parts.flatten, List.mem_cons_self, ?_, ?_⟩
  · intro row hRow
    rcases List.mem_cons.mp hRow with rfl | hRow
    · exact ⟨rule, hRule, values, hBound, hHead, hGuards,
        fun p hp => List.mem_cons_of_mem _ (hMembers p hp)⟩
    · obtain ⟨other, hOther, env, hBound, hHead, hGuards, hPremises⟩ :=
        ClosedRows.flatten parts (fun part hp => (hParts part hp).1) row hRow
      exact ⟨other, hOther, env, hBound, hHead, hGuards,
        fun p hp => List.mem_cons_of_mem _ (hPremises p hp)⟩
  · intro row hRow
    rcases List.mem_cons.mp hRow with rfl | hRow
    · exact hLocal
    · obtain ⟨part, hPart, hRow⟩ := List.mem_flatten.mp hRow
      exact (hParts part hPart).2 row hRow
termination_by rank root
decreasing_by
  rw [hHead]
  exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise

/-- 局部重放的正确性沿所有子证明传播到完整检查结果。 -/
theorem check_sound (localCheck : Nat → Bool) (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (meaning : Nat → Prop)
    (sound : ∀ rule, rule ∈ rules → ∀ values : Fin rule.arity → Nat,
      (∀ i, values i ≤ rule.head.eval values) →
      (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
      localCheck (rule.head.eval values) = true →
      (∀ premise, premise ∈ rule.premises → meaning (premise.eval values)) →
      meaning (rule.head.eval values))
    (root : Nat) (h : check localCheck rules rank root = true) : meaning root := by
  obtain ⟨hLocal, rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ :=
    (check_eq_true_iff localCheck rules rank descending root).mp h
  rw [hHead]
  apply sound rule hRule values (by rwa [← hHead]) hGuards (by rwa [← hHead])
  intro premise hPremise
  exact check_sound localCheck rules rank descending meaning sound (premise.eval values) (hPremises premise hPremise)
termination_by rank root
decreasing_by
  rw [hHead]
  exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (localTest : LocalTest T) (rules : List Rule) (rank : Nat → Nat) (descending : Descending rules rank)
    (root : Nat) (h : check localTest.checked rules rank root = true) :
    Derives T [] (condition rules localTest.condition (numₘ(root) : Code)) := by
  obtain ⟨rows, hRoot, hRows, hLocal⟩ := accepted_rows localTest.checked rules rank descending root h
  apply ObjectTrace.positive S hPower (step rules localTest.condition) ωₘ (numₘ(root))
    (rows.map (fun n => numₘ(n))) (List.mem_map.mpr ⟨root, hRoot, rfl⟩)
  · intro row hRow
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hRow
    exact FirstOrder.Derives.theory_weaken hInfinity (infinity_finite_numeral_mem_omega n)
  · intro row hRow
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hRow
    rw [step_apply]
    apply FirstOrder.Derives.conj_intro
    · obtain ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ := hRows n hn
      rw [ObjectHorn.step_apply]
      apply anyOf_intro (List.mem_map.mpr ⟨rule, hRule, rfl⟩)
      apply rule.positive C S.contains_successor n _ values hBound hHead hGuards
      intro premise hPremise
      exact ObjectFiniteSet.member_intro S (List.mem_map.mpr
        ⟨premise.eval values, hPremises premise hPremise, rfl⟩)
    · exact localTest.positive n (hLocal n hn)

/-- 负向递归直接排除任意对象轨迹中的该行，允许轨迹含非标准对象。 -/
theorem not_member {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (localTest : LocalTest T) (rules : List Rule) (rank : Nat → Nat) (descending : Descending rules rank)
    (root : Nat) (h : check localTest.checked rules rank root = false)
    {free : SetContext} {Γ : Context signature free} (trace : SetOpenTerm free)
    (hClosed : Derives T Γ (ObjectTrace.closed (step rules localTest.condition) trace)) :
    Derives T Γ (¬ₘ ((numₘ(root)) ∈ₘ trace)) := by
  classical
  apply FirstOrder.Derives.neg_intro
  have hStep := ObjectTrace.closed_elim (step rules localTest.condition) trace (numₘ(root))
    (FirstOrder.Derives.context_weaken_cons hClosed)
    (FirstOrder.Derives.assumption List.mem_cons_self)
  rw [step_apply] at hStep
  by_cases hLocal : localTest.checked root = true
  · have hHornNeg : Derives T Γ (¬ₘ ObjectHorn.step rules (numₘ(root)) trace) := by
      rw [ObjectHorn.step_apply]
      apply anyOf_negative
      intro formula hFormula
      obtain ⟨rule, hRule, rfl⟩ := List.mem_map.mp hFormula
      apply rule.negative C A root trace
      intro values hBound hHead hGuards
      have hExists : ∃ premise, premise ∈ rule.premises ∧
          check localTest.checked rules rank (premise.eval values) = false := by
        apply Classical.byContradiction
        intro hNo
        have hTrue := (check_eq_true_iff localTest.checked rules rank descending root).mpr
          ⟨hLocal, rule, hRule, values, hBound, hHead, hGuards, fun p hp => by
            cases hChild : check localTest.checked rules rank (p.eval values) with
            | false => exact False.elim (hNo ⟨p, hp, hChild⟩)
            | true => rfl⟩
        rw [h] at hTrue
        cases hTrue
      obtain ⟨premise, hPremise, hFalse⟩ := hExists
      exact ⟨premise, hPremise,
        not_member C A localTest rules rank descending (premise.eval values) hFalse trace hClosed⟩
    exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hStep)
      (FirstOrder.Derives.context_weaken_cons hHornNeg)
  · have hNegative := localTest.negative root (Bool.eq_false_iff.mpr hLocal)
    have hNegative' : Derives T Γ (¬ₘ localTest.condition (numₘ(root) : SetOpenTerm free)) := by
      have hOpen := FirstOrder.Derives.free_substitution
        (VariableSubstitution.empty : VariableSubstitution signature [] [] free) hNegative
      apply FirstOrder.Derives.context_weaken (Γ := []) (by simp)
      simpa [Formula.substituteFree, Formula.substitute, Substitution.free_map, Context.substituteFree,
        Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped] using hOpen
    exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_right hStep)
      (FirstOrder.Derives.context_weaken_cons hNegative')
termination_by rank root
decreasing_by
  rw [hHead]
  exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (localTest : LocalTest T) (rules : List Rule) (rank : Nat → Nat) (descending : Descending rules rank)
    (root : Nat) (h : check localTest.checked rules rank root = false) :
    Derives T [] (¬ₘ condition rules localTest.condition (numₘ(root) : Code)) :=
  ObjectTrace.negative (step rules localTest.condition) ωₘ root
    (fun _ trace hClosed => not_member C A localTest rules rank descending root h trace hClosed)

end YesMetaZFC.Automation.ObjectCheckedTrace
