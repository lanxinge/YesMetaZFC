import YesMetaZFC.Automation.ObjectNumeralSyntax

/-! # 固定码表达式的迭代图

前槽携带步数，后槽携带上一步结果。两条固定 Horn 规则表示整个递推，
不按具体输入展开规则表；上一结果出现在输出表达式中，保证行码见证界。
-/
namespace YesMetaZFC.Automation.ObjectExpressionIteration
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation QuineEncoding
open ObjectHorn ObjectCodeProjection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def value_m (seed : Nat) (step : Expr 2) : Nat → Nat
  | 0 => seed
  | n + 1 => step.eval (fun i : Fin 2 => [n, value_m seed step n][i])

abbrev seedRule_m (seed : Nat) : Rule where
  arity := 0
  head := .node (.literal 0) [.literal 0, .literal seed]

abbrev stepRule_m (step : Expr 2) : Rule where
  arity := 2
  head := .node (.literal 0) [.succ (.var 0), step]
  premises := [.node (.literal 0) [.var 0, .var 1]]

def rules_m (seed : Nat) (step : Expr 2) := [seedRule_m seed, stepRule_m step]
def rank_m (row : Nat) := field row 0

theorem descending_m (seed : Nat) (step : Expr 2) : Descending (rules_m seed step) rank_m := by
  intro rule hRule values _ _ premise hPremise
  simp only [rules_m, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl
  · cases hPremise
  · obtain rfl := List.mem_singleton.mp hPremise
    simp [rank_m, Expr.eval]

private theorem accept_m (seed : Nat) (step : Expr 2) (hStep : 1 ∈ step.variables) (number : Nat) :
    Acceptance (rules_m seed step) (nodeValue 0 [number, value_m seed step number]) := by
  induction number with
  | zero =>
    exact Acceptance.of_rule (seedRule_m seed) (by simp [rules_m]) Fin.elim0
      (fun i => Fin.elim0 i) (by intro g hg; cases hg) (by intro p hp; cases hp)
  | succ number ih =>
    apply Acceptance.of_rule (stepRule_m step) (by simp [rules_m])
      (fun i : Fin 2 => [number, value_m seed step number][i])
    · intro i
      apply (stepRule_m step).head.variable_le
      change Fin 2 at i
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> simp [stepRule_m, Expr.node, Expr.list, Expr.variables, hStep]
    · intro g hg; cases hg
    · intro p hp; obtain rfl := List.mem_singleton.mp hp; exact ih

private def Meaning_m (seed : Nat) (step : Expr 2) (row : Nat) :=
  value_m seed step (field row 0) = field row 1

private theorem sound_m (seed : Nat) (step : Expr 2) (rule : Rule)
    (hRule : rule ∈ rules_m seed step) (values : Fin rule.arity → Nat)
    (hPremises : ∀ p, p ∈ rule.premises → Meaning_m seed step (p.eval values)) :
    Meaning_m seed step (rule.head.eval values) := by
  simp only [rules_m, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl
  · simp [Meaning_m, Expr.eval, value_m]
  · have h := hPremises _ List.mem_cons_self
    simp [Meaning_m, Expr.eval] at h ⊢
    rw [value_m, h]
    congr 1
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> rfl

def checked_m (seed : Nat) (step : Expr 2) (number output : Nat) :=
  check (rules_m seed step) rank_m (nodeValue 0 [number, output])

theorem checked_iff_m (seed : Nat) (step : Expr 2) (hStep : 1 ∈ step.variables)
    (number output : Nat) : checked_m seed step number output = true ↔ value_m seed step number = output := by
  constructor
  · intro h
    have h := check_sound (rules_m seed step) rank_m (descending_m seed step) (Meaning_m seed step)
      (fun r hr values _ _ hp => sound_m seed step r hr values hp) _ h
    simpa [Meaning_m] using h
  · intro h
    rw [← h]
    exact acceptance_check _ _ (descending_m seed step) _ (accept_m seed step hStep number)

def condition_m (seed : Nat) (step : Expr 2) {bound free : SetContext}
    (number output : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition (rules_m seed step) (IntrinsicQuotation.node 0 [number, output])

@[simp] theorem condition_substituteMapped_m (seed : Nat) (step : Expr 2)
    {sb sf tb tf : SetContext} (number output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition_m seed step number output).substituteMapped bs fs =
      condition_m seed step (number.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition_m]

theorem positive_m {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (seed : Nat) (step : Expr 2) (hStep : 1 ∈ step.variables) (number : Nat) :
    Derives T [] (condition_m seed step (numₘ(number)) (numₘ(value_m seed step number) : Code)) := by
  obtain ⟨rows, hRoot, hRows⟩ := accept_m seed step hStep number
  exact ObjectHorn.transport _ (FirstOrder.Derives.eq_symm (node_evaluate C 0 [number, value_m seed step number]))
    (ObjectHorn.positive C S hPower hInfinity _ _ rows hRoot hRows)

theorem negative_m {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (seed : Nat) (step : Expr 2) (hStep : 1 ∈ step.variables) (number output : Nat)
    (h : value_m seed step number ≠ output) :
    Derives T [] (¬ₘ condition_m seed step (numₘ(number)) (numₘ(output) : Code)) := by
  have hc : checked_m seed step number output = false :=
    Bool.eq_false_iff.mpr (fun ht => h ((checked_iff_m seed step hStep number output).mp ht))
  exact ObjectHorn.transport_negative _ (FirstOrder.Derives.eq_symm (node_evaluate C 0 [number, output]))
    (ObjectHorn.negative C A (check_rejection _ _ (descending_m seed step) _ hc))

end YesMetaZFC.Automation.ObjectExpressionIteration
