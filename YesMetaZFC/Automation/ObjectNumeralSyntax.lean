import YesMetaZFC.Automation.ObjectHornLocal
import YesMetaZFC.Automation.ObjectHornValues
import YesMetaZFC.Automation.ObjectCodeProjection

/-! # 当前内核中自然数项的 quotation 图

零为 emptySet 的应用，后继为 successor 的一元应用。只使用两个固定规则，
不沿用旧 Hilbert quotation 的常项与应用标签。
-/
namespace YesMetaZFC.Automation.ObjectNumeralSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation NatPacket QuineEncoding
open ObjectHorn ObjectCodeProjection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

abbrev node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields
abbrev zeroCode : Nat := treeValue (SyntaxEncode.term (numₘ(0) : Code))
abbrev successorSymbol : Nat := treeValue (leaf FunctionSymbol.successor.ctorIdx)
def value : Nat → Nat
  | 0 => zeroCode
  | n + 1 => nodeValue 2 [successorSymbol, value n]

theorem value_encode_m {bound free : SetContext} (number : Nat) :
    value number = treeValue (SyntaxEncode.term (numₘ(number) : SetTerm bound free)) := by
  induction number with
  | zero => rfl
  | succ number ih =>
    change nodeValue 2 [successorSymbol, value number] =
      nodeValue 2 [successorSymbol, treeValue (SyntaxEncode.term (numₘ(number) : SetTerm bound free))]
    rw [ih]

theorem value_encode (number : Nat) : value number = treeValue (SyntaxEncode.term (numₘ(number) : Code)) :=
  value_encode_m number

abbrev zeroRule : Rule where
  arity := 0
  head := node 0 [.literal 0, .literal zeroCode]
abbrev successorRule : Rule where
  arity := 2
  head := node 0 [.succ (.var 0), node 2 [.literal successorSymbol, .var 1]]
  premises := [node 0 [.var 0, .var 1]]
def rules : List Rule := [zeroRule, successorRule]
def rank (row : Nat) : Nat := field row 0

theorem descending : Descending rules rank := by
  intro rule hRule values _ _ premise hPremise
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl
  · cases hPremise
  · obtain rfl := List.mem_singleton.mp hPremise
    simp [rank, Expr.eval]

private theorem accept (number : Nat) : Acceptance rules (nodeValue 0 [number, value number]) := by
  induction number with
  | zero =>
    exact Acceptance.of_rule zeroRule (by simp [rules]) Fin.elim0 (fun i => Fin.elim0 i)
      (by intro g hg; cases hg) (by intro p hp; cases hp)
  | succ number ih =>
    exact Acceptance.of_rule successorRule (by simp [rules])
      (fun i : Fin 2 => [number, value number][i])
      (fun i => successorRule.head.variable_le _ (by exact (show ∀ j : Fin 2, j ∈ successorRule.head.variables from by decide) i))
      (by intro g hg; cases hg) (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact ih)

private def Meaning (row : Nat) : Prop := value (field row 0) = field row 1
private theorem sound (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hPremises : ∀ p, p ∈ rule.premises → Meaning (p.eval values)) : Meaning (rule.head.eval values) := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl
  · simp [Meaning, Expr.eval, value]
  · simpa [Meaning, Expr.eval, value] using congrArg (fun n => nodeValue 2 [successorSymbol, n])
      (hPremises _ List.mem_cons_self)

def checked (number output : Nat) : Bool := check rules rank (nodeValue 0 [number, output])
theorem checked_iff (number output : Nat) : checked number output = true ↔ value number = output := by
  constructor
  · intro h
    have h := check_sound rules rank descending Meaning (fun r hr values _ _ hp => sound r hr values hp) _ h
    simpa [Meaning] using h
  · intro h
    rw [← h]
    exact acceptance_check rules rank descending _ (accept number)

def condition {bound free : SetContext} (number output : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 0 [number, output])
@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (number output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition number output).substituteMapped bs fs = condition (number.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition]

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ) (number : Nat) :
    Derives T [] (condition (numₘ(number)) (numₘ(value number) : Code)) := by
  obtain ⟨rows, hRoot, hRows⟩ := accept number
  exact ObjectHorn.transport rules (FirstOrder.Derives.eq_symm (node_evaluate C 0 [number, value number]))
    (ObjectHorn.positive C S hPower hInfinity rules _ rows hRoot hRows)

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (number output : Nat) (h : value number ≠ output) :
    Derives T [] (¬ₘ condition (numₘ(number)) (numₘ(output) : Code)) := by
  have hCheck : checked number output = false := Bool.eq_false_iff.mpr (fun hTrue => h ((checked_iff _ _).mp hTrue))
  exact ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm (node_evaluate C 0 [number, output]))
    (ObjectHorn.negative C A (check_rejection rules rank descending _ hCheck))

end YesMetaZFC.Automation.ObjectNumeralSyntax
