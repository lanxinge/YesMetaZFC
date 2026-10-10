import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ExponentiationTrace

/-! # 只用于连接界的后继与幂项求值；不扩展证书核 -/
namespace YesMetaZFC.Automation.ObjectArithmeticTerm
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT QuineEncoding
open Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def shift {bound free : SetContext} : Nat → SetTerm bound free → SetTerm bound free
  | 0, input => input
  | n + 1, input => Sₘ(shift n input)

@[simp] theorem shift_numeral {bound free : SetContext} (k n : Nat) :
    shift k (numₘ(n) : SetTerm bound free) = numₘ(n + k) := by
  induction k <;> simp_all [shift, finite_numeral_term]

@[simp] theorem shift_substituteMapped {sb sf tb tf : SetContext} (k : Nat) (input : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (shift k input).substituteMapped bs fs = shift k (input.substituteMapped bs fs) := by
  induction k <;> simp_all [shift, Term.substituteMapped, Arguments.substituteMapped]

theorem power_congr {T : SetTheory} {left right a b : Code}
    (ha : Derives T [] (left ≐ₘ a)) (hb : Derives T [] (right ≐ₘ b)) :
    Derives T [] ((left ^ₘ right) ≐ₘ (a ^ₘ b)) := by
  have hl := Metatheory.Derives.term_context_congr_of_equality
    ((.bvar .here : SetTerm [SetSort.set] []) ^ₘ right.weakenBound SetSort.set) ha
  have hr := Metatheory.Derives.term_context_congr_of_equality
    (a.weakenBound SetSort.set ^ₘ (.bvar .here : SetTerm [SetSort.set] [])) hb
  simp only [Term.instantiateTop_app, Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound] at hl hr
  exact Metatheory.Derives.equality_trans hl hr

/-- 长度 n+2、元素不超过 n+8 的结构表的统一初等界。 -/
def tableBound {bound free : SetContext} (n : SetTerm bound free) : SetTerm bound free :=
  shift 8 n ^ₘ (numₘ(16) ^ₘ shift 2 n)

def tableBoundValue (n : Nat) : Nat := (n + 8) ^ (16 ^ (n + 2))

theorem tableBound_evaluate {T : SetTheory} (S : ArithmeticEvaluationSupport T) (n : Nat) :
    Derives T [] ((tableBound (numₘ(n)) : Code) ≐ₘ numₘ(tableBoundValue n)) := by
  unfold tableBound tableBoundValue
  rw [shift_numeral, shift_numeral]
  exact Metatheory.Derives.equality_trans
    (power_congr (Metatheory.Derives.equality_refl _)
      (Metatheory.Derives.equality_symm (standard_sequence_finite_numeral_exponentiation S 16 (n + 2))))
    (Metatheory.Derives.equality_symm (standard_sequence_finite_numeral_exponentiation S (n + 8) (16 ^ (n + 2))))

end YesMetaZFC.Automation.ObjectArithmeticTerm
