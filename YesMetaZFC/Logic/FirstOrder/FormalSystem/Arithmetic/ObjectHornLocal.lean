import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCheckedTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteJoin

/-! # 有限递归图作为局部查询

把已经证明下降的图直接封装为一元局部测试，供有限模式连接复用。
-/
namespace YesMetaZFC.Automation.ObjectHorn
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def unary (rules : List Rule) : FormulaTemplate.Unary where
  body := condition rules (.fvar .here)

@[simp] theorem unary_apply (rules : List Rule) {bound free : SetContext} (root : SetTerm bound free) :
    unary rules root = condition rules root := by
  simp [unary, FormulaTemplate.apply_one, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

def localTest {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (rules : List Rule) (rank : Nat → Nat) (descending : Descending rules rank) :
    ObjectCheckedTrace.LocalTest T where
  condition := unary rules
  delta0 := condition_delta0 _ _
  checked := check rules rank
  positive root h := by
    rw [unary_apply]
    exact check_positive C S hPower hInfinity rules rank descending root h
  negative root h := by
    rw [unary_apply]
    exact check_negative C S.toArithmeticSupport rules rank descending root h

end YesMetaZFC.Automation.ObjectHorn
