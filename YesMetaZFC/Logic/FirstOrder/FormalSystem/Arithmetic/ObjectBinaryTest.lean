import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLocalDecision
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeProjection

/-! # 二元数值表示的一元行封装

外壳检查覆盖任意自然数；参数仅由根行给出的有限界量化。
-/
namespace YesMetaZFC.Automation.ObjectBinaryTest
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding IntrinsicQuotation ObjectHorn ObjectCodeProjection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

structure Test (T : SetTheory) where
  condition : FormulaTemplate.Binary
  delta0 : Formula.IsDelta0 set_levy_bound condition.body
  checked : Nat → Nat → Bool
  positive : ∀ left right, checked left right = true → Derives T [] (condition (numₘ(left)) (numₘ(right) : Code))
  negative : ∀ left right, checked left right = false → Derives T [] (¬ₘ condition (numₘ(left)) (numₘ(right) : Code))

def checked {T : SetTheory} (test : Test T) (root : Nat) : Bool :=
  decide (root = nodeValue 0 [field root 0, field root 1]) && test.checked (field root 0) (field root 1)

@[simp] theorem checked_pair {T : SetTheory} (test : Test T) (left right : Nat) :
    checked test (nodeValue 0 [left, right]) = test.checked left right := by simp [checked]

def matrix {T : SetTheory} (test : Test T) {bound free : SetContext}
    (root left right : SetTerm bound free) : SetFormula bound free :=
  (root ≐ₘ IntrinsicQuotation.node 0 [left, right]) ∧ₘ test.condition left right

@[simp] theorem matrix_substituteMapped {T : SetTheory} (test : Test T) {sb sf tb tf : SetContext}
    (root left right : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (matrix test root left right).substituteMapped bs fs = matrix test
      (root.substituteMapped bs fs) (left.substituteMapped bs fs) (right.substituteMapped bs fs) := by
  simp [matrix, Formula.substituteMapped]

def template {T : SetTheory} (test : Test T) : FormulaTemplate.Unary where
  body := quantify 2 (Sₘ(.fvar .here))
    (matrix test (.fvar .here) (.bvar (project_bound_variable (0 : Fin 2))) (.bvar (project_bound_variable (1 : Fin 2))))

private theorem positive {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (test : Test T) (root : Nat) (h : checked test root = true) :
    Derives T [] (template test (numₘ(root) : Code)) := by
  obtain ⟨hShape, hTest⟩ := Bool.and_eq_true_iff.mp h
  have hShape := of_decide_eq_true hShape
  let values : Fin 2 → Nat := fun i => field root i.val
  have hMatrix : Derives T [] (matrix test (numₘ(root)) (numₘ(values 0)) (numₘ(values 1) : Code)) := by
    apply FirstOrder.Derives.conj_intro
    · rw [hShape]
      simpa [values] using FirstOrder.Derives.eq_symm (node_evaluate C 0 [field root 0, field root 1])
    · exact test.positive _ _ hTest
  have hBound : ∀ i, values i ≤ root := by
    intro i
    cases i using Fin.cases with
    | zero => exact Nat.le_of_lt (hShape ▸ node_field_lt 0 [field root 0, field root 1] _ List.mem_cons_self)
    | succ i =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      exact Nat.le_of_lt (hShape ▸ node_field_lt 0 [field root 0, field root 1] _ (List.mem_cons_of_mem _ List.mem_cons_self))
  unfold template FormulaTemplate.apply_one FormulaTemplate.instantiate
  apply quantify_positive (values := values)
  · intro i
    simpa [Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons, finite_numeral_term]
      using numeral_mem_of_lt hSuccessor (Nat.lt_succ_of_le (hBound i))
  · simpa [Term.substituteMapped, VariableSubstitution.cons, numeralSubstitution, project_bound_index, project_bound_variable, Variable.index, values] using hMatrix

private theorem negative {T : SetTheory} (C : CertificateCore T) (test : Test T) (root : Nat)
    (h : checked test root = false) : Derives T [] (¬ₘ template test (numₘ(root) : Code)) := by
  have hMatrix : ∀ values : Fin 2 → Nat, Derives T []
      (¬ₘ matrix test (numₘ(root)) (numₘ(values 0)) (numₘ(values 1) : Code)) := by
    intro values
    apply FirstOrder.Derives.neg_intro
    let body := matrix test (numₘ(root)) (numₘ(values 0)) (numₘ(values 1) : Code)
    have hBody : Derives T [body] body := FirstOrder.Derives.assumption List.mem_cons_self
    by_cases hShape : root = nodeValue 0 [values 0, values 1]
    · have hTest : test.checked (values 0) (values 1) = false := by simpa [hShape] using h
      exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_right hBody)
        (FirstOrder.Derives.context_weaken_cons (test.negative _ _ hTest))
    · exact FirstOrder.Derives.neg_elim
        (Metatheory.Derives.equality_trans (FirstOrder.Derives.conj_elim_left hBody)
          (FirstOrder.Derives.context_weaken_cons (node_evaluate C 0 [values 0, values 1])))
        (FirstOrder.Derives.context_weaken_cons (C.numeral_ne hShape))
  unfold template FormulaTemplate.apply_one FormulaTemplate.instantiate
  apply quantify_negative C.toFiniteCore (limit := root + 1)
  · rfl
  · intro values _
    simpa [Term.substituteMapped, VariableSubstitution.cons, numeralSubstitution, project_bound_index, project_bound_variable, Variable.index] using hMatrix values

def localTest {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ) (test : Test T) : ObjectCheckedTrace.LocalTest T where
  condition := template test
  delta0 := quantify_delta0 _ _ _ (.conj (.equal _ _) (test.condition.instantiate_delta0 test.delta0 _))
  checked := checked test
  positive := positive C hSuccessor test
  negative := negative C test

end YesMetaZFC.Automation.ObjectBinaryTest
