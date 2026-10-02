import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectParameterCertificate

/-! # 实际项与参数解码器的普通正负推导 -/
namespace YesMetaZFC.Automation.ObjectTermSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

@[simp] theorem term_substituteMapped {sb sf tb tf : SetContext} (b f input : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (termCondition b f input).substituteMapped bs fs =
      termCondition (b.substituteMapped bs fs) (f.substituteMapped bs fs) (input.substituteMapped bs fs) := by
  simp [termCondition]

@[simp] theorem parameter_substituteMapped {sb sf tb tf : SetContext} (count input : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (parameterCondition count input).substituteMapped bs fs =
      parameterCondition (count.substituteMapped bs fs) (input.substituteMapped bs fs) := by
  simp [parameterCondition]

def termTemplate : FormulaTemplate.Ternary where
  body := termCondition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

def parameterTemplate : FormulaTemplate.Binary where
  body := parameterCondition (.fvar .here) (.fvar (.there .here))

@[simp] theorem term_template_apply {bound free : SetContext} (b f input : SetTerm bound free) :
    termTemplate b f input = termCondition b f input := by
  simp [termTemplate, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

@[simp] theorem parameter_template_apply {bound free : SetContext} (count input : SetTerm bound free) :
    parameterTemplate count input = parameterCondition count input := by
  simp [parameterTemplate, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem term_template_delta0 : Formula.IsDelta0 set_levy_bound termTemplate.body := term_delta0 _ _ _
theorem parameter_template_delta0 : Formula.IsDelta0 set_levy_bound parameterTemplate.body := parameter_delta0 _ _

theorem term_positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ) (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (bound free : SetContext) (input : Tree) (result : SetTerm bound free)
    (h : SyntaxDecode.term bound free input = some result) :
    Derives T [] (termCondition (numₘ(bound.length)) (numₘ(free.length)) (numₘ(treeValue input) : Code)) := by
  rw [← SyntaxDecode.term_encode_of_decode bound free input result h]
  obtain ⟨rows, hRoot, hRows⟩ := term_accept result
  exact ObjectHorn.transport rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 0 [bound.length, free.length, treeValue (SyntaxEncode.term result)]))
    (ObjectHorn.positive C S hPower hInfinity rules _ rows hRoot hRows)

theorem term_negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (bound free : SetContext) (input : Tree) (h : SyntaxDecode.term bound free input = none) :
    Derives T [] (¬ₘ termCondition (numₘ(bound.length)) (numₘ(free.length)) (numₘ(treeValue input) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 0 [bound.length, free.length, treeValue input]))
    (ObjectHorn.negative C A (term_reject bound free input h))

theorem term_positive_at_tree {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ) (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (bound free : SetContext) (input : Tree) (result : SetTerm bound free)
    (h : SyntaxDecode.term bound free input = some result) :
    Derives T [] (termCondition (numₘ(bound.length)) (numₘ(free.length)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport rules (node_congr 0 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (Metatheory.Derives.equality_refl _)
      (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input)) .nil))))
    (term_positive C S hPower hInfinity bound free input result h)

theorem term_negative_at_tree {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (bound free : SetContext) (input : Tree) (h : SyntaxDecode.term bound free input = none) :
    Derives T [] (¬ₘ termCondition (numₘ(bound.length)) (numₘ(free.length)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport_negative rules (node_congr 0 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (Metatheory.Derives.equality_refl _)
      (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input)) .nil)))) (term_negative C A bound free input h)

theorem parameter_positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ) (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (count : Nat) (input : Tree) (parameters : SyntaxParameters.Parameters count)
    (h : SyntaxParameters.decode count input = some parameters) :
    Derives T [] (parameterCondition (numₘ(count)) (numₘ(treeValue input) : Code)) := by
  rw [← SyntaxParameters.encode_of_decode h]
  obtain ⟨rows, hRoot, hRows⟩ := envelope_accept parameters
  exact ObjectHorn.transport rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 3 [count, treeValue (SyntaxParameters.encode parameters)]))
    (ObjectHorn.positive C S hPower hInfinity rules _ rows hRoot hRows)

theorem parameter_negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (count : Nat) (input : Tree) (h : SyntaxParameters.decode count input = none) :
    Derives T [] (¬ₘ parameterCondition (numₘ(count)) (numₘ(treeValue input) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm (node_evaluate C 3 [count, treeValue input]))
    (ObjectHorn.negative C A (envelope_reject count input h))

theorem parameter_positive_at_tree {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ) (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (count : Nat) (input : Tree) (parameters : SyntaxParameters.Parameters count)
    (h : SyntaxParameters.decode count input = some parameters) :
    Derives T [] (parameterCondition (numₘ(count)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport rules (node_congr 3 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input)) .nil)))
    (parameter_positive C S hPower hInfinity count input parameters h)

theorem parameter_negative_at_tree {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (count : Nat) (input : Tree) (h : SyntaxParameters.decode count input = none) :
    Derives T [] (¬ₘ parameterCondition (numₘ(count)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport_negative rules (node_congr 3 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input)) .nil))) (parameter_negative C A count input h)

end YesMetaZFC.Automation.ObjectTermSyntax
