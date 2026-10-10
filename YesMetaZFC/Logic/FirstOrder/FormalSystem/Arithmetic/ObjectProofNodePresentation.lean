import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProofNodeAccept
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProofRow
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreePresentation

/-! # 从具体局部节点表示到完整证明树表示

规范模式通过蕴含连接原核检查，并接受任意实际证明编码。递归外壳同时检查
全部子证明；最后把数值结论传输到当前类型安全内核的 quotation。
-/
namespace YesMetaZFC.Automation.ObjectProofNode
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation QuineEncoding ObjectHorn ObjectCodeProjection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

private theorem node_mono (first second : Nat → Bool) (hLocal : ∀ code, first code = true → second code = true)
    (code : Nat) (h : ObjectProofTree.nodeChecked first code = true) : ObjectProofTree.nodeChecked second code = true := by
  obtain ⟨hCheck, shape, hShape, values, hCode, hChildren⟩ := (ObjectProofTree.node_iff first code).mp h
  apply (ObjectProofTree.node_iff second code).mpr
  refine ⟨hLocal code hCheck, shape, hShape, values, hCode, ?_⟩
  intro i hi
  exact node_mono first second hLocal (values i) (hChildren i hi)
termination_by code
decreasing_by
  rw [hCode]
  exact ObjectProofTree.payload_bound shape values i

/-- 自定义局部对象判定仅需可靠性及编码接受完备性，不要求在非规范外壳上采用同一算法。 -/
def ofNodeTest {Traw Thilbert : SetTheory} {axioms : AxiomPresentation Thilbert}
    {decoder : AxiomDecoder axioms} (codec : AxiomCodec decoder)
    (C : CertificateCore Traw) (S : FiniteSequenceGraphSupport Traw)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → Traw φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → Traw φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → Traw φ)
    (test : ObjectCheckedTrace.LocalTest Traw)
    (hSound : ∀ code, test.checked code = true → ProofTreeCode.localCheck decoder code = true)
    (hAccept : ∀ {free : SetContext} {formula : SetOpenFormula free}
      (proof : ProofCertificate axioms free formula), test.checked (ProofTreeCode.encode codec proof) = true) :
    Delta1ProofPresentation Traw Thilbert := by
  let rowTest := ObjectProofRow.localTest C S hSuccessor hPower hInfinity test
  have hRow : rowTest.checked = ObjectProofTree.rowCheck test.checked :=
    ObjectProofRow.localTest_checked C S hSuccessor hPower hInfinity test
  let checkProof (code : Nat) (formula : SetSentence) :=
    ObjectProofTree.checked test.checked code (treeValue (SyntaxEncode.formula formula))
  have hCheckSound {code : Nat} {formula : SetSentence} (h : checkProof code formula = true) : Derives Thilbert [] formula := by
    obtain ⟨shape, hShape, values, hCode, hFormula, hZero, hNode⟩ := (ObjectProofTree.root_iff _ _ _).mp h
    have hFree : field code 0 = 0 := by simpa only [hCode, ObjectProofTree.payload_free] using hZero
    have hValue : field code 1 = treeValue (SyntaxEncode.formula formula) := by
      simpa only [hCode, ObjectProofTree.payload_formula] using hFormula.symm
    apply (ProofTreeCode.nodeChecked_sound decoder code (node_mono _ _ hSound code hNode)).use
    simp [ProofTreeCode.readHeader, hFree, hValue, FirstOrder.Context.discharge]
  have hCheckComplete {formula : SetSentence} (h : Derives Thilbert [] formula) : ∃ code, checkProof code formula = true := by
    obtain ⟨certificate, hCertificate⟩ := ClosedProofCertificate.check_complete axioms h
    have hConclusion := (ClosedProofCertificate.check_eq_true_iff certificate formula).mp hCertificate
    refine ⟨ProofTreeCode.encode codec certificate.proof, ?_⟩
    rw [← hConclusion]
    exact ObjectProofTree.checked_of_node test.checked _ _
      (ProofTreeCode.encode_free codec certificate.proof) (ProofTreeCode.encode_formula codec certificate.proof)
      (ProofTreeCode.nodeChecked_encode_with codec test.checked hAccept certificate.proof)
  have hQuote (code : Nat) (formula : SetSentence) : Derives Traw []
      (IntrinsicQuotation.node 1 [numₘ(code), numₘ(treeValue (SyntaxEncode.formula formula))] ≐ₘ
        IntrinsicQuotation.node 1 [numₘ(code), IntrinsicQuotation.quote formula]) :=
    node_congr 1 (.cons (Metatheory.Derives.equality_refl _)
      (.cons (FirstOrder.Derives.eq_symm (quote_evaluate C formula)) .nil))
  exact {
    graph := ObjectProofTree.graph rowTest.condition rowTest.delta0
    checked := checkProof
    checked_sound := hCheckSound
    checked_complete := hCheckComplete
    condition_positive := fun {proofCode} {formula} h => by
      change Derives Traw [] (ObjectProofTree.template rowTest.condition (numₘ(proofCode)) (IntrinsicQuotation.quote formula))
      rw [ObjectProofTree.template_apply]
      exact ObjectCheckedTrace.transport ObjectProofTree.rules rowTest.condition (hQuote proofCode formula)
        (ObjectProofTree.positive C S hPower hInfinity rowTest test.checked hRow _ _ h)
    condition_negative := fun {proofCode} {formula} h => by
      change Derives Traw [] (¬ₘ ObjectProofTree.template rowTest.condition (numₘ(proofCode)) (IntrinsicQuotation.quote formula))
      rw [ObjectProofTree.template_apply]
      exact ObjectCheckedTrace.transport_negative ObjectProofTree.rules rowTest.condition (hQuote proofCode formula)
        (ObjectProofTree.negative C S.toArithmeticSupport rowTest test.checked hRow _ _ h) }

end YesMetaZFC.Automation.ObjectProofNode
