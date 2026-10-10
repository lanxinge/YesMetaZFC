import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProofTreeSpec

/-! # 完整带标注证明树检查的可靠性与完备性

元层检查器已连接全部六条实际核规则。它的对象正负实例仍须构造
与 localCheck 对应的 LocalTest；此处不假定该对象表示已经存在。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
open Nonlogical.BasicSetTheory IntrinsicQuotation
open _root_.YesMetaZFC.Automation
open ObjectHorn ObjectCodeProjection ObjectProofTree
set_option autoImplicit false

theorem nodeChecked_sound {T : SetTheory} {axioms : AxiomPresentation T} (decoder : AxiomDecoder axioms)
    (code : Nat) (h : ObjectProofTree.nodeChecked (localCheck decoder) code = true) : HeaderProvable T code := by
  obtain ⟨hLocal, shape, hShape, values, hCode, hChildren⟩ := (node_iff (localCheck decoder) code).mp h
  apply localCheck_sound decoder code hLocal
  intro child hChild
  rw [hCode, payload_children shape hShape] at hChild
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hChild
  exact nodeChecked_sound decoder (values i) (hChildren i hi)
termination_by code
decreasing_by
  rw [hCode]
  exact payload_bound shape values i

def checked {T : SetTheory} {axioms : AxiomPresentation T} (decoder : AxiomDecoder axioms)
    (code : Nat) (formula : SetSentence) : Bool :=
  ObjectProofTree.checked (localCheck decoder) code (treeValue (SyntaxEncode.formula formula))

theorem checked_sound {T : SetTheory} {axioms : AxiomPresentation T} (decoder : AxiomDecoder axioms)
    {code : Nat} {formula : SetSentence} (h : checked decoder code formula = true) : Derives T [] formula := by
  obtain ⟨shape, hShape, values, hCode, hFormula, hZero, hNode⟩ := (root_iff _ _ _).mp h
  have hFree : field code 0 = 0 := by simpa only [hCode, payload_free] using hZero
  have hValue : field code 1 = treeValue (SyntaxEncode.formula formula) := by
    simpa only [hCode, payload_formula] using hFormula.symm
  apply (nodeChecked_sound decoder code hNode).use
  simp [readHeader, hFree, hValue, Context.discharge]

private theorem node_intro_fields {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) (test : Nat → Bool)
    (hAccept : ∀ {free : SetContext} {formula : SetOpenFormula free} (proof : ProofCertificate axioms free formula),
      test (encode codec proof) = true) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) (shape : Shape) (hShape : shape ∈ shapes)
    (hCode : encode codec proof = payloadValue shape (fun i => field (encode codec proof) i.val))
    (hChildren : ∀ i, i ∈ shape.children →
      ObjectProofTree.nodeChecked test (field (encode codec proof) i.val) = true) :
    ObjectProofTree.nodeChecked test (encode codec proof) = true := by
  apply (node_iff _ _).mpr
  exact ⟨hAccept proof, shape, hShape, _, hCode, hChildren⟩

theorem nodeChecked_encode_with {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) (test : Nat → Bool)
    (hAccept : ∀ {free : SetContext} {formula : SetOpenFormula free} (proof : ProofCertificate axioms free formula),
      test (encode codec proof) = true) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) :
    ObjectProofTree.nodeChecked test (encode codec proof) = true := by
  induction proof with
  | logical_axiom certificate =>
    apply node_intro_fields codec test hAccept (.logical_axiom certificate) logicalShape (by simp [shapes])
    · simp [encode, payloadValue, logicalShape, List.ofFn_succ]
    · intro i hi; cases hi
  | theory_axiom certificate =>
    apply node_intro_fields codec test hAccept (.theory_axiom certificate) theoryShape (by simp [shapes])
    · simp [encode, payloadValue, theoryShape, List.ofFn_succ]
    · intro i hi; cases hi
  | modus_ponens premise implication ihP ihQ =>
    apply node_intro_fields codec test hAccept (.modus_ponens premise implication) mpShape (by simp [shapes])
    · simp [encode, payloadValue, mpShape, List.ofFn_succ]
    · intro i hi
      have hIndex : i.val = 2 ∨ i.val = 3 := by
        change i ∈ ([2, 3] : List (Fin 4)) at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> decide
      rcases hIndex with hIndex | hIndex
      · rw [hIndex]
        simp only [encode, field_node, get_zero, get_succ]
        exact ihP
      · rw [hIndex]
        simp only [encode, field_node, get_zero, get_succ]
        exact ihQ
  | forall_generalization premise ih =>
    apply node_intro_fields codec test hAccept (.forall_generalization premise) forallShape (by simp [shapes])
    · simp [encode, payloadValue, forallShape, List.ofFn_succ]
    · intro i hi
      have hIndex : i.val = 2 := by
        change i ∈ ([2] : List (Fin 3)) at hi
        have h := List.mem_singleton.mp hi
        subst i
        rfl
      rw [hIndex]
      simp only [encode, field_node, get_zero, get_succ]
      exact ih
  | free_strengthening premise ih =>
    apply node_intro_fields codec test hAccept (.free_strengthening premise) strengtheningShape (by simp [shapes])
    · simp [encode, payloadValue, strengtheningShape, List.ofFn_succ]
    · intro i hi
      have hIndex : i.val = 2 := by
        change i ∈ ([2] : List (Fin 3)) at hi
        have h := List.mem_singleton.mp hi
        subst i
        rfl
      rw [hIndex]
      simp only [encode, field_node, get_zero, get_succ]
      exact ih
  | free_substitution subst premise ih =>
    apply node_intro_fields codec test hAccept (.free_substitution subst premise) substitutionShape (by simp [shapes])
    · simp [encode, payloadValue, substitutionShape, List.ofFn_succ]
    · intro i hi
      have hIndex : i.val = 4 := by
        change i ∈ ([4] : List (Fin 5)) at hi
        have h := List.mem_singleton.mp hi
        subst i
        rfl
      rw [hIndex]
      simp only [encode, field_node, get_zero, get_succ]
      exact ih

/-- 原检查器是局部接受完备装配的直接实例。 -/
theorem nodeChecked_encode {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) :
    ObjectProofTree.nodeChecked (localCheck decoder) (encode codec proof) = true :=
  nodeChecked_encode_with codec (localCheck decoder) (localCheck_encode codec) proof

theorem checked_encode {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) (proof : ClosedProofCertificate axioms) :
    checked decoder (encode codec proof.proof) proof.conclusion = true := by
  exact ObjectProofTree.checked_of_node (localCheck decoder) _ _
    (encode_free codec proof.proof) (encode_formula codec proof.proof) (nodeChecked_encode codec proof.proof)

theorem checked_complete {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) {formula : SetSentence} (h : Derives T [] formula) :
    ∃ code, checked decoder code formula = true := by
  obtain ⟨certificate, hCertificate⟩ := ClosedProofCertificate.check_complete axioms h
  have hConclusion := (ClosedProofCertificate.check_eq_true_iff certificate formula).mp hCertificate
  exact ⟨encode codec certificate.proof, hConclusion ▸ checked_encode codec certificate⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
