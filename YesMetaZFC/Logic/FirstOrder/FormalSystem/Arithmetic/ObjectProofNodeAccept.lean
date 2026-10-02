import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProofNodeSound

/-! # 任意实际 Hilbert 节点的局部对象接受完备性 -/
namespace YesMetaZFC.Automation.ObjectProofNode
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation ObjectHorn ObjectCodeProjection
set_option autoImplicit false

private theorem accept (axiomChecked : Nat → Bool) (shape : Shape) (hShape : shape ∈ shapes)
    (values : Fin shape.arity → Nat) (hBound : ∀ i, values i ≤ shape.head.eval values)
    (hQueries : ∀ query, query ∈ shape.queries → queryChecked axiomChecked query.1 (query.2.eval values) = true) :
    checked axiomChecked (shape.head.eval values) = true :=
  (checked_iff _ _).mpr ⟨shape, hShape, values, hBound, rfl, hQueries⟩

private theorem all_bound (shape : Shape) (hAll : ∀ i, i ∈ shape.head.variables) (values : Fin shape.arity → Nat) :
    ∀ i, values i ≤ shape.head.eval values := fun i => shape.head.variable_le values (hAll i)

private theorem header_bound (shape : Shape) (missing child : Fin shape.arity)
    (hChild : child ∈ shape.head.variables) (hRest : ∀ i, i ≠ missing → i ∈ shape.head.variables)
    (values : Fin shape.arity → Nat) (hMissing : values missing = field (values child) 1) :
    ∀ i, values i ≤ shape.head.eval values := by
  intro i
  by_cases h : i = missing
  · rw [h, hMissing]
    exact Nat.le_trans (ObjectProjection.field_le _ _) (shape.head.variable_le values hChild)
  · exact shape.head.variable_le values (hRest i h)

private theorem formula_accept {free : SetContext} (input : SetOpenFormula free) :
    check ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank
      (nodeValue 4 [0, free.length, treeValue (SyntaxEncode.formula input)]) = true :=
  ObjectFormulaSyntax.checked_encode input

private theorem arguments_accept {free sorts : SetContext} (input : Arguments signature [] free sorts) :
    check ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank
      (nodeValue 1 [0, free.length, sorts.length, listValue ((SyntaxEncode.argumentsList input).map treeValue)]) = true :=
  (ObjectFormulaSyntax.checked_arguments_iff [] free sorts _).mpr ⟨input, rfl⟩

attribute [local simp] Fin.val_ofNat node Expr.eval queryChecked ObjectProjection.checked_field_iff
  formula_accept arguments_accept SyntaxEncode.formula ProofTreeCode.encode_formula ProofTreeCode.encode_free
  Formula.forallFreeTop

theorem checked_encode {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) (axiomChecked : Nat → Bool)
    (hAxiom : ∀ certificate, axiomChecked (nodeValue 0 [NatPacket.encode (codec.encode certificate),
      treeValue (SyntaxEncode.formula (axioms.sentence certificate))]) = true)
    {free : SetContext} {formula : SetOpenFormula free} (proof : ProofCertificate axioms free formula) :
    checked axiomChecked (ProofTreeCode.encode codec proof) = true := by
  cases proof with
  | logical_axiom certificate =>
    have h := accept axiomChecked logicalShape (by simp [shapes])
      (fun i : Fin 3 => [free.length, treeValue (SyntaxEncode.formula formula), treeValue (LogicalAxiomEncode.encode certificate)][i])
      (all_bound logicalShape (by decide) _) (by
        intro query hQuery
        obtain rfl := List.mem_singleton.mp hQuery
        exact ObjectLogicalAxiom.checked_encode certificate)
    simpa [logicalShape, ProofTreeCode.encode] using h
  | theory_axiom certificate =>
    have h := accept axiomChecked theoryShape (by simp [shapes])
      (fun i : Fin 3 => [free.length, treeValue (SyntaxEncode.formula (axioms.sentence certificate)), NatPacket.encode (codec.encode certificate)][i])
      (all_bound theoryShape (by decide) _) (by
        intro query hQuery
        dsimp only [theoryShape] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl
        · simpa [SyntaxCodeRenaming.fromSentence] using formula_accept (Formula.fromSentence (free := free) (axioms.sentence certificate))
        · exact hAxiom certificate)
    simpa [theoryShape, ProofTreeCode.encode] using h
  | @modus_ponens _ premiseFormula _ premise implication =>
    have h := accept axiomChecked mpShape (by simp [shapes])
      (fun i : Fin 5 => [free.length, treeValue (SyntaxEncode.formula formula), ProofTreeCode.encode codec premise,
        ProofTreeCode.encode codec implication, treeValue (SyntaxEncode.formula premiseFormula)][i])
      (header_bound mpShape 4 2 (by decide) (by decide) _ (by exact (ProofTreeCode.encode_formula codec premise).symm)) (by
        intro query hQuery
        dsimp only [mpShape] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl | rfl | rfl | rfl
        · exact formula_accept formula
        · exact formula_accept premiseFormula
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 0 free.length).mpr (ProofTreeCode.encode_free codec premise)
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 1 _).mpr (ProofTreeCode.encode_formula codec premise)
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec implication) 0 free.length).mpr (ProofTreeCode.encode_free codec implication)
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec implication) 1 _).mpr (ProofTreeCode.encode_formula codec implication))
    exact h
  | @forall_generalization _ sort premiseFormula premise =>
    cases sort
    have h := accept axiomChecked forallShape (by simp [shapes])
      (fun i : Fin 4 => [free.length, treeValue (SyntaxEncode.formula premiseFormula.abstractFreeTop),
        ProofTreeCode.encode codec premise, treeValue (SyntaxEncode.formula premiseFormula)][i])
      (header_bound forallShape 3 2 (by decide) (by decide) _ (by exact (ProofTreeCode.encode_formula codec premise).symm)) (by
        intro query hQuery
        dsimp only [forallShape] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl | rfl
        · exact formula_accept premiseFormula
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 0 _).mpr (ProofTreeCode.encode_free codec premise)
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 1 _).mpr (ProofTreeCode.encode_formula codec premise)
        · exact (ObjectSyntaxTransform.checked_abstractTop premiseFormula _).mpr rfl)
    exact h
  | @free_strengthening _ sort _ premise =>
    cases sort
    have h := accept axiomChecked strengtheningShape (by simp [shapes])
      (fun i : Fin 4 => [free.length, treeValue (SyntaxEncode.formula formula), ProofTreeCode.encode codec premise,
        treeValue (SyntaxEncode.formula (formula.weakenFree SetSort.set))][i])
      (header_bound strengtheningShape 3 2 (by decide) (by decide) _ (by exact (ProofTreeCode.encode_formula codec premise).symm)) (by
        intro query hQuery
        dsimp only [strengtheningShape] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl | rfl
        · exact formula_accept formula
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 0 _).mpr (ProofTreeCode.encode_free codec premise)
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 1 _).mpr (ProofTreeCode.encode_formula codec premise)
        · exact (ObjectSyntaxTransform.checked_weakenFree formula _).mpr rfl)
    exact h
  | @free_substitution source _ subst premiseFormula premise =>
    have h := accept axiomChecked substitutionShape (by simp [shapes])
      (fun i : Fin 6 => [free.length, treeValue (SyntaxEncode.formula (premiseFormula.substituteFree subst)), source.length,
        listValue ((SyntaxEncode.argumentsList (SyntaxEncode.substitutionArguments source subst)).map treeValue),
        ProofTreeCode.encode codec premise, treeValue (SyntaxEncode.formula premiseFormula)][i])
      (header_bound substitutionShape 5 4 (by decide) (by decide) _ (by exact (ProofTreeCode.encode_formula codec premise).symm)) (by
        intro query hQuery
        dsimp only [substitutionShape] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl | rfl | rfl
        · exact formula_accept premiseFormula
        · exact arguments_accept _
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 0 _).mpr (ProofTreeCode.encode_free codec premise)
        · exact (ObjectProjection.checked_field_iff (ProofTreeCode.encode codec premise) 1 _).mpr (ProofTreeCode.encode_formula codec premise)
        · exact (ObjectSyntaxTransform.checked_substituteFree premiseFormula subst _).mpr rfl)
    exact h

end YesMetaZFC.Automation.ObjectProofNode
