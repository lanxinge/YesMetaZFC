import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProofNode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreeReplay

/-! # 局部对象模式到实际 Hilbert 核检查的可靠连接 -/
namespace YesMetaZFC.Automation.ObjectProofNode
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation ObjectHorn ObjectCodeProjection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

abbrev ctx (free : Nat) : SetContext := List.replicate free .set

theorem formula_iff (free input : Nat) :
    check ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank (nodeValue 4 [0, free, input]) = true ↔
    ∃ formula : SetOpenFormula (ctx free), treeValue (SyntaxEncode.formula formula) = input := by
  simpa only [ObjectFormulaSyntax.checked, ctx, List.length_replicate, List.length_nil] using ObjectFormulaSyntax.checked_iff [] (ctx free) input

theorem arguments_iff (free sorts input : Nat) :
    check ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank (nodeValue 1 [0, free, sorts, input]) = true ↔
    ∃ args : Arguments signature [] (ctx free) (ctx sorts), listValue ((SyntaxEncode.argumentsList args).map treeValue) = input := by
  simpa only [ctx, List.length_replicate, List.length_nil] using ObjectFormulaSyntax.checked_arguments_iff [] (ctx free) (ctx sorts) input

theorem header_of_value (free : SetContext) (input : Nat) (formula : SetOpenFormula free)
    (hLength : field input 0 = free.length) (hFormula : treeValue (SyntaxEncode.formula formula) = field input 1) :
    ProofTreeCode.readHeader free input = some formula := by
  simp [ProofTreeCode.readHeader, hLength, ← hFormula]

@[simp] theorem header_node (free : SetContext) (tag : Nat) (formula : SetOpenFormula free) (extra : List Nat) :
    ProofTreeCode.readHeader free (nodeValue tag (free.length :: treeValue (SyntaxEncode.formula formula) :: extra)) = some formula := by
  simp [ProofTreeCode.readHeader]

theorem checked_sound {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) (axiomChecked : Nat → Bool)
    (hAxiom : ∀ packet output, axiomChecked (nodeValue 0 [packet, output]) = true →
      ∃ certificate, NatPacket.encode (codec.encode certificate) = packet ∧
        treeValue (SyntaxEncode.formula (axioms.sentence certificate)) = output)
    (root : Nat) (h : checked axiomChecked root = true) : ProofTreeCode.localCheck decoder root = true := by
  obtain ⟨shape, hShape, values, _, rfl, hQueries⟩ := (checked_iff axiomChecked root).mp h
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at hShape
  rcases hShape with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [logicalShape, theoryShape, mpShape, forallShape, strengtheningShape, substitutionShape] at values hQueries ⊢
  all_goals simp only [List.forall_mem_cons, List.not_mem_nil, forall_false, implies_true, and_true, queryChecked,
    node, formula, projection, transform, Expr.node_eval, Expr.eval, List.map_cons, List.map_nil,
    ObjectProjection.checked_field_iff] at hQueries ⊢
  · obtain ⟨formula, certificate, hCertificate, hFormula⟩ := (ObjectLogicalAxiom.checked_number_iff _ _ _).mp hQueries
    rw [← hCertificate, ← hFormula]
    simpa only [ProofTreeCode.encode, ctx, List.length_replicate] using ProofTreeCode.localCheck_encode codec (.logical_axiom certificate)
  · obtain ⟨_, hPacket⟩ := hQueries
    obtain ⟨certificate, hCertificate, hFormula⟩ := hAxiom _ _ hPacket
    rw [← hCertificate, ← hFormula]
    simpa only [ProofTreeCode.encode, ctx, List.length_replicate, SyntaxCodeRenaming.fromSentence]
      using ProofTreeCode.localCheck_encode codec (ProofCertificate.theory_axiom (free := ctx (values 0)) certificate)
  · obtain ⟨hConclusion, hPremise, hPLength, hPValue, hQLength, hQValue⟩ := hQueries
    obtain ⟨conclusion, hConclusion⟩ := (formula_iff _ _).mp hConclusion
    obtain ⟨premise, hPremise⟩ := (formula_iff _ _).mp hPremise
    have hP := header_of_value (ctx (values 0)) (values 2) premise (by simpa using hPLength) (hPremise.trans hPValue.symm)
    have hQ := header_of_value (ctx (values 0)) (values 3) (.imp premise conclusion) (by simpa using hQLength)
      (by simpa [SyntaxEncode.formula, hPremise, hConclusion] using hQValue.symm)
    rw [← hConclusion]
    have hRoot := header_node (ctx (values 0)) 2 conclusion [values 2, values 3]
    simp only [List.length_replicate] at hRoot
    unfold ProofTreeCode.localCheck ProofTreeCode.localRun
    rw [field_node, get_zero]
    dsimp only
    rw [hRoot]
    simp [hP, hQ]
  · obtain ⟨hPremise, hLength, hValue, hTransform⟩ := hQueries
    obtain ⟨premise, hPremise⟩ := (formula_iff _ _).mp hPremise
    have hP := header_of_value (ctx (values 0 + 1)) (values 2) premise (by simpa using hLength) (hPremise.trans hValue.symm)
    have hOutput := (ObjectSyntaxTransform.checked_abstractTop premise (values 1)).mp (by rwa [hPremise])
    rw [← hOutput]
    have hRoot := header_node (ctx (values 0)) 3 (premise.forallFreeTop .set) [values 2]
    simp only [List.length_replicate, Formula.forallFreeTop, SyntaxEncode.formula, treeValue_node, List.map_cons, List.map_nil] at hRoot
    unfold ProofTreeCode.localCheck ProofTreeCode.localRun
    rw [field_node, get_zero]
    dsimp only
    rw [hRoot]
    simp [← List.replicate_succ, hP, Formula.forallFreeTop]
  · obtain ⟨hConclusion, hLength, hValue, hTransform⟩ := hQueries
    obtain ⟨conclusion, hConclusion⟩ := (formula_iff _ _).mp hConclusion
    have hOutput := (ObjectSyntaxTransform.checked_weakenFree conclusion (values 3)).mp (by rwa [hConclusion])
    have hP := header_of_value (.set :: ctx (values 0)) (values 2) (conclusion.weakenFree SetSort.set)
      (by simpa using hLength) (hOutput.trans hValue.symm)
    rw [← hConclusion]
    have hRoot := header_node (ctx (values 0)) 4 conclusion [values 2]
    simp only [List.length_replicate] at hRoot
    unfold ProofTreeCode.localCheck ProofTreeCode.localRun
    rw [field_node, get_zero]
    dsimp only
    rw [hRoot]
    simp [hP]
  · obtain ⟨hPremise, hArgs, hLength, hValue, hTransform⟩ := hQueries
    obtain ⟨premise, hPremise⟩ := (formula_iff _ _).mp hPremise
    obtain ⟨args, hArgs⟩ := (arguments_iff _ _ _).mp hArgs
    have hP := header_of_value (ctx (values 2)) (values 4) premise (by simpa using hLength) (hPremise.trans hValue.symm)
    have hOutput := (ObjectSyntaxTransform.checked_substituteFree premise (SyntaxDecode.substitution args) (values 1)).mp
      (by simpa only [ObjectSyntaxTransform.checked, SyntaxCodeRenaming.substitutionArguments_substitution, hArgs, hPremise] using hTransform)
    rw [← hOutput, ← hArgs]
    have hRoot := header_node (ctx (values 0)) 5 (premise.substituteFree (SyntaxDecode.substitution args))
      [values 2, listValue ((SyntaxEncode.argumentsList args).map treeValue), values 4]
    simp only [List.length_replicate] at hRoot
    unfold ProofTreeCode.localCheck ProofTreeCode.localRun
    rw [field_node, get_zero]
    dsimp only
    rw [hRoot]
    rw [field_node, get_succ, get_succ, get_zero]
    simp [hP]

end YesMetaZFC.Automation.ObjectProofNode
