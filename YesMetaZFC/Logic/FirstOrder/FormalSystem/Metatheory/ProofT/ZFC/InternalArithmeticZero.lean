import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalArithmeticRules

/-! # 加乘幂求值的零参数证明 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def seedCode (𝒩 : Structure.{0,0,0,x} signature) (operation : ArithmeticOperation) (first : 𝒩.Carrier .set) :=
  term 𝒩 (fun _ => first) (seedTerm operation)

theorem zero_term_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []] = numeral 𝒩 ObjectNumeralSyntax.zeroCode :=
  tree_numeral h𝒩 (SyntaxEncode.term (numₘ(0) : SetOpenTerm []))

theorem seed_numeral (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : ArithmeticOperation)
    {left first : 𝒩.Carrier .set} (hf : mem 𝒩 first (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) :
    mem 𝒩 (seedCode 𝒩 operation first) (w 𝒩) ∧
      PureSourceNumeralSyntax.Graph 𝒩 (PureSourceArithmetic.seed 𝒩 operation left) (seedCode 𝒩 operation first) := by
  cases operation with
  | addition => exact ⟨hf, hFirst⟩
  | multiplication =>
    change mem 𝒩 (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]) (w 𝒩) ∧
      PureSourceNumeralSyntax.Graph 𝒩 (z 𝒩) (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []])
    rw [zero_term_code h𝒩]
    exact ⟨numeral_natural h𝒩 _, PureSourceNumeralSyntax.zero h𝒩⟩
  | exponentiation =>
    have hCode : seedCode 𝒩 .exponentiation first =
        PureSourceNumeralSyntax.next 𝒩 (numeral 𝒩 ObjectNumeralSyntax.zeroCode) := by
      change node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []),
        (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []])] = _
      rw [zero_term_code h𝒩, successor_symbol h𝒩]; rfl
    rw [hCode]
    exact ⟨PureSourceNumeralSyntax.next_natural h𝒩 (numeral_natural h𝒩 _),
      PureSourceNumeralSyntax.successor h𝒩 (omega_closed h𝒩).1 (numeral_natural h𝒩 _) (PureSourceNumeralSyntax.zero h𝒩)⟩

theorem evaluation_zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : ArithmeticOperation)
    {left first second result : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first)
    (hs : mem 𝒩 second (w 𝒩)) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 (z 𝒩) second)
    (ho : mem 𝒩 result (w 𝒩)) (hResult : PureSourceNumeralSyntax.Graph 𝒩 (PureSourceArithmetic.arithmetic 𝒩 operation left (z 𝒩)) result) :
    ProvableCode 𝒩 (evaluationCode 𝒩 (operationTerm operation) first second result) := by
  have h := of_natural_derives h𝒩 _ (zero_evaluation_derives operation) hl hf hFirst
  have hShape : formula 𝒩 (fun _ => first) (zeroEvaluationBody operation) =
      evaluationCode 𝒩 (operationTerm operation) first
        (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]) (seedCode 𝒩 operation first) := by
    cases operation <;> rfl
  rw [hShape, zero_term_code h𝒩] at h
  obtain ⟨hn, hg⟩ := seed_numeral h𝒩 operation hf hFirst
  have hSeedNat := (PureSourceArithmetic.specification h𝒩 operation hl (omega_closed h𝒩).1).1
  rw [PureSourceArithmetic.at_zero h𝒩 operation hl] at hSeedNat hResult
  have hOutput := PureSourceNumeralSyntax.functional h𝒩 hSeedNat hn ho hg hResult
  rw [(PureSourceNumeralSyntax.zero_iff h𝒩 hs).mp hSecond, ← hOutput]
  exact h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
