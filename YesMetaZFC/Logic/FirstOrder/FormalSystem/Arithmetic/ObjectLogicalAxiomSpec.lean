import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLogicalAxiomSound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLogicalAxiomAccept
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.LogicalAxiomCanonical

/-! # 逻辑公理模式与实际解码器的全自然数等价 -/
namespace YesMetaZFC.Automation.ObjectLogicalAxiom
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation ObjectHorn
set_option autoImplicit false

private theorem extract {root : Nat} (h : Meaning root) (free packet output : Nat)
    (hRoot : root = nodeValue 0 [free, packet, output]) :
    ∃ formula : SetOpenFormula (ctx free), ∃ certificate : HilbertBaseAxiom signature formula,
      treeValue (LogicalAxiomEncode.encode certificate) = packet ∧ treeValue (SyntaxEncode.formula formula) = output := by
  cases h with
  | logical source formula certificate =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRoot
    simp only [List.cons.injEq, and_true] at h
    obtain rfl := h.2.1
    exact ⟨formula, certificate, h.2.2⟩

theorem checked_number_iff (free packet output : Nat) :
    checked (nodeValue 0 [free, packet, output]) = true ↔
      ∃ formula : SetOpenFormula (ctx free), ∃ certificate : HilbertBaseAxiom signature formula,
        treeValue (LogicalAxiomEncode.encode certificate) = packet ∧ treeValue (SyntaxEncode.formula formula) = output := by
  constructor
  · intro h
    exact extract (checked_sound _ h) free packet output rfl
  · rintro ⟨formula, certificate, rfl, rfl⟩
    simpa only [List.length_replicate] using checked_encode certificate

/-- 使用与现有局部检查相同的实际 quotation 解码及 Hilbert 证书解码。 -/
theorem checked_decode_iff (free packet output : Nat) :
    checked (nodeValue 0 [free, packet, output]) = true ↔
      ∃ result : LogicalAxiomDecode.Result (ctx free),
        (decodeTree packet).bind (LogicalAxiomDecode.decode (ctx free)) = some result ∧
        treeValue (SyntaxEncode.formula result.1) = output := by
  rw [checked_number_iff]
  constructor
  · rintro ⟨formula, certificate, rfl, rfl⟩
    exact ⟨⟨formula, certificate⟩, by simp, rfl⟩
  · rintro ⟨result, hDecode, hOutput⟩
    obtain ⟨tree, hTree, hCertificate⟩ := Option.bind_eq_some_iff.mp hDecode
    refine ⟨result.1, result.2, ?_, hOutput⟩
    rw [LogicalAxiomEncode.encode_of_decode (ctx free) tree result hCertificate]
    exact treeValue_of_decode hTree

end YesMetaZFC.Automation.ObjectLogicalAxiom
