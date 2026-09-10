import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalProofTraceReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalVerificationTrace

/-! # 原验证矩阵及完整证明矩阵的内部数码反射 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem verificationRoot_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (φ : SetSentence)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named) :
    TermEvaluates (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) (fun _ => named) (verificationRoot φ) := by
  let env : Env 𝒩 [] [.set] := templateEnv (.cons input .nil)
  have hv : NumeralValues 𝒩 (fun _ => named) := fun _ => ⟨hn, input, hi, hg⟩
  have he : (Env.empty : Env 𝒩 [] []).pushFree input = env := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry
      cases entry with
      | here => rfl
      | there entry => cases entry
  have hc : ObjectCodeInstantiation.prepend named (fun _ => named) = (fun _ => named) := by
    funext i; cases i <;> rfl
  have hQuote := InternalPositiveFormula.weaken_evaluation
    (tree_term_evaluation h𝒩 (fun _ => named) hv (SyntaxEncode.formula φ)) input named
  rw [he, hc] at hQuote
  apply node_term_evaluation h𝒩 env _ hv 1
  intro field hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact variable_evaluation h𝒩 env _ hv .here hi hg
  · exact hQuote

/-- 原检查器正文的反射，不再要求调用者提供轨迹骨架或连边证明。 -/
theorem verification_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (φ : SetSentence)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (ht : (ReducedProvability.verificationMatrix φ).satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set])) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) (ReducedProvability.verificationMatrix φ)) := by
  rw [verificationMatrix_trace] at ht ⊢
  exact proof_trace_values h𝒩 _ (fun _ => named) (fun _ => ⟨hn, input, hi, hg⟩)
    (verificationRoot_evaluation h𝒩 φ hi hn hg) ht

theorem proof_matrix_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (φ : SetSentence)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (ht : (ReducedProvability.proofMatrix φ).satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set])) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) (ReducedProvability.proofMatrix φ)) := by
  rw [ReducedProvability.proofMatrix_split] at ht
  exact ReducedProvability.matrix_of_verification h𝒩 φ hi hn hg
    (verification_reflection h𝒩 φ hi hn hg ht.2)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
