import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveFormula

/-! # 闭 quotation 表项嵌入任意上下文后的求值 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralReflection
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {bound free : SetContext}

/-- 闭项的值与代码在槽位扩充下不变，直接复用原闭项求值证明。 -/
theorem closed (input : SetTerm [] [])
    (h : ∀ values, NumeralValues 𝒩 values → TermEvaluates (Env.empty : Env 𝒩 [] []) values input) :
    Evaluates 𝒩 (FixedAxiomTable.row_term (bound := bound) (free := free) input) := by
  intro target env values hv bs fs _ _
  have hSyntax : (FixedAxiomTable.row_term input).substituteMapped bs fs =
      input.substituteMapped (VariableSubstitution.empty : VariableSubstitution signature [] [] target) VariableSubstitution.empty := by
    rw [FixedAxiomTable.row_term, Term.embedClosed_substituteMapped]
    have hs := Term.embedClosed_substituteMapped (sourceBound := []) (sourceFree := [])
      (targetBound := []) (targetFree := target) input VariableSubstitution.empty VariableSubstitution.empty
    rw [show input.embedClosed [] [] = input from FixedAxiomTable.row_term_empty input] at hs
    exact hs.symm
  rw [hSyntax]
  have he : (input.substituteMapped (VariableSubstitution.empty : VariableSubstitution signature [] [] target) VariableSubstitution.empty).eval env =
      input.eval (Env.empty : Env 𝒩 [] []) := by
    change (input.substitute (.map VariableSubstitution.empty VariableSubstitution.empty)).eval env = _
    rw [Term.eval_substitute]
    congr 1
    exact Env.ext (fun entry => nomatch entry) (fun entry => nomatch entry)
  have hc := ObjectCodeInstantiation.term_mapped (PureSourceCoding.node 𝒩) values values
    (VariableSubstitution.empty : VariableSubstitution signature [] [] target) VariableSubstitution.empty
    (fun entry => nomatch entry) (fun entry => nomatch entry) input
  simpa only [TermEvaluates, he, termEqualityCode, term, hc] using h values hv

theorem tree (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (input : NatPacket.Tree) :
    Evaluates 𝒩 (FixedAxiomTable.row_term (bound := bound) (free := free) (IntrinsicQuotation.tree input)) :=
  closed _ (fun values hv => tree_term_evaluation h𝒩 values hv input)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
