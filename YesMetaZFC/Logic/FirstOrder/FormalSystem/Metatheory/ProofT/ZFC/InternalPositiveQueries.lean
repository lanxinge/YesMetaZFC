import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveQuantifiers
import YesMetaZFC.Automation.ObjectPositiveReflection
import YesMetaZFC.Automation.ObjectBinaryTest

/-! # 模板正反射到原查询项及统一源推导的接口 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralReflection
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

theorem unary_terms (template : FormulaTemplate.Unary) (h : Positive 𝒩 template.body)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input : SetOpenTerm free} (hi : TermEvaluates env values input) :
    (template input).satisfies env → ProvableCode 𝒩 (formula 𝒩 values (template input)) := by
  apply h env values hv VariableSubstitution.empty (VariableSubstitution.cons input VariableSubstitution.empty)
    (fun entry => nomatch entry)
  intro entry
  cases entry with
  | here => exact hi
  | there entry => cases entry

theorem binary_terms (template : FormulaTemplate.Binary) (h : Positive 𝒩 template.body)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {left right : SetOpenTerm free} (hl : TermEvaluates env values left) (hr : TermEvaluates env values right) :
    (template left right).satisfies env → ProvableCode 𝒩 (formula 𝒩 values (template left right)) := by
  apply h env values hv VariableSubstitution.empty
    (VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty))
    (fun entry => nomatch entry)
  intro entry
  cases entry with
  | here => exact hl
  | there entry => cases entry with
    | here => exact hr
    | there entry => cases entry

section
attribute [local irreducible] Positive Evaluates

/-- 任意二元检查器的原有界行封装保持正反射。 -/
theorem binaryTest (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {T : SetTheory}
    (C : CertificateCore T) (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (test : ObjectBinaryTest.Test T) (h : Positive 𝒩 test.condition.body) :
    Positive 𝒩 (ObjectBinaryTest.localTest C hSuccessor test).condition.body := by
  apply quantify h𝒩 2 (successor h𝒩 (fvar _))
  apply conj h𝒩 (InternalPositiveFormula.equal h𝒩 (fvar _) (node h𝒩 0 ?_))
    (binary test.condition h (bvar _) (bvar _))
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact bvar _

end

theorem unary_named (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {body : SetOpenFormula [.set]} (h : Positive 𝒩 body)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (ht : body.satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set])) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) body) := by
  let env : Env 𝒩 [] [.set] := templateEnv (.cons input .nil)
  have hv : NumeralValues 𝒩 (fun _ => named) := fun _ => ⟨hn, input, hi, hg⟩
  have hp := h env (fun _ => named) hv VariableSubstitution.empty VariableSubstitution.freeId
    (fun entry => nomatch entry) (by
      intro entry
      cases entry with
      | here => exact variable_evaluation h𝒩 env _ hv .here hi hg
      | there entry => cases entry)
  have hs : body.substituteMapped VariableSubstitution.empty VariableSubstitution.freeId = body := by
    have he : (VariableSubstitution.empty : VariableSubstitution signature [] [] [.set]) = (fun {sort} (entry : Variable [] sort) => Term.bvar entry) := by
      funext sort entry
      cases entry
    rw [he]
    exact Formula.substituteMapped_id body
  rw [hs] at hp
  exact hp ht

/-- 普通 Derives 的统一终点，只要求实际查询的正反射。 -/
theorem positive_derives (body : SetOpenFormula [.set])
    (h : ∀ (𝒩 : Structure.{0,0,0,0} signature), Theory.Models 𝒩 intrinsic_zfc_theory → Positive 𝒩 body) :
    Derives intrinsic_zfc_theory [] (ObjectPositiveReflection.onNaturals ReducedProofPresentation.presentation.graph body) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  change (ObjectPositiveReflection.onNaturals ReducedProofPresentation.presentation.graph body).satisfies (Env.empty : Env 𝒩 [] [])
  unfold ObjectPositiveReflection.onNaturals
  rw [Formula.satisfies_forallFreeTop]
  intro input hInput
  apply (atNumber_satisfies _ body _).mpr
  intro named hn hg
  have he : (Env.empty : Env 𝒩 [] []).pushFree input =
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry
      cases entry with
      | here => rfl
      | there entry => cases entry
  exact unary_named h𝒩 (h 𝒩 h𝒩) hInput.1 hn hg (he ▸ hInput.2)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
