import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalProofRowReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalVerificationTrace

/-! # 局部行反射与原递归连边的证明装配

局部查询只需实际真值，内部证明由已完成的反射产生。
连边仍须提供原 Horn 步骤的证明；轨迹项不要求是自然数或外部有限集合。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureSourceInstantiation ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

/-- 实际 step 的 Horn 部分与局部部分合并，不改写检查器正文。 -/
theorem checked_step_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (hLocal : InternalPositiveFormula.Positive 𝒩 localCondition.body)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {row : SetOpenTerm free} (hr : TermEvaluates env values row) (trace : SetOpenTerm free)
    (hLinks : ProvableCode 𝒩 (formula 𝒩 values (ObjectHorn.step rules row trace)))
    (hQuery : (localCondition row).satisfies env) :
    ProvableCode 𝒩 (formula 𝒩 values (ObjectCheckedTrace.step rules localCondition row trace)) := by
  rw [ObjectCheckedTrace.step_apply]
  exact values_modus_ponens (values := values) h𝒩 _ _ hv
    (InternalPositiveFormula.unary_terms localCondition hLocal env values hv hr hQuery)
    (reflection_rule h𝒩 values hv (boolean_rule_derives .conj true true _ _) hLinks)

/-- 当前 verifier 的单行装配已不接收局部查询反射假设。 -/
theorem proof_step_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {row : SetOpenTerm free} (hr : TermEvaluates env values row) (trace : SetOpenTerm free)
    (hLinks : ProvableCode 𝒩 (formula 𝒩 values (ObjectHorn.step ObjectProofTree.rules row trace)))
    (hQuery : (ReducedProofPresentation.rowTest.condition row).satisfies env) :
    ProvableCode 𝒩 (formula 𝒩 values
      (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition row trace)) :=
  checked_step_values h𝒩 _ _ (InternalProofQueryReflection.currentRow h𝒩) env values hv hr trace hLinks hQuery

/-- 已有有限骨架入口只需连边证明和局部真值，局部证明义务全部消去。 -/
theorem finite_verification_of_links (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] [.set]) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (φ : SetSentence) (rows : List (SetOpenTerm [.set])) (hRoot : verificationRoot φ ∈ rows)
    (hRows : ∀ row ∈ rows, TermEvaluates env values row)
    (hLinks : ∀ row ∈ rows, ProvableCode 𝒩 (formula 𝒩 values
      (ObjectHorn.step ObjectProofTree.rules row (ObjectFiniteSet.term rows))))
    (hQueries : ∀ row ∈ rows, (ReducedProofPresentation.rowTest.condition row).satisfies env) :
    ProvableCode 𝒩 (formula 𝒩 values (ReducedProvability.verificationMatrix φ)) := by
  apply finite_verification h𝒩 env values hv φ rows hRoot hRows
  intro row hr
  exact proof_step_values h𝒩 env values hv (hRows row hr) _ (hLinks row hr) (hQueries row hr)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
