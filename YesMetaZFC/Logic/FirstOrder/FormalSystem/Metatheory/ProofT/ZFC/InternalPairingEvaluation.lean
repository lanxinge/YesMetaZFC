import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPairingRules

/-! # Gödel 配对的数码求值与复合项闭包

正／负序反射选择分支，再将相应多项式的求值证明接入原配对定义。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
set_option maxHeartbeats 100000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem pairing_branch_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (lower : Bool)
    {left right first second result : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first)
    (hs : mem 𝒩 second (w 𝒩)) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (ho : mem 𝒩 result (w 𝒩)) (hResult : PureSourceNumeralSyntax.Graph 𝒩 (pair 𝒩 left right) result)
    (hGuard : if lower then mem 𝒩 left right else ¬ mem 𝒩 left right) :
    ProvableCode 𝒩 (evaluationCode 𝒩 pairingOperation first second result) := by
  let values := evaluationValues first second result
  have hv := evaluation_numeralValues hl hr (pairing_spec h𝒩 hl hr).1 hf hs ho hFirst hSecond hResult
  have hL : ProvableCode 𝒩 (formula 𝒩 values pairingLeftNatural) := natural h𝒩 hl hf hFirst
  have hR : ProvableCode 𝒩 (formula 𝒩 values pairingRightNatural) := natural h𝒩 hr hs hSecond
  have hOrder := order h𝒩 hl hr hf hs hFirst hSecond
  have hG : ProvableCode 𝒩 (formula 𝒩 values ((pairingGuard lower).weakenFree SetSort.set)) := by
    cases lower
    · exact hOrder.2 hGuard
    · exact hOrder.1 hGuard
  have hPoly := pairing_polynomial_evaluation h𝒩 lower hl hr hf hFirst hs hSecond
  have hg : PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 (pairingPolynomial lower) left right) result :=
    (pairing_polynomial_value h𝒩 lower hl hr hGuard) ▸ hResult
  have hP : ProvableCode 𝒩 (formula 𝒩 values (ObjectNumeralEvaluation.body (pairingPolynomial lower))) := by
    change ProvableCode 𝒩 (evaluationCode 𝒩 (pairingPolynomial lower) first second result)
    rw [evaluationCode_eq]
    exact hPoly.2 result ho hg
  exact values_modus_ponens (values := values) h𝒩 (ObjectNumeralEvaluation.body (pairingPolynomial lower)) _ hv hP
    (values_modus_ponens (values := values) h𝒩 ((pairingGuard lower).weakenFree SetSort.set) _ hv hG
      (values_modus_ponens (values := values) h𝒩 pairingRightNatural _ hv hR
        (values_modus_ponens (values := values) h𝒩 pairingLeftNatural _ hv hL
          (specialize_values h𝒩 _ (pairing_branch_derives lower) hv))))

/-- 包括相等坐标在内的全部内部自然数配对求值。 -/
theorem pairing_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) : BinaryEvaluates 𝒩 pairingOperation := by
  intro left right hl hr
  refine ⟨(pairing_spec h𝒩 hl hr).1, ?_⟩
  intro first second result hf hFirst hs hSecond ho hResult
  classical
  by_cases h : mem 𝒩 left right
  · exact pairing_branch_evaluation h𝒩 true hl hr hf hFirst hs hSecond ho hResult h
  · exact pairing_branch_evaluation h𝒩 false hl hr hf hFirst hs hSecond ho hResult h

theorem pairing_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {left right : SetOpenTerm free} (hl : TermEvaluates env values left) (hr : TermEvaluates env values right) :
    TermEvaluates env values (godel_pairing_term left right) :=
  binary_term_evaluation h𝒩 env values hv pairingOperation (pairing_evaluation h𝒩) hl hr

theorem pairing_evaluation_derives : Derives intrinsic_zfc_theory []
    (ObjectNumeralReflection.forallNatural
      (ObjectNumeralEvaluation.atRight ReducedProofPresentation.presentation.graph pairingOperation (.fvar .here)) : SetSentence) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  apply (forallNatural_satisfies _ _).mpr
  intro right hr
  apply (evaluationAll_satisfies _ _ _).mpr
  intro left hl first hf hFirst second hs hSecond result ho hResult
  exact (pairing_evaluation h𝒩 left right hl hr).2 first second result hf hFirst hs hSecond ho hResult

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
