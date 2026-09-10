import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalArithmeticZero

/-! # 全部内部自然数的加、乘、幂数码求值

加法的后继步使用数码等式；乘法使用加法求值；幂使用乘法求值。
归纳骨架只写一次，结果均提供原证明图接受的实际证明码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity PureSourceNumerals
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
set_option maxHeartbeats 80000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

/-- 三个合法数码参数的求值证明接口；结果数码可以非标准。 -/
def ArithmeticEvaluates (𝒩 : Structure.{0,0,0,x} signature) (operation : ArithmeticOperation) : Prop :=
  ∀ left right first second result, mem 𝒩 left (w 𝒩) → mem 𝒩 right (w 𝒩) →
    mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 left first →
    mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 right second →
    mem 𝒩 result (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (PureSourceArithmetic.arithmetic 𝒩 operation left right) result →
      ProvableCode 𝒩 (evaluationCode 𝒩 (operationTerm operation) first second result)

def stepCode (𝒩 : Structure.{0,0,0,x} signature) (operation : ArithmeticOperation) (first previous result : 𝒩.Carrier .set) :=
  formula 𝒩 (ObjectCodeInstantiation.prepend result (evaluationValues first previous previous)) (stepEvaluationBody operation)

def ArithmeticStepEvaluates (𝒩 : Structure.{0,0,0,x} signature) (operation : ArithmeticOperation) : Prop :=
  ∀ left current first previous result, mem 𝒩 left (w 𝒩) → mem 𝒩 current (w 𝒩) →
    mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 left first →
    mem 𝒩 previous (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 current previous →
    mem 𝒩 result (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (PureSourceArithmetic.step 𝒩 operation left left current) result →
      ProvableCode 𝒩 (stepCode 𝒩 operation first previous result)

theorem arithmetic_from_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : ArithmeticOperation)
    (hStep : ArithmeticStepEvaluates 𝒩 operation) : ArithmeticEvaluates 𝒩 operation := by
  intro left right first second result hl hr hf hFirst hs hSecond ho hResult
  have hClosed (left right : 𝒩.Carrier .set) (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩)) :
      mem 𝒩 (binaryValue 𝒩 (operationTerm operation) left right) (w 𝒩) := by
    rw [operation_value]
    exact (PureSourceArithmetic.specification h𝒩 operation hl hr).1
  have hAgree (left right : 𝒩.Carrier .set) (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩)) :
      binaryValue 𝒩 (operationTerm operation) left right = binaryValue (canonical h𝒩) (operationTerm operation) left right := by
    cases operation
    · exact PureSourceArithmetic.addition_agrees h𝒩 hl hr
    · exact PureSourceArithmetic.multiplication_agrees h𝒩 hl hr
    · exact PureSourceArithmetic.exponentiation_agrees h𝒩 hl hr
  apply evaluation_induction h𝒩 (operationTerm operation) hClosed hAgree ?_ ?_ hl hr hf hFirst hs hSecond ho
    ((operation_value operation left right).symm ▸ hResult)
  · intro left first second result hl hf hFirst hs hSecond ho hResult
    rw [operation_value] at hResult
    exact evaluation_zero h𝒩 operation hl hf hFirst hs hSecond ho hResult
  · intro left right first second previous result hl hr hf hFirst hs hSecond hp hPrevious hProof ho hResult
    rw [operation_value] at hPrevious hResult
    have hStepResult := hResult
    rw [PureSourceArithmetic.at_successor h𝒩 operation hl hr] at hStepResult
    have hNext := hStep left _ first previous result hl
      (PureSourceArithmetic.specification h𝒩 operation hl hr).1 hf hFirst hp hPrevious ho hStepResult
    have hShape : formula 𝒩 (ObjectCodeInstantiation.prepend result (evaluationValues first second previous)) (stepEvaluationBody operation) =
        stepCode 𝒩 operation first previous result := by cases operation <;> rfl
    apply evaluation_successor h𝒩 operation hl hr hf hFirst hs hSecond hp hPrevious ho hResult hProof
    rwa [hShape]

/-- 加法求值不要求数码或输入外部有限。 -/
theorem addition_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) : ArithmeticEvaluates 𝒩 .addition := by
  apply arithmetic_from_step h𝒩 .addition
  intro left current first previous result _ hc _ _ hp hPrevious ho hResult
  have h := equal h𝒩 ((omega_closed h𝒩).2 current hc)
    (PureSourceNumeralSyntax.next_natural h𝒩 hp) ho
    (PureSourceNumeralSyntax.successor h𝒩 hc hp hPrevious) hResult rfl
  change ProvableCode 𝒩 (node 𝒩 3 [(node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), previous]), result])
  rwa [successor_symbol h𝒩]

/-- 乘法后继步消费刚证明的加法求值。 -/
theorem multiplication_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) : ArithmeticEvaluates 𝒩 .multiplication := by
  apply arithmetic_from_step h𝒩 .multiplication
  intro left current first previous result hl hc hf hFirst hp hPrevious ho hResult
  exact addition_evaluation h𝒩 current left previous first result hc hl hp hPrevious hf hFirst ho hResult

/-- 幂的后继步消费乘法求值，包含零底数与零指数。 -/
theorem exponentiation_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) : ArithmeticEvaluates 𝒩 .exponentiation := by
  apply arithmetic_from_step h𝒩 .exponentiation
  intro left current first previous result hl hc hf hFirst hp hPrevious ho hResult
  exact multiplication_evaluation h𝒩 current left previous first result hc hl hp hPrevious hf hFirst ho hResult

theorem arithmetic_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : ArithmeticOperation) :
    ArithmeticEvaluates 𝒩 operation := by
  cases operation
  · exact addition_evaluation h𝒩
  · exact multiplication_evaluation h𝒩
  · exact exponentiation_evaluation h𝒩

/-- 统一求值反射是源理论的实际闭句定理。 -/
theorem arithmetic_evaluation_derives (operation : ArithmeticOperation) : Derives intrinsic_zfc_theory []
    (ObjectNumeralReflection.forallNatural
      (ObjectNumeralEvaluation.atRight ReducedProofPresentation.presentation.graph (operationTerm operation) (.fvar .here)) : SetSentence) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  apply (forallNatural_satisfies _ _).mpr
  intro right hr
  apply (evaluationAll_satisfies _ _ _).mpr
  intro left hl first hf hFirst second hs hSecond result ho hResult
  rw [operation_value] at hResult
  exact arithmetic_evaluation h𝒩 operation left right first second result hl hr hf hFirst hs hSecond ho hResult

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
