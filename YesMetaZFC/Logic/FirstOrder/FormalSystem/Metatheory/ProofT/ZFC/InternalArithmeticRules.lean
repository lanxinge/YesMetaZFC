import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralOrderRules
import YesMetaZFC.Model.ZFC.Pure.PureSourceArithmeticRecurrence

/-! # 加乘幂求值的源推导与内部后继证明组合 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity PureSourceNumerals
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 80000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}
abbrev ArithmeticOperation := PureSourceArithmetic.Operation

def operationTerm (operation : ArithmeticOperation) : BinaryTerm :=
  match operation with
  | .addition => natural_addition_term (.fvar .here) (.fvar (.there .here))
  | .multiplication => natural_multiplication_term (.fvar .here) (.fvar (.there .here))
  | .exponentiation => natural_exponentiation_term (.fvar .here) (.fvar (.there .here))

theorem operation_value (operation : ArithmeticOperation) (left right : 𝒩.Carrier .set) :
    binaryValue 𝒩 (operationTerm operation) left right = PureSourceArithmetic.arithmetic 𝒩 operation left right := by
  cases operation <;> rfl

def seedTerm (operation : ArithmeticOperation) : SetOpenTerm [.set] :=
  match operation with
  | .addition => .fvar .here
  | .multiplication => ∅ₘ
  | .exponentiation => Sₘ(∅ₘ)

def zeroEvaluationBody (operation : ArithmeticOperation) : SetOpenFormula [.set] :=
  ObjectNumeralEvaluation.termAt (operationTerm operation) (.fvar .here) ∅ₘ ≐ₘ seedTerm operation

theorem zero_evaluation_derives (operation : ArithmeticOperation) : Derives intrinsic_zfc_theory []
    (.imp naturalBody (zeroEvaluationBody operation)) := by
  apply source_complete
  intro 𝒩 h𝒩 env hl
  have h := PureSourceArithmetic.at_zero h𝒩 operation hl
  cases operation <;> exact h

def previousEvaluationBody (operation : ArithmeticOperation) : SetOpenFormula [.set,.set,.set,.set] :=
  (ObjectNumeralEvaluation.body (operationTerm operation)).weakenFree SetSort.set

def stepEvaluationBody (operation : ArithmeticOperation) : SetOpenFormula [.set,.set,.set,.set] :=
  let previous : SetOpenTerm [.set,.set,.set,.set] := .fvar (.there .here)
  let left : SetOpenTerm [.set,.set,.set,.set] := .fvar (.there (.there .here))
  let output : SetOpenTerm [.set,.set,.set,.set] := .fvar .here
  match operation with
  | .addition => Sₘ(previous) ≐ₘ output
  | .multiplication => natural_addition_term previous left ≐ₘ output
  | .exponentiation => natural_multiplication_term previous left ≐ₘ output

def nextEvaluationBody (operation : ArithmeticOperation) : SetOpenFormula [.set,.set,.set,.set] :=
  ObjectNumeralEvaluation.termAt (operationTerm operation) (.fvar (.there (.there .here)))
    Sₘ(.fvar (.there (.there (.there .here)))) ≐ₘ (.fvar .here)

def evaluationLeftNatural : SetOpenFormula [.set,.set,.set,.set] := (.fvar (.there (.there .here))) ∈ₘ ωₘ
def evaluationRightNatural : SetOpenFormula [.set,.set,.set,.set] := (.fvar (.there (.there (.there .here)))) ∈ₘ ωₘ

theorem successor_evaluation_derives (operation : ArithmeticOperation) : Derives intrinsic_zfc_theory []
    (.imp evaluationLeftNatural (.imp evaluationRightNatural
      (.imp (previousEvaluationBody operation) (.imp (stepEvaluationBody operation) (nextEvaluationBody operation))))) := by
  apply source_complete
  intro 𝒩 h𝒩 env hl hr hp hn
  have h := PureSourceArithmetic.at_successor h𝒩 operation hl hr
  cases operation <;> change _ = _ at hp hn ⊢
  · exact h.trans ((congrArg (suc 𝒩) hp).trans hn)
  · exact h.trans ((congrArg (fun v => sum 𝒩 v _) hp).trans hn)
  · exact h.trans ((congrArg (fun v => product 𝒩 v _) hp).trans hn)

theorem evaluation_numeralValues {left right output first second result : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩)) (hv : mem 𝒩 result (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hResult : PureSourceNumeralSyntax.Graph 𝒩 output result) : NumeralValues 𝒩 (evaluationValues first second result) :=
  numeralValues_prepend (pair_numeralValues hl hr hf hs hFirst hSecond) ho hv hResult

/-- 递推等式的证明码由四个合法数码的特化及四次 MP 得到。 -/
theorem evaluation_successor (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : ArithmeticOperation)
    {left right first second previous result : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first)
    (hs : mem 𝒩 second (w 𝒩)) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hp : mem 𝒩 previous (w 𝒩)) (hPrevious : PureSourceNumeralSyntax.Graph 𝒩 (PureSourceArithmetic.arithmetic 𝒩 operation left right) previous)
    (ho : mem 𝒩 result (w 𝒩)) (hResult : PureSourceNumeralSyntax.Graph 𝒩 (PureSourceArithmetic.arithmetic 𝒩 operation left (suc 𝒩 right)) result)
    (hProof : ProvableCode 𝒩 (evaluationCode 𝒩 (operationTerm operation) first second previous))
    (hStep : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend result (evaluationValues first second previous)) (stepEvaluationBody operation))) :
    ProvableCode 𝒩 (evaluationCode 𝒩 (operationTerm operation) first (PureSourceNumeralSyntax.next 𝒩 second) result) := by
  let values := ObjectCodeInstantiation.prepend result (evaluationValues first second previous)
  have hv := numeralValues_prepend
    (evaluation_numeralValues hl hr (PureSourceArithmetic.specification h𝒩 operation hl hr).1 hf hs hp hFirst hSecond hPrevious)
    (PureSourceArithmetic.specification h𝒩 operation hl ((omega_closed h𝒩).2 right hr)).1 ho hResult
  have hLeft : ProvableCode 𝒩 (formula 𝒩 values evaluationLeftNatural) := natural h𝒩 hl hf hFirst
  have hRight : ProvableCode 𝒩 (formula 𝒩 values evaluationRightNatural) := natural h𝒩 hr hs hSecond
  have hPrev : ProvableCode 𝒩 (formula 𝒩 values (previousEvaluationBody operation)) := by
    cases operation <;> exact hProof
  have h := values_modus_ponens (values := values) h𝒩 (stepEvaluationBody operation) (nextEvaluationBody operation) hv hStep
    (values_modus_ponens (values := values) h𝒩 (previousEvaluationBody operation) _ hv hPrev
      (values_modus_ponens (values := values) h𝒩 evaluationRightNatural _ hv hRight
        (values_modus_ponens (values := values) h𝒩 evaluationLeftNatural _ hv hLeft
          (specialize_values h𝒩 _ (successor_evaluation_derives operation) hv))))
  have hShape : formula 𝒩 values (nextEvaluationBody operation) =
      evaluationCode 𝒩 (operationTerm operation) first
        (node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), second]) result := by
    cases operation <;> rfl
  rw [hShape, successor_symbol h𝒩] at h
  exact h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
