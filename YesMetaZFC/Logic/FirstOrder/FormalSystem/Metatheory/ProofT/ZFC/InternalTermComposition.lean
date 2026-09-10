import YesMetaZFC.Automation.ObjectCodeSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalArithmeticEvaluation

/-! # 固定复合项的内部求值组合

把子项及运算结果的数码加入有限参数环境，特化源同余定理后逐次 MP。
只对固定的外部项骨架组合；操作数、数码和内部证明长度均不要求外部标准。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 100000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def termEqualityCode {free : SetContext} (𝒩 : Structure.{0,0,0,x} signature)
    (values : Nat → 𝒩.Carrier .set) (input : SetOpenTerm free) (result : 𝒩.Carrier .set) :=
  node 𝒩 3 [term 𝒩 values input, result]

/-- 数值封闭性及任意合法结果数码的实际等式证明。 -/
def TermEvaluates {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set)
    (input : SetOpenTerm free) : Prop :=
  mem 𝒩 (input.eval env) (w 𝒩) ∧ ∀ result, mem 𝒩 result (w 𝒩) →
    PureSourceNumeralSyntax.Graph 𝒩 (input.eval env) result → ProvableCode 𝒩 (termEqualityCode 𝒩 values input result)

def BinaryEvaluates (𝒩 : Structure.{0,0,0,x} signature) (operation : BinaryTerm) : Prop :=
  ∀ left right, mem 𝒩 left (w 𝒩) → mem 𝒩 right (w 𝒩) →
    mem 𝒩 (binaryValue 𝒩 operation left right) (w 𝒩) ∧
    ∀ first second result, mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 left first →
      mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 right second →
      mem 𝒩 result (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation left right) result →
        ProvableCode 𝒩 (evaluationCode 𝒩 operation first second result)

theorem termAt_code {free : SetContext} (values : Nat → 𝒩.Carrier .set)
    (operation : BinaryTerm) (left right : SetOpenTerm free) :
    term 𝒩 values (ObjectNumeralEvaluation.termAt operation left right) =
      term 𝒩 (ObjectCodeInstantiation.prepend (term 𝒩 values left) (fun _ => term 𝒩 values right)) operation := by
  apply ObjectCodeInstantiation.term_mapped
  · intro sort entry; cases entry
  · intro sort entry
    cases entry with
    | here => rfl
    | there entry => cases entry with
      | here => rfl
      | there entry => cases entry

theorem evaluationCode_eq (operation : BinaryTerm) (first second result : 𝒩.Carrier .set) :
    evaluationCode 𝒩 operation first second result =
      node 𝒩 3 [term 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) operation, result] := by
  change node 𝒩 3 [ObjectCodeInstantiation.term _ (ObjectCodeInstantiation.prepend result _)
    (operation.weakenFree SetSort.set), result] = _
  rw [ObjectCodeInstantiation.term_weakenFree]

def liftThree {free : SetContext} (input : SetOpenTerm free) : SetOpenTerm (.set :: .set :: .set :: free) :=
  ((input.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set

theorem liftThree_code {free : SetContext} (values : Nat → 𝒩.Carrier .set)
    (first second result : 𝒩.Carrier .set) (input : SetOpenTerm free) :
    term 𝒩 (ObjectCodeInstantiation.prepend result (ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values)))
      (liftThree input) = term 𝒩 values input := by
  simp only [liftThree, term, ObjectCodeInstantiation.term_weakenFree]

def compositionLeft {free : SetContext} (left : SetOpenTerm free) : SetOpenFormula (.set :: .set :: .set :: free) :=
  liftThree left ≐ₘ (.fvar (.there (.there .here)))
def compositionRight {free : SetContext} (right : SetOpenTerm free) : SetOpenFormula (.set :: .set :: .set :: free) :=
  liftThree right ≐ₘ (.fvar (.there .here))
def compositionOperation {free : SetContext} (operation : BinaryTerm) : SetOpenFormula (.set :: .set :: .set :: free) :=
  ObjectNumeralEvaluation.termAt operation (.fvar (.there (.there .here))) (.fvar (.there .here)) ≐ₘ (.fvar .here)
def compositionResult {free : SetContext} (operation : BinaryTerm) (left right : SetOpenTerm free) : SetOpenFormula (.set :: .set :: .set :: free) :=
  ObjectNumeralEvaluation.termAt operation (liftThree left) (liftThree right) ≐ₘ (.fvar .here)

theorem composition_derives {free : SetContext} (operation : BinaryTerm) (left right : SetOpenTerm free) :
    Derives intrinsic_zfc_theory []
      (.imp (compositionLeft left) (.imp (compositionRight right)
        (.imp (compositionOperation (free := free) operation) (compositionResult operation left right)))) := by
  apply source_complete
  intro 𝒩 _ env
  simp only [compositionLeft, compositionRight, compositionOperation, compositionResult, Formula.satisfies, termAt_eval]
  intro hl hr hp
  rw [hl, hr]
  exact hp

theorem compose_proof (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (operation : BinaryTerm) (left right : SetOpenTerm free)
    (hl : mem 𝒩 (left.eval env) (w 𝒩)) (hr : mem 𝒩 (right.eval env) (w 𝒩))
    (hout : mem 𝒩 (binaryValue 𝒩 operation (left.eval env) (right.eval env)) (w 𝒩))
    {first second result : 𝒩.Carrier .set}
    (hf : mem 𝒩 first (w 𝒩)) (hFirst : PureSourceNumeralSyntax.Graph 𝒩 (left.eval env) first)
    (hs : mem 𝒩 second (w 𝒩)) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second)
    (ho : mem 𝒩 result (w 𝒩)) (hResult : PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation (left.eval env) (right.eval env)) result)
    (hLeft : ProvableCode 𝒩 (termEqualityCode 𝒩 values left first))
    (hRight : ProvableCode 𝒩 (termEqualityCode 𝒩 values right second))
    (hOperation : ProvableCode 𝒩 (evaluationCode 𝒩 operation first second result)) :
    ProvableCode 𝒩 (termEqualityCode 𝒩 values (ObjectNumeralEvaluation.termAt operation left right) result) := by
  let extended := ObjectCodeInstantiation.prepend result (ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values))
  have he := numeralValues_prepend (numeralValues_prepend (numeralValues_prepend hv hl hf hFirst) hr hs hSecond) hout ho hResult
  have hL : formula 𝒩 extended (compositionLeft left) = termEqualityCode 𝒩 values left first := by
    change node 𝒩 3 [term 𝒩 extended (liftThree left), first] = _
    rw [liftThree_code]; rfl
  have hR : formula 𝒩 extended (compositionRight right) = termEqualityCode 𝒩 values right second := by
    change node 𝒩 3 [term 𝒩 extended (liftThree right), second] = _
    rw [liftThree_code]; rfl
  have hO : formula 𝒩 extended (compositionOperation (free := free) operation) = evaluationCode 𝒩 operation first second result := by
    change node 𝒩 3 [term 𝒩 extended (ObjectNumeralEvaluation.termAt operation _ _), result] = _
    rw [termAt_code, evaluationCode_eq]; rfl
  have hC : formula 𝒩 extended (compositionResult operation left right) =
      termEqualityCode 𝒩 values (ObjectNumeralEvaluation.termAt operation left right) result := by
    change node 𝒩 3 [term 𝒩 extended (ObjectNumeralEvaluation.termAt operation _ _), result] = _
    rw [termAt_code, liftThree_code, liftThree_code]
    unfold termEqualityCode
    rw [termAt_code]
  have h := values_modus_ponens (values := extended) h𝒩 (compositionOperation (free := free) operation) (compositionResult operation left right) he
    (hO.symm ▸ hOperation)
    (values_modus_ponens (values := extended) h𝒩 (compositionRight right) _ he (hR.symm ▸ hRight)
      (values_modus_ponens (values := extended) h𝒩 (compositionLeft left) _ he (hL.symm ▸ hLeft)
        (specialize_values h𝒩 _ (composition_derives operation left right) he)))
  rwa [hC] at h

/-- 一个运算的数码求值接口可作用于任意已求值的复合子项。 -/
theorem binary_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (operation : BinaryTerm) (hop : BinaryEvaluates 𝒩 operation)
    {left right : SetOpenTerm free} (hl : TermEvaluates env values left) (hr : TermEvaluates env values right) :
    TermEvaluates env values (ObjectNumeralEvaluation.termAt operation left right) := by
  have hp := hop (left.eval env) (right.eval env) hl.1 hr.1
  constructor
  · rw [termAt_eval]; exact hp.1
  · intro result ho hResult
    rw [termAt_eval] at hResult
    obtain ⟨first, hf, hFirst⟩ := PureSourceNumeralSyntax.total h𝒩 hl.1
    obtain ⟨second, hs, hSecond⟩ := PureSourceNumeralSyntax.total h𝒩 hr.1
    exact compose_proof h𝒩 env values hv operation left right hl.1 hr.1 hp.1 hf hFirst hs hSecond ho hResult
      (hl.2 first hf hFirst) (hr.2 second hs hSecond) (hp.2 first second result hf hFirst hs hSecond ho hResult)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
