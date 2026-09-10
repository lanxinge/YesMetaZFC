import YesMetaZFC.Automation.ObjectNumeralEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralQuantifiers

/-! # 二元项求值的可分离数码归纳

固定的二元项只需自然数封闭性、最终阶段对应及实际零／后继证明构造。
三个数码槽位共用受限量词，不使用任意外部性质归纳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity PureSourceNumerals
open PureSourceInstantiation ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
set_option maxHeartbeats 30000
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

abbrev BinaryTerm := ObjectNumeralEvaluation.BinaryTerm

def binaryValue (𝒩 : Structure.{0,0,0,x} signature) (operation : BinaryTerm) (left right : 𝒩.Carrier .set) :=
  operation.eval (templateEnv (.cons left (.cons right .nil)) : Env 𝒩 [] [.set,.set])

def evaluationValues {α : Type x} (first second result : α) :=
  ObjectCodeInstantiation.prepend result (ObjectCodeInstantiation.prepend first (fun _ => second))

def evaluationCode (𝒩 : Structure.{0,0,0,x} signature) (operation : BinaryTerm) (first second result : 𝒩.Carrier .set) :=
  formula 𝒩 (evaluationValues first second result) (ObjectNumeralEvaluation.body operation)

theorem termAt_eval {bound free : SetContext} (env : Env 𝒩 bound free)
    (operation : BinaryTerm) (left right : SetTerm bound free) :
    (ObjectNumeralEvaluation.termAt operation left right).eval env = binaryValue 𝒩 operation (left.eval env) (right.eval env) := by
  change (operation.substitute (.map VariableSubstitution.empty
    (VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty)))).eval env = _
  rw [Term.eval_substitute]
  apply congrArg (fun env => operation.eval env)
  apply Env.ext
  · intro sort entry; cases entry
  · intro sort entry
    cases entry with
    | here => rfl
    | there entry => cases entry with
      | here => rfl
      | there entry => cases entry

theorem evaluationAt_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (operation : BinaryTerm) (left right : SetTerm bound free) :
    (ObjectNumeralEvaluation.atPair ReducedProofPresentation.presentation.graph operation left right).satisfies env ↔
      ∀ first, mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (left.eval env) first →
      ∀ second, mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second →
      ∀ result, mem 𝒩 result (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation (left.eval env) (right.eval env)) result →
        ProvableCode 𝒩 (evaluationCode 𝒩 operation first second result) := by
  simp only [ObjectNumeralEvaluation.atPair, forallNumeral_satisfies, provableCode_satisfies,
    termAt_eval, formula_eval, Term.eval_weakenFree, ObjectNumeralReflection.map_prepend]
  rfl

theorem evaluationAll_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (operation : BinaryTerm) (right : SetTerm bound free) :
    (ObjectNumeralEvaluation.atRight ReducedProofPresentation.presentation.graph operation right).satisfies env ↔
      ∀ left, mem 𝒩 left (w 𝒩) →
      ∀ first, mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 left first →
      ∀ second, mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second →
      ∀ result, mem 𝒩 result (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation left (right.eval env)) result →
        ProvableCode 𝒩 (evaluationCode 𝒩 operation first second result) := by
  simp only [ObjectNumeralEvaluation.atRight, forallNatural_satisfies, evaluationAt_satisfies, Term.eval_weakenFree]
  rfl

theorem evaluationValues_natural {first second result : 𝒩.Carrier .set}
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩)) (ho : mem 𝒩 result (w 𝒩)) :
    ∀ i, mem 𝒩 (evaluationValues first second result i) (w 𝒩) := by
  intro i; cases i with
  | zero => exact ho
  | succ i => cases i <;> assumption

theorem evaluationAll_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : BinaryTerm)
    (hClosed : ∀ left right, mem 𝒩 left (w 𝒩) → mem 𝒩 right (w 𝒩) → mem 𝒩 (binaryValue 𝒩 operation left right) (w 𝒩))
    (hAgree : ∀ left right, mem 𝒩 left (w 𝒩) → mem 𝒩 right (w 𝒩) →
      binaryValue 𝒩 operation left right = binaryValue (canonical h𝒩) operation left right)
    {right : 𝒩.Carrier .set} (hr : mem 𝒩 right (w 𝒩)) :
    (ObjectNumeralEvaluation.atRight ReducedProofPresentation.presentation.graph operation (.fvar .here)).satisfies
      (templateEnv (.cons right .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectNumeralEvaluation.atRight ReducedProofPresentation.presentation.graph operation (.fvar .here)).satisfies
      (templateEnv (.cons right .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [evaluationAll_satisfies, evaluationAll_satisfies]
  apply forall_congr'; intro left
  change (mem 𝒩 left (w 𝒩) → _) ↔ (mem 𝒩 left (w (canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro hl
  apply forall_congr'; intro first
  apply imp_congr_right; intro hf
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hl hf)
  apply forall_congr'; intro second
  apply imp_congr_right; intro hs
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hr hs)
  apply forall_congr'; intro result
  apply imp_congr_right; intro ho
  change (PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation left right) result → _) ↔
    (PureSourceNumeralSyntax.Graph (canonical h𝒩) (binaryValue (canonical h𝒩) operation left right) result → _)
  rw [← hAgree left right hl hr]
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 (hClosed left right hl hr) ho)
  unfold evaluationCode
  exact (PureSourceLocalTests.provableCode_agreement h𝒩
    (formula_natural h𝒩 (evaluationValues_natural hf hs ho) (ObjectNumeralEvaluation.body operation))).trans
      (iff_of_eq (congrArg (fun code : 𝒩.Carrier .set => ProvableCode (canonical h𝒩) code)
        (formula_agrees h𝒩 (evaluationValues_natural hf hs ho) (ObjectNumeralEvaluation.body operation))))

/-- 后继步可使用任意合法的中间值数码，其存在来自已完成的数码图总性。 -/
theorem evaluation_induction (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : BinaryTerm)
    (hClosed : ∀ left right, mem 𝒩 left (w 𝒩) → mem 𝒩 right (w 𝒩) → mem 𝒩 (binaryValue 𝒩 operation left right) (w 𝒩))
    (hAgree : ∀ left right, mem 𝒩 left (w 𝒩) → mem 𝒩 right (w 𝒩) →
      binaryValue 𝒩 operation left right = binaryValue (canonical h𝒩) operation left right)
    (hZero : ∀ left first second result, mem 𝒩 left (w 𝒩) → mem 𝒩 first (w 𝒩) →
      PureSourceNumeralSyntax.Graph 𝒩 left first → mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (z 𝒩) second →
      mem 𝒩 result (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation left (z 𝒩)) result →
      ProvableCode 𝒩 (evaluationCode 𝒩 operation first second result))
    (hStep : ∀ left right first second previous result,
      mem 𝒩 left (w 𝒩) → mem 𝒩 right (w 𝒩) → mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 left first →
      mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 right second →
      mem 𝒩 previous (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation left right) previous →
      ProvableCode 𝒩 (evaluationCode 𝒩 operation first second previous) →
      mem 𝒩 result (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation left (suc 𝒩 right)) result →
      ProvableCode 𝒩 (evaluationCode 𝒩 operation first (PureSourceNumeralSyntax.next 𝒩 second) result))
    {left right first second result : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first)
    (hs : mem 𝒩 second (w 𝒩)) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (ho : mem 𝒩 result (w 𝒩)) (hResult : PureSourceNumeralSyntax.Graph 𝒩 (binaryValue 𝒩 operation left right) result) :
    ProvableCode 𝒩 (evaluationCode 𝒩 operation first second result) := by
  have hAll := PureSourceInduction.induction h𝒩
    (ObjectNumeralEvaluation.atRight ReducedProofPresentation.presentation.graph operation (.fvar .here)) .nil
    (fun _ h => evaluationAll_agrees h𝒩 operation hClosed hAgree h) (by
      apply (evaluationAll_satisfies _ _ _).mpr
      intro left hl first hf hFirst second hs hSecond result ho hResult
      exact hZero left first second result hl hf hFirst hs hSecond ho hResult) (by
      intro right hr hProperty
      apply (evaluationAll_satisfies _ _ _).mpr
      intro left hl first hf hFirst second hs hSecond result ho hResult
      obtain ⟨prior, hp, hPrior, rfl⟩ := (PureSourceNumeralSyntax.successor_iff h𝒩 hr hs).mp hSecond
      obtain ⟨previous, hv, hPrevious⟩ := PureSourceNumeralSyntax.total h𝒩 (hClosed left right hl hr)
      exact hStep left right first prior previous result hl hr hf hFirst hp hPrior hv hPrevious
        ((evaluationAll_satisfies _ _ _).mp hProperty left hl first hf hFirst prior hp hPrior previous hv hPrevious) ho hResult)
  exact (evaluationAll_satisfies _ _ _).mp (hAll right hr) left hl first hf hFirst second hs hSecond result ho hResult

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
