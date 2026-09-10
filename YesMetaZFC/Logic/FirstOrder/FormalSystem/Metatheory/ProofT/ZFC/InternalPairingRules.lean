import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalArithmeticTerms
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralOrderReflection

/-! # Gödel 配对的分支多项式与源推导

严格小于时采用右坐标平方分支，其余情况采用左坐标平方分支。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def pairingOperation : BinaryTerm := godel_pairₘ(.fvar .here, .fvar (.there .here))
def pairingPolynomial (lower : Bool) : BinaryTerm :=
  let left : BinaryTerm := .fvar .here
  let right : BinaryTerm := .fvar (.there .here)
  if lower then natural_addition_term (natural_exponentiation_term right numₘ(2)) left
  else natural_addition_term (natural_addition_term (natural_exponentiation_term left numₘ(2)) left) right

def pairingGuard (lower : Bool) : SetOpenFormula [.set,.set] := if lower then orderBody else .neg orderBody

theorem pairing_polynomial_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (lower : Bool)
    {left right : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hGuard : if lower then mem 𝒩 left right else ¬ mem 𝒩 left right) :
    pair 𝒩 left right = binaryValue 𝒩 (pairingPolynomial lower) left right := by
  cases lower with
  | true => exact (pairing_spec h𝒩 hl hr).2.1 hGuard
  | false =>
    have hReverse : right = left ∨ mem 𝒩 right left := by
      rcases natural_compare h𝒩 hl hr with h | h | h
      · exact Or.inl h.symm
      · exact False.elim (hGuard h)
      · exact Or.inr h
    exact (pairing_spec h𝒩 hl hr).2.2 hReverse

def pairingLeftNatural : SetOpenFormula [.set,.set,.set] := (.fvar (.there .here)) ∈ₘ ωₘ
def pairingRightNatural : SetOpenFormula [.set,.set,.set] := (.fvar (.there (.there .here))) ∈ₘ ωₘ

theorem pairing_branch_derives (lower : Bool) : Derives intrinsic_zfc_theory []
    (.imp pairingLeftNatural (.imp pairingRightNatural (.imp ((pairingGuard lower).weakenFree SetSort.set)
      (.imp (ObjectNumeralEvaluation.body (pairingPolynomial lower)) (ObjectNumeralEvaluation.body pairingOperation))))) := by
  apply source_complete
  intro 𝒩 h𝒩 env hl hr hg hp
  have h := pairing_polynomial_value h𝒩 lower hl hr
  cases lower <;> exact (h hg).trans hp

/-- 多项式的复合项求值复用一般同余组合，而非重新建立算术归纳。 -/
theorem pairing_polynomial_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (lower : Bool)
    {left right first second : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first)
    (hs : mem 𝒩 second (w 𝒩)) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second) :
    TermEvaluates (templateEnv (.cons left (.cons right .nil)) : Env 𝒩 [] [.set,.set])
      (ObjectCodeInstantiation.prepend first (fun _ => second)) (pairingPolynomial lower) := by
  let env : Env 𝒩 [] [.set,.set] := templateEnv (.cons left (.cons right .nil))
  let values := ObjectCodeInstantiation.prepend first (fun _ => second)
  have hv := pair_numeralValues hl hr hf hs hFirst hSecond
  have hL := variable_evaluation h𝒩 env values hv .here hl hFirst
  have hR := variable_evaluation h𝒩 env values hv (.there .here) hr hSecond
  have hTwo := numeral_term_evaluation h𝒩 env values hv 2
  cases lower with
  | true =>
    exact arithmetic_term_evaluation h𝒩 env values hv .addition
      (arithmetic_term_evaluation h𝒩 env values hv .exponentiation hR hTwo) hL
  | false =>
    exact arithmetic_term_evaluation h𝒩 env values hv .addition
      (arithmetic_term_evaluation h𝒩 env values hv .addition
        (arithmetic_term_evaluation h𝒩 env values hv .exponentiation hL hTwo) hL) hR

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
