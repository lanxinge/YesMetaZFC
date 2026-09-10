import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalTermComposition

/-! # 变量、数码和任意复合算术项的求值

后继和加乘幂共享二元项组合，其中后继忽略第二个槽位。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem variable_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (entry : Variable free .set) (hi : mem 𝒩 (env.freeVal entry) (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 (env.freeVal entry) (values entry.index)) :
    TermEvaluates env values (.fvar entry) :=
  ⟨hi, fun _ hn hNamed => equal h𝒩 hi (numeralValues_natural hv entry.index) hn hg hNamed rfl⟩

theorem zero_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values) :
    TermEvaluates env values (∅ₘ : SetOpenTerm free) := by
  refine ⟨(omega_closed h𝒩).1, ?_⟩
  intro named hn hg
  have h := specialize_values h𝒩 ((∅ₘ : SetOpenTerm free) ≐ₘ ∅ₘ) (Metatheory.Derives.equality_refl _) hv
  change ProvableCode 𝒩 (node 𝒩 3 [(node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]),
    (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []])]) at h
  change ProvableCode 𝒩 (node 𝒩 3 [(node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]), named])
  rw [(PureSourceNumeralSyntax.zero_iff h𝒩 hn).mp hg]
  rwa [zero_term_code h𝒩] at h ⊢

def successorOperation : BinaryTerm := Sₘ(.fvar .here)

theorem successor_binary_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    BinaryEvaluates 𝒩 successorOperation := by
  intro left right hl _
  refine ⟨(omega_closed h𝒩).2 left hl, ?_⟩
  intro first second result hf hFirst _ _ ho hResult
  have h := equal h𝒩 ((omega_closed h𝒩).2 left hl) (PureSourceNumeralSyntax.next_natural h𝒩 hf) ho
    (PureSourceNumeralSyntax.successor h𝒩 hl hf hFirst) hResult rfl
  change ProvableCode 𝒩 (node 𝒩 3 [(node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), first]), result])
  rwa [successor_symbol h𝒩]

theorem successor_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input : SetOpenTerm free} (hi : TermEvaluates env values input) : TermEvaluates env values Sₘ(input) :=
  binary_term_evaluation h𝒩 env values hv successorOperation (successor_binary_evaluation h𝒩) hi hi

theorem numeral_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values) (n : Nat) :
    TermEvaluates env values (numₘ(n) : SetOpenTerm free) := by
  induction n with
  | zero => exact zero_evaluation h𝒩 env values hv
  | succ n ih => exact successor_term_evaluation h𝒩 env values hv ih

theorem arithmetic_binary_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (operation : ArithmeticOperation) :
    BinaryEvaluates 𝒩 (operationTerm operation) := by
  intro left right hl hr
  constructor
  · rw [operation_value]; exact (PureSourceArithmetic.specification h𝒩 operation hl hr).1
  · intro first second result hf hFirst hs hSecond ho hResult
    rw [operation_value] at hResult
    exact arithmetic_evaluation h𝒩 operation left right first second result hl hr hf hFirst hs hSecond ho hResult

theorem arithmetic_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (operation : ArithmeticOperation) {left right : SetOpenTerm free}
    (hl : TermEvaluates env values left) (hr : TermEvaluates env values right) :
    TermEvaluates env values (ObjectNumeralEvaluation.termAt (operationTerm operation) left right) :=
  binary_term_evaluation h𝒩 env values hv _ (arithmetic_binary_evaluation h𝒩 operation) hl hr

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
