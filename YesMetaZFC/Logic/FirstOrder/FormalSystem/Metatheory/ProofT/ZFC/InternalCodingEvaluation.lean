import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPairingEvaluation

/-! # 字段列、节点和参数化语法编码项的求值

直接消费既有 structural_list、IntrinsicQuotation 与 ObjectHorn 表达式。
参数化项／参数列／公式编码复用已有关系保持遍历，不另建编码 AST。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem fields_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (fields : List (SetOpenTerm free)) (hFields : ∀ field ∈ fields, TermEvaluates env values field) :
    TermEvaluates env values (structural_list_code_term fields) := by
  induction fields with
  | nil =>
    exact successor_term_evaluation h𝒩 env values hv
      (pairing_term_evaluation h𝒩 env values hv (numeral_term_evaluation h𝒩 env values hv 0)
        (zero_evaluation h𝒩 env values hv))
  | cons head tail ih =>
    exact successor_term_evaluation h𝒩 env values hv
      (pairing_term_evaluation h𝒩 env values hv (numeral_term_evaluation h𝒩 env values hv 1)
        (pairing_term_evaluation h𝒩 env values hv (hFields head (List.mem_cons_self ..))
          (ih (fun field h => hFields field (List.mem_cons_of_mem head h)))))

theorem node_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (tag : Nat) (fields : List (SetOpenTerm free)) (hFields : ∀ field ∈ fields, TermEvaluates env values field) :
    TermEvaluates env values (IntrinsicQuotation.node tag fields) :=
  successor_term_evaluation h𝒩 env values hv
    (pairing_term_evaluation h𝒩 env values hv (numeral_term_evaluation h𝒩 env values hv tag)
      (fields_term_evaluation h𝒩 env values hv fields hFields))

/-- 实际 Horn 表达式包括任意内部数值参数和动态标签节点。 -/
theorem horn_expr_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {n : Nat} (inputs : Fin n → SetOpenTerm free) (hInputs : ∀ i, TermEvaluates env values (inputs i))
    (expr : ObjectHorn.Expr n) : TermEvaluates env values (expr.term inputs) := by
  induction expr with
  | literal n => exact numeral_term_evaluation h𝒩 env values hv n
  | var i => exact hInputs i
  | succ body ih => exact successor_term_evaluation h𝒩 env values hv ih
  | pair left right hl hr => exact pairing_term_evaluation h𝒩 env values hv hl hr

theorem parameterized_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (inputs : Nat → SetOpenTerm free) (hInputs : ∀ i, TermEvaluates env values (inputs i))
    {sb sf : SetContext} {sort : SetSort} (input : Term signature sb sf sort) :
    TermEvaluates env values (ObjectCodeInstantiation.term IntrinsicQuotation.node inputs input) :=
  ObjectCodeInstantiation.term_property IntrinsicQuotation.node inputs (TermEvaluates env values)
    (node_term_evaluation h𝒩 env values hv) hInputs input

theorem parameterized_arguments_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (inputs : Nat → SetOpenTerm free) (hInputs : ∀ i, TermEvaluates env values (inputs i))
    {sb sf sorts : SetContext} (input : Arguments signature sb sf sorts) :
    ∀ field ∈ ObjectCodeInstantiation.arguments IntrinsicQuotation.node inputs input, TermEvaluates env values field :=
  ObjectCodeInstantiation.arguments_property IntrinsicQuotation.node inputs (TermEvaluates env values)
    (node_term_evaluation h𝒩 env values hv) hInputs input

theorem parameterized_formula_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (inputs : Nat → SetOpenTerm free) (hInputs : ∀ i, TermEvaluates env values (inputs i))
    {sb sf : SetContext} (input : SetFormula sb sf) :
    TermEvaluates env values (ObjectCodeInstantiation.formula IntrinsicQuotation.node inputs input) :=
  ObjectCodeInstantiation.formula_property IntrinsicQuotation.node inputs (TermEvaluates env values)
    (node_term_evaluation h𝒩 env values hv) hInputs input

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
