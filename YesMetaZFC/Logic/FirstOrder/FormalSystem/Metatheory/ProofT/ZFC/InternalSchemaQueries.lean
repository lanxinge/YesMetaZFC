import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalSchemaReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveQueries

/-! # verifier 实际公理查询的内部正反射终点 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalSchemaReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation
open InternalPositiveFormula InternalNumeralReflection ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local irreducible] Positive Evaluates ReducedAxioms.basis ReducedAxiomNumber.entries
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem axiomTest (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    Positive 𝒩 ReducedAxiomNumber.localTest.condition.body :=
  binaryTest h𝒩 intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.contains_successor
    ReducedAxiomNumber.binaryTest (axiomCondition h𝒩 (fvar _) (fvar _))

theorem packet_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input output : SetOpenTerm free} (hi : TermEvaluates env values input) (ho : TermEvaluates env values output) :
    (SchemaPacket.condition input output).satisfies env →
      ProvableCode 𝒩 (formula 𝒩 values (SchemaPacket.condition input output)) := by
  rw [← SchemaPacket.template_apply]
  exact binary_terms SchemaPacket.template (packet h𝒩 (fvar _) (fvar _)) env values hv hi ho

theorem axiom_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input output : SetOpenTerm free} (hi : TermEvaluates env values input) (ho : TermEvaluates env values output) :
    (ReducedAxiomNumber.condition input output).satisfies env →
      ProvableCode 𝒩 (formula 𝒩 values (ReducedAxiomNumber.condition input output)) := by
  rw [← ReducedAxiomNumber.template_apply]
  exact binary_terms ReducedAxiomNumber.template (axiomCondition h𝒩 (fvar _) (fvar _)) env values hv hi ho

theorem axiom_query_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {root : SetOpenTerm free} (hr : TermEvaluates env values root) :
    (ReducedAxiomNumber.localTest.condition root).satisfies env →
      ProvableCode 𝒩 (formula 𝒩 values (ReducedAxiomNumber.localTest.condition root)) :=
  unary_terms _ (axiomTest h𝒩) env values hv hr

theorem axiom_query_named (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root named : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 root named)
    (ht : ReducedAxiomNumber.localTest.condition.body.satisfies (templateEnv (.cons root .nil) : Env 𝒩 [] [.set])) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) ReducedAxiomNumber.localTest.condition.body) :=
  unary_named h𝒩 (axiomTest h𝒩) hr hn hg ht

theorem axiom_query_positive_derives : Derives intrinsic_zfc_theory []
    (ObjectPositiveReflection.onNaturals ReducedProofPresentation.presentation.graph ReducedAxiomNumber.localTest.condition.body) :=
  positive_derives _ (fun _ h𝒩 => axiomTest h𝒩)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalSchemaReflection
