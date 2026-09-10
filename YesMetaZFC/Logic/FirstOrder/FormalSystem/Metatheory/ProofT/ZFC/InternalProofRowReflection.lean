import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalProofQueries

/-! # 实际逻辑、节点与证明行查询的公开反射终点 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalProofQueryReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation
open InternalPositiveFormula InternalNumeralReflection ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local irreducible] Positive Evaluates ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

theorem logical_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {root : SetOpenTerm free} (hr : TermEvaluates env values root) :
    ((ObjectLogicalAxiom.localTest C S hSuccessor hPower hInfinity).condition root).satisfies env →
      ProvableCode 𝒩 (formula 𝒩 values ((ObjectLogicalAxiom.localTest C S hSuccessor hPower hInfinity).condition root)) :=
  unary_terms _ (logical h𝒩 C S hSuccessor hPower hInfinity) env values hv hr

theorem node_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {root : SetOpenTerm free} (hr : TermEvaluates env values root) :
    (ReducedProofPresentation.nodeTest.condition root).satisfies env →
      ProvableCode 𝒩 (formula 𝒩 values (ReducedProofPresentation.nodeTest.condition root)) :=
  unary_terms _ (currentNode h𝒩) env values hv hr

theorem row_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {root : SetOpenTerm free} (hr : TermEvaluates env values root) :
    (ReducedProofPresentation.rowTest.condition root).satisfies env →
      ProvableCode 𝒩 (formula 𝒩 values (ReducedProofPresentation.rowTest.condition root)) :=
  unary_terms _ (currentRow h𝒩) env values hv hr

theorem row_named_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root named : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 root named)
    (ht : ReducedProofPresentation.rowTest.condition.body.satisfies (templateEnv (.cons root .nil) : Env 𝒩 [] [.set])) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) ReducedProofPresentation.rowTest.condition.body) :=
  unary_named h𝒩 (currentRow h𝒩) hr hn hg ht

theorem logical_positive_derives {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ) :
    Derives intrinsic_zfc_theory [] (ObjectPositiveReflection.onNaturals ReducedProofPresentation.presentation.graph
      (ObjectLogicalAxiom.localTest C S hSuccessor hPower hInfinity).condition.body) :=
  positive_derives _ (fun _ h𝒩 => logical h𝒩 C S hSuccessor hPower hInfinity)

theorem node_positive_derives : Derives intrinsic_zfc_theory []
    (ObjectPositiveReflection.onNaturals ReducedProofPresentation.presentation.graph ReducedProofPresentation.nodeTest.condition.body) :=
  positive_derives _ (fun _ h𝒩 => currentNode h𝒩)

theorem row_positive_derives : Derives intrinsic_zfc_theory []
    (ObjectPositiveReflection.onNaturals ReducedProofPresentation.presentation.graph ReducedProofPresentation.rowTest.condition.body) :=
  positive_derives _ (fun _ h𝒩 => currentRow h𝒩)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalProofQueryReflection
