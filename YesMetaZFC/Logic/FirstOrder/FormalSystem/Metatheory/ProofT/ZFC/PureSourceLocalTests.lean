import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceSchemas
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofCodeSemantics

/-! # 当前节点、局部行与完整证明图的对应

复用实际规则表。所有自然数输入都在范围内，包括非标准证明码；
没有把标准正负实例提升为未经证明的反射原则。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceLocalTests
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceHorn
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
variable {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
variable (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
variable (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
variable (hInfinity : ∀ {φ}, infinity_theory φ → T φ)

theorem logical : UnaryAgreement h𝒩 (ObjectLogicalAxiom.localTest C S hSuccessor hPower hInfinity).condition := by
  apply PureSourceHorn.localTest
  intro rule hr
  obtain ⟨shape, _, rfl⟩ := List.mem_map.mp hr
  intro query hq
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hq
  cases q.1 with
  | false => exact horn_localTest h𝒩 C S hPower hInfinity ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank ObjectFormulaSyntax.descending
  | true => exact horn_localTest h𝒩 C S hPower hInfinity ObjectSyntaxTransform.rules ObjectSyntaxTransform.rank ObjectSyntaxTransform.descending

theorem query (test : ObjectCheckedTrace.LocalTest T) (hTest : UnaryAgreement h𝒩 test.condition)
    (kind : ObjectProofNode.Kind) :
    UnaryAgreement h𝒩 (ObjectProofNode.queryTest C S hSuccessor hPower hInfinity test kind).condition := by
  cases kind with
  | projection => exact horn_localTest h𝒩 C S hPower hInfinity ObjectProjection.rules ObjectProjection.rank ObjectProjection.descending
  | «syntax» => exact horn_localTest h𝒩 C S hPower hInfinity ObjectFormulaSyntax.rules ObjectFormulaSyntax.rank ObjectFormulaSyntax.descending
  | transform => exact horn_localTest h𝒩 C S hPower hInfinity ObjectSyntaxTransform.rules ObjectSyntaxTransform.rank ObjectSyntaxTransform.descending
  | logical => exact logical h𝒩 C S hSuccessor hPower hInfinity
  | «axiom» => exact hTest

theorem node (test : ObjectCheckedTrace.LocalTest T) (hTest : UnaryAgreement h𝒩 test.condition) :
    UnaryAgreement h𝒩 (ObjectProofNode.localTest C S hSuccessor hPower hInfinity test).condition := by
  apply PureSourceHorn.localTest
  intro rule hr
  obtain ⟨shape, _, rfl⟩ := List.mem_map.mp hr
  intro q hq
  obtain ⟨query, _, rfl⟩ := List.mem_map.mp hq
  exact PureSourceLocalTests.query h𝒩 C S hSuccessor hPower hInfinity test hTest query.1

theorem row (test : ObjectCheckedTrace.LocalTest T) (hTest : UnaryAgreement h𝒩 test.condition) :
    UnaryAgreement h𝒩 (ObjectProofRow.localTest C S hSuccessor hPower hInfinity test).condition := by
  apply PureSourceHorn.localTest
  intro rule hr
  simp only [ObjectProofRow.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · intro query hq
    simp only [ObjectProofRow.zeroRule, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst query
    exact hTest
  · intro query hq
    simp only [ObjectProofRow.zeroTagRule, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact horn_localTest h𝒩 C S hPower hInfinity ObjectProjection.rules ObjectProjection.rank ObjectProjection.descending
    · exact hTest
  · intro query hq
    cases hq

theorem currentNode : UnaryAgreement h𝒩 ReducedProofPresentation.nodeTest.condition :=
  node h𝒩 intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedAxiomNumber.localTest PureSourceSchemas.axiomTest

theorem currentRow : UnaryAgreement h𝒩 ReducedProofPresentation.rowTest.condition :=
  row h𝒩 intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedProofPresentation.nodeTest (currentNode h𝒩)

/-- 实际整树轨迹的行正文：Horn 连边及当前局部检查同时保持。 -/
theorem row_agrees {value : 𝒩.Carrier .set} (hValue : mem 𝒩 value (w 𝒩)) (trace : 𝒩.Carrier .set) :
    PureNaturalRosserAgreement.Row 𝒩 value trace ↔ PureNaturalRosserAgreement.Row (canonical h𝒩) value trace := by
  unfold PureNaturalRosserAgreement.Row ObjectCheckedTrace.step
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr (step_agrees h𝒩 _ hValue trace)
  rw [NaturalRosserSemantics.unary_satisfies, NaturalRosserSemantics.unary_satisfies]
  exact currentRow h𝒩 value hValue

/-- 结论码也可非标准；为内部证明构造的可分离性质提供最终阶段对应。 -/
theorem codeProof_agreement {code conclusion : 𝒩.Carrier .set}
    (hCode : mem 𝒩 code (w 𝒩)) (hConclusion : mem 𝒩 conclusion (w 𝒩)) :
    ReducedProofCodeSemantics.CodeProof 𝒩 code conclusion ↔
      ReducedProofCodeSemantics.CodeProof (canonical h𝒩) code conclusion := by
  unfold ReducedProofCodeSemantics.CodeProof
  rw [ReducedProofPresentation.graph_condition]
  apply PureSourceBounds.trace_agrees h𝒩
  · simp only [PureSourceCoding.node_eval, List.map_cons, List.map_nil]
    change PureSourceCoding.node 𝒩 1 [code, conclusion] = PureSourceCoding.node (canonical h𝒩) 1 [code, conclusion]
    exact PureSourceCoding.node_agrees h𝒩 1 (by simp [hCode, hConclusion])
  · intro trace _ row _ hRow
    exact row_agrees h𝒩 hRow trace

theorem provableCode_agreement {conclusion : 𝒩.Carrier .set}
    (hConclusion : mem 𝒩 conclusion (w 𝒩)) :
    ReducedProofCodeSemantics.ProvableCode 𝒩 conclusion ↔
      ReducedProofCodeSemantics.ProvableCode (canonical h𝒩) conclusion := by
  apply exists_congr
  intro proof
  change (mem 𝒩 proof (w 𝒩) ∧ _) ↔ (mem 𝒩 proof (w (canonical h𝒩)) ∧ _)
  rw [← PureSourceInfinity.omega_agrees h𝒩]
  exact and_congr_right (fun hProof => codeProof_agreement h𝒩 hProof hConclusion)

/-- 任意固定结论的完整证明关系，在全部内部自然数证明码上对应。 -/
theorem proof_agreement (formula : SetSentence) : PureNaturalRosserAgreement.ProofAgreement h𝒩 formula := by
  apply PureNaturalRosserAgreement.proof_agreement_of_rows h𝒩 formula
  intro trace _ row _ hRow
  exact row_agrees h𝒩 hRow trace

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceLocalTests
