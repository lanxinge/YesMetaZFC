import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalLocalDecisionReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalSyntaxReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalProjectionReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalTransformReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalSchemaQueries

/-! # 原逻辑公理、证明节点与证明行的内部正反射

二十七类逻辑公理只消费一般语法与四种变换；六类证明节点再加入投影和实际公理查询。
最后保留零码、零标签和其他标签的原行封装，不额外假设输入具有规范外壳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalProofQueryReflection
open Nonlogical.BasicSetTheory InternalPositiveFormula InternalNumeralReflection
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] Positive Evaluates ReducedAxioms.basis ReducedAxiomNumber.entries
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
variable {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
variable (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
variable (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
variable (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
include h𝒩

/-- 原逻辑模式表的所有分支，包括量词、相等与全部命题联结词。 -/
theorem logical :
    Positive 𝒩 (ObjectLogicalAxiom.localTest C S hSuccessor hPower hInfinity).condition.body := by
  apply InternalPositiveFormula.localTest h𝒩
  intro rule hr
  obtain ⟨shape, _, rfl⟩ := List.mem_map.mp hr
  intro query hq
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hq
  cases q.1 with
  | false => exact horn h𝒩 _ (fun _ => syntax_positive h𝒩) (fvar _)
  | true => exact horn h𝒩 _ (fun _ => transform_positive h𝒩) (fvar _)

theorem query (test : ObjectCheckedTrace.LocalTest T) (hTest : Positive 𝒩 test.condition.body)
    (kind : ObjectProofNode.Kind) :
    Positive 𝒩 (ObjectProofNode.queryTest C S hSuccessor hPower hInfinity test kind).condition.body := by
  cases kind with
  | projection => exact horn h𝒩 _ (fun _ => projection_positive h𝒩) (fvar _)
  | «syntax» => exact horn h𝒩 _ (fun _ => syntax_positive h𝒩) (fvar _)
  | transform => exact horn h𝒩 _ (fun _ => transform_positive h𝒩) (fvar _)
  | logical => exact logical h𝒩 C S hSuccessor hPower hInfinity
  | «axiom» => exact hTest

/-- 子证明的局部头部条件全部检查；递归子证明有效性仍由原整树图负责。 -/
theorem node (test : ObjectCheckedTrace.LocalTest T) (hTest : Positive 𝒩 test.condition.body) :
    Positive 𝒩 (ObjectProofNode.localTest C S hSuccessor hPower hInfinity test).condition.body := by
  apply InternalPositiveFormula.localTest h𝒩
  intro rule hr
  obtain ⟨shape, _, rfl⟩ := List.mem_map.mp hr
  intro q hq
  obtain ⟨query, _, rfl⟩ := List.mem_map.mp hq
  exact InternalProofQueryReflection.query h𝒩 C S hSuccessor hPower hInfinity test hTest query.1

theorem row (test : ObjectCheckedTrace.LocalTest T) (hTest : Positive 𝒩 test.condition.body) :
    Positive 𝒩 (ObjectProofRow.localTest C S hSuccessor hPower hInfinity test).condition.body := by
  apply InternalPositiveFormula.localTest h𝒩
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
    · exact horn h𝒩 _ (fun _ => projection_positive h𝒩) (fvar _)
    · exact hTest
  · intro query hq
    cases hq

/-- 当前节点条件的反射，公理参数已由实际 schema／有限表查询消去。 -/
theorem currentNode : Positive 𝒩 ReducedProofPresentation.nodeTest.condition.body :=
  node h𝒩 intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedAxiomNumber.localTest (InternalSchemaReflection.axiomTest h𝒩)

/-- 当前 verifier 实际消费的局部行条件。 -/
theorem currentRow : Positive 𝒩 ReducedProofPresentation.rowTest.condition.body :=
  row h𝒩 intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedProofPresentation.nodeTest (currentNode h𝒩)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalProofQueryReflection
