import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofTree
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedAxiomNumber
import YesMetaZFC.Automation.ObjectProofNodePresentation

/-! # 原支撑理论上的具体完整证明树 Δ₁ 表示

局部参数已由公式识别、四种语法变换、二十七类逻辑公理、完整等价公理基及
六种节点模式实际构造。最终接口通过任意上下文推导等价回到原支撑理论；
本模块不声称已经把有限支撑基消去为裸 ZFC。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofPresentation
open Nonlogical.BasicSetTheory IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
set_option autoImplicit false
attribute [local irreducible] ReducedAxioms.basis

/-- 已构造的一元 Δ₀ 节点条件及其全自然数正负普通推导。 -/
def nodeTest : ObjectCheckedTrace.LocalTest intrinsic_zfc_theory :=
  ObjectProofNode.localTest intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedAxiomNumber.localTest

theorem nodeTest_checked : nodeTest.checked = ObjectProofNode.checked ReducedAxiomNumber.localTest.checked :=
  ObjectProofNode.localTest_checked intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedAxiomNumber.localTest

private theorem node_sound (code : Nat) (h : nodeTest.checked code = true) :
    ProofTreeCode.localCheck ReducedProofTree.decoder code = true := by
  rw [nodeTest_checked] at h
  apply ObjectProofNode.checked_sound ReducedProofTree.codec ReducedAxiomNumber.localTest.checked _ code h
  intro packet output hPacket
  exact (ReducedAxiomNumber.checked_iff packet output).mp (by simpa using hPacket)

private theorem node_accept {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate ReducedAxioms.axiomPresentation free formula) :
    nodeTest.checked (ProofTreeCode.encode ReducedProofTree.codec proof) = true := by
  rw [nodeTest_checked]
  apply ObjectProofNode.checked_encode ReducedProofTree.codec ReducedAxiomNumber.localTest.checked _ proof
  intro certificate
  rw [ReducedAxiomNumber.localTest_checked_pair]
  exact (ReducedAxiomNumber.checked_iff _ _).mpr ⟨certificate, rfl, rfl⟩

/-- 等价公理基上的完整对象证明关系；不再接收待构造的 LocalTest 参数。 -/
def reduced : Delta1ProofPresentation intrinsic_zfc_theory ReducedAxioms.theory :=
  ObjectProofNode.ofNodeTest ReducedProofTree.codec intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity nodeTest node_sound node_accept

/-- 最终对象证明关系表示原支撑理论的普通 Hilbert 推导。 -/
def presentation : Delta1ProofPresentation intrinsic_zfc_theory intrinsic_zfc_theory :=
  ReducedAxioms.liftProofPresentation reduced

/-- 完整图实际消费的行测试，供任意原模型中的轨迹对应使用。 -/
def rowTest : ObjectCheckedTrace.LocalTest intrinsic_zfc_theory :=
  ObjectProofRow.localTest intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity nodeTest

theorem graph_condition : presentation.graph.condition = ObjectProofTree.template rowTest.condition := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofPresentation
