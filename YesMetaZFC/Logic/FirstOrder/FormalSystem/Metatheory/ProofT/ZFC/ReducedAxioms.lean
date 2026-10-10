import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportAxiomBasis
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.BaseAxiomPacketSpec
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteAxioms

/-! # 与原支撑理论推导等价的完整公理对象表示

基础 ZFC 公理像不变；支撑部分以原公理中的有限闭模板为基。
公理集合不同，但任意上下文中的普通推导完全等价。对象表示的目标明确写为
theory；完整证明表示构成后由 liftProofPresentation 直接回到原 intrinsic_zfc_theory。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedAxioms
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.Automation
set_option autoImplicit false

def basis : FiniteAxiomBasis intrinsic_proof_theory := SupportAxiomBasis.intrinsic_proof.compact

def theory : SetTheory := Theory.union intrinsic_zfc_axiom_theory basis.theory

/-- 基础公理包保留原格式；标签 10 的有限索引包供支撑闭模板使用。 -/
def key (index : Nat) : Nat := NatPacket.encode (.node 10 [leaf index])

theorem subset {φ : SetSentence} (h : theory φ) : intrinsic_zfc_theory φ := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (basis.sound φ h)

/-- 原理论的所有参数公理都在有限基中回放，不只是已列出的模板本身。 -/
theorem axiom_derives {φ : SetSentence} (h : intrinsic_zfc_theory φ) : Derives theory [] φ := by
  rcases h with h | h
  · exact FirstOrder.Derives.theory_axiom (Or.inl h)
  · exact (basis.complete h).theory_weaken (fun h => Or.inr h)

theorem derives_iff {free : SetContext} {Γ : Context signature free} {φ : SetOpenFormula free} :
    Derives theory Γ φ ↔ Derives intrinsic_zfc_theory Γ φ :=
  ⟨fun h => h.theory_weaken subset, fun h => FirstOrder.Derives.theory_cut axiom_derives h⟩

def axiomPresentation : AxiomPresentation theory :=
  AxiomPresentation.union intrinsic_zfc_base_axiom_presentation
    (ObjectFiniteAxioms.certificates basis.axioms)

/-- 全部公理基的固定二元 Delta0 公式、实际检查及正负推导。 -/
def presentation : Delta1AxiomPresentation intrinsic_zfc_theory theory :=
  BaseAxiomPacket.presentation.union
    (ObjectFiniteAxioms.presentation intrinsic_zfc_certificate_core basis.axioms key)

/-- 将基理论的完整证明表示沿已证明的推导等价传回原支撑理论。 -/
def liftProofPresentation (P : Delta1ProofPresentation intrinsic_zfc_theory theory) :
    Delta1ProofPresentation intrinsic_zfc_theory intrinsic_zfc_theory where
  graph := P.graph
  checked := P.checked
  checked_sound h := derives_iff.mp (P.checked_sound h)
  checked_complete h := P.checked_complete (derives_iff.mpr h)
  condition_positive := P.condition_positive
  condition_negative := P.condition_negative

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedAxioms
