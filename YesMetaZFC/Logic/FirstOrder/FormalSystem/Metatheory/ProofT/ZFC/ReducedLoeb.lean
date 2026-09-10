import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Loeb
import YesMetaZFC.Automation.ObjectLoebFixedPoint
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedIntrospection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedRosser

/-! # 当前原可证明性谓词的 Löb 定理

固定点由原对角构造给出；内部公式和条件性 Löb 规则共用同一可证明性谓词。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedNaturalProofPresentation.presentation

theorem derivability_m : DerivabilityConditions_m intrinsic_zfc_theory provable :=
  ⟨necessitation, distribution, introspection⟩

noncomputable def loebSentence_m (φ : SetSentence) : SetSentence :=
  ObjectLoeb.fixedPoint_m intrinsic_zfc_core.code_domain
    ReducedNaturalProofPresentation.presentation.graph φ

theorem loeb_fixed_point_m (φ : SetSentence) :
    Derives intrinsic_zfc_theory [] (loebSentence_m φ ↔ₘ (provable (loebSentence_m φ) ⟶ₘ φ)) :=
  ObjectLoeb.fixed_point_m ReducedRosser.diagonalSupport
    ReducedNaturalProofPresentation.presentation.graph φ

/-- 内部 Löb 公式：□(□φ → φ) → □φ。 -/
theorem loeb_axiom_m (φ : SetSentence) :
    Derives intrinsic_zfc_theory [] (provable (provable φ ⟶ₘ φ) ⟶ₘ provable φ) :=
  derivability_m.loeb_axiom_m φ (loebSentence_m φ) (loeb_fixed_point_m φ)

/-- Löb 规则：原理论若证明其对 φ 的反射，原理论就证明 φ。 -/
theorem loeb_m (φ : SetSentence)
    (h : Derives intrinsic_zfc_theory [] (provable φ ⟶ₘ φ)) :
    Derives intrinsic_zfc_theory [] φ :=
  derivability_m.loeb_m φ (loebSentence_m φ) (loeb_fixed_point_m φ) h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
