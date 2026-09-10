import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProvability
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProvabilitySemantics

/-! # 当前普通可证明性的第二可导性条件

先在任意源模型中构造内部 MP 证明码，再由既有强完备性导出普通 Hilbert 推导。
结论只使用当前自然数证明图，不增加可导性条件作为假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
open Nonlogical.BasicSetTheory PureFinalArithmetic PureNaturalRosserAgreement
open _root_.YesMetaZFC.Automation
open NaturalRosserSemantics hiding mem
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x

theorem provable_satisfies {𝒩 : Structure.{0,0,0,x} signature} (formula : SetSentence) :
    (provable formula).TrueIn 𝒩 ↔ ∃ code, mem 𝒩 code (w 𝒩) ∧ Proof 𝒩 code formula := by
  change ((NaturalProofPresentation.graph ReducedProofPresentation.presentation.graph).provability
    (IntrinsicQuotation.quote formula)).satisfies (Env.empty : Env 𝒩 [] []) ↔ _
  rw [Delta0ProofGraph.provability_satisfies]
  apply exists_congr
  intro code
  exact natural_graph_satisfies (𝒩 := 𝒩) ReducedProofPresentation.presentation.graph code _

/-- D2：实际普通可证明性在理论内部保持蕴涵。 -/
theorem distribution (φ ψ : SetSentence) :
    Derives intrinsic_zfc_theory []
      (Formula.imp (provable (Formula.imp φ ψ)) (Formula.imp (provable φ) (provable ψ))) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  change (provable (Formula.imp φ ψ)).TrueIn 𝒩 → (provable φ).TrueIn 𝒩 → (provable ψ).TrueIn 𝒩
  intro hImplication hPremise
  obtain ⟨implication, hi, hImplication⟩ := (provable_satisfies _).mp hImplication
  obtain ⟨premise, hp, hPremise⟩ := (provable_satisfies _).mp hPremise
  exact (provable_satisfies ψ).mpr ⟨ReducedProofLocalConstruction.mpCode 𝒩 premise implication ψ,
    ReducedProofComposition.modus_ponens h𝒩 φ ψ hp hi hPremise hImplication⟩

/-- 联合 D1、D2，把已有蕴涵推导提升为可证明性之间的蕴涵。 -/
theorem preserves_implication {φ ψ : SetSentence}
    (h : Derives intrinsic_zfc_theory [] (Formula.imp φ ψ)) :
    Derives intrinsic_zfc_theory [] (Formula.imp (provable φ) (provable ψ)) :=
  Derives.imp_elim (distribution φ ψ) (necessitation h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
