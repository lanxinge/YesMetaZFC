import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Provability
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedNaturalProofPresentation

/-! # 当前 ZFC 证明图上的普通可证明性

使用已有的内部自然数证明码约束和完整证明图；这不是 Rosser 比较谓词。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
open Nonlogical.BasicSetTheory
set_option autoImplicit false
attribute [local irreducible] ReducedNaturalProofPresentation.presentation

noncomputable def provable (formula : SetSentence) : SetSentence :=
  ReducedNaturalProofPresentation.presentation.provable formula

noncomputable def consistency : SetSentence :=
  ReducedNaturalProofPresentation.presentation.consistency

theorem provable_sigma1 (formula : SetSentence) :
    Formula.IsSigma1 set_levy_bound (provable formula) :=
  ReducedNaturalProofPresentation.presentation.provable_sigma1 formula

theorem consistency_pi1 : Formula.IsPi1 set_levy_bound consistency :=
  ReducedNaturalProofPresentation.presentation.consistency_pi1

/-- 当前完整源理论的第一可导性条件。 -/
theorem necessitation {formula : SetSentence}
    (hDerives : Derives intrinsic_zfc_theory [] formula) :
    Derives intrinsic_zfc_theory [] (provable formula) :=
  ReducedNaturalProofPresentation.presentation.necessitation hDerives

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
