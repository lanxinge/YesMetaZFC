import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SecondIncompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedLoeb

/-! # 当前原理论的哥德尔第二不完备定理

使用已有一致性句子、普通证明图、quotation 和实际 Löb 固定点。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedNaturalProofPresentation.presentation

/-- 原理论证明：若自身一致，就不存在自身一致性的内部证明码。 -/
theorem second_incompleteness_internal_m :
    Derives intrinsic_zfc_theory [] (consistency ⟶ₘ ¬ₘ provable consistency) :=
  derivability_m.second_incompleteness_internal_m
    (loebSentence_m .falsum) (loeb_fixed_point_m .falsum)

/-- 只假定原理论一致，原理论便不能证明已有的一致性句子。 -/
theorem second_incompleteness_m
    (hT : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    ¬ Derives intrinsic_zfc_theory [] consistency :=
  derivability_m.second_incompleteness_m
    (loebSentence_m .falsum) (loeb_fixed_point_m .falsum) hT

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
