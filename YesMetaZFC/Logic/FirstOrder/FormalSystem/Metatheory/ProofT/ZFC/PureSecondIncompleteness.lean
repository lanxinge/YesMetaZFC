import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SecondIncompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureLoeb

/-! # 裸 ZFC 的哥德尔第二不完备定理

一致性句子为纯语言中的 ¬□⊥；□ 使用嵌入后的原 quotation 与检查器。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProvability
open Nonlogical.BasicSetTheory PureSentenceTransfer
set_option autoImplicit false
attribute [local irreducible] ReducedNaturalProofPresentation.presentation PureRosser.translate

/-- 此纯一致性句子正是已有原一致性句子的消元翻译。 -/
theorem consistency_translation_m :
    consistency_m = PureRosser.translate ReducedProvability.consistency :=
  (translate_neg_m (ReducedProvability.provable .falsum)).symm

/-- 裸 ZFC 证明：若自身一致，就不存在自身一致性的内部证明码。 -/
theorem second_incompleteness_internal_m :
    Derives PureModel.theory [] (.imp consistency_m (.neg (provable_m consistency_m))) :=
  derivability_m.second_incompleteness_internal_m
    (loebSentence_m .falsum) (loeb_fixed_point_m .falsum)

/-- 只假定裸 ZFC 一致，裸 ZFC 便不能证明此一致性句子。 -/
theorem second_incompleteness_m
    (hT : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    ¬ Derives PureModel.theory [] consistency_m :=
  derivability_m.second_incompleteness_m
    (loebSentence_m .falsum) (loeb_fixed_point_m .falsum) hT

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProvability
