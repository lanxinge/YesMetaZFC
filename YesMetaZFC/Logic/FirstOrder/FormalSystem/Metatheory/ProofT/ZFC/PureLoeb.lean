import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureProvability

/-! # 裸 ZFC 中的 Löb 定理

原固定点在任意原模型上的对应由可证明性对应及固定点等价推出。
经嵌入往返后，它是纯语言可证明性算子的实际固定点。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProvability
open Nonlogical.BasicSetTheory PureSentenceTransfer
set_option autoImplicit false
attribute [local irreducible] ReducedNaturalProofPresentation.presentation PureRosser.translate

noncomputable def loebSentence_m (φ : Sentence ℒ) : Sentence ℒ :=
  PureRosser.translate (ReducedProvability.loebSentence_m (embed_m φ))

theorem source_fixed_point_agreement_m (φ : Sentence ℒ) :
    PureZFCModels.reduction.Agrees (ReducedProvability.loebSentence_m (embed_m φ))
      (loebSentence_m φ) :=
  agreement_of_iff_m (ReducedProvability.loeb_fixed_point_m (embed_m φ))
    (agreement_imp_m (source_agreement_m _) (embed_agreement_m φ))

theorem loeb_fixed_point_m (φ : Sentence ℒ) :
    Derives PureModel.theory [] (.iff (loebSentence_m φ)
      (.imp (provable_m (loebSentence_m φ)) φ)) := by
  have hFixed := translate_derives_iff_imp_m (ReducedProvability.loeb_fixed_point_m (embed_m φ))
  have hBox : Derives PureModel.theory []
      (.iff (PureRosser.translate (ReducedProvability.provable
        (ReducedProvability.loebSentence_m (embed_m φ)))) (provable_m (loebSentence_m φ))) :=
    translate_derives_iff_m (ReducedProvability.derivability_m.iff_m
      (embed_translate_m (source_fixed_point_agreement_m φ)))
  apply Completeness.strong_completeness PureRosserSchedule.target
  intro ℳ hℳ
  exact (hFixed.semantically_entails ℳ hℳ).trans
    (imp_congr (hBox.semantically_entails ℳ hℳ)
      ((translate_embed_m φ).semantically_entails ℳ hℳ))

/-- 裸 ZFC 的内部 Löb 公式。 -/
theorem loeb_axiom_m (φ : Sentence ℒ) :
    Derives PureModel.theory []
      (.imp (provable_m (.imp (provable_m φ) φ)) (provable_m φ)) :=
  derivability_m.loeb_axiom_m φ (loebSentence_m φ) (loeb_fixed_point_m φ)

/-- 裸 ZFC 若证明自身对纯句子 φ 的反射，便证明 φ。 -/
theorem loeb_m (φ : Sentence ℒ)
    (h : Derives PureModel.theory [] (.imp (provable_m φ) φ)) :
    Derives PureModel.theory [] φ :=
  derivability_m.loeb_m φ (loebSentence_m φ) (loeb_fixed_point_m φ) h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProvability
