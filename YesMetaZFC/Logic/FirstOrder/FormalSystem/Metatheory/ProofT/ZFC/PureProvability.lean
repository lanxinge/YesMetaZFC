import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSentenceTransfer
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceLocalTests
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedLoeb

/-! # 裸 ZFC 中由原编码表示的普通可证明性

先嵌入纯句子，再使用原完整证明图及 quotation，最后消去支撑语言。
检查器保持原证书格式；双向推导证明它也恰好表示纯理论的可推导性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProvability
open Nonlogical.BasicSetTheory PureSentenceTransfer PureSourceNumerals
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct
attribute [local irreducible] ReducedProofPresentation.presentation
attribute [local irreducible] ReducedNaturalProofPresentation.presentation
attribute [local irreducible] PureRosser.translate
universe x

noncomputable def provable_m (φ : Sentence ℒ) : Sentence ℒ :=
  PureRosser.translate (ReducedProvability.provable (embed_m φ))

noncomputable def consistency_m : Sentence ℒ := .neg (provable_m .falsum)

/-- 任意原模型及其规范重扩张在全部内部证明码上给出同一可证明性真值。 -/
theorem source_canonical_m {𝒩 : Structure.{0,0,0,x} signature}
    (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (φ : SetSentence) :
    (ReducedProvability.provable φ).TrueIn 𝒩 ↔
      (ReducedProvability.provable φ).TrueIn (canonical h𝒩) := by
  unfold ReducedProvability.provable Delta1ProofPresentation.provable
    ReducedNaturalProofPresentation.presentation NaturalProofPresentation.presentation
  have h := PureSourceLocalTests.provableCode_agreement h𝒩
    (PureSourceCoding.quotation_natural h𝒩 φ)
  exact (ReducedProofCodeSemantics.provableCode_satisfies
    (Env.empty : Env 𝒩 [] []) (IntrinsicQuotation.quote φ)).trans
    (h.trans ((Iff.of_eq (congrArg (ReducedProofCodeSemantics.ProvableCode (canonical h𝒩))
      (quotation_agrees h𝒩 φ))).trans
      (ReducedProofCodeSemantics.provableCode_satisfies
        (Env.empty : Env (canonical h𝒩) [] []) (IntrinsicQuotation.quote φ)).symm))

theorem source_agreement_m (φ : SetSentence) :
    PureZFCModels.reduction.Agrees (ReducedProvability.provable φ)
      (PureRosser.translate (ReducedProvability.provable φ)) := by
  intro 𝒩 h𝒩
  exact (PureRosser.translate_truth_iff (PureZFCModels.reduct_models h𝒩)
    (ReducedProvability.provable φ)).trans (source_canonical_m h𝒩 φ).symm

theorem source_roundtrip_m (φ : SetSentence) :
    Derives intrinsic_zfc_theory [] (.iff (ReducedProvability.provable φ)
      (embed_m (PureRosser.translate (ReducedProvability.provable φ)))) :=
  embed_translate_m (source_agreement_m φ)

/-- 原检查器接受某个嵌入句子证书，当且仅当裸 ZFC 能推导该纯句子。 -/
theorem checked_iff_m (φ : Sentence ℒ) :
    (∃ p, ReducedNaturalProofPresentation.presentation.checked p (embed_m φ) = true) ↔
      Derives PureModel.theory [] φ := by
  constructor
  · rintro ⟨p, h⟩
    exact (derives_iff_m φ).mp (ReducedNaturalProofPresentation.presentation.checked_sound h)
  · intro h
    exact ReducedNaturalProofPresentation.presentation.checked_complete (embed_derives_m h)

theorem necessitation_m {φ : Sentence ℒ} (h : Derives PureModel.theory [] φ) :
    Derives PureModel.theory [] (provable_m φ) :=
  PureRosser.translate_derives (ReducedProvability.necessitation (embed_derives_m h))

theorem distribution_m (φ ψ : Sentence ℒ) :
    Derives PureModel.theory [] (.imp (provable_m (.imp φ ψ))
      (.imp (provable_m φ) (provable_m ψ))) :=
  translate_derives_imp_imp_m (ReducedProvability.distribution (embed_m φ) (embed_m ψ))

theorem introspection_m (φ : Sentence ℒ) :
    Derives PureModel.theory [] (.imp (provable_m φ) (provable_m (provable_m φ))) := by
  have h : Derives intrinsic_zfc_theory []
      (.imp (ReducedProvability.provable (embed_m φ)) (embed_m (provable_m φ))) :=
    Derives.imp_elim (Derives.logical_axiom (.biconditional_elim_left _ _))
      (source_roundtrip_m (embed_m φ))
  exact translate_derives_imp_m
    (Derives.imp_trans (ReducedProvability.introspection (embed_m φ))
      (ReducedProvability.derivability_m.imp_m h))

theorem derivability_m : DerivabilityConditions_m PureModel.theory provable_m :=
  ⟨necessitation_m, distribution_m, introspection_m⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProvability
