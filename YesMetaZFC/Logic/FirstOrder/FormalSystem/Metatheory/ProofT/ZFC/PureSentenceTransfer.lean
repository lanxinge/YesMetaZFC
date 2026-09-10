import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosser

/-! # 纯句子的嵌入及双向推导传输

复用关系翻译的全部 binder 与语义接口；纯隶属语言嵌入原支撑语言。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSentenceTransfer
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x

def inclusion_m : Interpretation ℒ signature where
  sort _ := .set
  function f := nomatch f
  relation _ := .rel .membership (.cons (.fvar .here) (.cons (.fvar (.there .here)) .nil))

def embed_m (φ : Sentence ℒ) : SetSentence := sentence inclusion_m φ

theorem embed_imp_m (φ ψ : Sentence ℒ) :
    embed_m (.imp φ ψ) = .imp (embed_m φ) (embed_m ψ) := rfl

theorem translate_imp_m (φ ψ : SetSentence) :
    PureRosser.translate (.imp φ ψ) = .imp (PureRosser.translate φ) (PureRosser.translate ψ) := rfl

theorem translate_iff_m (φ ψ : SetSentence) :
    PureRosser.translate (.iff φ ψ) = .iff (PureRosser.translate φ) (PureRosser.translate ψ) := rfl

theorem translate_neg_m (φ : SetSentence) :
    PureRosser.translate (.neg φ) = .neg (PureRosser.translate φ) := rfl

/-- 在抽象公式上先固定逻辑外壳，避免实例层展开检查器正文。 -/
theorem translate_derives_imp_m {φ ψ : SetSentence}
    (h : Derives intrinsic_zfc_theory [] (.imp φ ψ)) :
    Derives PureModel.theory [] (.imp (PureRosser.translate φ) (PureRosser.translate ψ)) :=
  PureRosser.translate_derives h

theorem translate_derives_imp_imp_m {φ ψ χ : SetSentence}
    (h : Derives intrinsic_zfc_theory [] (.imp φ (.imp ψ χ))) :
    Derives PureModel.theory [] (.imp (PureRosser.translate φ)
      (.imp (PureRosser.translate ψ) (PureRosser.translate χ))) :=
  PureRosser.translate_derives h

theorem translate_derives_iff_m {φ ψ : SetSentence}
    (h : Derives intrinsic_zfc_theory [] (.iff φ ψ)) :
    Derives PureModel.theory [] (.iff (PureRosser.translate φ) (PureRosser.translate ψ)) :=
  PureRosser.translate_derives h

theorem translate_derives_iff_imp_m {φ ψ χ : SetSentence}
    (h : Derives intrinsic_zfc_theory [] (.iff φ (.imp ψ χ))) :
    Derives PureModel.theory [] (.iff (PureRosser.translate φ)
      (.imp (PureRosser.translate ψ) (PureRosser.translate χ))) :=
  PureRosser.translate_derives h

def reductExpansion_m (𝒩 : Structure.{0,0,0,x} signature) : Expansion inclusion_m 𝒩 where
  function f := nomatch f
  relation := (PureProjectEmbedding.reduct 𝒩).relInterp

theorem reduct_realizes_m (𝒩 : Structure.{0,0,0,x} signature) :
    Realizes (reductExpansion_m 𝒩) where
  function f := nomatch f
  relation r a := by
    cases r
    cases a with | cons a b =>
    cases b with | cons b c =>
    cases c
    rfl

theorem embed_truth_m (𝒩 : Structure.{0,0,0,x} signature) (φ : Sentence ℒ) :
    (embed_m φ).TrueIn 𝒩 ↔ φ.TrueIn (PureProjectEmbedding.reduct 𝒩) :=
  sentence_correct (reductExpansion_m 𝒩) (reduct_realizes_m 𝒩) φ

theorem reduct_expansion_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) :
    PureProjectEmbedding.reduct (PureCompletedStage.expansion hℳ).model = ℳ := by
  cases ℳ with
  | mk C hn f r =>
    change Structure.mk (fun _ => C .set) _ _ _ = Structure.mk C hn f r
    congr 1
    · funext s
      cases s
    · funext s a
      cases s
      cases a with | cons a b =>
      cases b with | cons b c =>
      cases c
      rfl

theorem translate_embed_m (φ : Sentence ℒ) :
    Derives PureModel.theory [] (.iff (PureRosser.translate (embed_m φ)) φ) := by
  apply Completeness.strong_completeness PureRosserSchedule.target
  intro ℳ hℳ
  exact (PureRosser.translate_truth_iff hℳ (embed_m φ)).trans
    ((embed_truth_m (PureCompletedStage.expansion hℳ).model φ).trans
      (by rw [reduct_expansion_m hℳ]; rfl))

theorem embed_derives_m {φ : Sentence ℒ} (h : Derives PureModel.theory [] φ) :
    Derives intrinsic_zfc_theory [] (embed_m φ) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  exact (embed_truth_m 𝒩 φ).mpr
    (h.semantically_entails _ (PureZFCModels.reduct_models h𝒩))

theorem derives_iff_m (φ : Sentence ℒ) :
    Derives intrinsic_zfc_theory [] (embed_m φ) ↔ Derives PureModel.theory [] φ :=
  ⟨fun h => Derives.iff_elim_left (translate_embed_m φ) (PureRosser.translate_derives h),
    embed_derives_m⟩

/-- 反向往返只用于已证明任意原模型对应的指定句子。 -/
theorem embed_translate_m {φ : SetSentence}
    (h : PureZFCModels.reduction.Agrees φ (PureRosser.translate φ)) :
    Derives intrinsic_zfc_theory [] (.iff φ (embed_m (PureRosser.translate φ))) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  exact (h 𝒩 h𝒩).symm.trans (embed_truth_m 𝒩 (PureRosser.translate φ)).symm

theorem embed_agreement_m (φ : Sentence ℒ) :
    PureZFCModels.reduction.Agrees (embed_m φ) (PureRosser.translate (embed_m φ)) := by
  intro 𝒩 h𝒩
  exact ((translate_embed_m φ).semantically_entails _ (PureZFCModels.reduct_models h𝒩)).trans
    (embed_truth_m 𝒩 φ).symm

theorem agreement_imp_m {φ ψ : SetSentence}
    (hφ : PureZFCModels.reduction.Agrees φ (PureRosser.translate φ))
    (hψ : PureZFCModels.reduction.Agrees ψ (PureRosser.translate ψ)) :
    PureZFCModels.reduction.Agrees (.imp φ ψ) (PureRosser.translate (.imp φ ψ)) :=
  fun 𝒩 h𝒩 => imp_congr (hφ 𝒩 h𝒩) (hψ 𝒩 h𝒩)

theorem agreement_of_iff_m {φ ψ : SetSentence}
    (h : Derives intrinsic_zfc_theory [] (.iff φ ψ))
    (hψ : PureZFCModels.reduction.Agrees ψ (PureRosser.translate ψ)) :
    PureZFCModels.reduction.Agrees φ (PureRosser.translate φ) := by
  intro 𝒩 h𝒩
  exact ((PureRosser.translate_derives h).semantically_entails _
    (PureZFCModels.reduct_models h𝒩)).trans
    ((hψ 𝒩 h𝒩).trans (h.semantically_entails 𝒩 h𝒩).symm)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSentenceTransfer
