import YesMetaZFC.Model.ZFC.Pure.PureSupportModels
import YesMetaZFC.Model.ZFC.Pure.PureProjectEmbedding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosserTransfer

/-! # 完整原 ZFC 支撑理论的扩张与纯约化

两边的模型保持均由实际公理验证给出。指定 Rosser 句子的真值对应仍是独立义务。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureZFCModels
open PureModel Nonlogical.BasicSetTheory QuineEncoding PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

/-- 最终扩张的约化仍是原隶属模型，故保留全部原 ZFC 公理模式。 -/
theorem reduced_expansion_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (PureProjectEmbedding.reduct (E hℳ).model) theory :=
  (Project.FirstOrderSemantics.models_iff
    (ℳ := PureProjectEmbedding.reduct (E hℳ).model) (project_models (M := ℳ) hℳ).1 _).mpr (project_models (M := ℳ) hℳ)

theorem base_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model intrinsic_zfc_axiom_theory := by
  rintro formula ⟨sentence, hSentence, rfl⟩
  apply (PureProjectEmbedding.sentence_correct (fun left right => PureFinalBasic.subset_value hℳ left right) sentence).mp
  exact reduced_expansion_models hℳ _ ⟨sentence, hSentence, rfl⟩

/-- 整个原理论的统一验证入口，包括原 ZFC 公理像和全部支撑公理。 -/
theorem models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model intrinsic_zfc_theory := by
  intro formula hFormula
  rcases hFormula with h | h
  · exact base_models hℳ formula h
  · exact PureSupportModels.support_models hℳ formula h

/-- 原理论全部公理的实际纯翻译，在任意裸 ZFC 模型中成立。 -/
theorem translated_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models ℳ (_root_.YesMetaZFC.Automation.RelationalTranslation.theory
      PureCompletedStage.interpretation intrinsic_zfc_theory) :=
  (_root_.YesMetaZFC.Automation.RelationalTranslation.models_iff
    (PureCompletedStage.functional hℳ) intrinsic_zfc_theory).mpr (models hℳ)

/-- 任意原理论模型中的子集符号都满足其原定义。 -/
theorem source_subset {𝒩 : Structure.{0,0,0,x} signature}
    (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (left right : 𝒩.Carrier SetSort.set) :
    𝒩.relInterp .subset (.cons left (.cons right .nil)) ↔
      ∀ element, 𝒩.relInterp .membership (.cons element (.cons left .nil)) →
        𝒩.relInterp .membership (.cons element (.cons right .nil)) := by
  have hAxiom : subset_definition_axiom.satisfies (Env.empty : Env 𝒩 [] []) :=
    h𝒩 _ (intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      (subset_theory_subset_intrinsic_syntax_carrier_theory (Or.inl rfl)))
  have hOpen := (forall_close_iff _).mp hAxiom (templateEnv (.cons right (.cons left .nil)))
  change (𝒩.relInterp .subset (.cons left (.cons right .nil)) ↔
    (subset_condition (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons right (.cons left .nil)) : Env 𝒩 [] [SetSort.set,SetSort.set])) at hOpen
  exact hOpen.trans (PureFinalBasic.subset_semantics 𝒩 left right)

/-- 原理论的任意模型约化后满足裸 ZFC，不要求它是规范扩张。 -/
theorem reduct_models {𝒩 : Structure.{0,0,0,x} signature}
    (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    Theory.Models (PureProjectEmbedding.reduct 𝒩) theory := by
  rintro formula ⟨sentence, hSentence, rfl⟩
  exact (PureProjectEmbedding.sentence_correct (source_subset h𝒩) sentence).mpr
    (h𝒩 _ (intrinsic_zfc_axiom_mem hSentence))

theorem expands : _root_.YesMetaZFC.Automation.SemanticTransfer.Expands intrinsic_zfc_theory theory :=
  fun _ hℳ => ⟨(E hℳ).model, models hℳ⟩

def reduction : _root_.YesMetaZFC.Automation.SemanticTransfer.Reduction intrinsic_zfc_theory theory where
  model := PureProjectEmbedding.reduct
  models _ hℳ := reduct_models hℳ

/-- 模型扩张这一侧已无待填参数；真值对应仍须针对指定句子证明。 -/
def contract {target : Sentence ℒ} (hAgrees : reduction.Agrees ReducedRosser.sentence target) :
    PureRosserTransfer.Contract target where
  expands := expands
  reduction := reduction
  agrees := hAgrees

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureZFCModels
