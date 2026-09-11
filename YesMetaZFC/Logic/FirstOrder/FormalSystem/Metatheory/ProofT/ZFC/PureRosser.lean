import YesMetaZFC.Model.ZFC.Pure.PureZFCModels
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosserSchedule

/-! # 当前完整证明树 Rosser 句子的纯隶属配置

句子和比较式固定使用最终解释及内部自然数证明图，不接受外部目标公式。纯固定点有裸 ZFC 的实际
Hilbert 推导，两套公平调度也已给出。比较式仍表示原证明树及原 quotation，不能
把翻译后的固定点误称为对纯语言自身 quotation 重新对角化的结果。

任意原模型约化前后的句子真值对应由 `Agreement` 明确列出；规范扩张中的
`truth_iff` 不充当这个证明。`agreement_iff_comparison` 将其归约到比较式，
具体证明与只假定一致性的终局见 `PureRosserComplete`。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosser
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
set_option maxRecDepth 4096
attribute [local irreducible] ReducedRosser.presentation ReducedRosser.sentence
universe x

/-- 保留公式的定义式供内核验证，不在模块初始化时展开巨大 quotation。 -/
noncomputable def translate (source : SetSentence) : Sentence ℒ :=
  RelationalTranslation.sentence PureCompletedStage.interpretation source

/-- 当前 Rosser 固定点的实际纯隶属闭句。 -/
noncomputable def sentence : Sentence ℒ := translate ReducedRosser.sentence

/-- 原证明树上的 Rosser 比较式，结论码固定为当前源句子的 quotation。 -/
noncomputable def comparison : Sentence ℒ :=
  translate (ReducedRosser.presentation.predicate_of ReducedRosser.sentence)

/-- 规范扩张中的源真值与实际纯翻译真值一致。 -/
theorem translate_truth_iff {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) (source : SetSentence) :
    (translate source).TrueIn ℳ ↔ source.TrueIn (PureCompletedStage.expansion hℳ).model :=
  RelationalTranslation.sentence_correct
    (PureCompletedStage.expansion hℳ) (PureCompletedStage.realizes hℳ) source

theorem truth_iff {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) :
    sentence.TrueIn ℳ ↔ ReducedRosser.sentence.TrueIn (PureCompletedStage.expansion hℳ).model :=
  translate_truth_iff hℳ ReducedRosser.sentence

/-- 完整公理验证与固定公平调度给出源推导的实际纯 Hilbert 推导。 -/
theorem translate_derives {source : SetSentence}
    (hDerives : Derives intrinsic_zfc_theory [] source) :
    Derives PureModel.theory [] (translate source) := by
  apply Completeness.strong_completeness PureRosserSchedule.target
  intro ℳ hℳ
  exact (translate_truth_iff hℳ source).mpr
    (hDerives.semantically_entails _ (PureZFCModels.models hℳ))

/-- 先在公式参数上验证联结词保持，避免归约具体 quotation。 -/
theorem translate_fixed_point {source predicate : SetSentence}
    (hFixed : Derives intrinsic_zfc_theory [] (.iff source (.neg predicate))) :
    Derives PureModel.theory [] (.iff (translate source) (.neg (translate predicate))) :=
  translate_derives (source := .iff source (.neg predicate)) hFixed

/-- 裸 ZFC 证明配置句子等价于其 Rosser 比较式的否定。 -/
theorem fixed_point :
    Derives PureModel.theory [] (.iff sentence (.neg comparison)) :=
  translate_fixed_point
    (source := ReducedRosser.sentence)
    (predicate := ReducedRosser.presentation.predicate_of ReducedRosser.sentence)
    ReducedRosser.fixed_point

/-- 固定点在所有裸 ZFC 模型中成立。 -/
theorem fixed_point_truth {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) :
    sentence.TrueIn ℳ ↔ ¬ comparison.TrueIn ℳ :=
  fixed_point.semantically_entails ℳ hℳ

/-- 剩余的句子级约化真值对应，量化任意原理论模型。 -/
def Agreement : Prop :=
  PureZFCModels.reduction.Agrees ReducedRosser.sentence sentence

/-- 对角部分已消去后，剩余义务只涉及指定证明树的 Rosser 比较。 -/
def ComparisonAgreement : Prop :=
  PureZFCModels.reduction.Agrees
    (ReducedRosser.presentation.predicate_of ReducedRosser.sentence) comparison

/-- 两个固定点把句子对应与比较式对应严格等价起来。 -/
theorem agreement_iff_comparison : Agreement ↔ ComparisonAgreement := by
  classical
  have hSource (𝒩 : Structure.{0,0,0,0} signature)
      (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
      ReducedRosser.sentence.TrueIn 𝒩 ↔
        ¬ (ReducedRosser.presentation.predicate_of ReducedRosser.sentence).TrueIn 𝒩 :=
    ReducedRosser.fixed_point.semantically_entails 𝒩 h𝒩
  constructor
  · intro hAgrees 𝒩 h𝒩
    have hNeg := (fixed_point_truth (PureZFCModels.reduct_models h𝒩)).symm.trans
      ((hAgrees 𝒩 h𝒩).trans (hSource 𝒩 h𝒩))
    constructor
    · intro hTarget
      apply Classical.byContradiction
      intro hSourceFalse
      exact (hNeg.mpr hSourceFalse) hTarget
    · intro hSourceTrue
      apply Classical.byContradiction
      intro hTargetFalse
      exact (hNeg.mp hTargetFalse) hSourceTrue
  · intro hAgrees 𝒩 h𝒩
    exact (fixed_point_truth (PureZFCModels.reduct_models h𝒩)).trans
      ((not_congr (hAgrees 𝒩 h𝒩)).trans (hSource 𝒩 h𝒩).symm)

/-- 纯 ZFC 一致性已经足以保证当前源支撑理论的一致性。 -/
theorem source_consistent
    (hConsistent : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    Derives.Consistent intrinsic_zfc_theory ([] : Context signature []) :=
  SemanticTransfer.consistent_of_expands PureRosserSchedule.target
    PureZFCModels.expands hConsistent

/-- 目标句子、扩张、约化和调度均已固定；该底层接口显式接收真值对应。 -/
noncomputable def contract (hAgrees : Agreement) : PureRosserTransfer.Contract sentence :=
  PureZFCModels.contract (target := sentence) hAgrees

theorem independent_of_agreement (hAgrees : Agreement)
    (hConsistent : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    (¬ Derives PureModel.theory [] sentence) ∧
      (¬ Derives PureModel.theory [] (.neg sentence)) :=
  PureRosserTransfer.independent (contract hAgrees)
    PureRosserSchedule.source PureRosserSchedule.target hConsistent

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosser
