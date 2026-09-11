import YesMetaZFC.Model.Interpretation.RelationalTransfer
import YesMetaZFC.Model.Interpretation.ModelClosure
import YesMetaZFC.Model.ZFC.Pure.PureCompletedStage

/-! # 旧阶段规格到最终纯扩张的统一传输

每个接口只核验原公式依赖的逐符号图相等，不展开整份嵌套不动点解释。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalTransfer
open PureModel Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureCompletedStage.expansion hℳ

/-- 只组合相邻扩张的证书，最终接口不再逐符号展开所有中间图。 -/
theorem fromTransform_extension : CoveredExtension PureTransformStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    PureTransformStage.functionCovered PureTransformStage.relationCovered
    PureCompletedStage.functionCovered PureCompletedStage.relationCovered :=
  PureAllSchemaStage.prior_extension.trans (PureLogicalStage.prior_extension.trans PureCompletedStage.prior_extension)

theorem fromRelated_extension : CoveredExtension PureRelatedStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    PureRelatedStage.functionCovered PureRelatedStage.relationCovered
    PureCompletedStage.functionCovered PureCompletedStage.relationCovered :=
  PureLogicalSchemaStage.prior_extension.trans (PureTransformStage.prior_extension.trans fromTransform_extension)

theorem fromStructure_extension : CoveredExtension PureStructureStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    PureStructureStage.functionCovered PureStructureStage.relationCovered
    PureCompletedStage.functionCovered PureCompletedStage.relationCovered :=
  PureRelatedStage.prior_extension.trans fromRelated_extension

theorem fromRoundTwo_extension : CoveredExtension PureRoundTwoStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered
    PureCompletedStage.functionCovered PureCompletedStage.relationCovered :=
  PureStructureStage.prior_extension.trans fromStructure_extension

theorem fromRoundTwo (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureRoundTwoStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  fromRoundTwo_extension.transfer _ (PureRoundTwoStage.realizes hℳ) _ (PureCompletedStage.realizes hℳ) body hCovered args

theorem fromRelated (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureRelatedStage.functionCovered PureRelatedStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureRelatedStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  fromRelated_extension.transfer _ (PureRelatedStage.realizes hℳ) _ (PureCompletedStage.realizes hℳ) body hCovered args

theorem fromTransform (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureTransformStage.functionCovered PureTransformStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureTransformStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  fromTransform_extension.transfer _ (PureTransformStage.realizes hℳ) _ (PureCompletedStage.realizes hℳ) body hCovered args

theorem fromStructure (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureStructureStage.functionCovered PureStructureStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureStructureStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  fromStructure_extension.transfer _ (PureStructureStage.realizes hℳ) _ (PureCompletedStage.realizes hℳ) body hCovered args

theorem fromRoundTwoSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureRoundTwoStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  simpa only [YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (PureRoundTwoStage.expansion hℳ).model),
    YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (E hℳ).model)] using
    fromRoundTwo hℳ body hCovered .nil

theorem fromRelatedSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureRelatedStage.functionCovered PureRelatedStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureRelatedStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  simpa only [YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (PureRelatedStage.expansion hℳ).model),
    YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (E hℳ).model)] using
    fromRelated hℳ body hCovered .nil

theorem fromTransformSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureTransformStage.functionCovered PureTransformStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureTransformStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  simpa only [YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (PureTransformStage.expansion hℳ).model),
    YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (E hℳ).model)] using
    fromTransform hℳ body hCovered .nil

theorem fromStructureSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureStructureStage.functionCovered PureStructureStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureStructureStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  simpa only [YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (PureStructureStage.expansion hℳ).model),
    YesMetaZFC.Automation.ModelClosure.templateEnv_nil (ℳ := (E hℳ).model)] using
    fromStructure hℳ body hCovered .nil

theorem functionFromArithmetic (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : PureCompletedStage.interpretation.function symbol = PureArithmeticStage.interpretation.function symbol)
    (args : Values (E hℳ).model.Carrier (S.funcDomain symbol)) :
    (E hℳ).function symbol args = (PureArithmeticStage.expansion hℳ).function symbol args :=
  function_regraph PureArithmeticStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    symbol hGraph args

theorem functionFromDifference (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : PureCompletedStage.interpretation.function symbol = PureDifferenceStage.interpretation.function symbol)
    (args : Values (E hℳ).model.Carrier (S.funcDomain symbol)) :
    (E hℳ).function symbol args = (PureDifferenceStage.expansion hℳ).function symbol args :=
  function_regraph PureDifferenceStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureDifferenceStage.expansion hℳ) (PureDifferenceStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    symbol hGraph args

theorem functionFromRoundTwo (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : PureCompletedStage.interpretation.function symbol = PureRoundTwoStage.interpretation.function symbol)
    (args : Values (E hℳ).model.Carrier (S.funcDomain symbol)) :
    (E hℳ).function symbol args = (PureRoundTwoStage.expansion hℳ).function symbol args :=
  function_regraph PureRoundTwoStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureRoundTwoStage.expansion hℳ) (PureRoundTwoStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    symbol hGraph args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalTransfer
