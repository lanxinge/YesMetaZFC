import YesMetaZFC.Model.ZFC.Pure.PureFinalTransfer

/-! # 最终扩张中的三个原极值公理 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalExtrema
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem transfer (hℳ : Theory.Models ℳ theory) {free : SortContext S} (body : Formula S [] free)
    (hCovered : formulaCovered PureStageTwoBase.functionCovered PureNaturalRelations.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureStageTwoSemantics.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  transfer_covered PureNaturalRelations.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureStageTwoSemantics.expansion hℳ) (PureStageTwoSemantics.realizes hℳ)
    (E hℳ) (PureCompletedStage.realizes hℳ)
    PureStageTwoBase.functionCovered PureNaturalRelations.relationCovered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered args

theorem minimum_linear_order (hℳ : Theory.Models ℳ theory) :
    minimum_linear_order_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_values
  intro args
  apply (transfer hℳ _ rfl args).mp
  cases args with | cons output tail =>
  cases tail with | cons subset tail =>
  cases tail with | cons carrier tail =>
  cases tail with | cons relation tail =>
  cases tail
  exact PureStageTwoSemantics.minimum_definition_correct hℳ relation carrier subset output

theorem minimum_natural_order (hℳ : Theory.Models ℳ theory) :
    minimum_natural_order_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_values
  intro args
  apply (transfer hℳ _ rfl args).mp
  cases args with | cons output tail =>
  cases tail with | cons subset tail =>
  cases tail with | cons carrier tail =>
  cases tail with | cons relation tail =>
  cases tail
  exact PureStageTwoSemantics.minimum_natural_definition_correct hℳ relation carrier subset output

theorem maximum_natural_order (hℳ : Theory.Models ℳ theory) :
    maximum_natural_order_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_values
  intro args
  apply (transfer hℳ _ rfl args).mp
  cases args with | cons output tail =>
  cases tail with | cons subset tail =>
  cases tail with | cons carrier tail =>
  cases tail with | cons relation tail =>
  cases tail
  exact PureStageTwoSemantics.maximum_natural_definition_correct hℳ relation carrier subset output

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalExtrema
