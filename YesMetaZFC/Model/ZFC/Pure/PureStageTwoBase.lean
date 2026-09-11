import YesMetaZFC.Model.ZFC.Pure.PureOrderExtrema

/-! # 第二轮函数的阶段扩张

新增函数使用已经证明存在唯一的图；第一轮关系仍使用原纯定义。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageTwoBase
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureFunctionDefinitions.parameterSorts
universe x

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .minimum => PureOrderExtrema.graph .minimum
  | .maximum => PureOrderExtrema.graph .maximum
  | symbol => PureStageBase.functionGraph symbol

def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .minimum | .maximum => true
  | symbol => PureStageBase.functionCovered symbol

def interpretation : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureRoundOneRelations.interpretation.relation

theorem map_values {ℳ : Structure.{0, 0, 0, x} ℒ} {sorts : SortContext Nonlogical.BasicSetTheory.signature}
    (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues interpretation args = mapValues PureRoundOneRelations.interpretation args := rfl

theorem functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case minimum => exact PureOrderExtrema.functional hℳ .minimum (mapValues interpretation args)
  case maximum => exact PureOrderExtrema.functional hℳ .maximum (mapValues interpretation args)
  all_goals exact PureRoundOneRelations.functional hℳ _ args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageTwoBase
