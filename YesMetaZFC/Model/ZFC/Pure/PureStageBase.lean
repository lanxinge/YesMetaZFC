import YesMetaZFC.Model.ZFC.Pure.PureRelationSetOperations
import YesMetaZFC.Model.ZFC.Pure.PureOmegaAndReverse
import YesMetaZFC.Model.ZFC.Pure.PureMappingOperations
import YesMetaZFC.Model.ZFC.Pure.PureCoordinateSpecifications
import YesMetaZFC.Model.Interpretation.RelationalDefinitions

/-! # 已消去符号的阶段模型

已完成函数使用其实际纯图。未处理函数临时取空集、未处理关系暂取假，只用于构造
验证当前定义的阶段模型；这些分支不计入消去成果，也不声称实现完整支撑理论。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageBase
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureFunctionDefinitions.parameterSorts
universe x

def emptyGraph {parameters : SortContext ℒ} : Formula ℒ [] (setSort :: parameters) :=
  PureFunctionDefinitions.comprehension .falsum

private theorem empty_functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext ℒ} (args : Values ℳ.Carrier parameters) :
    ∃ output, emptyGraph.satisfies (templateEnv (.cons output args)) ∧
      ∀ other, emptyGraph.satisfies (templateEnv (.cons other args)) → other = output := by
  obtain ⟨output, hEmpty⟩ := PureModel.empty hℳ
  have hGraph : emptyGraph.satisfies (templateEnv (.cons output args)) :=
    (PureFunctionDefinitions.comprehension_correct .falsum args output).mpr
      (fun element => ⟨hEmpty element, False.elim⟩)
  exact ⟨output, hGraph, fun other hOther =>
    PureFunctionDefinitions.comprehension_unique hℳ .falsum args other output hOther hGraph⟩

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .emptySet => PureFunctionDefinitions.graph .emptySet
  | .powerSet => PureFunctionDefinitions.graph .powerSet
  | .unorderedPair => PureFunctionDefinitions.graph .unorderedPair
  | .singleton => PureFunctionDefinitions.graph .singleton
  | .union => PureFunctionDefinitions.graph .union
  | .successor => PureFunctionDefinitions.graph .successor
  | .orderedPair => PureRelationFunctions.graph .orderedPair
  | .leftProjection => PureRelationFunctions.graph .leftProjection
  | .rightProjection => PureRelationFunctions.graph .rightProjection
  | .application => PureRelationFunctions.graph .application
  | .cartesianProduct => PureMappingDefinitions.graph .cartesianProduct
  | .mappingCollection => PureMappingDefinitions.graph .mappingCollection
  | .domain => PureRelationCoordinates.graph .domain
  | .range => PureRelationCoordinates.graph .range
  | .identity => PureMappingOperations.graph .identity
  | .restriction => PureMappingOperations.graph .restriction
  | .binaryUnion => PureRelationSetOperations.graph .binaryUnion
  | .symmetricDifference => PureRelationSetOperations.graph .symmetricDifference
  | .relationConverse => PureRelationSetOperations.graph .relationConverse
  | .relationComposition => PureRelationSetOperations.graph .relationComposition
  | .membershipRelation => PureRelationSetOperations.graph .membershipRelation
  | .image => PureRelationSetOperations.graph .image
  | .inductiveCore => PureRelationSetOperations.graph .inductiveCore
  | .omega => PureOmegaAndReverse.graph .omega
  | .orderedPairReverse => PureOmegaAndReverse.graph .orderedPairReverse
  | _ => emptyGraph

def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .emptySet | .powerSet | .unorderedPair | .singleton | .union | .successor | .orderedPair | .leftProjection | .rightProjection | .application | .cartesianProduct | .mappingCollection | .domain | .range | .identity | .restriction | .binaryUnion | .symmetricDifference | .relationConverse | .relationComposition | .membershipRelation | .image | .inductiveCore | .omega | .orderedPairReverse => true
  | _ => false

def interpretation : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation symbol := match symbol with
    | .membership => PureRelationDefinitions.relationGraph .membership
    | .subset => PureRelationDefinitions.relationGraph .subset
    | .isOrderedPair => PureRelationDefinitions.relationGraph .isOrderedPair
    | .isRelation => PureRelationDefinitions.relationGraph .isRelation
    | .isFunction => PureRelationDefinitions.relationGraph .isFunction
    | .isMapping => PureMappingDefinitions.isMappingGraph
    | _ => .falsum

theorem functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case emptySet => exact PureFunctionDefinitions.functional hℳ .emptySet (mapValues interpretation args)
  case powerSet => exact PureFunctionDefinitions.functional hℳ .powerSet (mapValues interpretation args)
  case unorderedPair => exact PureFunctionDefinitions.functional hℳ .unorderedPair (mapValues interpretation args)
  case singleton => exact PureFunctionDefinitions.functional hℳ .singleton (mapValues interpretation args)
  case union => exact PureFunctionDefinitions.functional hℳ .union (mapValues interpretation args)
  case successor => exact PureFunctionDefinitions.functional hℳ .successor (mapValues interpretation args)
  case orderedPair => exact PureRelationFunctions.functional hℳ .orderedPair (mapValues interpretation args)
  case leftProjection => exact PureRelationFunctions.functional hℳ .leftProjection (mapValues interpretation args)
  case rightProjection => exact PureRelationFunctions.functional hℳ .rightProjection (mapValues interpretation args)
  case application => exact PureRelationFunctions.functional hℳ .application (mapValues interpretation args)
  case cartesianProduct => exact PureMappingDefinitions.functional hℳ .cartesianProduct (mapValues interpretation args)
  case mappingCollection => exact PureMappingDefinitions.functional hℳ .mappingCollection (mapValues interpretation args)
  case domain => exact PureRelationCoordinates.functional hℳ .domain (mapValues interpretation args)
  case range => exact PureRelationCoordinates.functional hℳ .range (mapValues interpretation args)
  case identity => exact PureMappingOperations.functional hℳ .identity (mapValues interpretation args)
  case restriction => exact PureMappingOperations.functional hℳ .restriction (mapValues interpretation args)
  case binaryUnion => exact PureRelationSetOperations.functional hℳ .binaryUnion (mapValues interpretation args)
  case symmetricDifference => exact PureRelationSetOperations.functional hℳ .symmetricDifference (mapValues interpretation args)
  case relationConverse => exact PureRelationSetOperations.functional hℳ .relationConverse (mapValues interpretation args)
  case relationComposition => exact PureRelationSetOperations.functional hℳ .relationComposition (mapValues interpretation args)
  case membershipRelation => exact PureRelationSetOperations.functional hℳ .membershipRelation (mapValues interpretation args)
  case image => exact PureRelationSetOperations.functional hℳ .image (mapValues interpretation args)
  case inductiveCore => exact PureRelationSetOperations.functional hℳ .inductiveCore (mapValues interpretation args)
  case omega => exact PureOmegaAndReverse.functional hℳ .omega (mapValues interpretation args)
  case orderedPairReverse => exact PureOmegaAndReverse.functional hℳ .orderedPairReverse (mapValues interpretation args)
  all_goals exact empty_functional hℳ (mapValues interpretation args)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageBase
