import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSequenceFilters

/-! # 递归序列族与其并集的统一扩张

先实现两个序列族，再以其并集实现原 ω 递归序列算子。各阶段的定义保持通过
纯公式翻译证明，避免在模型选择项上进行庞大的定义展开。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceStage
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature

def filterFunction (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .nonemptyFiniteSequenceSpace => PureSequenceFilters.graph .nonemptyFiniteSequenceSpace
  | .recursiveSequenceSpace => PureSequenceFilters.graph .recursiveSequenceSpace
  | symbol => PureCollectionStage.functionGraph symbol

def filterCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .nonemptyFiniteSequenceSpace | .recursiveSequenceSpace => true
  | symbol => PureCollectionStage.functionCovered symbol

def filterInterpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := filterFunction
  relation := PureNaturalRelations.interpretation.relation

theorem filter_functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional filterInterpretation ℳ := by
  intro symbol args
  cases symbol
  case nonemptyFiniteSequenceSpace => exact PureSequenceFilters.functional hℳ .nonemptyFiniteSequenceSpace args
  case recursiveSequenceSpace => exact PureSequenceFilters.functional hℳ .recursiveSequenceSpace args
  all_goals exact PureCollectionStage.functional hℳ _ args

noncomputable def filterExpansion {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Expansion filterInterpretation ℳ :=
  expansion (filter_functional hℳ)

theorem filter_realizes {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Realizes (filterExpansion hℳ) :=
  expansion_realizes (filter_functional hℳ)

def omegaSpec : Formula S [] [s,s,s,s] :=
  Nonlogical.BasicSetTheory.omega_recursive_sequence_spec (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar .here)

def omegaGraph : Formula ℒ [] [setSort,setSort,setSort,setSort] := openFormula filterInterpretation omegaSpec

theorem omega_dependencies_covered :
    formulaCovered filterCovered PureNaturalRelations.relationCovered omegaSpec = true := rfl

/-- 原定义为递归序列族的并集；其纯图在任意输入上都有唯一输出。 -/
theorem omega_functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source seed recursion : Carrier ℳ) :
    ∃ output, omegaGraph.satisfies (templateEnv (.cons output (.cons source (.cons seed (.cons recursion .nil))))) ∧
      ∀ other, omegaGraph.satisfies (templateEnv (.cons other (.cons source (.cons seed (.cons recursion .nil))))) → other = output := by
  let output := (filterExpansion hℳ).function .union
    (.cons ((filterExpansion hℳ).function .recursiveSequenceSpace (.cons source (.cons seed (.cons recursion .nil)))) .nil)
  refine ⟨output, ?_, ?_⟩
  · exact (openFormula_correct (filterExpansion hℳ) (filter_realizes hℳ) omegaSpec
      (.cons output (.cons source (.cons seed (.cons recursion .nil))))).mpr rfl
  · intro other hOther
    exact (openFormula_correct (filterExpansion hℳ) (filter_realizes hℳ) omegaSpec
      (.cons other (.cons source (.cons seed (.cons recursion .nil))))).mp hOther

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .omegaRecursiveSequence => omegaGraph
  | symbol => filterFunction symbol

def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .omegaRecursiveSequence => true
  | symbol => filterCovered symbol

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureNaturalRelations.interpretation.relation

theorem functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case omegaRecursiveSequence =>
    cases args with | cons source tail =>
    cases tail with | cons seed tail =>
    cases tail with | cons recursion tail =>
    cases tail
    exact omega_functional hℳ source seed recursion
  all_goals exact filter_functional hℳ _ args

noncomputable def expansion {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)

theorem realizes {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) :=
  expansion_realizes (functional hℳ)

theorem transfer_from_collection {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext S} (spec : Formula S [] parameters)
    (hTranslate : openFormula interpretation spec = openFormula PureCollectionStage.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    spec.satisfies (templateEnv args : Env (PureCollectionStage.expansion hℳ).model [] parameters) ↔
      spec.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureCollectionStage.realizes hℳ) _ (realizes hℳ) spec hTranslate args

theorem filter_graph_equation {symbol : Nonlogical.BasicSetTheory.FunctionSymbol}
    (primitive : PureSequenceFilters.Primitive symbol) :
    interpretation.function symbol = PureSequenceFilters.graph primitive := by
  cases primitive <;> rfl

theorem filter_translation {symbol : Nonlogical.BasicSetTheory.FunctionSymbol}
    (primitive : PureSequenceFilters.Primitive symbol) :
    openFormula interpretation (PureSequenceFilters.specification primitive) =
      openFormula PureCollectionStage.interpretation (PureSequenceFilters.specification primitive) := by
  cases primitive <;> rfl

theorem filter_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureSequenceFilters.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) symbol ((PureSequenceFilters.specification primitive)) args output := by
  apply ((realizes hℳ).function symbol args output).symm.trans
  rw [filter_graph_equation primitive]
  exact (PureSequenceFilters.graph_correct hℳ primitive args output).trans
    (transfer_from_collection hℳ _ (filter_translation primitive) (.cons output args))

/-- 最后加入的 ω 算子逐参数满足原并集规格。 -/
theorem omega_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source seed recursion output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .omegaRecursiveSequence (omegaSpec) (.cons source (.cons seed (.cons recursion .nil))) output := by
  apply ((realizes hℳ).function .omegaRecursiveSequence (.cons source (.cons seed (.cons recursion .nil))) output).symm.trans
  have hTranslation : openFormula interpretation omegaSpec = omegaGraph := rfl
  have h := openFormula_correct (expansion hℳ) (realizes hℳ) omegaSpec
    (.cons output (.cons source (.cons seed (.cons recursion .nil))))
  rw [hTranslation] at h
  exact h

theorem inherited_round_one {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureRoundOneRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureRoundOneRelations.condition primitive) := by
  cases primitive <;> rfl

theorem inherited_natural {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureNaturalRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureNaturalRelations.condition primitive) := by
  cases primitive <;> rfl

/-- 后续序列算子不改变前三个集合构造的图和原规格。 -/
theorem bounded_graph_equation {symbol : Nonlogical.BasicSetTheory.FunctionSymbol}
    (primitive : PureBoundedDefinitions.Primitive symbol) :
    interpretation.function symbol = PureBoundedDefinitions.graph primitive := by
  cases primitive <;> rfl

theorem bounded_translation {symbol : Nonlogical.BasicSetTheory.FunctionSymbol}
    (primitive : PureBoundedDefinitions.Primitive symbol) :
    openFormula interpretation (PureBoundedDefinitions.specification primitive) =
      openFormula PureCollectionStage.interpretation (PureBoundedDefinitions.specification primitive) := by
  cases primitive <;> rfl

theorem bounded_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureBoundedDefinitions.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) symbol ((PureBoundedDefinitions.specification primitive)) args output := by
  apply ((realizes hℳ).function symbol args output).symm.trans
  rw [bounded_graph_equation primitive]
  have hOld := ((PureCollectionStage.realizes hℳ).function symbol args output).trans
    (PureCollectionStage.bounded_specification hℳ primitive args output)
  rw [PureCollectionStage.bounded_graph_equation primitive] at hOld
  exact hOld.trans (transfer_from_collection hℳ _ (bounded_translation primitive) (.cons output args))

theorem finite_sequence_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .finiteSequenceSpace
      ((Nonlogical.BasicSetTheory.finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here))) (.cons source .nil) output := by
  apply ((realizes hℳ).function .finiteSequenceSpace (.cons source .nil) output).symm.trans
  have hOld := ((PureCollectionStage.realizes hℳ).function .finiteSequenceSpace (.cons source .nil) output).trans
    (PureCollectionStage.finite_sequence_specification hℳ source output)
  exact hOld.trans (transfer_from_collection hℳ _ rfl (.cons output (.cons source .nil)))

theorem round_one_definition_correct {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : PureRoundOneRelations.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureRoundOneRelations.condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion hℳ) (realizes hℳ) symbol (PureRoundOneRelations.condition primitive)
    (inherited_round_one primitive) args

theorem natural_definition_correct {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : PureNaturalRelations.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureNaturalRelations.condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion hℳ) (realizes hℳ) symbol (PureNaturalRelations.condition primitive)
    (inherited_natural primitive) args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceStage
