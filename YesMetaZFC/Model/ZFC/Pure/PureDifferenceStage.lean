import YesMetaZFC.Model.Interpretation.RelationalInheritance
import YesMetaZFC.Model.ZFC.Pure.PureMinimumDifference

/-! # 最小差异点的统一纯扩张

只替换最小差异点的纯图；通过公式翻译保持之前的原规格与关系正文。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureDifferenceStage
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .minimumDifference => PureMinimumDifference.graph
  | symbol => PureSequenceStage.functionGraph symbol

def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .minimumDifference => true
  | symbol => PureSequenceStage.functionCovered symbol

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureSequenceStage.interpretation.relation

theorem functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case minimumDifference =>
    cases args with | cons relation tail =>
    cases tail with | cons carrier tail =>
    cases tail with | cons first tail =>
    cases tail with | cons second tail =>
    cases tail
    exact PureMinimumDifference.functional hℳ relation carrier first second
  all_goals exact PureSequenceStage.functional hℳ _ args

noncomputable def expansion {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)

theorem realizes {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) :=
  expansion_realizes (functional hℳ)

theorem transfer_from_sequence {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext S} (spec : Formula S [] parameters)
    (hTranslate : openFormula interpretation spec = openFormula PureSequenceStage.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    spec.satisfies (templateEnv args : Env (PureSequenceStage.expansion hℳ).model [] parameters) ↔
      spec.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureSequenceStage.realizes hℳ) _ (realizes hℳ) spec hTranslate args

/-- 其余函数仍实现同一纯图；用图的唯一性比较选择值。 -/
theorem function_preserved {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) (hSymbol : symbol ≠ .minimumDifference)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureSequenceStage.expansion hℳ).function symbol args := by
  have hGraph : interpretation.function symbol = PureSequenceStage.interpretation.function symbol := by
    cases symbol <;> first | rfl | exact False.elim (hSymbol rfl)
  exact function_regraph _ _ _ _ (PureSequenceStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem relation_preserved {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (symbol : Nonlogical.BasicSetTheory.RelationSymbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureSequenceStage.expansion hℳ).relation symbol args := by
  exact relation_regraph _ _ _ _ (PureSequenceStage.realizes hℳ) _ (realizes hℳ) symbol rfl args

/-- 新的选择值在原 guard 下逐参数满足原最小差异点规格。 -/
theorem minimum_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {relation carrier target first second : Carrier ℳ}
    (hOrder : (expansion hℳ).relation .isWellOrder (.cons relation (.cons carrier .nil)))
    (hFirst : (expansion hℳ).relation .isMapping (.cons first (.cons carrier (.cons target .nil))))
    (hSecond : (expansion hℳ).relation .isMapping (.cons second (.cons carrier (.cons target .nil))))
    (hNe : first ≠ second) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .minimumDifference
      (PureMinimumDifference.specification) (.cons relation (.cons carrier (.cons first (.cons second .nil)))) output := by
  apply ((realizes hℳ).function .minimumDifference (.cons relation (.cons carrier (.cons first (.cons second .nil)))) output).symm.trans
  exact (PureMinimumDifference.agrees hℳ
    ((relation_preserved hℳ .isWellOrder _).mp hOrder)
    ((relation_preserved hℳ .isMapping _).mp hFirst)
    ((relation_preserved hℳ .isMapping _).mp hSecond) hNe output).trans
    (transfer_from_sequence hℳ _ rfl (.cons output (.cons relation (.cons carrier (.cons first (.cons second .nil))))))

/-- 任意源项与任意环境上的原定义实例。 -/
theorem definition_instance_correct {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {bound free : SortContext S} (env : Env (expansion hℳ).model bound free)
    (relation carrier target first second output : Term S bound free s) :
    (Nonlogical.BasicSetTheory.minimum_difference_definition_instance relation carrier target first second output).satisfies env := by
  intro hGuard
  exact (minimum_specification hℳ hGuard.1 hGuard.2.1.1 hGuard.2.1.2 hGuard.2.2 (output.eval env)).trans
    ((PureMinimumDifference.specification_correct (expansion hℳ).model
      (relation.eval env) (carrier.eval env) (first.eval env) (second.eval env) (output.eval env)).trans
        (PureMinimumDifference.specification_eval env relation carrier first second output).symm)

/-- 前三项有界收集规格在新模型中保持。 -/
theorem bounded_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureBoundedDefinitions.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) symbol ((PureBoundedDefinitions.specification primitive)) args output := by
  have hSymbol : symbol ≠ .minimumDifference := by cases primitive <;> intro h <;> cases h
  rw [FunctionSpecification, function_preserved hℳ symbol hSymbol args]
  apply (PureSequenceStage.bounded_specification hℳ primitive args output).trans
  apply transfer_from_sequence hℳ
  cases primitive <;> rfl

theorem finite_sequence_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .finiteSequenceSpace
      ((Nonlogical.BasicSetTheory.finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here))) (.cons source .nil) output := by
  rw [FunctionSpecification, function_preserved hℳ .finiteSequenceSpace (by intro h; cases h)]
  exact (PureSequenceStage.finite_sequence_specification hℳ source output).trans
    (transfer_from_sequence hℳ _ rfl (.cons output (.cons source .nil)))

theorem filter_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureSequenceFilters.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) symbol ((PureSequenceFilters.specification primitive)) args output := by
  have hSymbol : symbol ≠ .minimumDifference := by cases primitive <;> intro h <;> cases h
  rw [FunctionSpecification, function_preserved hℳ symbol hSymbol args]
  apply (PureSequenceStage.filter_specification hℳ primitive args output).trans
  apply transfer_from_sequence hℳ
  cases primitive <;> rfl

theorem omega_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source seed recursion output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .omegaRecursiveSequence (PureSequenceStage.omegaSpec) (.cons source (.cons seed (.cons recursion .nil))) output := by
  rw [FunctionSpecification, function_preserved hℳ .omegaRecursiveSequence (by intro h; cases h)]
  exact (PureSequenceStage.omega_specification hℳ source seed recursion output).trans
    (transfer_from_sequence hℳ _ rfl (.cons output (.cons source (.cons seed (.cons recursion .nil)))))

theorem inherited_round_one {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureRoundOneRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureRoundOneRelations.condition primitive) := by
  cases primitive <;> rfl

theorem inherited_natural {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureNaturalRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureNaturalRelations.condition primitive) := by
  cases primitive <;> rfl

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

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureDifferenceStage
