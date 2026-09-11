import YesMetaZFC.Model.Interpretation.RelationalInheritance
import YesMetaZFC.Model.ZFC.Pure.PureRelatedSyntaxSets
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding

/-! # 相关语法及其集合的统一纯扩张

两个集合函数在任意参数上有唯一输出，并满足原 guard 下的完整定义。
三个相关语法关系与上一批普通语法、结构定义在此模型中保持成立；
分离规则谓词按已有公式码识别和原蕴涵码等式定义。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedStage
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def functionGraph (symbol : FunctionSymbol) : Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .relatedTermSet => PureRelatedSyntaxSets.graph .term
  | .relatedFormulaSet => PureRelatedSyntaxSets.graph .formula
  | symbol => PureRelatedSyntaxStage.interpretation.function symbol

def prior : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureRelatedSyntaxStage.interpretation.relation

def modusPonensBody : Formula S [] [s,s,s] :=
  FormalSystem.modus_ponens_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation symbol := match symbol with
    | .modusPonens => openFormula prior modusPonensBody
    | symbol => PureRelatedSyntaxStage.interpretation.relation symbol

def functionCovered : FunctionSymbol → Bool
  | .relatedTermSet | .relatedFormulaSet => true
  | symbol => PureRelatedSyntaxStage.functionCovered symbol
def relationCovered : RelationSymbol → Bool
  | .modusPonens => true
  | symbol => PureRelatedSyntaxStage.relationCovered symbol

/-- 上一阶段完成清单中的函数图、关系图均保持不变，且仍被当前清单覆盖。 -/
theorem prior_extension : CoveredExtension PureStructureStage.interpretation interpretation.function interpretation.relation
    PureStructureStage.functionCovered PureStructureStage.relationCovered functionCovered relationCovered := by
  constructor <;> intro symbol h <;> cases symbol <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case relatedTermSet =>
    cases args with | cons symbols tail =>
    cases tail
    exact PureRelatedSyntaxSets.functional hℳ .term symbols
  case relatedFormulaSet =>
    cases args with | cons symbols tail =>
    cases tail
    exact PureRelatedSyntaxSets.functional hℳ .formula symbols
  all_goals exact PureRelatedSyntaxStage.functional hℳ _ args

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : interpretation.function symbol = PureRelatedSyntaxStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureRelatedSyntaxStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureRelatedSyntaxStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureRelatedSyntaxStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureRelatedSyntaxStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureRelatedSyntaxStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem term_set_specification (hℳ : Theory.Models ℳ theory) (symbols output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .relatedTermSet ((PureRelatedSyntaxSets.specification .term)) (.cons symbols .nil) output :=
  ((realizes hℳ).function .relatedTermSet (.cons symbols .nil) output).symm.trans
    ((PureRelatedSyntaxSets.graph_correct hℳ .term symbols output).trans (transfer hℳ _ rfl _))

theorem formula_set_specification (hℳ : Theory.Models ℳ theory) (symbols output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .relatedFormulaSet ((PureRelatedSyntaxSets.specification .formula)) (.cons symbols .nil) output :=
  ((realizes hℳ).function .relatedFormulaSet (.cons symbols .nil) output).symm.trans
    ((PureRelatedSyntaxSets.graph_correct hℳ .formula symbols output).trans (transfer hℳ _ rfl _))

theorem term_set_definition (hℳ : Theory.Models ℳ theory) (symbols output : Carrier ℳ) :
    (FormalSystem.related_term_set_definition_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons symbols .nil)) : Env (expansion hℳ).model [] [s,s]) :=
  fun _ => term_set_specification hℳ symbols output

theorem formula_set_definition (hℳ : Theory.Models ℳ theory) (symbols output : Carrier ℳ) :
    (FormalSystem.related_formula_set_definition_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons symbols .nil)) : Env (expansion hℳ).model [] [s,s]) :=
  fun _ => formula_set_specification hℳ symbols output

/-- 任意既有规格正文在两步扩张中保持纯翻译，就能逐参数传输到当前模型。 -/
theorem prior_transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hRelations : openFormula PureRelatedSyntaxStage.interpretation body = openFormula PureStructureStage.interpretation body)
    (hSets : openFormula interpretation body = openFormula PureRelatedSyntaxStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureStructureStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) :=
  transfer_regraph _ _ _ _ (PureStructureStage.realizes hℳ) _ (realizes hℳ) body (hSets.trans hRelations) args

theorem prior_function (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : interpretation.function symbol = PureStructureStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureStructureStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureStructureStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

/-- 旧实际函数图及正文在本批保持时，原规格整体保持。 -/
theorem inherited_specification (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (spec : Formula S [] (s :: S.funcDomain symbol))
    (hGraph : interpretation.function symbol = PureStructureStage.interpretation.function symbol)
    (hRelations : openFormula PureRelatedSyntaxStage.interpretation spec = openFormula PureStructureStage.interpretation spec)
    (hSets : openFormula interpretation spec = openFormula PureRelatedSyntaxStage.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ)
    (hSpec : FunctionSpecification (PureStructureStage.expansion hℳ) symbol spec args output) :
    FunctionSpecification (expansion hℳ) symbol (spec) args output :=
  specification_regraph _ (PureStructureStage.realizes hℳ) _ (realizes hℳ) symbol spec
    hGraph (hSets.trans hRelations) args output hSpec

theorem related_term_definition (hℳ : Theory.Models ℳ theory) (symbols depth code : Carrier ℳ) :
    (FormalSystem.related_term_code_at_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons symbols (.cons depth (.cons code .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  (transfer hℳ _ rfl _).mp (PureRelatedSyntaxStage.term_definition hℳ symbols depth code)

theorem related_term_list_definition (hℳ : Theory.Models ℳ theory) (symbols depth length code : Carrier ℳ) :
    (FormalSystem.related_term_list_code_at_definition_instance (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))).satisfies
      (templateEnv (.cons symbols (.cons depth (.cons length (.cons code .nil)))) : Env (expansion hℳ).model [] [s,s,s,s]) :=
  (transfer hℳ _ rfl _).mp (PureRelatedSyntaxStage.term_list_definition hℳ symbols depth length code)

theorem related_formula_definition (hℳ : Theory.Models ℳ theory) (symbols depth code : Carrier ℳ) :
    (FormalSystem.related_formula_code_at_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons symbols (.cons depth (.cons code .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  (transfer hℳ _ rfl _).mp (PureRelatedSyntaxStage.formula_definition hℳ symbols depth code)

theorem term_definition (hℳ : Theory.Models ℳ theory) (depth code : Carrier ℳ) :
    (FormalSystem.term_code_at_definition_instance (.fvar .here) (.fvar (.there .here))).satisfies
      (templateEnv (.cons depth (.cons code .nil)) : Env (expansion hℳ).model [] [s,s]) :=
  (transfer_regraph _ _ _ _ (PureSyntaxStage.realizes hℳ) _ (realizes hℳ) _ rfl _).mp
    (PureSyntaxStage.term_definition hℳ depth code)

theorem term_list_definition (hℳ : Theory.Models ℳ theory) (depth length code : Carrier ℳ) :
    (FormalSystem.term_list_code_at_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons depth (.cons length (.cons code .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  (transfer_regraph _ _ _ _ (PureSyntaxStage.realizes hℳ) _ (realizes hℳ) _ rfl _).mp
    (PureSyntaxStage.term_list_definition hℳ depth length code)

theorem formula_definition (hℳ : Theory.Models ℳ theory) (depth code : Carrier ℳ) :
    (FormalSystem.formula_code_at_definition_instance (.fvar .here) (.fvar (.there .here))).satisfies
      (templateEnv (.cons depth (.cons code .nil)) : Env (expansion hℳ).model [] [s,s]) :=
  (transfer_regraph _ _ _ _ (PureSyntaxStage.realizes hℳ) _ (realizes hℳ) _ rfl _).mp
    (PureSyntaxStage.formula_definition hℳ depth code)

theorem nonlogical_definition (hℳ : Theory.Models ℳ theory) :
    FormalSystem.related_nonlogical_symbol_set_definition_axiom.satisfies
      (templateEnv .nil : Env (expansion hℳ).model [] []) :=
  (prior_transfer hℳ _ rfl rfl _).mp (PureStructureStage.nonlogical_definition hℳ )

theorem structure_definition (hℳ : Theory.Models ℳ theory) (carrier assignment symbols : Carrier ℳ) :
    (expansion hℳ).relation .isStructure (.cons carrier (.cons assignment (.cons symbols .nil))) ↔
      PureStructureStage.structureBody.satisfies (templateEnv (.cons carrier (.cons assignment (.cons symbols .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  realizes_definition (expansion hℳ) (realizes hℳ) .isStructure PureStructureStage.structureBody rfl _

/-- 分离规则精确保留原良构性条件及蕴涵码等式。 -/
theorem modus_ponens_definition (hℳ : Theory.Models ℳ theory) (premise implication conclusion : Carrier ℳ) :
    (expansion hℳ).relation .modusPonens (.cons premise (.cons implication (.cons conclusion .nil))) ↔
      modusPonensBody.satisfies (templateEnv (.cons premise (.cons implication (.cons conclusion .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  realizes_definition (expansion hℳ) (realizes hℳ) .modusPonens modusPonensBody rfl _

theorem modus_ponens_dependencies : formulaCovered functionCovered relationCovered modusPonensBody = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedStage
