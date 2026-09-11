import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureLogicalSchemaSets
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRelatedStage

/-! # 九个逻辑公理集合的统一扩张

七个命题公理集合、量词分配公理集合和等式自反公理集合均由纯分离给出，
保留修正后的原模式成员正文。前一阶段已完成的全部实际图保持不变。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalSchemaStage
open PureModel PureLogicalSchemaSets
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
  | .implicationDistributionAxiomSet => graph .implicationDistribution
  | .selfImplicationAxiomSet => graph .selfImplication
  | .weakeningAxiomSet => graph .weakening
  | .contradictionAxiomSet => graph .contradiction
  | .classicalAxiomSet => graph .classical
  | .explosionAxiomSet => graph .explosion
  | .caseAnalysisAxiomSet => graph .caseAnalysis
  | .quantifierDistributionAxiomSet => graph .quantifierDistribution
  | .equalityReflexivityAxiomSet => graph .equalityReflexivity
  | symbol => PureRelatedStage.interpretation.function symbol

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureRelatedStage.interpretation.relation

def functionCovered : FunctionSymbol → Bool
  | .implicationDistributionAxiomSet => true
  | .selfImplicationAxiomSet => true
  | .weakeningAxiomSet => true
  | .contradictionAxiomSet => true
  | .classicalAxiomSet => true
  | .explosionAxiomSet => true
  | .caseAnalysisAxiomSet => true
  | .quantifierDistributionAxiomSet => true
  | .equalityReflexivityAxiomSet => true
  | symbol => PureRelatedStage.functionCovered symbol
def relationCovered := PureRelatedStage.relationCovered

/-- 当前扩张保留上一完整阶段的覆盖与实际图。 -/
theorem prior_extension : CoveredExtension PureRelatedStage.interpretation interpretation.function interpretation.relation
    PureRelatedStage.functionCovered PureRelatedStage.relationCovered functionCovered relationCovered := by
  constructor <;> intro symbol h <;> cases symbol <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case implicationDistributionAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .implicationDistribution
  case selfImplicationAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .selfImplication
  case weakeningAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .weakening
  case contradictionAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .contradiction
  case classicalAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .classical
  case explosionAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .explosion
  case caseAnalysisAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .caseAnalysis
  case quantifierDistributionAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .quantifierDistribution
  case equalityReflexivityAxiomSet =>
    cases args
    exact PureLogicalSchemaSets.functional hℳ .equalityReflexivity
  all_goals exact PureRelatedStage.functional hℳ _ args

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

noncomputable def value (hℳ : Theory.Models ℳ theory) : Kind → Carrier ℳ
  | .implicationDistribution => (expansion hℳ).function .implicationDistributionAxiomSet .nil
  | .selfImplication => (expansion hℳ).function .selfImplicationAxiomSet .nil
  | .weakening => (expansion hℳ).function .weakeningAxiomSet .nil
  | .contradiction => (expansion hℳ).function .contradictionAxiomSet .nil
  | .classical => (expansion hℳ).function .classicalAxiomSet .nil
  | .explosion => (expansion hℳ).function .explosionAxiomSet .nil
  | .caseAnalysis => (expansion hℳ).function .caseAnalysisAxiomSet .nil
  | .quantifierDistribution => (expansion hℳ).function .quantifierDistributionAxiomSet .nil
  | .equalityReflexivity => (expansion hℳ).function .equalityReflexivityAxiomSet .nil

theorem value_graph (hℳ : Theory.Models ℳ theory) (kind : Kind) :
    (graph kind).satisfies (templateEnv (.cons (value hℳ kind) .nil)) := by
  cases kind
  case implicationDistribution => exact ((realizes hℳ).function .implicationDistributionAxiomSet .nil _).mpr rfl
  case selfImplication => exact ((realizes hℳ).function .selfImplicationAxiomSet .nil _).mpr rfl
  case weakening => exact ((realizes hℳ).function .weakeningAxiomSet .nil _).mpr rfl
  case contradiction => exact ((realizes hℳ).function .contradictionAxiomSet .nil _).mpr rfl
  case classical => exact ((realizes hℳ).function .classicalAxiomSet .nil _).mpr rfl
  case explosion => exact ((realizes hℳ).function .explosionAxiomSet .nil _).mpr rfl
  case caseAnalysis => exact ((realizes hℳ).function .caseAnalysisAxiomSet .nil _).mpr rfl
  case quantifierDistribution => exact ((realizes hℳ).function .quantifierDistributionAxiomSet .nil _).mpr rfl
  case equalityReflexivity => exact ((realizes hℳ).function .equalityReflexivityAxiomSet .nil _).mpr rfl

theorem syntax_transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureSyntaxStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureSyntaxStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureSyntaxStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

/-- 九种模式的精确成员规格在同一个实际扩张中成立。 -/
theorem membership_specification (hℳ : Theory.Models ℳ theory) (kind : Kind) (code : Carrier ℳ) :
    membership ℳ code (value hℳ kind) ↔
      (condition kind).satisfies (templateEnv (.cons code .nil) : Env (expansion hℳ).model [] [s]) :=
  ((graph_correct hℳ kind _).mp (value_graph hℳ kind) code).trans
    (syntax_transfer hℳ (condition kind) (by cases kind <;> rfl) (.cons code .nil))

/-- 七项命题公理模式的整个源闭句在统一模型中成立。 -/
theorem propositional_axioms (hℳ : Theory.Models ℳ theory) :
    FormalSystem.propositional_axiom_schema_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) := by
  intro code
  exact ⟨membership_specification hℳ .implicationDistribution code,
    membership_specification hℳ .selfImplication code,
    membership_specification hℳ .weakening code,
    membership_specification hℳ .contradiction code,
    membership_specification hℳ .classical code,
    membership_specification hℳ .explosion code,
    membership_specification hℳ .caseAnalysis code⟩

theorem quantifier_distribution_definition (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.membership_formula (.fvar .here) quantifier_distribution_axiom_set_term |>.iff
      (FormalSystem.quantifier_distribution_axiom_condition (.fvar .here))).satisfies
      (templateEnv (.cons code .nil) : Env (expansion hℳ).model [] [s]) :=
  membership_specification hℳ .quantifierDistribution code

theorem equality_reflexivity_definition (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.membership_formula (.fvar .here) equality_reflexivity_axiom_set_term |>.iff
      (FormalSystem.equality_reflexivity_axiom_condition (.fvar .here))).satisfies
      (templateEnv (.cons code .nil) : Env (expansion hℳ).model [] [s]) :=
  membership_specification hℳ .equalityReflexivity code

theorem dependencies_covered (kind : Kind) : formulaCovered functionCovered relationCovered (condition kind) = true := by cases kind <;> rfl

theorem prior_relation_graph (symbol : RelationSymbol) :
    interpretation.relation symbol = PureRelatedStage.interpretation.relation symbol := rfl

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : interpretation.function symbol = PureRelatedStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureRelatedStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureRelatedStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureRelatedStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureRelatedStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureRelatedStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

/-- 旧函数图及原规格正文的纯翻译保持时，整个规格在当前模型中保持。 -/
theorem inherited_specification (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (spec : Formula S [] (s :: S.funcDomain symbol))
    (hGraph : interpretation.function symbol = PureRelatedStage.interpretation.function symbol)
    (hTranslate : openFormula interpretation spec = openFormula PureRelatedStage.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ)
    (hSpec : FunctionSpecification (PureRelatedStage.expansion hℳ) symbol spec args output) :
    FunctionSpecification (expansion hℳ) symbol (spec) args output :=
  specification_regraph _ (PureRelatedStage.realizes hℳ) _ (realizes hℳ) symbol spec
    hGraph hTranslate args output hSpec

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalSchemaStage
