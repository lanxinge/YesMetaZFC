import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureDependentSchemaSets
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureTransformStage

/-! # 十二个逻辑公理模式集合的统一扩张

增加特化、空量化和等式替换三个集合，
保留修正后的原模式成员正文。前一阶段已完成的全部实际图保持不变。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureAllSchemaStage
open PureModel PureDependentSchemaSets
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
  | .specializationAxiomSet => graph .specialization
  | .vacuousQuantifierAxiomSet => graph .vacuousQuantifier
  | .equalitySubstitutionAxiomSet => graph .equalitySubstitution
  | symbol => PureTransformStage.interpretation.function symbol

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureTransformStage.interpretation.relation

def functionCovered : FunctionSymbol → Bool
  | .specializationAxiomSet => true
  | .vacuousQuantifierAxiomSet => true
  | .equalitySubstitutionAxiomSet => true
  | symbol => PureTransformStage.functionCovered symbol
def relationCovered := PureTransformStage.relationCovered

/-- 当前扩张保留上一完整阶段的覆盖与实际图。 -/
theorem prior_extension : CoveredExtension PureTransformStage.interpretation interpretation.function interpretation.relation
    PureTransformStage.functionCovered PureTransformStage.relationCovered functionCovered relationCovered := by
  constructor <;> intro symbol h <;> cases symbol <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case specializationAxiomSet =>
    cases args
    exact PureDependentSchemaSets.functional hℳ .specialization
  case vacuousQuantifierAxiomSet =>
    cases args
    exact PureDependentSchemaSets.functional hℳ .vacuousQuantifier
  case equalitySubstitutionAxiomSet =>
    cases args
    exact PureDependentSchemaSets.functional hℳ .equalitySubstitution
  all_goals exact PureTransformStage.functional hℳ _ args

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

noncomputable def value (hℳ : Theory.Models ℳ theory) : Kind → Carrier ℳ
  | .specialization => (expansion hℳ).function .specializationAxiomSet .nil
  | .vacuousQuantifier => (expansion hℳ).function .vacuousQuantifierAxiomSet .nil
  | .equalitySubstitution => (expansion hℳ).function .equalitySubstitutionAxiomSet .nil

theorem value_graph (hℳ : Theory.Models ℳ theory) (kind : Kind) :
    (graph kind).satisfies (templateEnv (.cons (value hℳ kind) .nil)) := by
  cases kind
  case specialization => exact ((realizes hℳ).function .specializationAxiomSet .nil _).mpr rfl
  case vacuousQuantifier => exact ((realizes hℳ).function .vacuousQuantifierAxiomSet .nil _).mpr rfl
  case equalitySubstitution => exact ((realizes hℳ).function .equalitySubstitutionAxiomSet .nil _).mpr rfl

theorem transform_transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureTransformStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureTransformStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureTransformStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem transform_translation {parameters : SortContext S} (body : Formula S [] parameters)
    (hCovered : formulaCovered PureTransformStage.functionCovered PureTransformStage.relationCovered body = true) :
    openFormula interpretation body = openFormula PureTransformStage.interpretation body :=
  prior_extension.translation body hCovered

/-- 本批三种模式的精确成员规格在同一个实际扩张中成立。 -/
theorem membership_specification (hℳ : Theory.Models ℳ theory) (kind : Kind) (code : Carrier ℳ) :
    membership ℳ code (value hℳ kind) ↔
      (condition kind).satisfies (templateEnv (.cons code .nil) : Env (expansion hℳ).model [] [s]) :=
  ((graph_correct hℳ kind _).mp (value_graph hℳ kind) code).trans
    (transform_transfer hℳ (condition kind) (transform_translation _ (PureDependentSchemaSets.dependencies_covered kind)) (.cons code .nil))

theorem dependencies_covered (kind : Kind) : formulaCovered functionCovered relationCovered (condition kind) = true := by cases kind <;> rfl

theorem prior_relation_graph (symbol : RelationSymbol) :
    interpretation.relation symbol = PureTransformStage.interpretation.relation symbol := rfl

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : interpretation.function symbol = PureTransformStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureTransformStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureTransformStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureTransformStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureTransformStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureTransformStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

/-- 旧函数图及原规格正文的纯翻译保持时，整个规格在当前模型中保持。 -/
theorem inherited_specification (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (spec : Formula S [] (s :: S.funcDomain symbol))
    (hGraph : interpretation.function symbol = PureTransformStage.interpretation.function symbol)
    (hTranslate : openFormula interpretation spec = openFormula PureTransformStage.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ)
    (hSpec : FunctionSpecification (PureTransformStage.expansion hℳ) symbol spec args output) :
    FunctionSpecification (expansion hℳ) symbol (spec) args output :=
  specification_regraph _ (PureTransformStage.realizes hℳ) _ (realizes hℳ) symbol spec
    hGraph hTranslate args output hSpec


theorem old_translation {parameters : SortContext S} (body : Formula S [] parameters)
    (hCovered : formulaCovered PureLogicalSchemaStage.functionCovered PureLogicalSchemaStage.relationCovered body = true) :
    openFormula interpretation body = openFormula PureLogicalSchemaStage.interpretation body :=
  (PureTransformStage.prior_extension.trans prior_extension).translation body hCovered

/-- 第一批九个模式的规格和整个闭句传入当前统一模型。 -/
theorem old_transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureLogicalSchemaStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureLogicalSchemaStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureLogicalSchemaStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

def oldTerm {bound free : SortContext S} : PureLogicalSchemaSets.Kind → Term S bound free s
  | .implicationDistribution => implication_distribution_axiom_set_term
  | .selfImplication => self_implication_axiom_set_term
  | .weakening => weakening_axiom_set_term
  | .contradiction => contradiction_axiom_set_term
  | .classical => classical_axiom_set_term
  | .explosion => explosion_axiom_set_term
  | .caseAnalysis => case_analysis_axiom_set_term
  | .quantifierDistribution => quantifier_distribution_axiom_set_term
  | .equalityReflexivity => equality_reflexivity_axiom_set_term

noncomputable def oldValue (hℳ : Theory.Models ℳ theory) (kind : PureLogicalSchemaSets.Kind) : Carrier ℳ :=
  (oldTerm kind).eval (templateEnv .nil : Env (expansion hℳ).model [] [])

theorem old_membership (hℳ : Theory.Models ℳ theory) (kind : PureLogicalSchemaSets.Kind) (code : Carrier ℳ) :
    membership ℳ code (oldValue hℳ kind) ↔
      (PureLogicalSchemaSets.condition kind).satisfies (templateEnv (.cons code .nil) : Env (expansion hℳ).model [] [s]) := by
  have hOld : (Formula.iff (membership_formula (.fvar .here) (oldTerm kind)) (PureLogicalSchemaSets.condition kind)).satisfies
      (templateEnv (.cons code .nil) : Env (PureLogicalSchemaStage.expansion hℳ).model [] [s]) := by
    cases kind
    case implicationDistribution => exact PureLogicalSchemaStage.membership_specification hℳ .implicationDistribution code
    case selfImplication => exact PureLogicalSchemaStage.membership_specification hℳ .selfImplication code
    case weakening => exact PureLogicalSchemaStage.membership_specification hℳ .weakening code
    case contradiction => exact PureLogicalSchemaStage.membership_specification hℳ .contradiction code
    case classical => exact PureLogicalSchemaStage.membership_specification hℳ .classical code
    case explosion => exact PureLogicalSchemaStage.membership_specification hℳ .explosion code
    case caseAnalysis => exact PureLogicalSchemaStage.membership_specification hℳ .caseAnalysis code
    case quantifierDistribution => exact PureLogicalSchemaStage.membership_specification hℳ .quantifierDistribution code
    case equalityReflexivity => exact PureLogicalSchemaStage.membership_specification hℳ .equalityReflexivity code
  have h := (old_transfer hℳ _ (old_translation _ (by cases kind <;> rfl)) (.cons code .nil)).mp hOld
  cases kind <;> exact h

theorem propositional_axioms (hℳ : Theory.Models ℳ theory) :
    FormalSystem.propositional_axiom_schema_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) :=
  (old_transfer hℳ _ (old_translation _ rfl) .nil).mp (PureLogicalSchemaStage.propositional_axioms hℳ)

theorem quantifier_axioms (hℳ : Theory.Models ℳ theory) :
    FormalSystem.quantifier_axiom_schema_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) := by
  intro code
  exact ⟨membership_specification hℳ .specialization code,
    old_membership hℳ .quantifierDistribution code,membership_specification hℳ .vacuousQuantifier code⟩

theorem equality_axioms (hℳ : Theory.Models ℳ theory) :
    FormalSystem.equality_axiom_schema_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) := by
  intro code
  exact ⟨membership_specification hℳ .equalitySubstitution code,old_membership hℳ .equalityReflexivity code⟩

theorem old_value_graph (hℳ : Theory.Models ℳ theory) (kind : PureLogicalSchemaSets.Kind) :
    (PureLogicalSchemaSets.graph kind).satisfies (templateEnv (.cons (oldValue hℳ kind) .nil)) := by
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

theorem omega_eq (hℳ : Theory.Models ℳ theory) :
    (expansion hℳ).function .omega .nil = PureNaturalInduction.omega hℳ := by
  have h := ((realizes hℳ).function .omega .nil _).mpr rfl
  exact (((PureSyntaxStage.realizes hℳ).function .omega .nil _).mp h).trans (PureSyntaxOperator.omega_eq hℳ)

theorem old_member_bounded (hℳ : Theory.Models ℳ theory) (kind : PureLogicalSchemaSets.Kind) (code : Carrier ℳ)
    (h : membership ℳ code (oldValue hℳ kind)) : membership ℳ code (PureNaturalInduction.omega hℳ) :=
  PureLogicalSchemaSets.member_bounded hℳ kind code
    (((PureFunctionDefinitions.comprehension_correct (PureLogicalSchemaSets.member kind) .nil _).mp (old_value_graph hℳ kind) code).mp h)

theorem member_bounded (hℳ : Theory.Models ℳ theory) (kind : Kind) (code : Carrier ℳ)
    (h : membership ℳ code (value hℳ kind)) : membership ℳ code (PureNaturalInduction.omega hℳ) := by
  have hBound := PureDependentSchemaSets.member_bounded hℳ kind code
    (((PureFunctionDefinitions.comprehension_correct (PureDependentSchemaSets.member kind) .nil _).mp (value_graph hℳ kind) code).mp h)
  have hOmega : (PureTransformStage.expansion hℳ).function .omega .nil = PureNaturalInduction.omega hℳ := by
    have hGraph := ((PureTransformStage.realizes hℳ).function .omega .nil _).mpr rfl
    exact (((PureSyntaxStage.realizes hℳ).function .omega .nil _).mp hGraph).trans (PureSyntaxOperator.omega_eq hℳ)
  exact hOmega ▸ hBound

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureAllSchemaStage
