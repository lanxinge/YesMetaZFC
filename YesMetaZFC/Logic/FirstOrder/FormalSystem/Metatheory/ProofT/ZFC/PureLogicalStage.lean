import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureLogicalClosure

/-! # 逻辑公理集合与识别关系的统一扩张

同一模型中的基础集合是十二个模式的并集，逻辑集合是全称闭合生成算子的
最小不动点；识别关系精确取其成员关系。满足原闭合性和生成性两项规格。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalStage
open PureModel PureLogicalClosure
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory FormalSystem
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def codeGraph : Formula ℒ [] [setSort] :=
  .existsE setSort <| .conj (applyTemplate logicalGraph (.cons (.bvar .here) .nil))
    (PureRelationDefinitions.mem (.fvar .here) (.bvar .here))

theorem logical_unique (hℳ : Theory.Models ℳ theory) {first second : Carrier ℳ}
    (hFirst : logicalGraph.satisfies (templateEnv (.cons first .nil)))
    (hSecond : logicalGraph.satisfies (templateEnv (.cons second .nil))) : first = second := by
  obtain ⟨output,_,hUnique⟩ := logical_functional hℳ
  exact (hUnique first hFirst).trans (hUnique second hSecond).symm

theorem code_graph_correct (hℳ : Theory.Models ℳ theory) {output : Carrier ℳ}
    (hOutput : logicalGraph.satisfies (templateEnv (.cons output .nil))) (code : Carrier ℳ) :
    codeGraph.satisfies (templateEnv (.cons code .nil)) ↔ membership ℳ code output := by
  change (∃ candidate, _ ∧ membership ℳ code candidate) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,hMember⟩
    have hGraph : logicalGraph.satisfies (templateEnv (.cons candidate .nil)) := (applyTemplate_satisfies _ _ _).mp hCandidate
    exact logical_unique hℳ hGraph hOutput ▸ hMember
  · intro hMember
    exact ⟨output,(applyTemplate_satisfies _ _ _).mpr hOutput,hMember⟩

def functionGraph (symbol : FunctionSymbol) : Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) := match symbol with
  | .baseLogicalAxiomSet => baseGraph
  | .logicalAxiomSet => logicalGraph
  | symbol => PureAllSchemaStage.interpretation.function symbol
def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation symbol := match symbol with
    | .isLogicalAxiomCode => codeGraph
    | symbol => PureAllSchemaStage.interpretation.relation symbol
def functionCovered : FunctionSymbol → Bool
  | .baseLogicalAxiomSet | .logicalAxiomSet => true
  | symbol => PureAllSchemaStage.functionCovered symbol
def relationCovered : RelationSymbol → Bool
  | .isLogicalAxiomCode => true
  | symbol => PureAllSchemaStage.relationCovered symbol

/-- 当前扩张保留上一完整阶段的覆盖与实际图。 -/
theorem prior_extension : CoveredExtension PureAllSchemaStage.interpretation interpretation.function interpretation.relation
    PureAllSchemaStage.functionCovered PureAllSchemaStage.relationCovered functionCovered relationCovered := by
  constructor <;> intro symbol h <;> cases symbol <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case baseLogicalAxiomSet => cases args; exact base_functional hℳ
  case logicalAxiomSet => cases args; exact logical_functional hℳ
  all_goals exact PureAllSchemaStage.functional hℳ _ args
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

noncomputable def baseValue (hℳ : Theory.Models ℳ theory) : Carrier ℳ := (expansion hℳ).function .baseLogicalAxiomSet .nil
noncomputable def logicalValue (hℳ : Theory.Models ℳ theory) : Carrier ℳ := (expansion hℳ).function .logicalAxiomSet .nil
theorem base_graph (hℳ : Theory.Models ℳ theory) : baseGraph.satisfies (templateEnv (.cons (baseValue hℳ) .nil)) :=
  ((realizes hℳ).function .baseLogicalAxiomSet .nil _).mpr rfl
theorem logical_graph (hℳ : Theory.Models ℳ theory) : logicalGraph.satisfies (templateEnv (.cons (logicalValue hℳ) .nil)) :=
  ((realizes hℳ).function .logicalAxiomSet .nil _).mpr rfl

theorem prior_translation {parameters : SortContext S} (body : Formula S [] parameters)
    (hCovered : formulaCovered PureAllSchemaStage.functionCovered PureAllSchemaStage.relationCovered body = true) :
    openFormula interpretation body = openFormula PureAllSchemaStage.interpretation body :=
  prior_extension.translation body hCovered

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureAllSchemaStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureAllSchemaStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureAllSchemaStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem base_membership (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ) :
    membership ℳ code (baseValue hℳ) ↔ baseCondition.satisfies
      (templateEnv (.cons code .nil) : Env (expansion hℳ).model [] [s]) :=
  ((base_correct hℳ _).mp (base_graph hℳ) code).trans
    (transfer hℳ baseCondition (prior_translation _ rfl) (.cons code .nil))

theorem generation_specification (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ) :
    membership ℳ code (logicalValue hℳ) ↔ generation.satisfies
      (templateEnv (.cons code (.cons (logicalValue hℳ) .nil)) : Env (expansion hℳ).model [] [s,s]) :=
  (logical_fixed hℳ (logical_graph hℳ) code).trans
    (transfer hℳ generation (prior_translation _ dependencies_covered) (.cons code (.cons (logicalValue hℳ) .nil)))

theorem base_subset (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ)
    (hCode : membership ℳ code (baseValue hℳ)) : membership ℳ code (logicalValue hℳ) := by
  have hBase := ((base_correct hℳ _).mp (base_graph hℳ) code).mp hCode
  have hStep := (body_correct hℳ (logicalValue hℳ) code).mpr (Or.inl hBase)
  exact ((PureLeastFixedPoint.fixed hℳ body .nil (PureNaturalInduction.omega hℳ) (body_bounded hℳ)
    (body_mono hℳ) (logical_graph hℳ)).1 code).mpr hStep

theorem closure_rule (hℳ : Theory.Models ℳ theory) (source index target : Carrier ℳ)
    (hSource : membership ℳ source (logicalValue hℳ))
    (hClosure : (canonical_forall_closure_code_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons source (.cons index (.cons target .nil))) : Env (expansion hℳ).model [] [s,s,s])) :
    membership ℳ target (logicalValue hℳ) := by
  have hOld : Closure hℳ source index target := (transfer hℳ _ (prior_translation _ rfl) _).mpr hClosure
  have hStep := (body_correct hℳ (logicalValue hℳ) target).mpr (Or.inr ⟨source,index,hSource,hOld⟩)
  exact ((PureLeastFixedPoint.fixed hℳ body .nil (PureNaturalInduction.omega hℳ) (body_bounded hℳ)
    (body_mono hℳ) (logical_graph hℳ)).1 target).mpr hStep

theorem logical_closed (hℳ : Theory.Models ℳ theory) :
    (logical_axiom_code_closed_condition (logical_axiom_set_term : Term S [] [] s)).satisfies
      (templateEnv .nil : Env (expansion hℳ).model [] []) := by
  constructor
  · exact ((realizes hℳ).relation .subset (.cons (baseValue hℳ) (.cons (logicalValue hℳ) .nil))).mp
      ((PureRelationDefinitions.subset_correct _ _).mpr (base_subset hℳ))
  · intro source index target h
    exact closure_rule hℳ source index target h.1 h.2

theorem logical_generated (hℳ : Theory.Models ℳ theory) :
    (logical_axiom_code_generated_condition (logical_axiom_set_term : Term S [] [] s)).satisfies
      (templateEnv .nil : Env (expansion hℳ).model [] []) := by
  intro code
  exact generation_specification hℳ code

theorem logical_definition (hℳ : Theory.Models ℳ theory) :
    logical_axiom_set_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) :=
  ⟨logical_closed hℳ,logical_generated hℳ⟩
theorem base_definition (hℳ : Theory.Models ℳ theory) :
    base_logical_axiom_set_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) := by
  intro code; exact base_membership hℳ code

theorem code_definition (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ) :
    (expansion hℳ).relation .isLogicalAxiomCode (.cons code .nil) ↔ membership ℳ code (logicalValue hℳ) :=
  ((realizes hℳ).relation .isLogicalAxiomCode (.cons code .nil)).symm.trans (code_graph_correct hℳ (logical_graph hℳ) code)

theorem logical_code_axioms (hℳ : Theory.Models ℳ theory) :
    logical_axiom_code_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) :=
  ⟨base_definition hℳ,logical_definition hℳ,fun code => code_definition hℳ code⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalStage
