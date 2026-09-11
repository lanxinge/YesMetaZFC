import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Automation.RelationalCongruence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSyntaxTransform
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFreeVariableOccurs
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureLogicalSchemaStage

/-! # 语法操作的统一扩张

先以最小依赖解释核验两个递归方程，再通过纯翻译相同传入保留全部已完成符号的扩张。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}
namespace PureSyntaxTransform
def localInterpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := PureSyntaxStage.interpretation.function
  relation symbol := match symbol with
    | .syntaxTransform => graph
    | symbol => PureSyntaxStage.interpretation.relation symbol
noncomputable def localExpansion (hℳ : Theory.Models ℳ theory) : Expansion localInterpretation ℳ where
  function := (E hℳ).function
  relation := relations hℳ (state hℳ)
theorem local_map_values {sorts : SortContext S} (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues localInterpretation args = mapValues PureSyntaxStage.interpretation args := rfl

theorem local_realizes (hℳ : Theory.Models ℳ theory) : Realizes (localExpansion hℳ) where
  function symbol args output := by
    change (PureSyntaxStage.interpretation.function symbol).satisfies (templateEnv (.cons output (mapValues localInterpretation args))) ↔ _
    rw [local_map_values]
    exact (PureSyntaxStage.realizes hℳ).function symbol args output
  relation symbol args := by
    cases symbol
    case syntaxTransform =>
      cases args with | cons a0 tail0 =>
      cases tail0 with | cons a1 tail1 =>
      cases tail1 with | cons a2 tail2 =>
      cases tail2 with | cons a3 tail3 =>
      cases tail3 with | cons a4 tail4 =>
      cases tail4 with | cons a5 tail5 =>
      cases tail5 with | cons a6 tail6 =>
      cases tail6
      exact graph_correct hℳ a0 a1 a2 a3 a4 a5 a6
    all_goals
      rw [local_map_values]
      exact (PureSyntaxStage.realizes hℳ).relation _ args

theorem local_definition (hℳ : Theory.Models ℳ theory) (a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ) :
    (FormalSystem.syntax_transform_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here)))))))).satisfies
      (templateEnv (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))) : Env (localExpansion hℳ).model [] [s,s,s,s,s,s,s]) := by
  apply (equation hℳ a0 a1 a2 a3 a4 a5 a6).trans
  have h := PredicateExpansion.evaluate_correct (relations hℳ (state hℳ))
    (templateEnv (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))) : Env (E hℳ).model [] [s,s,s,s,s,s,s]) condition
  rw [← PredicateExpansion.with_templateEnv] at h
  exact h.symm
end PureSyntaxTransform
namespace PureFreeVariableOccurs
def localInterpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := PureSyntaxStage.interpretation.function
  relation symbol := match symbol with
    | .freeVariableOccurs => graph
    | symbol => PureSyntaxStage.interpretation.relation symbol
noncomputable def localExpansion (hℳ : Theory.Models ℳ theory) : Expansion localInterpretation ℳ where
  function := (E hℳ).function
  relation := relations hℳ (state hℳ)
theorem local_map_values {sorts : SortContext S} (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues localInterpretation args = mapValues PureSyntaxStage.interpretation args := rfl

theorem local_realizes (hℳ : Theory.Models ℳ theory) : Realizes (localExpansion hℳ) where
  function symbol args output := by
    change (PureSyntaxStage.interpretation.function symbol).satisfies (templateEnv (.cons output (mapValues localInterpretation args))) ↔ _
    rw [local_map_values]
    exact (PureSyntaxStage.realizes hℳ).function symbol args output
  relation symbol args := by
    cases symbol
    case freeVariableOccurs =>
      cases args with | cons a0 tail0 =>
      cases tail0 with | cons a1 tail1 =>
      cases tail1 with | cons a2 tail2 =>
      cases tail2
      exact graph_correct hℳ a0 a1 a2
    all_goals
      rw [local_map_values]
      exact (PureSyntaxStage.realizes hℳ).relation _ args

theorem local_definition (hℳ : Theory.Models ℳ theory) (a0 a1 a2 : Carrier ℳ) :
    (FormalSystem.free_variable_occurs_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons a0 (.cons a1 (.cons a2 .nil))) : Env (localExpansion hℳ).model [] [s,s,s]) := by
  apply (equation hℳ a0 a1 a2).trans
  have h := PredicateExpansion.evaluate_correct (relations hℳ (state hℳ))
    (templateEnv (.cons a0 (.cons a1 (.cons a2 .nil))) : Env (E hℳ).model [] [s,s,s]) condition
  rw [← PredicateExpansion.with_templateEnv] at h
  exact h.symm
end PureFreeVariableOccurs
namespace PureTransformStage
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := PureLogicalSchemaStage.interpretation.function
  relation symbol := match symbol with
    | .syntaxTransform => PureSyntaxTransform.graph
    | .freeVariableOccurs => PureFreeVariableOccurs.graph
    | symbol => PureLogicalSchemaStage.interpretation.relation symbol
def functionCovered := PureLogicalSchemaStage.functionCovered
def relationCovered : RelationSymbol → Bool
  | .syntaxTransform | .freeVariableOccurs => true
  | symbol => PureLogicalSchemaStage.relationCovered symbol

/-- 当前扩张保留上一完整阶段的覆盖与实际图。 -/
theorem prior_extension : CoveredExtension PureLogicalSchemaStage.interpretation interpretation.function interpretation.relation
    PureLogicalSchemaStage.functionCovered PureLogicalSchemaStage.relationCovered functionCovered relationCovered := by
  constructor <;> intro symbol h <;> cases symbol <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  exact PureLogicalSchemaStage.functional hℳ
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureLogicalSchemaStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureLogicalSchemaStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureLogicalSchemaStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem syntax_transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureSyntaxStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureSyntaxStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureSyntaxStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem prior_function_graph (symbol : FunctionSymbol) : interpretation.function symbol = PureLogicalSchemaStage.interpretation.function symbol := rfl
def syntaxTransform_covered : RelationSymbol → Bool
  | .syntaxTransform => true
  | symbol => PureSyntaxStage.relationCovered symbol

theorem syntaxTransform_translation {parameters : SortContext S} (body : Formula S [] parameters)
    (hCovered : formulaCovered PureSyntaxStage.functionCovered syntaxTransform_covered body = true) :
    openFormula interpretation body = openFormula PureSyntaxTransform.localInterpretation body := by
  exact openFormula_congr PureSyntaxTransform.localInterpretation interpretation.function interpretation.relation
    PureSyntaxStage.functionCovered syntaxTransform_covered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered

theorem syntaxTransform_definition (hℳ : Theory.Models ℳ theory) (a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ) :
    (FormalSystem.syntax_transform_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here)))))))).satisfies
      (templateEnv (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))) : Env (expansion hℳ).model [] [s,s,s,s,s,s,s]) := by
  let sentence : Formula S [] [s,s,s,s,s,s,s] := FormalSystem.syntax_transform_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
  have hOld := (openFormula_correct (PureSyntaxTransform.localExpansion hℳ) (PureSyntaxTransform.local_realizes hℳ) sentence (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil)))))))).mpr (PureSyntaxTransform.local_definition hℳ a0 a1 a2 a3 a4 a5 a6)
  apply (openFormula_correct (expansion hℳ) (realizes hℳ) sentence (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil)))))))).mp
  rw [syntaxTransform_translation sentence rfl]
  exact hOld

theorem syntaxTransform_dependencies : formulaCovered functionCovered relationCovered PureSyntaxTransform.condition = true := rfl

def freeVariableOccurs_covered : RelationSymbol → Bool
  | .freeVariableOccurs => true
  | symbol => PureSyntaxStage.relationCovered symbol

theorem freeVariableOccurs_translation {parameters : SortContext S} (body : Formula S [] parameters)
    (hCovered : formulaCovered PureSyntaxStage.functionCovered freeVariableOccurs_covered body = true) :
    openFormula interpretation body = openFormula PureFreeVariableOccurs.localInterpretation body := by
  exact openFormula_congr PureFreeVariableOccurs.localInterpretation interpretation.function interpretation.relation
    PureSyntaxStage.functionCovered freeVariableOccurs_covered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered

theorem freeVariableOccurs_definition (hℳ : Theory.Models ℳ theory) (a0 a1 a2 : Carrier ℳ) :
    (FormalSystem.free_variable_occurs_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons a0 (.cons a1 (.cons a2 .nil))) : Env (expansion hℳ).model [] [s,s,s]) := by
  let sentence : Formula S [] [s,s,s] := FormalSystem.free_variable_occurs_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  have hOld := (openFormula_correct (PureFreeVariableOccurs.localExpansion hℳ) (PureFreeVariableOccurs.local_realizes hℳ) sentence (.cons a0 (.cons a1 (.cons a2 .nil)))).mpr (PureFreeVariableOccurs.local_definition hℳ a0 a1 a2)
  apply (openFormula_correct (expansion hℳ) (realizes hℳ) sentence (.cons a0 (.cons a1 (.cons a2 .nil)))).mp
  rw [freeVariableOccurs_translation sentence rfl]
  exact hOld

theorem freeVariableOccurs_dependencies : formulaCovered functionCovered relationCovered PureFreeVariableOccurs.condition = true := rfl
end PureTransformStage
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
