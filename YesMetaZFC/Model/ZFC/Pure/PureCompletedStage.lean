import YesMetaZFC.Model.Interpretation.RelationalInheritance
import YesMetaZFC.Model.ZFC.Pure.PureLogicalStage
import YesMetaZFC.Model.ZFC.Pure.PureValueStage

/-! # 有限支撑基全部符号的实际纯解释

最后加入两个求值关系，保留此前全部函数和关系图。每项原递归定义在当前模型
中逐参数成立；全部支撑公理及裸 ZFC Rosser 合同的总装配仍是独立的后续证明。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureCompletedStage
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory FormalSystem
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := PureLogicalStage.interpretation.function
  relation symbol := match symbol with
    | .termValue => PureValueFixedPoint.termGraph
    | .termListValue => PureValueFixedPoint.listGraph
    | symbol => PureLogicalStage.interpretation.relation symbol
def functionCovered := PureLogicalStage.functionCovered
def relationCovered : RelationSymbol → Bool
  | .termValue | .termListValue => true
  | symbol => PureLogicalStage.relationCovered symbol

/-- 当前扩张保留上一完整阶段的覆盖与实际图。 -/
theorem prior_extension : CoveredExtension PureLogicalStage.interpretation interpretation.function interpretation.relation
    PureLogicalStage.functionCovered PureLogicalStage.relationCovered functionCovered relationCovered := by
  constructor <;> intro symbol h <;> cases symbol <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  exact PureLogicalStage.functional hℳ
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem prior_function_graph (symbol : FunctionSymbol) : interpretation.function symbol = PureLogicalStage.interpretation.function symbol := rfl
theorem prior_translation {parameters : SortContext S} (body : Formula S [] parameters)
    (hCovered : formulaCovered PureLogicalStage.functionCovered PureLogicalStage.relationCovered body = true) :
    openFormula interpretation body = openFormula PureLogicalStage.interpretation body :=
  prior_extension.translation body hCovered

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureLogicalStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureLogicalStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureLogicalStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem value_translation {parameters : SortContext S} (body : Formula S [] parameters)
    (hCovered : formulaCovered PureRelatedStage.functionCovered PureValueStage.relationCovered body = true) :
    openFormula interpretation body = openFormula PureValueStage.interpretation body :=
  openFormula_congr PureValueStage.interpretation interpretation.function interpretation.relation
    PureRelatedStage.functionCovered PureValueStage.relationCovered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered

theorem termValue_definition (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment code result : Carrier ℳ) :
    PureValueStage.termValueDefinition.satisfies (templateEnv (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil)))))) : Env (expansion hℳ).model [] [s,s,s,s,s,s]) := by
  exact (transfer_regraph _ _ _ _ (PureValueStage.realizes hℳ) _ (realizes hℳ)
    _ (value_translation _ rfl) _).mp (PureValueStage.termValue_definition hℳ carrier interpretation symbols assignment code result)

theorem termListValue_definition (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment length code result : Carrier ℳ) :
    PureValueStage.termListValueDefinition.satisfies (templateEnv (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil))))))) : Env (expansion hℳ).model [] [s,s,s,s,s,s,s]) := by
  exact (transfer_regraph _ _ _ _ (PureValueStage.realizes hℳ) _ (realizes hℳ)
    _ (value_translation _ rfl) _).mp (PureValueStage.termListValue_definition hℳ carrier interpretation symbols assignment length code result)

theorem logical_code_axioms (hℳ : Theory.Models ℳ theory) :
    logical_axiom_code_definition_axiom.satisfies (templateEnv .nil : Env (expansion hℳ).model [] []) :=
  (transfer hℳ _ (prior_translation _ rfl) .nil).mp (PureLogicalStage.logical_code_axioms hℳ)

theorem schema_axioms (hℳ : Theory.Models ℳ theory) :
    (propositional_axiom_schema_definition_axiom.conj (quantifier_axiom_schema_definition_axiom.conj equality_axiom_schema_definition_axiom)).satisfies
      (templateEnv .nil : Env (expansion hℳ).model [] []) := by
  let sentence := propositional_axiom_schema_definition_axiom.conj (quantifier_axiom_schema_definition_axiom.conj equality_axiom_schema_definition_axiom)
  have hOld : sentence.satisfies (templateEnv .nil : Env (PureAllSchemaStage.expansion hℳ).model [] []) :=
    ⟨PureAllSchemaStage.propositional_axioms hℳ,PureAllSchemaStage.quantifier_axioms hℳ,PureAllSchemaStage.equality_axioms hℳ⟩
  have hTranslate : openFormula interpretation sentence = openFormula PureAllSchemaStage.interpretation sentence :=
    openFormula_congr PureAllSchemaStage.interpretation interpretation.function interpretation.relation
      PureAllSchemaStage.functionCovered PureAllSchemaStage.relationCovered
      (by intro symbol h; cases symbol <;> first | rfl | contradiction)
      (by intro symbol h; cases symbol <;> first | rfl | contradiction) sentence rfl
  exact (transfer_regraph _ _ _ _ (PureAllSchemaStage.realizes hℳ) _ (realizes hℳ)
    sentence hTranslate .nil).mp hOld
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureCompletedStage
