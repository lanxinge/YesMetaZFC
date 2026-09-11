import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSyntaxStage
import YesMetaZFC.Logic.FirstOrder.FormalSystem.SemanticInterpretation

/-! # 第三轮首批的统一扩张

非逻辑符号全集取模型内部 ω；结构谓词按原正文纯翻译。
三个递归语法谓词保持原方程，已有函数与规格通过纯翻译传输。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStructureStage
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
  | .relatedNonlogicalSymbolSet => PureSyntaxStage.interpretation.function .omega
  | symbol => PureSyntaxStage.interpretation.function symbol

def prior : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureSyntaxStage.interpretation.relation

def structureBody : Formula S [] [s,s,s] :=
  FormalSystem.structure_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation symbol := match symbol with
    | .isStructure => openFormula prior structureBody
    | symbol => PureSyntaxStage.interpretation.relation symbol

def functionCovered : FunctionSymbol → Bool
  | .relatedNonlogicalSymbolSet => true
  | symbol => PureSyntaxStage.functionCovered symbol
def relationCovered : RelationSymbol → Bool
  | .isStructure => true
  | symbol => PureSyntaxStage.relationCovered symbol

/-- 当前扩张保留上一完整阶段的覆盖与实际图。 -/
theorem prior_extension : CoveredExtension PureRoundTwoStage.interpretation interpretation.function interpretation.relation
    PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered functionCovered relationCovered := by
  constructor <;> intro symbol h <;> cases symbol <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case relatedNonlogicalSymbolSet =>
    cases args
    exact PureSyntaxStage.functional hℳ .omega .nil
  all_goals exact PureSyntaxStage.functional hℳ _ args

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : interpretation.function symbol = PureSyntaxStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureSyntaxStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureSyntaxStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureSyntaxStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureSyntaxStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureSyntaxStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem nonlogical_symbols (hℳ : Theory.Models ℳ theory) :
    (expansion hℳ).function .relatedNonlogicalSymbolSet .nil = (expansion hℳ).function .omega .nil := by
  have hGraph := ((realizes hℳ).function .relatedNonlogicalSymbolSet .nil _).mpr rfl
  exact ((realizes hℳ).function .omega .nil _).mp hGraph

theorem nonlogical_definition (hℳ : Theory.Models ℳ theory) :
    FormalSystem.related_nonlogical_symbol_set_definition_axiom.satisfies
      (templateEnv .nil : Env (expansion hℳ).model [] []) := nonlogical_symbols hℳ

theorem structure_definition (hℳ : Theory.Models ℳ theory) (carrier assignment symbols : Carrier ℳ) :
    (expansion hℳ).relation .isStructure (.cons carrier (.cons assignment (.cons symbols .nil))) ↔
      structureBody.satisfies (templateEnv (.cons carrier (.cons assignment (.cons symbols .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  realizes_definition (expansion hℳ) (realizes hℳ) .isStructure structureBody rfl _

theorem structure_dependencies : formulaCovered functionCovered relationCovered structureBody = true := rfl

/-- 第二轮任意旧正文保持纯翻译时，整项规格在当前统一模型中保持。 -/
theorem round_two_transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hSyntax : openFormula PureSyntaxStage.interpretation body = openFormula PureRoundTwoStage.interpretation body)
    (hStructure : openFormula interpretation body = openFormula PureSyntaxStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureRoundTwoStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) :=
  transfer_regraph _ _ _ _ (PureRoundTwoStage.realizes hℳ) _ (realizes hℳ) body (hStructure.trans hSyntax) args

/-- 既有实际函数图相同，且规格正文在两步扩张中保持时，原规格整体保持。 -/
theorem inherited_specification (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (spec : Formula S [] (s :: S.funcDomain symbol))
    (hGraph : interpretation.function symbol = PureSyntaxStage.interpretation.function symbol)
    (hSyntax : openFormula PureSyntaxStage.interpretation spec = openFormula PureRoundTwoStage.interpretation spec)
    (hStructure : openFormula interpretation spec = openFormula PureSyntaxStage.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ)
    (hSpec : FunctionSpecification (PureRoundTwoStage.expansion hℳ) symbol spec args output) :
    FunctionSpecification (expansion hℳ) symbol (spec) args output :=
  specification_regraph _ (PureRoundTwoStage.realizes hℳ) _ (realizes hℳ) symbol spec
    hGraph (hStructure.trans hSyntax) args output hSpec

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStructureStage
