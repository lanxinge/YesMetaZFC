import YesMetaZFC.Model.Interpretation.RelationalInheritance
import YesMetaZFC.Model.ZFC.Pure.PureSetStage

/-! # 有限宇宙与遗传有限关系

有限宇宙按原正文取有限层级值域之并，遗传有限关系按原正文取传递闭包的有限性。
这两个定义只消费已经给出纯图的符号。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteUniverseStage
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

def universeSpec : Formula S [] [s] := .equal (.fvar .here)
  (Nonlogical.BasicSetTheory.union_term (Nonlogical.BasicSetTheory.range_term Nonlogical.BasicSetTheory.finite_hierarchy_term))
def universeGraph : Formula ℒ [] [setSort] := openFormula PureSetStage.interpretation universeSpec
def hereditaryCondition : Formula S [] [s] := Nonlogical.BasicSetTheory.hereditarily_finite_condition (.fvar .here)
def hereditaryGraph : Formula ℒ [] [setSort] := openFormula PureSetStage.interpretation hereditaryCondition

theorem universe_functional (hℳ : Theory.Models ℳ theory) :
    ∃ output : Carrier ℳ, universeGraph.satisfies (templateEnv (.cons output .nil)) ∧
      ∀ other, universeGraph.satisfies (templateEnv (.cons other .nil)) → other = output := by
  let output := (PureSetStage.expansion hℳ).function .union
    (.cons ((PureSetStage.expansion hℳ).function .range
      (.cons ((PureSetStage.expansion hℳ).function .finiteHierarchy .nil) .nil)) .nil)
  have hCorrect (candidate : Carrier ℳ) :
      universeGraph.satisfies (templateEnv (.cons candidate .nil)) ↔ candidate = output :=
    openFormula_correct (PureSetStage.expansion hℳ) (PureSetStage.realizes hℳ) universeSpec (.cons candidate .nil)
  exact ⟨output,(hCorrect output).mpr rfl,fun other hOther => (hCorrect other).mp hOther⟩

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .finiteUniverse => universeGraph
  | symbol => PureSetStage.functionGraph symbol
def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .finiteUniverse => true
  | symbol => PureSetStage.functionCovered symbol
def relationCovered : Nonlogical.BasicSetTheory.RelationSymbol → Bool
  | .isHereditarilyFinite => true
  | symbol => PureNaturalRelations.relationCovered symbol
def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation symbol := match symbol with
    | .isHereditarilyFinite => hereditaryGraph
    | symbol => PureSetStage.interpretation.relation symbol

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case finiteUniverse => cases args; exact universe_functional hℳ
  all_goals exact PureSetStage.functional hℳ _ args
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureSetStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureSetStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureSetStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args
theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureSetStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureSetStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureSetStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem universe_specification (hℳ : Theory.Models ℳ theory) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .finiteUniverse (universeSpec) .nil output :=
  ((realizes hℳ).function .finiteUniverse .nil output).symm.trans
    ((openFormula_correct (PureSetStage.expansion hℳ) (PureSetStage.realizes hℳ) universeSpec (.cons output .nil)).trans
      (transfer hℳ universeSpec rfl (.cons output .nil)))
theorem universe_axiom (hℳ : Theory.Models ℳ theory) :
    Nonlogical.BasicSetTheory.finite_universe_definition_axiom.satisfies
      (templateEnv .nil : Env (expansion hℳ).model [] []) :=
  (universe_specification hℳ _).mp rfl
theorem hereditary_definition (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    (expansion hℳ).relation .isHereditarilyFinite (.cons input .nil) ↔
      hereditaryCondition.satisfies (templateEnv (.cons input .nil) : Env (expansion hℳ).model [] [s]) :=
  realizes_definition (expansion hℳ) (realizes hℳ) .isHereditarilyFinite hereditaryCondition rfl (.cons input .nil)
theorem hereditary_instance (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (expansion hℳ).model bound free) (input : Term S bound free s) :
    (Nonlogical.BasicSetTheory.hereditarily_finite_definition_instance input).satisfies env :=
  hereditary_definition hℳ (input.eval env)
theorem dependencies_covered :
    formulaCovered PureSetStage.functionCovered PureNaturalRelations.relationCovered universeSpec = true ∧
    formulaCovered PureSetStage.functionCovered PureNaturalRelations.relationCovered hereditaryCondition = true := ⟨rfl,rfl⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteUniverseStage
