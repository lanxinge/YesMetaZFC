import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSequenceFlatten

/-! # 第二轮全部符号的统一纯扩张

四个末尾函数均在同一扩张中满足原 guard 下的规格；旧图与旧正文通过纯翻译保持。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundTwoStage
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .finiteSequenceFlatten => PureSequenceFlatten.graph
  | symbol => PureConcatenationStage.functionGraph symbol
def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .finiteSequenceFlatten => true
  | symbol => PureConcatenationStage.functionCovered symbol
def relationCovered := PureConcatenationStage.relationCovered
def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureConcatenationStage.interpretation.relation

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case finiteSequenceFlatten =>
    cases args with | cons family tail =>
    cases tail
    exact PureSequenceFlatten.functional hℳ family
  all_goals exact PureConcatenationStage.functional hℳ _ args
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureConcatenationStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureConcatenationStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureConcatenationStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args
theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureConcatenationStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureConcatenationStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureConcatenationStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem relation_preserved (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.RelationSymbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureConcatenationStage.expansion hℳ).relation symbol args := by
  exact relation_regraph _ _ _ _ (PureConcatenationStage.realizes hℳ) _ (realizes hℳ) symbol rfl args

theorem prior_function (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureNaturalDifferenceStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureNaturalDifferenceStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureNaturalDifferenceStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem prior_transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureNaturalDifferenceStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureNaturalDifferenceStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureNaturalDifferenceStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

/-- 任一既有实际图与规格正文保持时，整个定义等价在第二轮终点保持。 -/
theorem inherited_specification (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (spec : Formula S [] (s :: S.funcDomain symbol))
    (hGraph : interpretation.function symbol = PureNaturalDifferenceStage.interpretation.function symbol)
    (hTranslate : openFormula interpretation spec = openFormula PureNaturalDifferenceStage.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ)
    (hSpec : FunctionSpecification (PureNaturalDifferenceStage.expansion hℳ) symbol spec args output) :
    FunctionSpecification (expansion hℳ) symbol (spec) args output :=
  specification_regraph _ (PureNaturalDifferenceStage.realizes hℳ) _ (realizes hℳ) symbol spec
    hGraph hTranslate args output hSpec

theorem order_type_specification (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ}
    (hGuard : (expansion hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil))) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .naturalOrderType (PureNaturalOrderType.specification) (.cons relation (.cons carrier .nil)) output := by
  rw [FunctionSpecification, function_preserved hℳ .naturalOrderType rfl]
  exact (PureConcatenationStage.order_type_specification hℳ ((relation_preserved hℳ _ _).mp hGuard) output).trans (transfer hℳ _ rfl _)

theorem subset_type_specification (hℳ : Theory.Models ℳ theory) {subset : Carrier ℳ}
    (hGuard : ∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .naturalSubsetType (PureNaturalSubsetType.specification) (.cons subset .nil) output := by
  rw [FunctionSpecification, function_preserved hℳ .naturalSubsetType rfl]
  exact (PureConcatenationStage.subset_type_specification hℳ hGuard output).trans (transfer hℳ _ rfl _)

theorem concatenation_specification (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : PureFiniteSequenceCore.Finite hℳ left) (hRight : PureFiniteSequenceCore.Finite hℳ right) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .finiteSequenceConcatenation (PureSequenceConcatenation.specification) (.cons left (.cons right .nil)) output := by
  rw [FunctionSpecification, function_preserved hℳ .finiteSequenceConcatenation rfl]
  exact (PureConcatenationStage.concatenation_specification hℳ hLeft hRight output).trans (transfer hℳ _ rfl _)

theorem flatten_specification (hℳ : Theory.Models ℳ theory) {family : Carrier ℳ}
    (hFamily : PureSequenceFlatten.Family hℳ family) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .finiteSequenceFlatten (PureSequenceFlatten.specification) (.cons family .nil) output :=
  ((realizes hℳ).function .finiteSequenceFlatten (.cons family .nil) output).symm.trans
    ((PureSequenceFlatten.agrees hℳ hFamily output).trans (transfer hℳ _ rfl _))

/-- 四项完整原定义实例在同一个最终扩张中成立。 -/
theorem order_type_definition (hℳ : Theory.Models ℳ theory) (relation carrier output : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.natural_order_type_definition_instance
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)).satisfies
        (templateEnv (.cons output (.cons relation (.cons carrier .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  fun hGuard => order_type_specification hℳ hGuard output

theorem subset_type_definition (hℳ : Theory.Models ℳ theory) (subset output : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.natural_subset_type_definition_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons subset .nil)) : Env (expansion hℳ).model [] [s,s]) := by
  intro hGuard
  have hOmega : (expansion hℳ).function .omega .nil = omega hℳ :=
    (function_preserved hℳ .omega rfl _).trans (PureConcatenationStage.omega_eq hℳ)
  have hSubset := ((realizes hℳ).relation .subset (.cons subset (.cons ((expansion hℳ).function .omega .nil) .nil))).mpr hGuard
  have hMembers := (PureRelationDefinitions.subset_correct subset _).mp hSubset
  rw [hOmega] at hMembers
  exact subset_type_specification hℳ hMembers output

theorem concatenation_definition (hℳ : Theory.Models ℳ theory) (left right output : Carrier ℳ) :
    (FormalSystem.finite_sequence_concatenation_definition_instance
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)).satisfies
        (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (expansion hℳ).model [] [s,s,s]) := by
  intro hGuard
  have hOld := (transfer hℳ PureSequenceConcatenation.guard rfl (.cons output (.cons left (.cons right .nil)))).mpr hGuard
  exact concatenation_specification hℳ ((PureConcatenationStage.finite_correct hℳ _ _).mp hOld.1)
    ((PureConcatenationStage.finite_correct hℳ _ _).mp hOld.2) output

theorem flatten_definition (hℳ : Theory.Models ℳ theory) (family output : Carrier ℳ) :
    (FormalSystem.finite_sequence_flatten_definition_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons family .nil)) : Env (expansion hℳ).model [] [s,s]) := by
  intro hGuard
  have hOld := (transfer hℳ PureSequenceFlatten.guard rfl (.cons output (.cons family .nil))).mpr hGuard
  exact flatten_specification hℳ ((PureSequenceFlatten.family_correct hℳ _ _).mp hOld) output

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundTwoStage
