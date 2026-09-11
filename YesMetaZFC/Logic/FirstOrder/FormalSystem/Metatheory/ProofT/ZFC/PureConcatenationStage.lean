import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureNaturalSubsetType
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSequenceConcatenation

/-! # 两个序型函数与有限拼接的统一扩张 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureConcatenationStage
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
  | .naturalOrderType => PureNaturalOrderType.graph
  | .naturalSubsetType => PureNaturalSubsetType.graph
  | .finiteSequenceConcatenation => PureSequenceConcatenation.graph
  | symbol => PureNaturalDifferenceStage.functionGraph symbol
def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .naturalOrderType | .naturalSubsetType | .finiteSequenceConcatenation => true
  | symbol => PureNaturalDifferenceStage.functionCovered symbol
def relationCovered := PureNaturalDifferenceStage.relationCovered
def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureNaturalDifferenceStage.interpretation.relation

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case naturalOrderType =>
    cases args with | cons relation tail =>
    cases tail with | cons carrier tail =>
    cases tail
    exact PureNaturalOrderType.functional hℳ relation carrier
  case naturalSubsetType =>
    cases args with | cons subset tail =>
    cases tail
    exact PureNaturalSubsetType.functional hℳ subset
  case finiteSequenceConcatenation =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    exact PureSequenceConcatenation.functional hℳ left right
  all_goals exact PureNaturalDifferenceStage.functional hℳ _ args
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureNaturalDifferenceStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureNaturalDifferenceStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureNaturalDifferenceStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args
theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureNaturalDifferenceStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureNaturalDifferenceStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureNaturalDifferenceStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem relation_preserved (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.RelationSymbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureNaturalDifferenceStage.expansion hℳ).relation symbol args := by
  exact relation_regraph _ _ _ _ (PureNaturalDifferenceStage.realizes hℳ) _ (realizes hℳ) symbol rfl args

theorem value_eq (hℳ : Theory.Models ℳ theory) (function input : Carrier ℳ) :
    (expansion hℳ).function .application (.cons function (.cons input .nil)) = value hℳ function input :=
  (function_preserved hℳ .application rfl _).trans (PureOrderSemantics.value_eq hℳ function input)
theorem domain_eq (hℳ : Theory.Models ℳ theory) (function : Carrier ℳ) :
    (expansion hℳ).function .domain (.cons function .nil) = PureOrderSemantics.domain hℳ function :=
  function_preserved hℳ .domain rfl _
theorem zero_eq (hℳ : Theory.Models ℳ theory) : (expansion hℳ).function .emptySet .nil = zero hℳ :=
  (function_preserved hℳ .emptySet rfl _).trans (PureOrderSemantics.zero_eq hℳ)
theorem omega_eq (hℳ : Theory.Models ℳ theory) : (expansion hℳ).function .omega .nil = omega hℳ :=
  (function_preserved hℳ .omega rfl _).trans (PureOrderSemantics.omega_eq hℳ)
theorem succ_eq (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    (expansion hℳ).function .successor (.cons input .nil) = succ hℳ input :=
  (function_preserved hℳ .successor rfl _).trans (PureNaturalDifferenceStage.function_from_difference hℳ .successor rfl _)

theorem finite_correct (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (expansion hℳ).model bound free) (sequence : Term S bound free s) :
    (FormalSystem.finite_sequence_condition sequence).satisfies env ↔ PureFiniteSequenceCore.Finite hℳ (sequence.eval env) := by
  change ((PureOrderSemantics.E hℳ).relation .isFunction (.cons (sequence.eval env) .nil) ∧
    membership ℳ ((expansion hℳ).function .domain (.cons (sequence.eval env) .nil)) ((expansion hℳ).function .omega .nil)) ↔ _
  rw [PureOrderSemantics.function_correct hℳ,domain_eq hℳ,omega_eq hℳ]
  rfl

noncomputable abbrev concat (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :=
  (expansion hℳ).function .finiteSequenceConcatenation (.cons left (.cons right .nil))
theorem concat_correct (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : PureFiniteSequenceCore.Finite hℳ left) (hRight : PureFiniteSequenceCore.Finite hℳ right) :
    PureSequenceConcatenation.Concats hℳ left right (concat hℳ left right) := by
  have hGraph := ((realizes hℳ).function .finiteSequenceConcatenation (.cons left (.cons right .nil)) _).mpr rfl
  exact (PureSequenceConcatenation.specification_correct hℳ hLeft hRight _).mp
    ((PureSequenceConcatenation.agrees hℳ hLeft hRight _).mp hGraph)

theorem order_type_specification (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ}
    (hGuard : (expansion hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil))) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .naturalOrderType (PureNaturalOrderType.specification) (.cons relation (.cons carrier .nil)) output :=
  ((realizes hℳ).function .naturalOrderType (.cons relation (.cons carrier .nil)) output).symm.trans
    ((PureNaturalOrderType.agrees hℳ ((relation_preserved hℳ _ _).mp hGuard) output).trans (transfer hℳ _ rfl _))

theorem subset_type_specification (hℳ : Theory.Models ℳ theory) {subset : Carrier ℳ}
    (hGuard : ∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .naturalSubsetType (PureNaturalSubsetType.specification) (.cons subset .nil) output :=
  ((realizes hℳ).function .naturalSubsetType (.cons subset .nil) output).symm.trans
    ((PureNaturalSubsetType.agrees hℳ hGuard output).trans (transfer hℳ _ rfl _))

theorem concatenation_specification (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : PureFiniteSequenceCore.Finite hℳ left) (hRight : PureFiniteSequenceCore.Finite hℳ right) (output : Carrier ℳ) :
    output = concat hℳ left right ↔
      PureSequenceConcatenation.specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  ((realizes hℳ).function .finiteSequenceConcatenation (.cons left (.cons right .nil)) output).symm.trans
    ((PureSequenceConcatenation.agrees hℳ hLeft hRight output).trans (transfer hℳ _ rfl _))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureConcatenationStage
