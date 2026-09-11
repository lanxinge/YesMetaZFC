import YesMetaZFC.Model.Interpretation.RelationalInheritance
import YesMetaZFC.Model.ZFC.Pure.PureTransitiveClosure
import YesMetaZFC.Model.ZFC.Pure.PureGodelPairing

/-! # 配对、传递闭包与有限层级的实际扩张 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSetStage
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
  | .godelPairing => PureGodelPairing.graph
  | .transitiveClosure => PureTransitiveClosure.graph
  | .finiteHierarchy => PureSetIterations.hierarchyGraph
  | symbol => PureArithmeticStage.functionGraph symbol

def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .godelPairing | .transitiveClosure | .finiteHierarchy => true
  | symbol => PureArithmeticStage.functionCovered symbol

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureArithmeticStage.interpretation.relation

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case godelPairing =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    exact PureGodelPairing.functional hℳ left right
  case transitiveClosure =>
    cases args with | cons source tail =>
    cases tail
    exact PureTransitiveClosure.functional hℳ source
  case finiteHierarchy => cases args; exact PureSetIterations.hierarchy_functional hℳ
  all_goals exact PureArithmeticStage.functional hℳ _ args

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureArithmeticStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureArithmeticStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureArithmeticStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureArithmeticStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureArithmeticStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureArithmeticStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

theorem omega_eq (hℳ : Theory.Models ℳ theory) : (expansion hℳ).function .omega .nil = omega hℳ :=
  (function_preserved hℳ .omega rfl .nil).trans (PureArithmeticStage.omega_eq hℳ)
theorem zero_eq (hℳ : Theory.Models ℳ theory) : (expansion hℳ).function .emptySet .nil = zero hℳ :=
  (function_preserved hℳ .emptySet rfl .nil).trans (PureArithmeticStage.zero_eq hℳ)
theorem succ_eq (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    (expansion hℳ).function .successor (.cons input .nil) = succ hℳ input :=
  (function_preserved hℳ .successor rfl _).trans (PureArithmeticStage.succ_eq hℳ input)
theorem value_eq (hℳ : Theory.Models ℳ theory) (function input : Carrier ℳ) :
    (expansion hℳ).function .application (.cons function (.cons input .nil)) = value hℳ function input :=
  (function_preserved hℳ .application rfl _).trans (PureArithmeticStage.value_eq hℳ function input)

theorem godel_specification (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .godelPairing (PureGodelPairing.specification) (.cons left (.cons right .nil)) output :=
  ((realizes hℳ).function .godelPairing _ output).symm.trans
    ((PureGodelPairing.agrees hℳ hLeft hRight output).trans (transfer hℳ _ rfl (.cons output (.cons left (.cons right .nil)))))

theorem closure_specification (hℳ : Theory.Models ℳ theory) (source output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .transitiveClosure (PureTransitiveClosure.specification) (.cons source .nil) output :=
  ((realizes hℳ).function .transitiveClosure _ output).symm.trans
    ((openFormula_correct (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ)
      PureTransitiveClosure.specification (.cons output (.cons source .nil))).trans (transfer hℳ _ rfl (.cons output (.cons source .nil))))

def hierarchySpec : Formula S [] [s] :=
  Nonlogical.BasicSetTheory.transfinite_recursion_spec_at (pre := [s]) Nonlogical.BasicSetTheory.finite_hierarchy_step
    Nonlogical.BasicSetTheory.empty_set_term (.fvar .here)

/-- 原 ω 递归规格逐字对应函数、定义域、初值及幂集后继方程。 -/
theorem hierarchy_semantics (hℳ : Theory.Models ℳ theory) (sequence : Carrier ℳ) :
    hierarchySpec.satisfies (templateEnv (.cons sequence .nil) : Env (expansion hℳ).model [] [s]) ↔
      (expansion hℳ).relation .isFunction (.cons sequence .nil) ∧
        (expansion hℳ).function .domain (.cons sequence .nil) = omega hℳ ∧
          value hℳ sequence (zero hℳ) = zero hℳ ∧
            ∀ input, membership ℳ input (omega hℳ) → ∀ next,
              value hℳ sequence (succ hℳ input) = next ↔
                next = (expansion hℳ).function .powerSet (.cons (value hℳ sequence input) .nil) := by
  simp only [hierarchySpec,Nonlogical.BasicSetTheory.transfinite_recursion_spec_at,
    Nonlogical.BasicSetTheory.transfinite_recursion_step_condition_at,Formula.satisfies]
  change ((expansion hℳ).relation .isFunction (.cons sequence .nil) ∧
    (expansion hℳ).function .domain (.cons sequence .nil) = (expansion hℳ).function .omega .nil ∧
    (expansion hℳ).function .application (.cons sequence (.cons ((expansion hℳ).function .emptySet .nil) .nil)) = (expansion hℳ).function .emptySet .nil ∧
    (∀ input, membership ℳ input ((expansion hℳ).function .omega .nil) → ∀ next,
      (expansion hℳ).function .application (.cons sequence (.cons ((expansion hℳ).function .successor (.cons input .nil)) .nil)) = next ↔
      next = (expansion hℳ).function .powerSet (.cons ((expansion hℳ).function .application (.cons sequence (.cons input .nil))) .nil))) ↔ _
  simp only [omega_eq hℳ,zero_eq hℳ,succ_eq hℳ,value_eq hℳ]
  rfl

/-- 选择的有限层级满足原公理的全部 ω 递推要求。 -/
theorem hierarchy_specification (hℳ : Theory.Models ℳ theory) :
    hierarchySpec.satisfies (templateEnv (.cons ((expansion hℳ).function .finiteHierarchy .nil) .nil) : Env (expansion hℳ).model [] [s]) := by
  let sequence := (expansion hℳ).function .finiteHierarchy .nil
  have hGraph := ((realizes hℳ).function .finiteHierarchy .nil sequence).mpr rfl
  have hIteration := PureSetIterations.hierarchy_iterates hℳ hGraph
  apply (hierarchy_semantics hℳ sequence).mpr
  refine ⟨?_,?_,hIteration.2.2.1,?_⟩
  · exact ((realizes hℳ).relation .isFunction (.cons sequence .nil)).mp
      ((PureRelationDefinitions.isFunction_satisfies (templateEnv (.cons sequence .nil)) (.fvar .here)).mpr hIteration.1)
  · have hDomain := (PureRelationCoordinates.domain_correct _ sequence).mp
      (((realizes hℳ).function .domain (.cons sequence .nil) _).mpr rfl)
    exact extensionality hℳ _ _ (fun input => (hDomain input).trans (hIteration.2.1 input).symm)
  · intro input hInput next
    have hPower := hIteration.2.2.2 input hInput
    have hEqual : value hℳ sequence (succ hℳ input) =
        (expansion hℳ).function .powerSet (.cons (value hℳ sequence input) .nil) :=
      ((realizes hℳ).function .powerSet (.cons (value hℳ sequence input) .nil) _).mp
        ((PureFunctionDefinitions.comprehension_correct _ _ _).mpr hPower)
    rw [hEqual]
    exact eq_comm

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSetStage
