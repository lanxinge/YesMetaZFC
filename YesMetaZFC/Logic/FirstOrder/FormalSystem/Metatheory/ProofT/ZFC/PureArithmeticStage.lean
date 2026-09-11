import YesMetaZFC.Automation.RelationalTransfer
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureOrdinalArithmetic

/-! # 加乘幂的实际模型扩张与有限迭代语义 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticStage
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev Operation := PureArithmeticRecurrence.Operation
variable {ℳ : Structure.{0,0,0,x} ℒ}

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .naturalAddition => PureOrdinalArithmetic.graph .addition
  | .naturalMultiplication => PureOrdinalArithmetic.graph .multiplication
  | .naturalExponentiation => PureOrdinalArithmetic.graph .exponentiation
  | symbol => PureDifferenceStage.functionGraph symbol

def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .naturalAddition | .naturalMultiplication | .naturalExponentiation => true
  | symbol => PureDifferenceStage.functionCovered symbol

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureDifferenceStage.interpretation.relation

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  case naturalAddition | naturalMultiplication | naturalExponentiation =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    exact PureOrdinalArithmetic.functional hℳ _ left right
  all_goals exact PureDifferenceStage.functional hℳ _ args

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory)
    (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureDifferenceStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureDifferenceStage.expansion hℳ).function symbol args := by
  exact function_regraph _ _ _ _ (PureDifferenceStage.realizes hℳ) _ (realizes hℳ) symbol hGraph args

theorem omega_eq (hℳ : Theory.Models ℳ theory) : (expansion hℳ).function .omega .nil = omega hℳ := function_preserved hℳ _ rfl _
theorem zero_eq (hℳ : Theory.Models ℳ theory) : (expansion hℳ).function .emptySet .nil = zero hℳ := function_preserved hℳ _ rfl _
theorem succ_eq (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    (expansion hℳ).function .successor (.cons input .nil) = succ hℳ input := function_preserved hℳ _ rfl _
theorem value_eq (hℳ : Theory.Models ℳ theory) (function input : Carrier ℳ) :
    (expansion hℳ).function .application (.cons function (.cons input .nil)) = value hℳ function input := function_preserved hℳ _ rfl _

def symbol : Operation → Nonlogical.BasicSetTheory.FunctionSymbol
  | .addition => .naturalAddition
  | .multiplication => .naturalMultiplication
  | .exponentiation => .naturalExponentiation

noncomputable def arithmetic (hℳ : Theory.Models ℳ theory) (operation : Operation) (left right : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition => (expansion hℳ).function .naturalAddition (.cons left (.cons right .nil))
  | .multiplication => (expansion hℳ).function .naturalMultiplication (.cons left (.cons right .nil))
  | .exponentiation => (expansion hℳ).function .naturalExponentiation (.cons left (.cons right .nil))

theorem arithmetic_graph (hℳ : Theory.Models ℳ theory) (operation : Operation) (left right output : Carrier ℳ) :
    (PureOrdinalArithmetic.graph operation).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      output = arithmetic hℳ operation left right := by
  cases operation
  · exact (realizes hℳ).function .naturalAddition (.cons left (.cons right .nil)) output
  · exact (realizes hℳ).function .naturalMultiplication (.cons left (.cons right .nil)) output
  · exact (realizes hℳ).function .naturalExponentiation (.cons left (.cons right .nil)) output

theorem arithmetic_correct (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    PureOrdinalArithmetic.OrdinalValue hℳ operation (arithmetic hℳ operation left right) left right :=
  (PureOrdinalArithmetic.agrees hℳ operation hLeft hRight _).mp ((arithmetic_graph hℳ operation _ _ _).mpr rfl)

theorem arithmetic_closed (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    membership ℳ (arithmetic hℳ operation left right) (omega hℳ) :=
  PureOrdinalArithmetic.closed hℳ operation hLeft hRight (arithmetic_correct hℳ operation hLeft hRight)

noncomputable def step (hℳ : Theory.Models ℳ theory) (operation : Operation) (left right current : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition => succ hℳ current
  | .multiplication => arithmetic hℳ .addition current right
  | .exponentiation => arithmetic hℳ .multiplication current left

theorem mapping_correct (hℳ : Theory.Models ℳ theory) (function source target : Carrier ℳ) :
    (expansion hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil))) ↔
      PureMappingDefinitions.IsMapping ℳ function source target :=
  ((realizes hℳ).relation .isMapping _).symm.trans (PureMappingDefinitions.isMapping_correct _ _ _)

theorem membership_correct (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :
    (expansion hℳ).relation .membership (.cons left (.cons right .nil)) ↔ membership ℳ left right := Iff.rfl

/-- 当前三个算术符号均已替换；原有限迭代规格仍保持逐值语义。 -/
theorem specification_semantics (hℳ : Theory.Models ℳ theory) (operation : Operation) (left right output : Carrier ℳ) :
    (PureArithmeticRecurrence.specification operation).satisfies
      (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (expansion hℳ).model [] [s,s,s]) ↔
      membership ℳ output (omega hℳ) ∧ ∃ sequence,
        PureArithmeticRecurrence.Iteration hℳ (PureArithmeticRecurrence.length operation left right)
          (PureArithmeticRecurrence.seed hℳ operation right) (step hℳ operation left right) sequence output := by
  cases operation <;>
    simp only [PureArithmeticRecurrence.specification, Nonlogical.BasicSetTheory.natural_addition_spec,
      Nonlogical.BasicSetTheory.natural_multiplication_spec, Nonlogical.BasicSetTheory.natural_exponentiation_spec,
      Nonlogical.BasicSetTheory.natural_addition_bound_graph_condition,
      Nonlogical.BasicSetTheory.natural_multiplication_bound_graph_condition,
      Nonlogical.BasicSetTheory.natural_exponentiation_bound_graph_condition,
      Nonlogical.BasicSetTheory.natural_addition_graph_condition,
      Nonlogical.BasicSetTheory.natural_multiplication_graph_condition,
      Nonlogical.BasicSetTheory.natural_exponentiation_graph_condition,
      Formula.satisfies_existsFreeTop, Formula.satisfies_forallFreeTop, Formula.satisfies,
      Nonlogical.BasicSetTheory.membership_formula, Nonlogical.BasicSetTheory.is_mapping_formula,
      Nonlogical.BasicSetTheory.function_application_term, Nonlogical.BasicSetTheory.successor_term,
      Nonlogical.BasicSetTheory.empty_set_term, Nonlogical.BasicSetTheory.omega_term,
      Nonlogical.BasicSetTheory.natural_addition_term, Nonlogical.BasicSetTheory.natural_multiplication_term,
      Term.eval, Arguments.eval, Term.eval_weakenFree, Expansion.model,
      omega_eq hℳ,zero_eq hℳ,succ_eq hℳ,value_eq hℳ,membership_correct hℳ,mapping_correct hℳ]
  all_goals rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticStage
