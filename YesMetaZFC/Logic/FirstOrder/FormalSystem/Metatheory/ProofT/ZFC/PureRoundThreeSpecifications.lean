import YesMetaZFC.Automation.RelationalInheritance
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureStructureStage

/-! # 第三轮首批对既有规格的保持

逐类消费第二轮的已证规格，核验语法识别与结构扩张保持原正文。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundThreeSpecifications
open PureModel PureNaturalInduction PureStructureStage
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem bounded_specification (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureBoundedDefinitions.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) symbol ((PureBoundedDefinitions.specification primitive)) args output :=
  inherited_specification hℳ symbol _ (by cases primitive <;> rfl) (by cases primitive <;> rfl) (by cases primitive <;> rfl) args output
    (PureRoundTwoSpecifications.bounded_specification hℳ primitive args output)

theorem filter_specification (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureSequenceFilters.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) symbol ((PureSequenceFilters.specification primitive)) args output :=
  inherited_specification hℳ symbol _ (by cases primitive <;> rfl) (by cases primitive <;> rfl) (by cases primitive <;> rfl) args output
    (PureRoundTwoSpecifications.filter_specification hℳ primitive args output)

theorem finite_sequence_specification (hℳ : Theory.Models ℳ theory) (source output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .finiteSequenceSpace
      ((Nonlogical.BasicSetTheory.finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here))) (.cons source .nil) output :=
  inherited_specification hℳ .finiteSequenceSpace _ rfl rfl rfl (.cons source .nil) output
    (PureRoundTwoSpecifications.finite_sequence_specification hℳ source output)

theorem omega_specification (hℳ : Theory.Models ℳ theory) (source seed recursion output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .omegaRecursiveSequence (PureSequenceStage.omegaSpec) (.cons source (.cons seed (.cons recursion .nil))) output :=
  inherited_specification hℳ .omegaRecursiveSequence _ rfl rfl rfl _ output
    (PureRoundTwoSpecifications.omega_specification hℳ source seed recursion output)

theorem difference_specification (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .naturalDifference (PureNaturalDifference.specification) (.cons left (.cons right .nil)) output :=
  inherited_specification hℳ .naturalDifference _ rfl rfl rfl _ output
    (PureRoundTwoSpecifications.difference_specification hℳ hLeft hRight output)

theorem godel_specification (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .godelPairing (PureGodelPairing.specification) (.cons left (.cons right .nil)) output :=
  inherited_specification hℳ .godelPairing _ rfl rfl rfl _ output
    (PureRoundTwoSpecifications.godel_specification hℳ hLeft hRight output)

noncomputable def arithmetic (hℳ : Theory.Models ℳ theory) (operation : PureArithmeticRecurrence.Operation) (left right : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition => (expansion hℳ).function .naturalAddition (.cons left (.cons right .nil))
  | .multiplication => (expansion hℳ).function .naturalMultiplication (.cons left (.cons right .nil))
  | .exponentiation => (expansion hℳ).function .naturalExponentiation (.cons left (.cons right .nil))

theorem arithmetic_specification (hℳ : Theory.Models ℳ theory) (operation : PureArithmeticRecurrence.Operation)
    {left right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    output = arithmetic hℳ operation left right ↔
      (PureArithmeticRecurrence.specification operation).satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (expansion hℳ).model [] [s,s,s]) := by
  have hOld := PureRoundTwoSpecifications.arithmetic_specification hℳ operation hLeft hRight output
  have hTransfer := round_two_transfer hℳ (PureArithmeticRecurrence.specification operation) (by cases operation <;> rfl) (by cases operation <;> rfl) (.cons output (.cons left (.cons right .nil)))
  cases operation <;> simp only [arithmetic] <;> rw [function_preserved hℳ _ rfl] <;> exact hOld.trans hTransfer

theorem closure_specification (hℳ : Theory.Models ℳ theory) (source output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .transitiveClosure (PureTransitiveClosure.specification) (.cons source .nil) output :=
  inherited_specification hℳ .transitiveClosure _ rfl rfl rfl _ output
    (PureRoundTwoSpecifications.closure_specification hℳ source output)

theorem hierarchy_specification (hℳ : Theory.Models ℳ theory) :
    PureSetStage.hierarchySpec.satisfies (templateEnv (.cons ((expansion hℳ).function .finiteHierarchy .nil) .nil) : Env (expansion hℳ).model [] [s]) := by
  rw [function_preserved hℳ .finiteHierarchy rfl .nil]
  exact (round_two_transfer hℳ _ rfl rfl _).mp (PureRoundTwoSpecifications.hierarchy_specification hℳ)

theorem universe_specification (hℳ : Theory.Models ℳ theory) (output : Carrier ℳ) :
    FunctionSpecification (expansion hℳ) .finiteUniverse (PureFiniteUniverseStage.universeSpec) .nil output :=
  inherited_specification hℳ .finiteUniverse _ rfl rfl rfl .nil output
    (PureRoundTwoSpecifications.universe_specification hℳ output)

theorem minimum_definition (hℳ : Theory.Models ℳ theory)
    (args : Values (expansion hℳ).model.Carrier [s,s,s,s,s,s]) :
    (Nonlogical.BasicSetTheory.minimum_difference_definition_instance
      (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here)).satisfies (templateEnv args) :=
  (round_two_transfer hℳ _ rfl rfl args).mp (PureRoundTwoSpecifications.minimum_definition hℳ args)

theorem round_one_definition (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : PureRoundOneRelations.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureRoundOneRelations.condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion hℳ) (realizes hℳ) symbol (PureRoundOneRelations.condition primitive) (by cases primitive <;> rfl) args

theorem natural_definition (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : PureNaturalRelations.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureNaturalRelations.condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion hℳ) (realizes hℳ) symbol (PureNaturalRelations.condition primitive) (by cases primitive <;> rfl) args

theorem hereditary_definition (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (expansion hℳ).model bound free) (input : Term S bound free s) :
    (Nonlogical.BasicSetTheory.hereditarily_finite_definition_instance input).satisfies env :=
  realizes_definition (expansion hℳ) (realizes hℳ) .isHereditarilyFinite PureFiniteUniverseStage.hereditaryCondition rfl (.cons (input.eval env) .nil)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundThreeSpecifications
