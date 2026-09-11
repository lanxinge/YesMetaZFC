import YesMetaZFC.Model.ZFC.Pure.PureSeparation
import YesMetaZFC.Model.ZFC.Pure.PureStageTwoSemantics
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.HereditarilyFinite

/-! # 第二轮的有界集合定义

有限子集收集、幂集二值编码图和指数序直接按原成员条件分离；母集也直接取自
原规格。定义在任意输入上存在且唯一，合法输入自然保留原定义实例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureBoundedDefinitions
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := SetSort.set

inductive Primitive : FunctionSymbol → Type where
  | finiteSubsetCollection : Primitive .finiteSubsetCollection
  | powerSetBijection : Primitive .powerSetBijection
  | indexOrder : Primitive .indexOrder

def condition {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    SetFormula [] (s :: signature.funcDomain symbol) :=
  match primitive with
  | .finiteSubsetCollection => finite_subset_collection_member_condition (.fvar .here)
  | .powerSetBijection => power_set_bijection_member_condition (.fvar (.there .here)) (.fvar .here)
  | .indexOrder =>
    let sourceCarrier : SetTerm [] [s,s,s,s,s] := .fvar (.there (.there .here))
    let targetCarrier : SetTerm [] [s,s,s,s,s] := .fvar (.there (.there (.there (.there .here))))
    let maps := mapping_collection_term sourceCarrier targetCarrier
    (membership_formula (.fvar .here) (cartesian_product_term maps maps)).conj
      (index_order_member_condition (.fvar (.there .here)) sourceCarrier
        (.fvar (.there (.there (.there .here)))) (.fvar .here))

def ambientTerm {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    SetTerm [] (signature.funcDomain symbol) :=
  match primitive with
  | .finiteSubsetCollection => power_set_term (.fvar .here)
  | .powerSetBijection => cartesian_product_term (power_set_term (.fvar .here))
      (mapping_collection_term (.fvar .here) binary_value_set_term)
  | .indexOrder =>
      let maps := mapping_collection_term (.fvar (.there .here)) (.fvar (.there (.there (.there .here))))
      cartesian_product_term maps maps

def specification {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    SetFormula [] (s :: signature.funcDomain symbol) :=
  match primitive with
  | .finiteSubsetCollection => finite_subset_collection_spec (.fvar (.there .here)) (.fvar .here)
  | .powerSetBijection => power_set_bijection_spec (.fvar (.there .here)) (.fvar .here)
  | .indexOrder => index_order_spec (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)

theorem dependencies_covered {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    formulaCovered PureStageTwoBase.functionCovered PureNaturalRelations.relationCovered (condition primitive) = true := by
  cases primitive <;> rfl

def body {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  openFormula PureNaturalRelations.interpretation (condition primitive)

def graph {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  PureFunctionDefinitions.comprehension (body primitive)

theorem condition_bounded (ℳ : Structure.{0,0,0,x} signature) {symbol : FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (signature.funcDomain symbol)) (element : ℳ.Carrier s)
    (h : (condition primitive).satisfies (templateEnv (.cons element args))) :
    ℳ.relInterp .membership (.cons element (.cons ((ambientTerm primitive).eval (templateEnv args)) .nil)) := by
  cases primitive
  all_goals
    cases args with | cons first tail =>
    first
    | cases tail; exact h.1
    | cases tail with | cons second tail =>
      cases tail with | cons third tail =>
      cases tail with | cons fourth tail =>
      cases tail
      exact h.1

theorem specification_correct (ℳ : Structure.{0,0,0,x} signature) {symbol : FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (signature.funcDomain symbol)) (output : ℳ.Carrier s) :
    (specification primitive).satisfies (templateEnv (.cons output args)) ↔
      ∀ element, ℳ.relInterp .membership (.cons element (.cons output .nil)) ↔
        (condition primitive).satisfies (templateEnv (.cons element args)) := by
  cases primitive
  all_goals
    cases args with | cons first tail =>
    first
    | cases tail
      simp only [specification, finite_subset_collection_spec, power_set_bijection_spec,
        membership_specification, Formula.satisfies_forallFreeTop, Formula.satisfies]
      rfl
    | cases tail with | cons second tail =>
      cases tail with | cons third tail =>
      cases tail with | cons fourth tail =>
      cases tail
      simp only [specification, index_order_spec, membership_specification, Formula.satisfies_forallFreeTop, Formula.satisfies]
      rfl

theorem graph_correct {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : FunctionSymbol} (primitive : Primitive symbol)
    (args : Values (PureStageTwoSemantics.expansion hℳ).model.Carrier (signature.funcDomain symbol)) (output : Carrier ℳ) :
    (graph primitive).satisfies (templateEnv (.cons output (mapValues PureNaturalRelations.interpretation args))) ↔
      (specification primitive).satisfies
        (templateEnv (.cons output args) : Env (PureStageTwoSemantics.expansion hℳ).model [] (s :: signature.funcDomain symbol)) := by
  rw [graph, PureFunctionDefinitions.comprehension_correct]
  apply Iff.trans ?_ (specification_correct (PureStageTwoSemantics.expansion hℳ).model primitive args output).symm
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (openFormula_correct (PureStageTwoSemantics.expansion hℳ)
    (PureStageTwoSemantics.realizes hℳ) (condition primitive) (.cons element args))

theorem functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : FunctionSymbol} (primitive : Primitive symbol)
    (args : Values (PureStageTwoSemantics.expansion hℳ).model.Carrier (signature.funcDomain symbol)) :
    ∃ output, (graph primitive).satisfies (templateEnv (.cons output (mapValues PureNaturalRelations.interpretation args))) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other (mapValues PureNaturalRelations.interpretation args))) → other = output := by
  apply PureSeparation.bounded_functional hℳ (body primitive) (mapValues PureNaturalRelations.interpretation args)
    ((ambientTerm primitive).eval (templateEnv args))
  intro element h
  exact condition_bounded (PureStageTwoSemantics.expansion hℳ).model primitive args element
    ((openFormula_correct (PureStageTwoSemantics.expansion hℳ) (PureStageTwoSemantics.realizes hℳ)
      (condition primitive) (.cons element args)).mp h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureBoundedDefinitions
