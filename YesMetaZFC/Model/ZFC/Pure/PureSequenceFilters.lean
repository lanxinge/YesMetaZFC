import YesMetaZFC.Model.ZFC.Pure.PureCollectionStage
import YesMetaZFC.Logic.FirstOrder.FormalSystem.FiniteSequenceConcatenation

/-! # 非空有限序列与递归序列的收集

两者均从已构造的有限序列空间中分离。递归条件保留原种子与逐步递推约束；
这里证明序列族的存在唯一性，其并集的全域递归性质由后续定理处理。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceFilters
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := SetSort.set

inductive Primitive : FunctionSymbol → Type where
  | nonemptyFiniteSequenceSpace : Primitive .nonemptyFiniteSequenceSpace
  | recursiveSequenceSpace : Primitive .recursiveSequenceSpace

def condition {symbol : FunctionSymbol} (primitive : Primitive symbol) : SetFormula [] (s :: signature.funcDomain symbol) :=
  match primitive with
  | .nonemptyFiniteSequenceSpace => nonempty_finite_sequence_member_condition (.fvar .here) (.fvar .here)
  | .recursiveSequenceSpace => recursive_sequence_member_condition (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar .here)

def specification {symbol : FunctionSymbol} (primitive : Primitive symbol) : SetFormula [] (s :: signature.funcDomain symbol) :=
  match primitive with
  | .nonemptyFiniteSequenceSpace => nonempty_finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here)
  | .recursiveSequenceSpace => recursive_sequence_space_spec (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar .here)

def body {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  openFormula PureCollectionStage.interpretation (condition primitive)

def graph {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  PureFunctionDefinitions.comprehension (body primitive)

theorem dependencies_covered {symbol : FunctionSymbol} (primitive : Primitive symbol) :
    formulaCovered PureCollectionStage.functionCovered PureNaturalRelations.relationCovered (condition primitive) = true := by
  cases primitive <;> rfl

theorem specification_correct (ℳ : Structure.{0,0,0,x} signature) {symbol : FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (signature.funcDomain symbol)) (output : ℳ.Carrier s) :
    (specification primitive).satisfies (templateEnv (.cons output args)) ↔
      ∀ element, ℳ.relInterp .membership (.cons element (.cons output .nil)) ↔
        (condition primitive).satisfies (templateEnv (.cons element args)) := by
  cases primitive
  case nonemptyFiniteSequenceSpace =>
    cases args with | cons source tail =>
    cases tail
    simp only [specification, nonempty_finite_sequence_space_spec, membership_specification,
      Formula.satisfies_forallFreeTop, Formula.satisfies]
    rfl
  case recursiveSequenceSpace =>
    cases args with | cons source tail =>
    cases tail with | cons seed tail =>
    cases tail with | cons recursion tail =>
    cases tail
    simp only [specification, recursive_sequence_space_spec, Formula.satisfies_forallFreeTop, Formula.satisfies]
    rfl

theorem graph_correct {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : FunctionSymbol} (primitive : Primitive symbol)
    (args : Values (PureCollectionStage.expansion hℳ).model.Carrier (signature.funcDomain symbol)) (output : Carrier ℳ) :
    (graph primitive).satisfies (templateEnv (.cons output (mapValues PureCollectionStage.interpretation args))) ↔
      (specification primitive).satisfies
        (templateEnv (.cons output args) : Env (PureCollectionStage.expansion hℳ).model [] (s :: signature.funcDomain symbol)) := by
  rw [graph, PureFunctionDefinitions.comprehension_correct]
  apply Iff.trans ?_ (specification_correct (PureCollectionStage.expansion hℳ).model primitive args output).symm
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (openFormula_correct (PureCollectionStage.expansion hℳ)
    (PureCollectionStage.realizes hℳ) (condition primitive) (.cons element args))

theorem finite_member_in_space {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (sequence source : Carrier ℳ)
    (h : (finite_sequence_member_condition (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons sequence (.cons source .nil)) : Env (PureCollectionStage.expansion hℳ).model [] [s,s])) :
    membership ℳ sequence ((PureCollectionStage.expansion hℳ).function .finiteSequenceSpace (.cons source .nil)) := by
  have hSpec := (PureCollectionStage.finite_sequence_specification hℳ source _).mp rfl
  simp only [finite_sequence_space_spec, Formula.satisfies_forallFreeTop, Formula.satisfies] at hSpec
  exact (hSpec sequence).mpr h

theorem functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : FunctionSymbol} (primitive : Primitive symbol)
    (args : Values (PureCollectionStage.expansion hℳ).model.Carrier (signature.funcDomain symbol)) :
    ∃ output, (graph primitive).satisfies (templateEnv (.cons output (mapValues PureCollectionStage.interpretation args))) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other (mapValues PureCollectionStage.interpretation args))) → other = output := by
  cases primitive
  case nonemptyFiniteSequenceSpace =>
    cases args with | cons source tail =>
    cases tail
    apply PureSeparation.bounded_functional hℳ (body .nonemptyFiniteSequenceSpace) (.cons source .nil)
      ((PureCollectionStage.expansion hℳ).function .finiteSequenceSpace (.cons source .nil))
    intro sequence hSequence
    exact ((openFormula_correct (PureCollectionStage.expansion hℳ) (PureCollectionStage.realizes hℳ)
      (condition .nonemptyFiniteSequenceSpace) (.cons sequence (.cons source .nil))).mp hSequence).1
  case recursiveSequenceSpace =>
    cases args with | cons source tail =>
    cases tail with | cons seed tail =>
    cases tail with | cons recursion tail =>
    cases tail
    apply PureSeparation.bounded_functional hℳ (body .recursiveSequenceSpace) (.cons source (.cons seed (.cons recursion .nil)))
      ((PureCollectionStage.expansion hℳ).function .finiteSequenceSpace (.cons source .nil))
    intro sequence hSequence
    have hCondition := (openFormula_correct (PureCollectionStage.expansion hℳ) (PureCollectionStage.realizes hℳ)
      (condition .recursiveSequenceSpace) (.cons sequence (.cons source (.cons seed (.cons recursion .nil))))).mp hSequence
    exact finite_member_in_space hℳ sequence source hCondition.1

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceFilters
