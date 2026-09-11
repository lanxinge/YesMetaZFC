import YesMetaZFC.Model.ZFC.Pure.PureStageTwoBase
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmetic

/-! # 第二轮自然数与可数性关系的原定义消去

原定义逐项翻译，特别保留可数性的满射条件及其对空集的既有约定。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalRelations
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x

inductive Primitive : Nonlogical.BasicSetTheory.RelationSymbol → Type where
  | isNaturalNumber : Primitive .isNaturalNumber
  | isInfinite : Primitive .isInfinite
  | isCountable : Primitive .isCountable
  | isUncountable : Primitive .isUncountable
  | isCountablyInfinite : Primitive .isCountablyInfinite
  | omegaPairLess : Primitive .omegaPairLess

def condition {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol) :
    Formula Nonlogical.BasicSetTheory.signature [] (Nonlogical.BasicSetTheory.signature.relDomain symbol) :=
  match primitive with
  | .isNaturalNumber => Nonlogical.BasicSetTheory.is_natural_number_condition (.fvar .here)
  | .isInfinite => Nonlogical.BasicSetTheory.is_infinite_condition (.fvar .here)
  | .isCountable => Nonlogical.BasicSetTheory.is_countable_condition (.fvar .here)
  | .isUncountable => Nonlogical.BasicSetTheory.is_uncountable_condition (.fvar .here)
  | .isCountablyInfinite => Nonlogical.BasicSetTheory.is_countably_infinite_condition (.fvar .here)
  | .omegaPairLess => Nonlogical.BasicSetTheory.omega_pair_less_condition (.fvar .here) (.fvar (.there .here))

def relationCovered : Nonlogical.BasicSetTheory.RelationSymbol → Bool
  | .isNaturalNumber
  | .isInfinite
  | .isCountable
  | .isUncountable
  | .isCountablyInfinite
  | .omegaPairLess => true
  | symbol => PureRoundOneRelations.relationCovered symbol

theorem dependencies_covered {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol) :
    formulaCovered PureStageTwoBase.functionCovered relationCovered (condition primitive) = true := by
  cases primitive <;> rfl

private def stage1 : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := PureStageTwoBase.functionGraph
  relation symbol := match symbol with
    | .isNaturalNumber => openFormula PureStageTwoBase.interpretation (condition .isNaturalNumber)
    | symbol => PureStageTwoBase.interpretation.relation symbol

private def stage2 : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := PureStageTwoBase.functionGraph
  relation symbol := match symbol with
    | .isInfinite => openFormula stage1 (condition .isInfinite)
    | symbol => stage1.relation symbol

private def stage3 : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := PureStageTwoBase.functionGraph
  relation symbol := match symbol with
    | .isCountable => openFormula stage2 (condition .isCountable)
    | symbol => stage2.relation symbol

private def stage4 : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := PureStageTwoBase.functionGraph
  relation symbol := match symbol with
    | .isUncountable => openFormula stage3 (condition .isUncountable)
    | symbol => stage3.relation symbol

private def stage5 : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := PureStageTwoBase.functionGraph
  relation symbol := match symbol with
    | .isCountablyInfinite => openFormula stage4 (condition .isCountablyInfinite)
    | symbol => stage4.relation symbol

private def stage6 : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := PureStageTwoBase.functionGraph
  relation symbol := match symbol with
    | .omegaPairLess => openFormula stage5 (condition .omegaPairLess)
    | symbol => stage5.relation symbol

def interpretation : Interpretation Nonlogical.BasicSetTheory.signature ℒ := stage6

def graph {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (_ : Primitive symbol) :
    Formula ℒ [] ((Nonlogical.BasicSetTheory.signature.relDomain symbol).map (fun _ => setSort)) :=
  interpretation.relation symbol

theorem graph_equation {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (condition primitive) := by
  cases primitive <;> rfl

/-- 新阶段仍逐项满足第一轮关系的原定义正文。 -/
theorem inherited_graph_equation {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureRoundOneRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureRoundOneRelations.condition primitive) := by
  cases primitive <;> rfl

theorem functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional interpretation ℳ := by
  intro symbol args
  have hMap : mapValues interpretation args = mapValues PureStageTwoBase.interpretation args := by
    generalize hSorts : Nonlogical.BasicSetTheory.signature.funcDomain symbol = sorts at args
    clear hSorts
    induction args with
    | nil => rfl
    | cons head tail ih => exact congrArg (Values.cons head) ih
  change ∃ output, (PureStageTwoBase.functionGraph symbol).satisfies
      (templateEnv (.cons output (mapValues interpretation args))) ∧
    ∀ other, (PureStageTwoBase.functionGraph symbol).satisfies
      (templateEnv (.cons other (mapValues interpretation args))) → other = output
  rw [hMap]
  exact PureStageTwoBase.functional hℳ symbol args

theorem definition_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : Primitive symbol)
    (args : Values (expansion (functional hℳ)).model.Carrier (Nonlogical.BasicSetTheory.signature.relDomain symbol)) :
    (expansion (functional hℳ)).relation symbol args ↔ (condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion (functional hℳ)) (expansion_realizes (functional hℳ))
    symbol (condition primitive) (graph_equation primitive) args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalRelations
