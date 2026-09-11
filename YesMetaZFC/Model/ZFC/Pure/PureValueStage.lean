import YesMetaZFC.Model.Interpretation.PredicateCongruence
import YesMetaZFC.Model.ZFC.Pure.PureValueFixedPoint

/-! # 两个求值关系的模型扩张

每次递归调用按实际结构和赋值四参数选择切片。正文语义核验这些参数保持不变，
因此候选算子的固定参数处理恰好恢复原互递归方程。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureValueStage
open PureModel PureNaturalInduction PureValueOperator PureValueFixedPoint
open PureSyntaxOperator (Kind tuple)
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory FormalSystem
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := PureRelatedStage.interpretation.function
  relation symbol := match symbol with
    | .termValue => termGraph
    | .termListValue => listGraph
    | symbol => PureRelatedStage.interpretation.relation symbol
noncomputable def valueRelations (hℳ : Theory.Models ℳ theory) : _root_.YesMetaZFC.Automation.PredicateExpansion.Relations (E hℳ).model := fun symbol args =>
  match symbol,args with
  | .termValue,.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil))))) =>
    membership ℳ (tuple hℳ .term (zero hℳ) code result) (state hℳ carrier interpretation symbols assignment)
  | .termListValue,.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil)))))) =>
    membership ℳ (tuple hℳ .termList length code result) (state hℳ carrier interpretation symbols assignment)
  | symbol,args => (E hℳ).relation symbol args
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ where
  function := (E hℳ).function
  relation := valueRelations hℳ

theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) where
  function symbol args output := by
    change (PureRelatedStage.interpretation.function symbol).satisfies (templateEnv (.cons output (mapValues interpretation args))) ↔ _
    exact (PureValueOperator.realizes hℳ).function symbol args output
  relation symbol args := by
    cases symbol
    case termValue =>
      cases args with | cons carrier tail0 =>
      cases tail0 with | cons interpretation tail1 =>
      cases tail1 with | cons symbols tail2 =>
      cases tail2 with | cons assignment tail3 =>
      cases tail3 with | cons code tail4 =>
      cases tail4 with | cons result tail5 =>
      cases tail5
      exact term_graph_correct hℳ carrier interpretation symbols assignment code result
    case termListValue =>
      cases args with | cons carrier tail0 =>
      cases tail0 with | cons interpretation tail1 =>
      cases tail1 with | cons symbols tail2 =>
      cases tail2 with | cons assignment tail3 =>
      cases tail3 with | cons length tail4 =>
      cases tail4 with | cons code tail5 =>
      cases tail5 with | cons result tail6 =>
      cases tail6
      exact list_graph_correct hℳ carrier interpretation symbols assignment length code result
    all_goals
      exact (PureValueOperator.realizes hℳ).relation _ args

def sourceFamilyRelations (𝒩 : Structure.{0,0,0,x} S)
    (family : 𝒩.Carrier s → 𝒩.Carrier s → 𝒩.Carrier s → 𝒩.Carrier s → 𝒩.Carrier s) : PredicateExpansion.Relations 𝒩 := fun symbol args =>
  match symbol,args with
  | .termValue,.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil))))) =>
    sourceRelations 𝒩 (family carrier interpretation symbols assignment) .termValue (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil))))))
  | .termListValue,.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil)))))) =>
    sourceRelations 𝒩 (family carrier interpretation symbols assignment) .termListValue (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil)))))))
  | symbol,args => 𝒩.relInterp symbol args

/-- 原正文的每个递归调用确实保持四个外层参数。 -/
theorem parameters_preserved (𝒩 : Structure.{0,0,0,x} S)
    (family : 𝒩.Carrier s → 𝒩.Carrier s → 𝒩.Carrier s → 𝒩.Carrier s → 𝒩.Carrier s)
    (kind : Kind) (carrier interpretation symbols assignment length code result : 𝒩.Carrier s) :
    PredicateExpansion.evaluate (sourceFamilyRelations 𝒩 family)
      (templateEnv (.cons length (.cons code (.cons result (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil))))))) : Env 𝒩 [] [s,s,s,s,s,s,s]) (condition kind) ↔
    PredicateExpansion.evaluate (sourceRelations 𝒩 (family carrier interpretation symbols assignment))
      (templateEnv (.cons length (.cons code (.cons result (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil))))))) : Env 𝒩 [] [s,s,s,s,s,s,s]) (condition kind) := by
  cases kind <;> rfl

theorem family_relations_actual (hℳ : Theory.Models ℳ theory) (symbol : RelationSymbol)
    (args : Values (E hℳ).model.Carrier (S.relDomain symbol)) :
    sourceFamilyRelations (E hℳ).model (state hℳ) symbol args ↔ valueRelations hℳ symbol args := by
  cases symbol
  case termValue =>
    match args with
    | .cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil))))) =>
      exact source_relations_actual hℳ (state hℳ carrier interpretation symbols assignment) .termValue (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil))))))
  case termListValue =>
    match args with
    | .cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil)))))) =>
      exact source_relations_actual hℳ (state hℳ carrier interpretation symbols assignment) .termListValue (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil)))))))
  all_goals rfl

theorem condition_satisfaction (hℳ : Theory.Models ℳ theory) (kind : Kind)
    (carrier interpretation symbols assignment length code result : Carrier ℳ) :
    (condition kind).satisfies (templateEnv (.cons length (.cons code (.cons result (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil))))))) : Env (expansion hℳ).model [] [s,s,s,s,s,s,s]) ↔
      Condition hℳ (state hℳ carrier interpretation symbols assignment) kind carrier interpretation symbols assignment length code result := by
  let env : Env (E hℳ).model [] [s,s,s,s,s,s,s] := templateEnv (.cons length (.cons code (.cons result (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))))))
  have h := PredicateExpansion.evaluate_correct (valueRelations hℳ) env (condition kind)
  rw [← PredicateExpansion.with_templateEnv] at h
  apply h.trans
  apply (PredicateExpansion.evaluate_congr (valueRelations hℳ) (sourceFamilyRelations (E hℳ).model (state hℳ))
    (fun symbol args => (family_relations_actual hℳ symbol args).symm) env (condition kind)).trans
  apply (parameters_preserved (E hℳ).model (state hℳ) kind carrier interpretation symbols assignment length code result).trans
  exact PredicateExpansion.evaluate_congr _ _ (source_relations_actual hℳ _) env (condition kind)

def termValueDefinition : Formula S [] [s,s,s,s,s,s] :=
  .iff (.rel .termValue (.cons (.fvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there (.there (.there .here)))) (.cons (.fvar (.there (.there (.there (.there .here))))) (.cons (.fvar (.there (.there (.there (.there (.there .here)))))) .nil))))))) (term_value_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))))
theorem termValue_definition (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment code result : Carrier ℳ) :
    termValueDefinition.satisfies (templateEnv (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil)))))) : Env (expansion hℳ).model [] [s,s,s,s,s,s]) := by
  change membership ℳ (tuple hℳ .term (zero hℳ) code result) (state hℳ carrier interpretation symbols assignment) ↔ _
  apply (equation hℳ .term carrier interpretation symbols assignment (zero hℳ) code result).trans
  rw [← condition_satisfaction hℳ]
  change (zero hℳ = (E hℳ).function .emptySet .nil ∧ _) ↔ _
  rw [zero_eq hℳ]
  exact ⟨And.right,fun h => ⟨rfl,h⟩⟩

def termListValueDefinition : Formula S [] [s,s,s,s,s,s,s] :=
  .iff (.rel .termListValue (.cons (.fvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there (.there (.there .here)))) (.cons (.fvar (.there (.there (.there (.there .here))))) (.cons (.fvar (.there (.there (.there (.there (.there .here)))))) (.cons (.fvar (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) (term_list_value_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here))))))))
theorem termListValue_definition (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment length code result : Carrier ℳ) :
    termListValueDefinition.satisfies (templateEnv (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil))))))) : Env (expansion hℳ).model [] [s,s,s,s,s,s,s]) := by
  change membership ℳ (tuple hℳ .termList length code result) (state hℳ carrier interpretation symbols assignment) ↔ _
  apply (equation hℳ .termList carrier interpretation symbols assignment length code result).trans
  rw [← condition_satisfaction hℳ]
  rfl

def relationCovered : RelationSymbol → Bool
  | .termValue | .termListValue => true
  | symbol => PureRelatedStage.relationCovered symbol
theorem dependencies_covered (kind : Kind) : formulaCovered PureRelatedStage.functionCovered relationCovered (condition kind) = true := by cases kind <;> rfl
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureValueStage
