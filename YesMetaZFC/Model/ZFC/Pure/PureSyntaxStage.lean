import YesMetaZFC.Model.Interpretation.RelationalTransfer
import YesMetaZFC.Model.ZFC.Pure.PureSyntaxFixedPoint

/-! # 三个递归语法谓词的模型扩张

函数解释直接沿用第二轮，三个关系取共同最小不动点的标签切片。
原递归定义实例由不动点方程证明，而非将循环正文当作非递归定义展开。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxStage
open PureModel PureNaturalInduction PureSyntaxOperator PureSyntaxFixedPoint
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := PureRoundTwoStage.interpretation.function
  relation symbol := match symbol with
    | .isTermCodeAt => graph2 .term
    | .isTermListCodeAt => graph3
    | .isFormulaCodeAt => graph2 .formula
    | symbol => PureRoundTwoStage.interpretation.relation symbol

def functionCovered := PureRoundTwoStage.functionCovered
def relationCovered : RelationSymbol → Bool
  | .isTermCodeAt | .isTermListCodeAt | .isFormulaCodeAt => true
  | symbol => PureRoundTwoStage.relationCovered symbol

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  exact PureRoundTwoStage.functional hℳ

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ where
  function := (E hℳ).function
  relation := relations hℳ (state hℳ)

theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) where
  function symbol args output := by
    change (PureRoundTwoStage.interpretation.function symbol).satisfies (templateEnv (.cons output (mapValues interpretation args))) ↔ _
    exact (PureRoundTwoStage.realizes hℳ).function symbol args output
  relation symbol args := by
    cases symbol
    case isTermCodeAt =>
      cases args with | cons depth tail =>
      cases tail with | cons code tail =>
      cases tail
      exact graph2_correct hℳ .term depth code
    case isTermListCodeAt =>
      cases args with | cons depth tail =>
      cases tail with | cons length tail =>
      cases tail with | cons code tail =>
      cases tail
      exact graph3_correct hℳ depth length code
    case isFormulaCodeAt =>
      cases args with | cons depth tail =>
      cases tail with | cons code tail =>
      cases tail
      exact graph2_correct hℳ .formula depth code
    all_goals
      exact (PureRoundTwoStage.realizes hℳ).relation _ args

theorem satisfaction (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (args : Values (E hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) ↔
      PredicateExpansion.evaluate (relations hℳ (state hℳ)) (templateEnv args : Env (E hℳ).model [] parameters) body := by
  have h := PredicateExpansion.evaluate_correct (relations hℳ (state hℳ)) (templateEnv args) body
  rw [← PredicateExpansion.with_templateEnv] at h
  exact h

theorem term_definition (hℳ : Theory.Models ℳ theory) (depth code : Carrier ℳ) :
    (FormalSystem.term_code_at_definition_instance (.fvar .here) (.fvar (.there .here))).satisfies
      (templateEnv (.cons depth (.cons code .nil)) : Env (expansion hℳ).model [] [s,s]) := by
  change membership ℳ (tuple hℳ .term depth (zero hℳ) code) (state hℳ) ↔ _
  apply (equation hℳ .term depth (zero hℳ) code).trans
  apply Iff.trans ?_ (satisfaction hℳ (FormalSystem.term_code_at_condition (.fvar .here) (.fvar (.there .here))) (.cons depth (.cons code .nil))).symm
  change (zero hℳ = (E hℳ).function .emptySet .nil ∧ _) ↔ _
  rw [zero_eq hℳ]
  exact ⟨And.right,fun h => ⟨rfl,h⟩⟩

theorem term_list_definition (hℳ : Theory.Models ℳ theory) (depth length code : Carrier ℳ) :
    (FormalSystem.term_list_code_at_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons depth (.cons length (.cons code .nil))) : Env (expansion hℳ).model [] [s,s,s]) := by
  change membership ℳ (tuple hℳ .termList depth length code) (state hℳ) ↔ _
  exact (equation hℳ .termList depth length code).trans
    (satisfaction hℳ (FormalSystem.term_list_code_at_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))) (.cons depth (.cons length (.cons code .nil)))).symm

theorem formula_definition (hℳ : Theory.Models ℳ theory) (depth code : Carrier ℳ) :
    (FormalSystem.formula_code_at_definition_instance (.fvar .here) (.fvar (.there .here))).satisfies
      (templateEnv (.cons depth (.cons code .nil)) : Env (expansion hℳ).model [] [s,s]) := by
  change membership ℳ (tuple hℳ .formula depth (zero hℳ) code) (state hℳ) ↔ _
  apply (equation hℳ .formula depth (zero hℳ) code).trans
  apply Iff.trans ?_ (satisfaction hℳ (FormalSystem.formula_code_at_condition (.fvar .here) (.fvar (.there .here))) (.cons depth (.cons code .nil))).symm
  change (zero hℳ = (E hℳ).function .emptySet .nil ∧ _) ↔ _
  rw [zero_eq hℳ]
  exact ⟨And.right,fun h => ⟨rfl,h⟩⟩

theorem dependencies_covered (kind : Kind) : formulaCovered functionCovered relationCovered (condition kind) = true := by cases kind <;> rfl

/-- 旧正文的纯翻译相同就可在新阶段逐参数传输。 -/
theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureRoundTwoStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (E hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureRoundTwoStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxStage
