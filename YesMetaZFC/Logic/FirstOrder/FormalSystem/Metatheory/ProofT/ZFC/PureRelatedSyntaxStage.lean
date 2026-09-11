import YesMetaZFC.Automation.RelationalTransfer
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRelatedSyntaxFixedPoint

/-! # 三个相关语法谓词的模型扩张

函数解释沿用前一阶段；每个符号集选择其内部不动点，三个关系取相应切片。
原递归定义实例由不动点方程证明，而非将循环正文当作非递归定义展开。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxStage
open PureModel PureNaturalInduction PureRelatedSyntaxOperator PureRelatedSyntaxFixedPoint
open PureSyntaxOperator (Kind tuple)
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
  function := PureStructureStage.interpretation.function
  relation symbol := match symbol with
    | .isRelatedTermCodeAt => graph2 .term
    | .isRelatedTermListCodeAt => graph3
    | .isRelatedFormulaCodeAt => graph2 .formula
    | symbol => PureStructureStage.interpretation.relation symbol

def functionCovered := PureStructureStage.functionCovered
def relationCovered : RelationSymbol → Bool
  | .isRelatedTermCodeAt | .isRelatedTermListCodeAt | .isRelatedFormulaCodeAt => true
  | symbol => PureStructureStage.relationCovered symbol

theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  exact PureStructureStage.functional hℳ

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ where
  function symbol args := match symbol,args with
    | .relatedNonlogicalSymbolSet,.nil => (E hℳ).function .omega .nil
    | symbol,args => (E hℳ).function symbol args
  relation symbol args := match symbol,args with
    | .isRelatedTermCodeAt,.cons symbols (.cons depth (.cons code .nil)) => membership ℳ (tuple hℳ .term depth (zero hℳ) code) (state hℳ symbols)
    | .isRelatedTermListCodeAt,.cons symbols (.cons depth (.cons length (.cons code .nil))) => membership ℳ (tuple hℳ .termList depth length code) (state hℳ symbols)
    | .isRelatedFormulaCodeAt,.cons symbols (.cons depth (.cons code .nil)) => membership ℳ (tuple hℳ .formula depth (zero hℳ) code) (state hℳ symbols)
    | symbol,args => (PureStructureStage.expansion hℳ).relation symbol args

theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) where
  function symbol args output := by
    cases symbol
    case relatedNonlogicalSymbolSet =>
      cases args
      exact (PureRoundTwoStage.realizes hℳ).function .omega .nil output
    all_goals
      exact (PureRoundTwoStage.realizes hℳ).function _ args output
  relation symbol args := by
    cases symbol
    case isRelatedTermCodeAt =>
      cases args with | cons symbols tail =>
      cases tail with | cons depth tail =>
      cases tail with | cons code tail =>
      cases tail
      exact graph2_correct hℳ .term symbols depth code
    case isRelatedTermListCodeAt =>
      cases args with | cons symbols tail =>
      cases tail with | cons depth tail =>
      cases tail with | cons length tail =>
      cases tail with | cons code tail =>
      cases tail
      exact graph3_correct hℳ symbols depth length code
    case isRelatedFormulaCodeAt =>
      cases args with | cons symbols tail =>
      cases tail with | cons depth tail =>
      cases tail with | cons code tail =>
      cases tail
      exact graph2_correct hℳ .formula symbols depth code
    all_goals
      exact (PureStructureStage.realizes hℳ).relation _ args

/-- 原递归正文中所有递归调用均携带当前符号集，故逐参数不动点可装配为整个关系解释。 -/
theorem condition_satisfaction (hℳ : Theory.Models ℳ theory) (kind : Kind) (symbols depth length code : Carrier ℳ) :
    (condition kind).satisfies (templateEnv (.cons depth (.cons length (.cons code (.cons symbols .nil)))) : Env (expansion hℳ).model [] [s,s,s,s]) ↔
      Condition hℳ (state hℳ symbols) kind symbols depth length code := by
  cases kind <;> rfl

theorem term_definition (hℳ : Theory.Models ℳ theory) (symbols depth code : Carrier ℳ) :
    (FormalSystem.related_term_code_at_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons symbols (.cons depth (.cons code .nil))) : Env (expansion hℳ).model [] [s,s,s]) := by
  change membership ℳ (tuple hℳ .term depth (zero hℳ) code) (state hℳ symbols) ↔ _
  apply (equation hℳ .term symbols depth (zero hℳ) code).trans
  rw [← condition_satisfaction hℳ]
  change (zero hℳ = (E hℳ).function .emptySet .nil ∧ _) ↔ _
  rw [zero_eq hℳ]
  exact ⟨And.right,fun h => ⟨rfl,h⟩⟩

theorem term_list_definition (hℳ : Theory.Models ℳ theory) (symbols depth length code : Carrier ℳ) :
    (FormalSystem.related_term_list_code_at_definition_instance (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))).satisfies
      (templateEnv (.cons symbols (.cons depth (.cons length (.cons code .nil)))) : Env (expansion hℳ).model [] [s,s,s,s]) := by
  change membership ℳ (tuple hℳ .termList depth length code) (state hℳ symbols) ↔ _
  exact (equation hℳ .termList symbols depth length code).trans (condition_satisfaction hℳ .termList symbols depth length code).symm

theorem formula_definition (hℳ : Theory.Models ℳ theory) (symbols depth code : Carrier ℳ) :
    (FormalSystem.related_formula_code_at_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons symbols (.cons depth (.cons code .nil))) : Env (expansion hℳ).model [] [s,s,s]) := by
  change membership ℳ (tuple hℳ .formula depth (zero hℳ) code) (state hℳ symbols) ↔ _
  apply (equation hℳ .formula symbols depth (zero hℳ) code).trans
  rw [← condition_satisfaction hℳ]
  change (zero hℳ = (E hℳ).function .emptySet .nil ∧ _) ↔ _
  rw [zero_eq hℳ]
  exact ⟨And.right,fun h => ⟨rfl,h⟩⟩

theorem dependencies_covered (kind : Kind) : formulaCovered functionCovered relationCovered (condition kind) = true := by cases kind <;> rfl

/-- 旧正文的纯翻译相同就可在新阶段逐参数传输。 -/
theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureStructureStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureStructureStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  exact transfer_regraph _ _ _ _ (PureStructureStage.realizes hℳ) _ (realizes hℳ) body hTranslate args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxStage
