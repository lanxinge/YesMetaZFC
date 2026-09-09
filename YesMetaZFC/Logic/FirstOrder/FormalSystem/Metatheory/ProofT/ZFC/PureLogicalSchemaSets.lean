import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureStructuralCodeBounds
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding

/-! # 九个独立逻辑公理模式集合

模式参数使用修正后的存在见证。各构造保留原良构性条件，以结构码的内部 ω
封闭性建立集合界，再用纯分离与外延性证明集合存在唯一。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalSchemaSets
open PureModel PureNaturalInduction PureStructuralCodeBounds
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory FormalSystem
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

inductive Kind where
  | implicationDistribution
  | selfImplication
  | weakening
  | contradiction
  | classical
  | explosion
  | caseAnalysis
  | quantifierDistribution
  | equalityReflexivity
  deriving DecidableEq

def parameters : Kind → SortContext S
  | .implicationDistribution => [s,s,s]
  | .selfImplication => [s]
  | .weakening => [s,s]
  | .contradiction => [s,s]
  | .classical => [s]
  | .explosion => [s,s]
  | .caseAnalysis => [s,s]
  | .quantifierDistribution => [s,s]
  | .equalityReflexivity => [s]

def constructor (kind : Kind) : Term S [] (parameters kind) s :=
  match kind with
  | .implicationDistribution => implication_distribution_axiom_code_term (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  | .selfImplication => self_implication_axiom_code_term (.fvar .here)
  | .weakening => weakening_axiom_code_term (.fvar .here) (.fvar (.there .here))
  | .contradiction => contradiction_axiom_code_term (.fvar .here) (.fvar (.there .here))
  | .classical => classical_axiom_code_term (.fvar .here)
  | .explosion => explosion_axiom_code_term (.fvar .here) (.fvar (.there .here))
  | .caseAnalysis => case_analysis_axiom_code_term (.fvar .here) (.fvar (.there .here))
  | .quantifierDistribution => quantifier_distribution_axiom_code_term (.fvar .here) (.fvar (.there .here))
  | .equalityReflexivity => equality_reflexivity_axiom_code_term (.fvar .here)

def condition (kind : Kind) : Formula S [] [s] :=
  match kind with
  | .implicationDistribution => implication_distribution_axiom_condition (.fvar .here)
  | .selfImplication => self_implication_axiom_condition (.fvar .here)
  | .weakening => weakening_axiom_condition (.fvar .here)
  | .contradiction => contradiction_axiom_condition (.fvar .here)
  | .classical => classical_axiom_condition (.fvar .here)
  | .explosion => explosion_axiom_condition (.fvar .here)
  | .caseAnalysis => case_analysis_axiom_condition (.fvar .here)
  | .quantifierDistribution => quantifier_distribution_axiom_condition (.fvar .here)
  | .equalityReflexivity => equality_reflexivity_axiom_condition (.fvar .here)

def member (kind : Kind) : Formula ℒ [] [setSort] := openFormula PureSyntaxStage.interpretation (condition kind)
def graph (kind : Kind) : Formula ℒ [] [setSort] := PureFunctionDefinitions.comprehension (member kind)

theorem constructor_natural (hℳ : Theory.Models ℳ theory) (kind : Kind)
    (args : Values (E hℳ).model.Carrier (parameters kind))
    (hArgs : ∀ entry : Variable (parameters kind) s, membership ℳ ((templateEnv args).freeVal entry) (omega hℳ)) :
    membership ℳ ((constructor kind).eval (templateEnv args)) (omega hℳ) := by
  -- 按实际语法树组合封闭性；不让回溯搜索猜测构造子和变量槽。
  cases kind with
  | implicationDistribution =>
    exact binary hℳ _ .implication _ _
      (binary hℳ _ .implication _ _ (hArgs .here)
        (binary hℳ _ .implication _ _ (hArgs (.there .here)) (hArgs (.there (.there .here)))))
      (binary hℳ _ .implication _ _
        (binary hℳ _ .implication _ _ (hArgs .here) (hArgs (.there .here)))
        (binary hℳ _ .implication _ _ (hArgs .here) (hArgs (.there (.there .here)))))
  | selfImplication =>
    exact binary hℳ _ .implication _ _ (hArgs .here)
      (binary hℳ _ .implication _ _ (hArgs .here) (hArgs .here))
  | weakening =>
    exact binary hℳ _ .implication _ _ (hArgs .here)
      (binary hℳ _ .implication _ _ (hArgs (.there .here)) (hArgs .here))
  | contradiction =>
    exact binary hℳ _ .implication _ _ (hArgs .here)
      (binary hℳ _ .implication _ _
        (unary hℳ _ .negation _ (hArgs .here)) (hArgs (.there .here)))
  | classical =>
    exact binary hℳ _ .implication _ _
      (binary hℳ _ .implication _ _ (unary hℳ _ .negation _ (hArgs .here)) (hArgs .here))
      (hArgs .here)
  | explosion =>
    exact binary hℳ _ .implication _ _ (unary hℳ _ .negation _ (hArgs .here))
      (binary hℳ _ .implication _ _ (hArgs .here) (hArgs (.there .here)))
  | caseAnalysis =>
    exact binary hℳ _ .implication _ _
      (binary hℳ _ .implication _ _ (hArgs .here) (hArgs (.there .here)))
      (binary hℳ _ .implication _ _
        (binary hℳ _ .implication _ _
          (unary hℳ _ .negation _ (hArgs .here)) (hArgs (.there .here)))
        (hArgs (.there .here)))
  | quantifierDistribution =>
    exact binary hℳ _ .implication _ _
      (unary hℳ _ .universal _
        (binary hℳ _ .implication _ _ (hArgs .here) (hArgs (.there .here))))
      (binary hℳ _ .implication _ _
        (unary hℳ _ .universal _ (hArgs .here))
        (unary hℳ _ .universal _ (hArgs (.there .here))))
  | equalityReflexivity =>
    exact binary hℳ _ .equality _ _ (hArgs .here) (hArgs .here)

/-- 原模式成员条件本身给出 ω 界，没有在新定义中补加限制。 -/
theorem condition_bounded (hℳ : Theory.Models ℳ theory) (kind : Kind) (code : Carrier ℳ)
    (hCondition : (condition kind).satisfies (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s])) :
    membership ℳ code (omega hℳ) := by
  cases kind
  case implicationDistribution =>
    change (∃ first second third, (((E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons second .nil))) ∧ (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons third .nil))) ∧ code =
      (constructor .implicationDistribution).eval (templateEnv (.cons first (.cons second (.cons third .nil))) : Env (E hℳ).model [] [s,s,s])) at hCondition
    obtain ⟨first,second,third,⟨⟨hFirst,hSecond⟩,hThird⟩,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .implicationDistribution (.cons first (.cons second (.cons third .nil)))
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry with
      | here => exact formula_at hℳ _ second hSecond
      | there entry =>
        cases entry with
        | here => exact formula_at hℳ _ third hThird
        | there entry =>
          cases entry
  case selfImplication =>
    change (∃ first, (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ code =
      (constructor .selfImplication).eval (templateEnv (.cons first .nil) : Env (E hℳ).model [] [s])) at hCondition
    obtain ⟨first,hFirst,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .selfImplication (.cons first .nil)
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry
  case weakening =>
    change (∃ first second, ((E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons second .nil))) ∧ code =
      (constructor .weakening).eval (templateEnv (.cons first (.cons second .nil)) : Env (E hℳ).model [] [s,s])) at hCondition
    obtain ⟨first,second,⟨hFirst,hSecond⟩,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .weakening (.cons first (.cons second .nil))
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry with
      | here => exact formula_at hℳ _ second hSecond
      | there entry =>
        cases entry
  case contradiction =>
    change (∃ first second, ((E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons second .nil))) ∧ code =
      (constructor .contradiction).eval (templateEnv (.cons first (.cons second .nil)) : Env (E hℳ).model [] [s,s])) at hCondition
    obtain ⟨first,second,⟨hFirst,hSecond⟩,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .contradiction (.cons first (.cons second .nil))
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry with
      | here => exact formula_at hℳ _ second hSecond
      | there entry =>
        cases entry
  case classical =>
    change (∃ first, (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ code =
      (constructor .classical).eval (templateEnv (.cons first .nil) : Env (E hℳ).model [] [s])) at hCondition
    obtain ⟨first,hFirst,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .classical (.cons first .nil)
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry
  case explosion =>
    change (∃ first second, ((E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons second .nil))) ∧ code =
      (constructor .explosion).eval (templateEnv (.cons first (.cons second .nil)) : Env (E hℳ).model [] [s,s])) at hCondition
    obtain ⟨first,second,⟨hFirst,hSecond⟩,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .explosion (.cons first (.cons second .nil))
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry with
      | here => exact formula_at hℳ _ second hSecond
      | there entry =>
        cases entry
  case caseAnalysis =>
    change (∃ first second, ((E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons second .nil))) ∧ code =
      (constructor .caseAnalysis).eval (templateEnv (.cons first (.cons second .nil)) : Env (E hℳ).model [] [s,s])) at hCondition
    obtain ⟨first,second,⟨hFirst,hSecond⟩,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .caseAnalysis (.cons first (.cons second .nil))
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry with
      | here => exact formula_at hℳ _ second hSecond
      | there entry =>
        cases entry
  case quantifierDistribution =>
    change (∃ first second, ((E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .successor (.cons ((E hℳ).function .emptySet .nil) .nil)) (.cons first .nil)) ∧ (E hℳ).relation .isFormulaCodeAt (.cons ((E hℳ).function .successor (.cons ((E hℳ).function .emptySet .nil) .nil)) (.cons second .nil))) ∧ code =
      (constructor .quantifierDistribution).eval (templateEnv (.cons first (.cons second .nil)) : Env (E hℳ).model [] [s,s])) at hCondition
    obtain ⟨first,second,⟨hFirst,hSecond⟩,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .quantifierDistribution (.cons first (.cons second .nil))
    intro entry
    cases entry with
    | here => exact formula_at hℳ _ first hFirst
    | there entry =>
      cases entry with
      | here => exact formula_at hℳ _ second hSecond
      | there entry =>
        cases entry
  case equalityReflexivity =>
    change (∃ first, (E hℳ).relation .isTermCodeAt (.cons ((E hℳ).function .emptySet .nil) (.cons first .nil)) ∧ code =
      (constructor .equalityReflexivity).eval (templateEnv (.cons first .nil) : Env (E hℳ).model [] [s])) at hCondition
    obtain ⟨first,hFirst,hEqual⟩ := hCondition
    rw [hEqual]
    apply constructor_natural hℳ .equalityReflexivity (.cons first .nil)
    intro entry
    cases entry with
    | here => exact term_at hℳ _ first hFirst
    | there entry =>
      cases entry

theorem member_bounded (hℳ : Theory.Models ℳ theory) (kind : Kind) (code : Carrier ℳ)
    (hMember : (member kind).satisfies (templateEnv (.cons code .nil))) : membership ℳ code (omega hℳ) :=
  condition_bounded hℳ kind code ((openFormula_correct (E hℳ) (PureSyntaxStage.realizes hℳ) (condition kind) (.cons code .nil)).mp hMember)

theorem functional (hℳ : Theory.Models ℳ theory) (kind : Kind) :
    ∃ output : Carrier ℳ, (graph kind).satisfies (templateEnv (.cons output .nil)) ∧
      ∀ other, (graph kind).satisfies (templateEnv (.cons other .nil)) → other = output :=
  PureSeparation.bounded_functional hℳ (member kind) .nil (omega hℳ) (member_bounded hℳ kind)

theorem graph_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (output : Carrier ℳ) :
    (graph kind).satisfies (templateEnv (.cons output .nil)) ↔
      ∀ code, membership ℳ code output ↔
        (condition kind).satisfies (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s]) := by
  apply (PureFunctionDefinitions.comprehension_correct (member kind) .nil output).trans
  apply forall_congr'; intro code
  exact iff_congr Iff.rfl (openFormula_correct (E hℳ) (PureSyntaxStage.realizes hℳ) (condition kind) (.cons code .nil))

theorem dependencies_covered (kind : Kind) :
    formulaCovered PureSyntaxStage.functionCovered PureSyntaxStage.relationCovered (condition kind) = true := by
  cases kind <;> decide +kernel

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalSchemaSets
