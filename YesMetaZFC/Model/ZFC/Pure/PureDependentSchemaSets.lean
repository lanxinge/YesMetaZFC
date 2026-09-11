import YesMetaZFC.Model.ZFC.Pure.PureTransformStage
import YesMetaZFC.Model.ZFC.Pure.PureTotalCodeBounds

/-! # 依赖语法操作的三个公理集合

保留特化、空量化、等式替换的完整原成员条件，包括变换关系与自由变量不出现条件。
模式外壳的总化编码范围给出分离界；并不将这个范围性质解释为良构性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureDependentSchemaSets
open PureModel
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
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureTransformStage.expansion hℳ

inductive Kind where
  | specialization | vacuousQuantifier | equalitySubstitution
  deriving DecidableEq

def parameters : Kind → SortContext S
  | .specialization | .vacuousQuantifier => [s,s]
  | .equalitySubstitution => [s,s,s,s]
def constructor (kind : Kind) : Term S [] (parameters kind) s := match kind with
  | .specialization => specialization_axiom_code_term (.fvar .here) (.fvar (.there .here))
  | .vacuousQuantifier => vacuous_quantifier_axiom_code_term (.fvar .here) (.fvar (.there .here))
  | .equalitySubstitution => equality_substitution_axiom_code_term (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
def condition : Kind → Formula S [] [s]
  | .specialization => specialization_axiom_condition (.fvar .here)
  | .vacuousQuantifier => vacuous_quantifier_axiom_condition (.fvar .here)
  | .equalitySubstitution => equality_substitution_axiom_condition (.fvar .here)
def member (kind : Kind) : Formula ℒ [] [setSort] := openFormula PureTransformStage.interpretation (condition kind)
def graph (kind : Kind) : Formula ℒ [] [setSort] := PureFunctionDefinitions.comprehension (member kind)

theorem constructor_bounded (hℳ : Theory.Models ℳ theory) (kind : Kind)
    (args : Values (E hℳ).model.Carrier (parameters kind)) :
    membership ℳ ((constructor kind).eval (templateEnv args)) ((E hℳ).function .omega .nil) := by
  apply (PureTransformStage.syntax_transfer hℳ
    (membership_formula (constructor kind) omega_term) (by cases kind <;> rfl) args).mp
  have hOmega : (PureSyntaxStage.expansion hℳ).function .omega .nil = PureNaturalInduction.omega hℳ := PureSyntaxOperator.omega_eq hℳ
  change membership ℳ ((constructor kind).eval (templateEnv args : Env (PureSyntaxStage.expansion hℳ).model [] (parameters kind))) ((PureSyntaxStage.expansion hℳ).function .omega .nil)
  rw [hOmega]
  cases kind <;> apply PureTotalCodeBounds.node hℳ _ .implication

/-- 在抽象源结构中提取模式外壳，避免展开具体递归关系的纯图。 -/
theorem constructor_witness (𝒩 : Structure.{0,0,0,x} S) (kind : Kind) (code : 𝒩.Carrier s)
    (h : (condition kind).satisfies (templateEnv (.cons code .nil) : Env 𝒩 [] [s])) :
    ∃ args : Values 𝒩.Carrier (parameters kind), code = (constructor kind).eval (templateEnv args) := by
  cases kind
  case specialization =>
    change (∃ body replacement result, _ ∧ (_ ∧ code =
      (constructor .specialization).eval (templateEnv (.cons body (.cons result .nil)) : Env 𝒩 [] [s,s]))) at h
    obtain ⟨body,_,result,_,_,rfl⟩ := h
    exact ⟨.cons body (.cons result .nil),rfl⟩
  case vacuousQuantifier =>
    change (∃ antecedent variableIndex body, _ ∧ (_ ∧ code =
      (constructor .vacuousQuantifier).eval (templateEnv (.cons antecedent (.cons body .nil)) : Env 𝒩 [] [s,s]))) at h
    obtain ⟨antecedent,_,body,_,_,rfl⟩ := h
    exact ⟨.cons antecedent (.cons body .nil),rfl⟩
  case equalitySubstitution =>
    change (∃ variableIndex replacement body result, _ ∧ code =
      (constructor .equalitySubstitution).eval (templateEnv (.cons variableIndex (.cons replacement (.cons body (.cons result .nil)))) : Env 𝒩 [] [s,s,s,s])) at h
    obtain ⟨variableIndex,replacement,body,result,_,rfl⟩ := h
    exact ⟨.cons variableIndex (.cons replacement (.cons body (.cons result .nil))),rfl⟩

theorem condition_bounded (hℳ : Theory.Models ℳ theory) (kind : Kind) (code : Carrier ℳ)
    (h : (condition kind).satisfies (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s])) :
    membership ℳ code ((E hℳ).function .omega .nil) := by
  obtain ⟨args,rfl⟩ := constructor_witness (E hℳ).model kind code h
  exact constructor_bounded hℳ kind args

theorem member_bounded (hℳ : Theory.Models ℳ theory) (kind : Kind) (code : Carrier ℳ)
    (h : (member kind).satisfies (templateEnv (.cons code .nil))) : membership ℳ code ((E hℳ).function .omega .nil) :=
  condition_bounded hℳ kind code ((openFormula_correct (E hℳ) (PureTransformStage.realizes hℳ) (condition kind) (.cons code .nil)).mp h)

theorem functional (hℳ : Theory.Models ℳ theory) (kind : Kind) :
    ∃ output : Carrier ℳ, (graph kind).satisfies (templateEnv (.cons output .nil)) ∧
      ∀ other, (graph kind).satisfies (templateEnv (.cons other .nil)) → other = output :=
  PureSeparation.bounded_functional hℳ (member kind) .nil ((E hℳ).function .omega .nil) (member_bounded hℳ kind)

theorem graph_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (output : Carrier ℳ) :
    (graph kind).satisfies (templateEnv (.cons output .nil)) ↔
      ∀ code, membership ℳ code output ↔ (condition kind).satisfies (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s]) := by
  apply (PureFunctionDefinitions.comprehension_correct (member kind) .nil output).trans
  apply forall_congr'; intro code
  exact iff_congr Iff.rfl (openFormula_correct (E hℳ) (PureTransformStage.realizes hℳ) (condition kind) (.cons code .nil))

theorem dependencies_covered (kind : Kind) :
    formulaCovered PureTransformStage.functionCovered PureTransformStage.relationCovered (condition kind) = true := by cases kind <;> rfl
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureDependentSchemaSets
