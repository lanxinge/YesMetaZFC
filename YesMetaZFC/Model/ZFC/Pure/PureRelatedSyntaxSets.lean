import YesMetaZFC.Model.ZFC.Pure.PureRelatedSyntaxStage

/-! # 相关项码与公式码的集合收集

成员条件保留原定义中的存在深度量词。递归方程的 ω guard 给出集合界，
因此任意符号集参数上都能用纯分离得到唯一集合。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxSets
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureRelatedSyntaxStage.expansion hℳ

inductive Kind where
  | term | formula
  deriving DecidableEq

def memberSource (kind : Kind) : Formula S [] [s,s] :=
  match kind with
  | .term => FormalSystem.related_term_code_condition (.fvar (.there .here)) (.fvar .here)
  | .formula => FormalSystem.related_formula_code_condition (.fvar (.there .here)) (.fvar .here)

def member (kind : Kind) : Formula ℒ [] [setSort,setSort] :=
  openFormula PureRelatedSyntaxStage.interpretation (memberSource kind)
def graph (kind : Kind) : Formula ℒ [] [setSort,setSort] :=
  PureFunctionDefinitions.comprehension (member kind)

def specification (kind : Kind) : Formula S [] [s,s] :=
  match kind with
  | .term => FormalSystem.related_term_set_spec (.fvar (.there .here)) (.fvar .here)
  | .formula => FormalSystem.related_formula_set_spec (.fvar (.there .here)) (.fvar .here)

theorem member_bounded (hℳ : Theory.Models ℳ theory) (kind : Kind) (symbols code : Carrier ℳ)
    (hMember : (member kind).satisfies (templateEnv (.cons code (.cons symbols .nil)))) :
    membership ℳ code (omega hℳ) := by
  have hSource := (openFormula_correct (E hℳ) (PureRelatedSyntaxStage.realizes hℳ) (memberSource kind) (.cons code (.cons symbols .nil))).mp hMember
  cases kind
  · change (∃ depth, membership ℳ (PureSyntaxOperator.tuple hℳ .term depth (zero hℳ) code)
      (PureRelatedSyntaxFixedPoint.state hℳ symbols)) at hSource
    obtain ⟨depth,hDepth⟩ := hSource
    exact (PureRelatedSyntaxOperator.condition_bounded hℳ .term
      ((PureRelatedSyntaxFixedPoint.equation hℳ .term symbols depth (zero hℳ) code).mp hDepth)).2.2
  · change (∃ depth, membership ℳ (PureSyntaxOperator.tuple hℳ .formula depth (zero hℳ) code)
      (PureRelatedSyntaxFixedPoint.state hℳ symbols)) at hSource
    obtain ⟨depth,hDepth⟩ := hSource
    exact (PureRelatedSyntaxOperator.condition_bounded hℳ .formula
      ((PureRelatedSyntaxFixedPoint.equation hℳ .formula symbols depth (zero hℳ) code).mp hDepth)).2.2

theorem functional (hℳ : Theory.Models ℳ theory) (kind : Kind) (symbols : Carrier ℳ) :
    ∃ output, (graph kind).satisfies (templateEnv (.cons output (.cons symbols .nil))) ∧
      ∀ other, (graph kind).satisfies (templateEnv (.cons other (.cons symbols .nil))) → other = output :=
  PureSeparation.bounded_functional hℳ (member kind) (.cons symbols .nil) (omega hℳ) (member_bounded hℳ kind symbols)

theorem graph_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (symbols output : Carrier ℳ) :
    (graph kind).satisfies (templateEnv (.cons output (.cons symbols .nil))) ↔
      (specification kind).satisfies (templateEnv (.cons output (.cons symbols .nil)) : Env (E hℳ).model [] [s,s]) := by
  apply (PureFunctionDefinitions.comprehension_correct (member kind) (.cons symbols .nil) output).trans
  cases kind <;> simp only [specification,FormalSystem.related_term_set_spec,FormalSystem.related_formula_set_spec,
    Formula.satisfies_forallFreeTop,Formula.satisfies] <;>
    apply forall_congr' <;> intro code <;> apply iff_congr Iff.rfl
  · exact openFormula_correct (E hℳ) (PureRelatedSyntaxStage.realizes hℳ) (memberSource .term) (.cons code (.cons symbols .nil))
  · exact openFormula_correct (E hℳ) (PureRelatedSyntaxStage.realizes hℳ) (memberSource .formula) (.cons code (.cons symbols .nil))

theorem dependencies_covered (kind : Kind) :
    formulaCovered PureRelatedSyntaxStage.functionCovered PureRelatedSyntaxStage.relationCovered (memberSource kind) = true := by cases kind <;> rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxSets
