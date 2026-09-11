import YesMetaZFC.Model.Interpretation.ModelClosure
import YesMetaZFC.Model.ZFC.Pure.PureCompletedStage
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportBasisTemplate

/-! # 最终纯扩张满足全部源语言分离实例

任意源谓词先翻译为实际纯公式，再使用裸 ZFC 分离。因而十一类参数闭模板
可以统一验证，无须为各个收集对象重复证明分离外壳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSupportSeparation
open PureModel Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

/-- 自由元素槽与原谓词的唯一 bound 槽具有相同语义。 -/
theorem atNewest_correct {𝒩 : Structure.{0,0,0,x} S} {free : SortContext S}
    (predicate : SetPredicate free) (env : Env 𝒩 [] free) (element : 𝒩.Carrier s) :
    predicate.atNewest.satisfies (env.pushFree element) ↔
      predicate.body.satisfies (env.pushBound element) := by
  rw [SetPredicate.atNewest, Formula.satisfies_instantiateTop]
  exact Formula.satisfies_weakenFree (env.pushBound element) element predicate.body

theorem weakened_body {𝒩 : Structure.{0,0,0,x} S} {free : SortContext S}
    (predicate : SetPredicate free) (env : Env 𝒩 [] free) (value element : 𝒩.Carrier s) :
    predicate.weakenFree.body.satisfies ((env.pushFree value).pushBound element) ↔
      predicate.body.satisfies (env.pushBound element) :=
  Formula.satisfies_weakenFree (env.pushBound element) value predicate.body

/-- 只在抽象源模型展开分离外壳，保持实际解释图不透明。 -/
theorem open_correct {𝒩 : Structure.{0,0,0,x} S} {free : SortContext S}
    (predicate : SetPredicate free) (env : Env 𝒩 [] free) :
    predicate.separation_open_axiom.satisfies env ↔
      ∀ source, ∃ output, ∀ element,
        𝒩.relInterp .membership (.cons element (.cons output .nil)) ↔
          𝒩.relInterp .membership (.cons element (.cons source .nil)) ∧
            predicate.body.satisfies (env.pushBound element) := by
  simp only [SetPredicate.separation_open_axiom, SetPredicate.separation_exists,
    SetPredicate.separation_spec, membership_specification, SetPredicate.separation_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop,
    Formula.satisfies, atNewest_correct, weakened_body]
  rfl

noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureCompletedStage.expansion hℳ

theorem open_axiom (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (predicate : SetPredicate free) (args : Values (E hℳ).model.Carrier free) :
    predicate.separation_open_axiom.satisfies (templateEnv args : Env (E hℳ).model [] free) := by
  apply (open_correct predicate (templateEnv args)).mpr
  intro source
  obtain ⟨output, hOutput⟩ := PureSeparation.exists_subset hℳ
    (openFormula PureCompletedStage.interpretation predicate.atNewest)
    (mapValues PureCompletedStage.interpretation args) source
  refine ⟨output, fun element => ?_⟩
  have hBody := openFormula_correct (E hℳ) (PureCompletedStage.realizes hℳ)
    predicate.atNewest (.cons element args)
  rw [templateEnv_cons args element] at hBody
  have hMeaning := hBody.trans (atNewest_correct predicate (templateEnv args) element)
  exact (hOutput element).trans (and_congr Iff.rfl hMeaning)

theorem separation_axiom (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (predicate : SetPredicate free) :
    predicate.separation_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) :=
  close_of_values predicate.separation_open_axiom (open_axiom hℳ predicate)

theorem parameter_template (hℳ : Theory.Models ℳ theory) (kind : SupportParameters.Kind) :
    (SupportAssembly.closedTemplate kind).satisfies (Env.empty : Env (E hℳ).model [] []) :=
  separation_axiom hℳ (SupportAssembly.predicate kind
    (SyntaxEncode.substitutionArguments _ VariableSubstitution.freeId))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSupportSeparation
