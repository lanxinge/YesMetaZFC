import YesMetaZFC.Model.ZFC.Pure.PureFunctionDefinitions
import YesMetaZFC.Model.SetTheory.FromFirstOrder
import YesMetaZFC.SetTheory.Separation

/-! # 任意当前纯公式的 ZF 分离接口

原 Project 分离模式经反向语法桥接受当前内在类型公式。集合图仍直接使用给定
纯正文，不引入新的谓词、公理或对模型标准性的假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSeparation
open PureModel
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Project.FirstOrderSemantics.reduct
universe x

def entryAt : {context : SortContext ℒ} → Fin context.length → Variable context setSort
  | .nil, entry => Fin.elim0 entry
  | .cons .set _, entry => Fin.cases .here (fun previous => .there (entryAt previous)) entry

theorem entryAt_position {context : SortContext ℒ} (entry : Variable context setSort) :
    entryAt entry.position = entry := by
  induction context with
  | nil => cases entry
  | cons introduced context ih =>
      cases introduced
      cases entry with
      | here => rfl
      | there previous => exact congrArg Variable.there (ih previous)

def parameterEnv {ℳ : Structure.{0, 0, 0, x} ℒ} {context : SortContext ℒ}
    (args : Values ℳ.Carrier context) (default : Carrier ℳ) :
    _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) context.length where
  bound entry := (templateEnv args).freeVal (entryAt entry)
  free := fun _ => default

theorem parameter_lookup {ℳ : Structure.{0, 0, 0, x} ℒ} {context : SortContext ℒ}
    (args : Values ℳ.Carrier context) (default : Carrier ℳ) (entry : Variable context setSort) :
    (parameterEnv args default).bound entry.position = (templateEnv args).freeVal entry := by
  simp only [parameterEnv, entryAt_position]

theorem parameter_cons {ℳ : Structure.{0, 0, 0, x} ℒ} {context : SortContext ℒ}
    (args : Values ℳ.Carrier context) (element default : Carrier ℳ) :
    parameterEnv (.cons element args) default = (parameterEnv args default).push element := by
  unfold parameterEnv _root_.YesMetaZFC.SetTheory.Env.push
  rw [_root_.YesMetaZFC.SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry <;> rfl
  · rfl

def schema {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: parameters)) :
    Project.UnarySchema parameters.length where
  body := Project.FromFirstOrder.translate (bound := []) (free := setSort :: parameters)
    (depth := parameters.length + 1) (fun {_} entry => nomatch entry) (fun {_} entry => entry.position) body
  freeClosed := Project.FromFirstOrder.freeClosed _ _ body

theorem schema_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: parameters))
    (args : Values ℳ.Carrier parameters) (element default : Carrier ℳ) :
    Project.Formula.satisfies ((parameterEnv args default).push element) (schema body).body ↔
      body.satisfies (templateEnv (.cons element args)) := by
  rw [← parameter_cons]
  exact Project.FromFirstOrder.correct (project_models hℳ).1 body _ _ _ _
    (fun entry => nomatch entry) (parameter_lookup (.cons element args) default)

/-- 任意纯正文的分离存在性，参数仍用当前核的值列传入。 -/
theorem exists_subset {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: parameters))
    (args : Values ℳ.Carrier parameters) (ambient : Carrier ℳ) :
    ∃ output, ∀ element, membership ℳ element output ↔
      membership ℳ element ambient ∧ body.satisfies (templateEnv (.cons element args)) := by
  obtain ⟨output, hOutput⟩ := _root_.YesMetaZFC.SetTheory.ZF.separation_exists_d
    (project_modelsZF hℳ) (schema body) (parameterEnv args ambient) ambient
  exact ⟨output, fun element => (hOutput element).trans
    (and_congr Iff.rfl (schema_correct hℳ body args element ambient))⟩

/-- 成员条件一旦具有集合母集，就给出实际纯图及任意参数的唯一输出。 -/
theorem bounded_functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: parameters))
    (args : Values ℳ.Carrier parameters) (ambient : Carrier ℳ)
    (hBound : ∀ element, body.satisfies (templateEnv (.cons element args)) → membership ℳ element ambient) :
    ∃ output, (PureFunctionDefinitions.comprehension body).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (PureFunctionDefinitions.comprehension body).satisfies (templateEnv (.cons other args)) → other = output := by
  obtain ⟨output, hOutput⟩ := exists_subset hℳ body args ambient
  have hGraph := (PureFunctionDefinitions.comprehension_correct body args output).mpr
    (fun element => (hOutput element).trans ⟨And.right, fun h => ⟨hBound element h, h⟩⟩)
  exact ⟨output, hGraph, fun other hOther =>
    PureFunctionDefinitions.comprehension_unique hℳ body args other output hOther hGraph⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSeparation
