import YesMetaZFC.Model.ZFC.Pure.PureFunctionDefinitions
import YesMetaZFC.SetTheory.Separation

/-! # Project 闭正文到纯语言参数模板

把 Project 的有限 bound 参数整体移为当前核的 free 槽。此桥让后续定义直接复用
已证明语义的 Project 公式；生成结果仍是当前纯隶属签名上的实际公式。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProjectTemplate
open PureModel
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x

def toPure {count : Nat} (body : Project.Formula 1 count) (hClosed : body.FreeClosed) :
    Formula ℒ [] (Project.fo_bound_context count) :=
  (Project.fo_formula body hClosed).substituteMapped (fun entry => .fvar entry) VariableSubstitution.empty

def parameterEnv {ℳ : Structure.{0, 0, 0, x} ℒ} {count : Nat}
    (args : Values ℳ.Carrier (Project.fo_bound_context count)) (default : Carrier ℳ) :
    _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) count where
  bound entry := (templateEnv args).freeVal (Project.fo_bound_variable entry)
  free := fun _ => default

theorem correct {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {count : Nat} (body : Project.Formula 1 count) (hClosed : body.FreeClosed)
    (args : Values ℳ.Carrier (Project.fo_bound_context count)) (default : Carrier ℳ) :
    (toPure body hClosed).satisfies (templateEnv args) ↔
      Project.Formula.satisfies (parameterEnv args default) body := by
  unfold toPure
  have h := Formula.satisfies_substitute (templateEnv args)
    (Substitution.map (fun entry => .fvar entry) VariableSubstitution.empty) (Project.fo_formula body hClosed)
  exact h.trans (Project.FirstOrderSemantics.formula_correct (project_models hℳ).1 body hClosed
    ((templateEnv args).pullback (Substitution.map (fun entry => .fvar entry) VariableSubstitution.empty))
    (fun _ => default))

theorem parameterEnv_cons {ℳ : Structure.{0, 0, 0, x} ℒ} {count : Nat}
    (args : Values ℳ.Carrier (Project.fo_bound_context count)) (element default : Carrier ℳ) :
    parameterEnv (ℳ := ℳ) (count := count + 1) (.cons element args) default = (parameterEnv args default).push element := by
  rw [_root_.YesMetaZFC.SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry <;> rfl
  · rfl

def setGraph {count : Nat} (schema : Project.UnarySchema count) :
    Formula ℒ [] (Project.fo_bound_context (count + 1)) :=
  PureFunctionDefinitions.comprehension (toPure schema.body schema.freeClosed)

theorem setGraph_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {count : Nat} (schema : Project.UnarySchema count)
    (args : Values ℳ.Carrier (Project.fo_bound_context count)) (output default : Carrier ℳ) :
    (setGraph schema).satisfies (templateEnv (.cons output args)) ↔
      ∀ element, membership ℳ element output ↔
        Project.Formula.satisfies ((parameterEnv args default).push element) schema.body := by
  rw [setGraph, PureFunctionDefinitions.comprehension_correct]
  simp only [correct hℳ schema.body schema.freeClosed _ default, parameterEnv_cons]

/-- 任意 Project 分离条件只需证明落入一个集合，即得到实际纯图的唯一输出。 -/
theorem bounded_functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {count : Nat} (schema : Project.UnarySchema count)
    (args : Values ℳ.Carrier (Project.fo_bound_context count)) (default ambient : Carrier ℳ)
    (hBound : ∀ element, Project.Formula.satisfies ((parameterEnv args default).push element) schema.body →
      membership ℳ element ambient) :
    ∃ output, (setGraph schema).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (setGraph schema).satisfies (templateEnv (.cons other args)) → other = output := by
  obtain ⟨output, hOutput⟩ := _root_.YesMetaZFC.SetTheory.ZF.separation_exists_d
    (project_modelsZF hℳ) schema (parameterEnv args default) ambient
  have hGraph : (setGraph schema).satisfies (templateEnv (.cons output args)) :=
    (setGraph_correct hℳ schema args output default).mpr (fun element =>
      (hOutput element).trans ⟨And.right, fun h => ⟨hBound element h, h⟩⟩)
  exact ⟨output, hGraph, fun other hOther => PureFunctionDefinitions.comprehension_unique
    hℳ (toPure schema.body schema.freeClosed) args other output hOther hGraph⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProjectTemplate
