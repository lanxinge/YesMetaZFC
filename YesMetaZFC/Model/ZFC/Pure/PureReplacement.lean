import YesMetaZFC.Model.ZFC.Pure.PureSeparation
import YesMetaZFC.Model.ZFC.Pure.PureKuratowskiProject
import YesMetaZFC.Model.ZFC.Pure.PureMappingDefinitions
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 当前纯公式的函数图收集

将带参数的二元纯正文直接送入 Project 替换接口，保留精确定义域和逐点规格。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureReplacement
open PureModel PureSeparation
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Project.FirstOrderSemantics.reduct
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

def schema {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: setSort :: parameters)) :
    Project.BinarySchema parameters.length where
  body := Project.FromFirstOrder.translate (bound := []) (free := setSort :: setSort :: parameters)
    (depth := parameters.length + 2) (fun {_} entry => nomatch entry) (fun {_} entry => entry.position) body
  freeClosed := Project.FromFirstOrder.freeClosed _ _ body

theorem schema_correct (hℳ : Theory.Models ℳ theory) {parameters : SortContext ℒ}
    (body : Formula ℒ [] (setSort :: setSort :: parameters)) (args : Values ℳ.Carrier parameters)
    (input output default : Carrier ℳ) :
    (schema body).denote (parameterEnv args default) input output ↔ body.satisfies (templateEnv (.cons output (.cons input args))) := by
  change Project.Formula.satisfies (((parameterEnv args default).push input).push output) (schema body).body ↔ _
  rw [← parameter_cons,← parameter_cons]
  exact Project.FromFirstOrder.correct (project_models hℳ).1 body _ _ _ _
    (fun entry => nomatch entry) (parameter_lookup (.cons output (.cons input args)) default)

theorem mapping_exists (hℳ : Theory.Models ℳ theory) {parameters : SortContext ℒ}
    (body : Formula ℒ [] (setSort :: setSort :: parameters)) (args : Values ℳ.Carrier parameters) (source target : Carrier ℳ)
    (hTotal : ∀ input, membership ℳ input source → ∃ output, body.satisfies (templateEnv (.cons output (.cons input args))))
    (hUnique : ∀ input, membership ℳ input source → ∀ first second,
      body.satisfies (templateEnv (.cons first (.cons input args))) → body.satisfies (templateEnv (.cons second (.cons input args))) → first = second)
    (hTarget : ∀ input, membership ℳ input source → ∀ output, body.satisfies (templateEnv (.cons output (.cons input args))) → membership ℳ output target) :
    ∃ function, PureMappingDefinitions.IsMapping ℳ function source target ∧ ∀ input output,
      PureKuratowski.PairMember ℳ input output function ↔ membership ℳ input source ∧ body.satisfies (templateEnv (.cons output (.cons input args))) := by
  obtain ⟨function,hFunction,hValues⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (schema body) (parameterEnv args source)
    (fun input hInput => by
      obtain ⟨output,hOutput⟩ := hTotal input hInput
      exact ⟨output,(schema_correct hℳ body args input output source).mpr hOutput⟩)
    (fun input hInput first second hFirst hSecond => hUnique input hInput first second
      ((schema_correct hℳ body args input first source).mp hFirst) ((schema_correct hℳ body args input second source).mp hSecond))
    (fun input output hInput hOutput => hTarget input hInput output ((schema_correct hℳ body args input output source).mp hOutput))
  exact ⟨function,hFunction,fun input output => (hValues input output).trans (and_congr Iff.rfl (schema_correct hℳ body args input output source))⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureReplacement
