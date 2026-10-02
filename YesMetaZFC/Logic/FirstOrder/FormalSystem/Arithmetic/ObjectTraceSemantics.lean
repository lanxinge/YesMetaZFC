import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.NaturalRosserSemantics

/-! # 有界对象轨迹的模型语义

展开轨迹时保留原幂集量词界，不假定候选轨迹在模型外部有限。
-/
namespace YesMetaZFC.Automation.ObjectTrace
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open RelationalTranslation NaturalRosserSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem condition_satisfies (step : FormulaTemplate.Binary)
    {bound free : SetContext} (env : Env 𝒩 bound free) (carrier root : SetTerm bound free) :
    (condition step carrier root).satisfies env ↔
      ∃ trace, mem 𝒩 trace (𝒩.funcInterp .powerSet (.cons (carrier.eval env) .nil)) ∧
        mem 𝒩 (root.eval env) trace ∧
        ∀ row, mem 𝒩 row trace →
          step.body.satisfies (templateEnv (.cons row (.cons trace .nil))) := by
  simp only [condition, witnessBody, closed, Formula.LevyBound.boundedExists,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership, Formula.satisfies,
    binary_satisfies, Arguments.eval, Term.eval_weakenBound]
  rfl

end YesMetaZFC.Automation.ObjectTrace
