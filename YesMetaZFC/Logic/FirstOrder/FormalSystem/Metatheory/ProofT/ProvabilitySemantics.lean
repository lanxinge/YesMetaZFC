import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Provability
import YesMetaZFC.Automation.NaturalRosserSemantics

/-! # 普通可证明性的任意模型语义 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.Delta0ProofGraph
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.NaturalRosserSemantics
set_option autoImplicit false
universe x

theorem provability_satisfies {𝒩 : Structure.{0,0,0,x} signature}
    (G : Delta0ProofGraph) {bound free : SetContext}
    (env : Env 𝒩 bound free) (conclusion : SetTerm bound free) :
    (G.provability conclusion).satisfies env ↔
      ∃ code, G.condition.body.satisfies (templateEnv (.cons code (.cons (conclusion.eval env) .nil))) := by
  simp only [provability, Formula.satisfies, binary_satisfies, Term.eval_weakenBound]
  rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.Delta0ProofGraph
