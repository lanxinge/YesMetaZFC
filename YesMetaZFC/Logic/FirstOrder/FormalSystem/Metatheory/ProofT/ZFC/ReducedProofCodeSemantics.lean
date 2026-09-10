import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceTraceComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureNaturalRosserAgreement
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProvabilitySemantics

/-! # 当前证明图在内部结论码上的语义

直接解释原有二元证明模板；不新增或替换可证明性谓词。
外部闭句的 quotation 只是结论参数的一个特例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofCodeSemantics
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceTraceComposition
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def CodeProof (𝒩 : Structure.{0,0,0,x} signature) (code conclusion : 𝒩.Carrier .set) : Prop :=
  ReducedProofPresentation.presentation.graph.condition.body.satisfies
    (templateEnv (.cons code (.cons conclusion .nil)))

/-- 原证明关系加内部自然数 guard 的存在投影。 -/
def ProvableCode (𝒩 : Structure.{0,0,0,x} signature) (conclusion : 𝒩.Carrier .set) : Prop :=
  ∃ proof, mem 𝒩 proof (w 𝒩) ∧ CodeProof 𝒩 proof conclusion

theorem provableCode_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (conclusion : SetTerm bound free) :
    ((NaturalProofPresentation.graph ReducedProofPresentation.presentation.graph).provability conclusion).satisfies env ↔
      ProvableCode 𝒩 (conclusion.eval env) := by
  rw [Delta0ProofGraph.provability_satisfies]
  exact exists_congr (fun proof => NaturalRosserSemantics.natural_graph_satisfies
    ReducedProofPresentation.presentation.graph proof (conclusion.eval env))

theorem codeProof_trace (code conclusion : 𝒩.Carrier .set) :
    CodeProof 𝒩 code conclusion ↔
      Witness (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition)
        (node 𝒩 1 [code, conclusion]) := by
  unfold CodeProof
  rw [ReducedProofPresentation.graph_condition]
  have h := ObjectTrace.condition_satisfies
    (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition)
    (templateEnv (.cons code (.cons conclusion .nil)) : Env 𝒩 [] [.set,.set])
    omega_term (IntrinsicQuotation.node 1 [.fvar .here, .fvar (.there .here)])
  simpa only [node_eval, List.map_cons, List.map_nil] using! h

theorem codeProof_quotation (code : 𝒩.Carrier .set) (formula : SetSentence) :
    CodeProof 𝒩 code ((IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] [])) ↔
      PureNaturalRosserAgreement.Proof 𝒩 code formula := Iff.rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofCodeSemantics
