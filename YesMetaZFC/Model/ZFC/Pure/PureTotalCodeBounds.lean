import YesMetaZFC.Model.ZFC.Pure.PureStructuralCodeBounds

/-! # 总化编码函数的输出界

Gödel 配对的合法分支返回自然数，其缺省分支为空集，因此任意输入的输出都在 ω。
这只是所选扩张的范围性质，不把非法输入上的缺省行为当作原理论的额外公理。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTotalCodeBounds
open PureModel PureNaturalInduction PureArithmeticSpecifications PureStructuralCodeBounds
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory FormalSystem
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem pairing (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :
    membership ℳ ((E hℳ).function .godelPairing (.cons left (.cons right .nil))) (omega hℳ) := by
  let output := (E hℳ).function .godelPairing (.cons left (.cons right .nil))
  have hGraph := ((PureSyntaxStage.realizes hℳ).function .godelPairing (.cons left (.cons right .nil)) output).mpr rfl
  change PureGodelPairing.graph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) at hGraph
  have hEnv (value : Carrier ℳ) : (templateEnv (.cons left (.cons right .nil))).pushFree value =
      templateEnv (.cons value (.cons left (.cons right .nil))) := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry; cases entry <;> rfl
  rw [PureGodelPairing.graph,← hEnv output,
    _root_.YesMetaZFC.Automation.TotalizedGraph.satisfies] at hGraph
  simp only [hEnv] at hGraph
  rcases hGraph with hBody | ⟨_,hEmpty⟩
  · exact ((PureGodelPairing.body_correct hℳ left right output).mp hBody).2.1
  · have hEmpty := (PureRelationFunctions.emptyFallback_correct (.cons left (.cons right .nil)) output).mp hEmpty
    have hEqual : output = zero hℳ := extensionality hℳ output (zero hℳ)
      (fun element => ⟨fun h => False.elim (hEmpty element h),fun h => False.elim (zero_spec hℳ element h)⟩)
    change membership ℳ output (omega hℳ)
    rw [hEqual]
    exact zero_mem hℳ

theorem raw_node (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (tag : StructuralCodeTag) (payload : SetTerm bound free) :
    membership ℳ ((structural_raw_node_code_term tag payload).eval env) (omega hℳ) := by
  change membership ℳ ((PureRoundTwoStage.expansion hℳ).function .successor
    (.cons ((E hℳ).function .godelPairing (.cons ((finite_numeral_term (structural_code_tag tag)).eval env) (.cons (payload.eval env) .nil))) .nil)) _
  rw [PureSyntaxOperator.succ_eq hℳ]
  exact succ_mem hℳ (pairing hℳ _ _)

theorem node (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (tag : StructuralCodeTag) (fields : List (SetTerm bound free)) :
    membership ℳ ((structural_node_code_term tag fields).eval env) (omega hℳ) := raw_node hℳ env tag _
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTotalCodeBounds
