import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Infinity
import YesMetaZFC.Logic.FirstOrder.Metatheory.Propositional
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # 将对象证明图的证明码限制在模型内部 ω

包装保留原检查器、全部实际证明编码及标准码正负表示，只排除非自然数对象作为
证明码。它不要求模型内部自然数在外部标准，也不修改任何非逻辑公理。
接入 Rosser 表示会改变对象图及随后生成的固定点 quotation，须明确执行这一迁移。
-/
namespace YesMetaZFC.Automation.NaturalProofPresentation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe x y

/-- 原正负表示确定任意标准码在所有原理论模型中的真值。 -/
theorem models_agree {Traw Thilbert : SetTheory}
    (original : Delta1ProofPresentation Traw Thilbert)
    {ℳ : Structure.{0,0,0,x} signature} {𝒩 : Structure.{0,0,0,y} signature}
    (hℳ : Theory.Models ℳ Traw) (h𝒩 : Theory.Models 𝒩 Traw)
    (number : Nat) (formula : SetSentence) :
    (original.code number formula).TrueIn ℳ ↔ (original.code number formula).TrueIn 𝒩 := by
  cases hChecked : original.checked number formula with
  | true =>
    have hProof := original.condition_positive (proofCode := number) (formula := formula) hChecked
    exact ⟨fun _ => hProof.semantically_entails 𝒩 h𝒩,
      fun _ => hProof.semantically_entails ℳ hℳ⟩
  | false =>
    have hProof := original.condition_negative (proofCode := number) (formula := formula) hChecked
    exact ⟨fun h => False.elim (hProof.semantically_entails ℳ hℳ h),
      fun h => False.elim (hProof.semantically_entails 𝒩 h𝒩 h)⟩

def template (graph : Delta0ProofGraph) : FormulaTemplate.Binary where
  body := ((.fvar .here : SetOpenTerm [.set,.set]) ∈ₘ ωₘ) ∧ₘ
    graph.condition (.fvar .here) (.fvar (.there .here))

theorem template_apply (graph : Delta0ProofGraph) {bound free : SetContext}
    (code conclusion : SetTerm bound free) :
    template graph code conclusion = (code ∈ₘ ωₘ) ∧ₘ graph.condition code conclusion := by
  change (_ ∧ₘ _).substituteMapped _ _ = _
  simp only [Formula.substituteMapped, FormulaTemplate.apply_two_substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons]

def graph (original : Delta0ProofGraph) : Delta0ProofGraph where
  condition := template original
  delta0 code conclusion := by
    rw [template_apply]
    exact Formula.IsDelta0.conj (Formula.IsDelta0.rel _ _) (original.delta0 code conclusion)

/-- 自然数 guard 使外层证明码存在量词也有界；分类相对于含 ω 的支撑语言。 -/
theorem comparison_delta0 (original : Delta0ProofGraph) (domain : Delta0CodeDomain)
    {bound free : SetContext} (left right : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound ((graph original).comparison domain left right) := by
  unfold Delta0ProofGraph.comparison
  apply Formula.IsDelta0.guarded_exists ωₘ
  · exact .conj (domain.delta0 _) (.conj ((graph original).delta0 _ _)
      ((graph original).no_smaller_delta0 _ _))
  · apply Formula.MembershipGuard.conj_right
    apply Formula.MembershipGuard.conj_left
    rw [show (graph original).condition = template original from rfl, template_apply]
    exact .conj_left .membership

/-- 由原自然数定理填入 guard，保留原完整证明表示的全部标准实例。 -/
def presentation {Traw Thilbert : SetTheory}
    (original : Delta1ProofPresentation Traw Thilbert)
    (hNumeral : ∀ number : Nat,
      Derives Traw [] ((numₘ(number) : SetTerm [] []) ∈ₘ ωₘ)) :
    Delta1ProofPresentation Traw Thilbert where
  graph := graph original.graph
  checked := original.checked
  checked_sound := original.checked_sound
  checked_complete := original.checked_complete
  condition_positive {proofCode} {formula} h := by
    change Derives Traw [] (template original.graph (numₘ(proofCode)) (IntrinsicQuotation.quote formula))
    rw [template_apply]
    exact Derives.conj_intro (hNumeral proofCode) (original.condition_positive h)
  condition_negative {proofCode} {formula} h := by
    change Derives Traw [] (¬ₘ template original.graph (numₘ(proofCode)) (IntrinsicQuotation.quote formula))
    rw [template_apply]
    apply Derives.neg_intro
    exact Derives.neg_elim
      (Derives.conj_elim_right (Derives.assumption List.mem_cons_self))
      (original.condition_negative h).context_weaken_cons

/-- 对象语义直接排除所有非自然数输入；不是只排除外部无穷码。 -/
theorem natural_of_satisfied (original : Delta0ProofGraph)
    {ℳ : Structure.{0,0,0,x} signature} {bound free : SetContext}
    (env : Env ℳ bound free) (code conclusion : SetTerm bound free)
    (h : ((graph original).condition code conclusion).satisfies env) :
    (code ∈ₘ ωₘ).satisfies env := by
  rw [show (graph original).condition = template original from rfl, template_apply] at h
  exact h.1

end YesMetaZFC.Automation.NaturalProofPresentation
