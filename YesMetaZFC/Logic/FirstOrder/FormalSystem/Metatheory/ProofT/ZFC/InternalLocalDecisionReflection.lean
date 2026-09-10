import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveQueries

/-! # 原有限局部规则表的内部正反射

每条规则保留原头表达式、全部查询及原有界见证块。
参数元数只决定固定的公式骨架，见证值和查询轨迹可以非标准。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] Positive Evaluates
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
variable {T : SetTheory} {bound free : SetContext}
include h𝒩

theorem localMatrix (rule : ObjectLocalDecision.Rule T)
    (hQueries : ∀ query ∈ rule.queries, Positive 𝒩 query.1.condition.body)
    {inputs : Fin rule.arity → SetTerm bound free} {root : SetTerm bound free}
    (hi : ∀ i, Evaluates 𝒩 (inputs i)) (hr : Evaluates 𝒩 root) :
    Positive 𝒩 (rule.matrix inputs root) := by
  apply conj h𝒩 (equal h𝒩 hr (expression h𝒩 rule.head inputs hi))
  apply allOf h𝒩
  intro formula hf
  obtain ⟨query, hq, rfl⟩ := List.mem_map.mp hf
  exact unary query.1.condition (hQueries query hq) (expression h𝒩 query.2 inputs hi)

theorem localRule (rule : ObjectLocalDecision.Rule T)
    (hQueries : ∀ query ∈ rule.queries, Positive 𝒩 query.1.condition.body) :
    Positive 𝒩 rule.template.body :=
  quantify h𝒩 rule.arity (successor h𝒩 (fvar _))
    (localMatrix h𝒩 rule hQueries (fun _ => bvar _) (fvar _))

/-- 先证明任意规则，再对原有限规则表作析取，不展开或重写领域规则。 -/
theorem localTest (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (rules : List (ObjectLocalDecision.Rule T))
    (hQueries : ∀ rule ∈ rules, ∀ query ∈ rule.queries, Positive 𝒩 query.1.condition.body) :
    Positive 𝒩 (ObjectLocalDecision.localTest C hSuccessor rules).condition.body := by
  apply anyOf h𝒩
  intro formula hf
  obtain ⟨rule, hr, rfl⟩ := List.mem_map.mp hf
  exact localRule h𝒩 rule (hQueries rule hr)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
