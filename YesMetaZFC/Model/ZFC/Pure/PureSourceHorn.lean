import YesMetaZFC.Model.ZFC.Pure.PureSourceCoding
import YesMetaZFC.Automation.ObjectHornSemantics

/-! # 有界 Horn 轨迹与局部规则的对应

每个候选轨迹行属于内部 ω，参数界为该行的后继。规则中的全部表达式因而在
合法自然数输入上求值；递归前提只读取同一个集合轨迹。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceHorn
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem expr_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {n : Nat}
    {values : Fin n → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩)) (expr : ObjectHorn.Expr n) :
    mem 𝒩 (exprValue 𝒩 values expr) (w 𝒩) := by
  induction expr with
  | literal number => exact PureSourceCoding.numeral_natural h𝒩 number
  | var i => exact hValues i
  | succ body ih => exact (omega_closed h𝒩).2 _ ih
  | pair left right ihLeft ihRight => exact (PureSourceCoding.pairing_spec h𝒩 ihLeft ihRight).1

theorem expr_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {n : Nat}
    {values : Fin n → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩)) (expr : ObjectHorn.Expr n) :
    exprValue 𝒩 values expr = exprValue (canonical h𝒩) values expr := by
  induction expr with
  | literal number => exact numeral_agrees h𝒩 number
  | var i => rfl
  | succ body ih =>
    exact (successor_agrees h𝒩 _).trans (congrArg (suc (canonical h𝒩)) ih)
  | pair left right ihLeft ihRight =>
    change pair 𝒩 (exprValue 𝒩 values left) (exprValue 𝒩 values right) = _
    rw [PureSourceCoding.pairing_agrees h𝒩 (expr_natural h𝒩 hValues left) (expr_natural h𝒩 hValues right), ihLeft, ihRight]
    rfl

theorem rule_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (rule : ObjectHorn.Rule)
    {row : 𝒩.Carrier .set} (hRow : mem 𝒩 row (w 𝒩)) (trace : 𝒩.Carrier .set) :
    rule.template.body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) ↔
      rule.template.body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env (canonical h𝒩) [] [.set,.set]) := by
  rw [rule_satisfies, rule_satisfies]
  apply exists_congr
  intro values
  change ((∀ i, mem 𝒩 (values i) (suc 𝒩 row)) ∧ _) ↔
    ((∀ i, mem 𝒩 (values i) (suc (canonical h𝒩) row)) ∧ _)
  rw [← successor_agrees h𝒩 row]
  apply and_congr_right
  intro hBound
  have hNatural i := member_natural h𝒩 ((omega_closed h𝒩).2 row hRow) (hBound i)
  simp only [expr_agrees h𝒩 hNatural]
  rfl

theorem step_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (rules : List ObjectHorn.Rule)
    {row : 𝒩.Carrier .set} (hRow : mem 𝒩 row (w 𝒩)) (trace : 𝒩.Carrier .set) :
    (ObjectHorn.step rules).body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) ↔
      (ObjectHorn.step rules).body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env (canonical h𝒩) [] [.set,.set]) := by
  rw [step_satisfies, step_satisfies]
  exact exists_congr (fun rule => and_congr Iff.rfl (rule_agrees h𝒩 rule hRow trace))

/-- 任意固定规则表的整个对象轨迹图保持，包括非标准轨迹。 -/
theorem condition_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (rules : List ObjectHorn.Rule)
    {bound free : SetContext} (env : Env 𝒩 bound free) (other : Env (canonical h𝒩) bound free)
    (root : SetTerm bound free) (hRoot : root.eval env = root.eval other) :
    (ObjectHorn.condition rules root).satisfies env ↔ (ObjectHorn.condition rules root).satisfies other := by
  apply PureSourceBounds.trace_agrees h𝒩 _ _ _ _ hRoot
  intro trace _ row _ hRow
  exact step_agrees h𝒩 rules hRow trace

def UnaryAgreement (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (condition : FormulaTemplate.Unary) : Prop :=
  ∀ row, mem 𝒩 row (w 𝒩) →
    (condition.body.satisfies (templateEnv (.cons row .nil) : Env 𝒩 [] [.set]) ↔
      condition.body.satisfies (templateEnv (.cons row .nil) : Env (canonical h𝒩) [] [.set]))

theorem horn_localTest {T : SetTheory} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (rules : List ObjectHorn.Rule) (rank : Nat → Nat) (descending : ObjectHorn.Descending rules rank) :
    UnaryAgreement h𝒩 (ObjectHorn.localTest C S hPower hInfinity rules rank descending).condition := by
  intro row _
  exact condition_agrees h𝒩 rules _ _ _ rfl

theorem local_rule_agrees {T : SetTheory} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rule : ObjectLocalDecision.Rule T)
    (hQueries : ∀ query ∈ rule.queries, UnaryAgreement h𝒩 query.1.condition) :
    UnaryAgreement h𝒩 rule.template := by
  intro row hRow
  rw [local_rule_satisfies, local_rule_satisfies]
  apply exists_congr
  intro values
  change ((∀ i, mem 𝒩 (values i) (suc 𝒩 row)) ∧ _) ↔
    ((∀ i, mem 𝒩 (values i) (suc (canonical h𝒩) row)) ∧ _)
  rw [← successor_agrees h𝒩 row]
  apply and_congr_right
  intro hBound
  have hNatural i := member_natural h𝒩 ((omega_closed h𝒩).2 row hRow) (hBound i)
  apply and_congr
  · rw [expr_agrees h𝒩 hNatural]
  · apply forall_congr'; intro query
    apply imp_congr_right; intro hQuery
    rw [← expr_agrees h𝒩 hNatural query.2]
    exact hQueries query hQuery _ (expr_natural h𝒩 hNatural query.2)

theorem localTest {T : SetTheory} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (C : CertificateCore T) (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (rules : List (ObjectLocalDecision.Rule T))
    (hQueries : ∀ rule ∈ rules, ∀ query ∈ rule.queries, UnaryAgreement h𝒩 query.1.condition) :
    UnaryAgreement h𝒩 (ObjectLocalDecision.localTest C hSuccessor rules).condition := by
  intro row hRow
  simp only [ObjectLocalDecision.localTest, ObjectLocalDecision.template, anyOf_satisfies]
  constructor
  · rintro ⟨formula, hFormula, h⟩
    obtain ⟨rule, hRule, rfl⟩ := List.mem_map.mp hFormula
    exact ⟨_, List.mem_map.mpr ⟨rule, hRule, rfl⟩, (local_rule_agrees h𝒩 rule (hQueries rule hRule) row hRow).mp h⟩
  · rintro ⟨formula, hFormula, h⟩
    obtain ⟨rule, hRule, rfl⟩ := List.mem_map.mp hFormula
    exact ⟨_, List.mem_map.mpr ⟨rule, hRule, rfl⟩, (local_rule_agrees h𝒩 rule (hQueries rule hRule) row hRow).mpr h⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceHorn
