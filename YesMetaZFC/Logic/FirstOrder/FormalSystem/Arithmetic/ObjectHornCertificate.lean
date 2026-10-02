import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornDerives
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Infinity

/-!
# 递归规则证书到普通 Hilbert 推导

接受证书给出有限闭合行集。拒绝证书必须递归拒绝每个匹配且守卫成立的规则中的
至少一个前提；归纳类型排除了循环借用拒绝结论。对象负向证明消去任意轨迹。
-/
namespace YesMetaZFC.Automation.ObjectHorn
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def ClosedRows (rules : List Rule) (rows : List Nat) : Prop :=
  ∀ root, root ∈ rows → ∃ rule, rule ∈ rules ∧ ∃ values : Fin rule.arity → Nat,
    (∀ i, values i ≤ root) ∧ root = rule.head.eval values ∧
    (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) ∧
    (∀ premise, premise ∈ rule.premises → premise.eval values ∈ rows)

def Acceptance (rules : List Rule) (root : Nat) : Prop :=
  ∃ rows, root ∈ rows ∧ ClosedRows rules rows

theorem ClosedRows.flatten {rules : List Rule} (rows : List (List Nat))
    (hRows : ∀ part, part ∈ rows → ClosedRows rules part) : ClosedRows rules rows.flatten := by
  intro root hRoot
  obtain ⟨part, hPart, hRoot⟩ := List.mem_flatten.mp hRoot
  obtain ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ := hRows part hPart root hRoot
  exact ⟨rule, hRule, values, hBound, hHead, hGuards,
    fun premise hPremise => List.mem_flatten.mpr ⟨part, hPart, hPremises premise hPremise⟩⟩

theorem Acceptance.of_rule {rules : List Rule} (rule : Rule) (hRule : rule ∈ rules)
    (values : Fin rule.arity → Nat)
    (hBound : ∀ i, values i ≤ rule.head.eval values)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) := by
  classical
  let parts := rule.premises.attach.map (fun premise => (hPremises premise.1 premise.2).choose)
  have hParts : ∀ part, part ∈ parts → ClosedRows rules part := by
    intro part hPart
    obtain ⟨premise, _, rfl⟩ := List.mem_map.mp hPart
    exact (hPremises premise.1 premise.2).choose_spec.2
  have hMember : ∀ premise, premise ∈ rule.premises → premise.eval values ∈ parts.flatten := by
    intro premise hPremise
    exact List.mem_flatten.mpr ⟨(hPremises premise hPremise).choose,
      List.mem_map.mpr ⟨⟨premise, hPremise⟩, List.mem_attach _ _, rfl⟩,
      (hPremises premise hPremise).choose_spec.1⟩
  refine ⟨rule.head.eval values :: parts.flatten, List.mem_cons_self, ?_⟩
  intro root hRoot
  rcases List.mem_cons.mp hRoot with rfl | hRoot
  · exact ⟨rule, hRule, values, hBound, rfl, hGuards,
      fun premise hPremise => List.mem_cons_of_mem _ (hMember premise hPremise)⟩
  · obtain ⟨other, hOther, env, hBound, hHead, hGuards, hPremises⟩ :=
      ClosedRows.flatten parts hParts root hRoot
    exact ⟨other, hOther, env, hBound, hHead, hGuards,
      fun premise hPremise => List.mem_cons_of_mem _ (hPremises premise hPremise)⟩

inductive Rejection (rules : List Rule) : Nat → Prop where
  | intro (root : Nat) (children : Nat → Prop)
      (reject : ∀ rule, rule ∈ rules → ∀ values : Fin rule.arity → Nat,
        (∀ i, values i ≤ root) → root = rule.head.eval values →
        (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
        ∃ premise, premise ∈ rule.premises ∧ children (premise.eval values))
      (childRejections : ∀ child, children child → Rejection rules child) :
      Rejection rules root

theorem Rejection.of_rule {rules : List Rule} (root : Nat)
    (reject : ∀ rule, rule ∈ rules → ∀ values : Fin rule.arity → Nat,
      (∀ i, values i ≤ root) → root = rule.head.eval values →
      (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
      ∃ premise, premise ∈ rule.premises ∧ Rejection rules (premise.eval values)) :
    Rejection rules root :=
  .intro root (Rejection rules) reject (fun _ h => h)

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (rules : List Rule) (root : Nat) (rows : List Nat)
    (hRoot : root ∈ rows) (hRows : ClosedRows rules rows) :
    Derives T [] (condition rules (numₘ(root) : Code)) := by
  apply ObjectTrace.positive S hPower (step rules) ωₘ (numₘ(root))
    (rows.map (fun n => numₘ(n))) (List.mem_map.mpr ⟨root, hRoot, rfl⟩)
  · intro row hRow
    obtain ⟨number, _, rfl⟩ := List.mem_map.mp hRow
    exact FirstOrder.Derives.theory_weaken hInfinity (infinity_finite_numeral_mem_omega number)
  · intro row hRow
    obtain ⟨number, hNumber, rfl⟩ := List.mem_map.mp hRow
    obtain ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ := hRows number hNumber
    rw [step_apply]
    apply anyOf_intro (List.mem_map.mpr ⟨rule, hRule, rfl⟩)
    apply rule.positive C S.contains_successor number _ values hBound hHead hGuards
    intro premise hPremise
    exact ObjectFiniteSet.member_intro S (List.mem_map.mpr
      ⟨premise.eval values, hPremises premise hPremise, rfl⟩)

/-- 拒绝证书在任意上下文、任意对象轨迹处排除根行。 -/
theorem Rejection.not_member {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    {rules : List Rule} {root : Nat} (rejection : Rejection rules root)
    {free : SetContext} {Γ : Context signature free} (trace : SetOpenTerm free)
    (hClosed : Derives T Γ (ObjectTrace.closed (step rules) trace)) :
    Derives T Γ (¬ₘ ((numₘ(root)) ∈ₘ trace)) := by
  induction rejection with
  | intro root children reject _ ih =>
    have hStepNeg : Derives T Γ (¬ₘ (step rules (numₘ(root)) trace)) := by
      rw [step_apply]
      apply anyOf_negative
      intro φ hφ
      obtain ⟨rule, hRule, rfl⟩ := List.mem_map.mp hφ
      apply rule.negative C A root trace
      intro values hBound hHead hGuards
      obtain ⟨premise, hPremise, hChild⟩ := reject rule hRule values hBound hHead hGuards
      exact ⟨premise, hPremise, ih _ hChild⟩
    apply FirstOrder.Derives.neg_intro
    exact FirstOrder.Derives.neg_elim
      (ObjectTrace.closed_elim (step rules) trace (numₘ(root))
        (FirstOrder.Derives.context_weaken_cons hClosed)
        (FirstOrder.Derives.assumption List.mem_cons_self))
      (FirstOrder.Derives.context_weaken_cons hStepNeg)

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    {rules : List Rule} {root : Nat} (rejection : Rejection rules root) :
    Derives T [] (¬ₘ condition rules (numₘ(root) : Code)) :=
  ObjectTrace.negative (step rules) ωₘ root
    (fun _ trace hClosed => rejection.not_member C A trace hClosed)

/-- 有良基下降的失败分支可直接组装拒绝证书；rank 仅用于元层终止证明。 -/
theorem Rejection.of_rank (rules : List Rule) (bad : Nat → Prop) (rank : Nat → Nat)
    (hStep : ∀ root, bad root → ∀ rule, rule ∈ rules → ∀ values : Fin rule.arity → Nat,
      (∀ i, values i ≤ root) → root = rule.head.eval values →
      (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
      ∃ premise, premise ∈ rule.premises ∧ bad (premise.eval values) ∧
        rank (premise.eval values) < rank root)
    (root : Nat) (hBad : bad root) : Rejection rules root := by
  apply Rejection.intro root (fun child => bad child ∧ rank child < rank root)
  · exact hStep root hBad
  · intro child hChild
    exact Rejection.of_rank rules bad rank hStep child hChild.1
termination_by rank root

end YesMetaZFC.Automation.ObjectHorn
