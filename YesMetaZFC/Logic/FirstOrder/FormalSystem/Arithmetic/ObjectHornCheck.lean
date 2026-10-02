import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues

/-! # 有良基秩的有限规则图的可计算检查

检查器枚举当前行所界定的有限赋值，并沿严格下降的秩递归。
有限闭合轨迹的语义不自动排除循环；下降条件在这里显式消除这种漏洞。
正负对象推导均由实际布尔检查结果生成，不假设对象模型的自然数是标准的。
-/
namespace YesMetaZFC.Automation.ObjectHorn
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 完整枚举给定有限界内的变量赋值。 -/
def environments (bound : Nat) : (arity : Nat) → List (Fin arity → Nat)
  | 0 => [Fin.elim0]
  | n + 1 => (List.range (bound + 1)).flatMap fun head =>
      (environments bound n).map fun tail => Fin.cases head tail

theorem mem_environments (bound arity : Nat) (values : Fin arity → Nat) :
    values ∈ environments bound arity ↔ ∀ i, values i ≤ bound := by
  induction arity with
  | zero =>
    have h : values = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp only [environments, List.mem_singleton, h]
    exact ⟨fun _ i => Fin.elim0 i, fun _ => True.intro⟩
  | succ n ih =>
    simp only [environments, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨head, hHead, tail, hTail, rfl⟩ i
      cases i using Fin.cases with
      | zero => exact Nat.le_of_lt_succ (List.mem_range.mp hHead)
      | succ i => exact (ih tail).mp hTail i
    · intro h
      refine ⟨values 0, List.mem_range.mpr (Nat.lt_succ_of_le (h 0)),
        (fun i => values i.succ), (ih _).mpr (fun i => h i.succ), ?_⟩
      funext i
      cases i using Fin.cases <;> rfl

/-- 只对实际匹配且满足守卫的规则要求严格下降。 -/
def Descending (rules : List Rule) (rank : Nat → Nat) : Prop :=
  ∀ rule, rule ∈ rules → ∀ values : Fin rule.arity → Nat,
    (∀ i, values i ≤ rule.head.eval values) →
    (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
    ∀ premise, premise ∈ rule.premises →
      rank (premise.eval values) < rank (rule.head.eval values)

/-- 有限搜索只是参考检查器；其语义不依赖任何对象公式或可证性判断。 -/
def check (rules : List Rule) (rank : Nat → Nat) (root : Nat) : Bool :=
  rules.any fun rule => (environments root rule.arity).any fun values =>
    (root == rule.head.eval values) &&
    rule.guards.all (fun guard => decide (guard.1.eval values < guard.2.eval values)) &&
    rule.premises.all (fun premise =>
      if _h : rank (premise.eval values) < rank root then
        check rules rank (premise.eval values)
      else false)
termination_by rank root

theorem check_eq_true_iff (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (root : Nat) :
    check rules rank root = true ↔
      ∃ rule, rule ∈ rules ∧ ∃ values : Fin rule.arity → Nat,
        (∀ i, values i ≤ root) ∧ root = rule.head.eval values ∧
        (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) ∧
        (∀ premise, premise ∈ rule.premises → check rules rank (premise.eval values) = true) := by
  rw [check]
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq, mem_environments]
  constructor
  · rintro ⟨rule, hRule, values, hBound, ⟨hHead, hGuards⟩, hPremises⟩
    refine ⟨rule, hRule, values, hBound, hHead, hGuards, ?_⟩
    intro premise hPremise
    have h := hPremises premise hPremise
    split at h
    · exact h
    · cases h
  · rintro ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩
    refine ⟨rule, hRule, values, hBound, ⟨hHead, hGuards⟩, ?_⟩
    intro premise hPremise
    have hRank : rank (premise.eval values) < rank root := by
      rw [hHead]
      exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise
    simp only [dif_pos hRank]
    exact hPremises premise hPremise

theorem check_acceptance (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (root : Nat)
    (h : check rules rank root = true) : Acceptance rules root := by
  obtain ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ :=
    (check_eq_true_iff rules rank descending root).mp h
  rw [hHead]
  apply Acceptance.of_rule rule hRule values (by rwa [← hHead]) hGuards
  intro premise hPremise
  exact check_acceptance rules rank descending (premise.eval values) (hPremises premise hPremise)
termination_by rank root
decreasing_by
  rw [hHead]
  exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise

theorem acceptance_check (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (root : Nat)
    (h : Acceptance rules root) : check rules rank root = true := by
  obtain ⟨rows, hRoot, hRows⟩ := h
  obtain ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ := hRows root hRoot
  apply (check_eq_true_iff rules rank descending root).mpr
  refine ⟨rule, hRule, values, hBound, hHead, hGuards, ?_⟩
  intro premise hPremise
  exact acceptance_check rules rank descending (premise.eval values)
    ⟨rows, hPremises premise hPremise, hRows⟩
termination_by rank root
decreasing_by
  rw [hHead]
  exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise

theorem check_rejection (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (root : Nat)
    (h : check rules rank root = false) : Rejection rules root := by
  classical
  apply Rejection.of_rank rules (fun n => check rules rank n = false) rank ?_ root h
  intro root hFalse rule hRule values hBound hHead hGuards
  have hFailure : ¬ ∀ premise, premise ∈ rule.premises → check rules rank (premise.eval values) = true := by
    intro hPremises
    have hTrue := (check_eq_true_iff rules rank descending root).mpr
      ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩
    rw [hFalse] at hTrue
    cases hTrue
  have hExists : ∃ premise, premise ∈ rule.premises ∧ check rules rank (premise.eval values) ≠ true := by
    apply Classical.byContradiction
    intro hNo
    apply hFailure
    intro premise hPremise
    apply Classical.byContradiction
    exact fun hBad => hNo ⟨premise, hPremise, hBad⟩
  obtain ⟨premise, hPremise, hFailure⟩ := hExists
  refine ⟨premise, hPremise, Bool.eq_false_iff.mpr hFailure, ?_⟩
  rw [hHead]
  exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise

/-- 可靠性可按单步规则证明，再沿有限秩传播到整个已接受证明树。 -/
theorem check_sound (rules : List Rule) (rank : Nat → Nat)
    (descending : Descending rules rank) (meaning : Nat → Prop)
    (sound : ∀ rule, rule ∈ rules → ∀ values : Fin rule.arity → Nat,
      (∀ i, values i ≤ rule.head.eval values) →
      (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
      (∀ premise, premise ∈ rule.premises → meaning (premise.eval values)) →
      meaning (rule.head.eval values))
    (root : Nat) (h : check rules rank root = true) : meaning root := by
  obtain ⟨rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ :=
    (check_eq_true_iff rules rank descending root).mp h
  rw [hHead]
  apply sound rule hRule values (by rwa [← hHead]) hGuards
  intro premise hPremise
  exact check_sound rules rank descending meaning sound (premise.eval values) (hPremises premise hPremise)
termination_by rank root
decreasing_by
  rw [hHead]
  exact descending rule hRule values (by rwa [← hHead]) hGuards premise hPremise

theorem check_positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (rules : List Rule) (rank : Nat → Nat) (descending : Descending rules rank)
    (root : Nat) (h : check rules rank root = true) :
    Derives T [] (condition rules (numₘ(root) : Code)) := by
  obtain ⟨rows, hRoot, hRows⟩ := check_acceptance rules rank descending root h
  exact positive C S hPower hInfinity rules root rows hRoot hRows

theorem check_negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (rules : List Rule) (rank : Nat → Nat) (descending : Descending rules rank)
    (root : Nat) (h : check rules rank root = false) :
    Derives T [] (¬ₘ condition rules (numₘ(root) : Code)) :=
  negative C A (check_rejection rules rank descending root h)

end YesMetaZFC.Automation.ObjectHorn
