import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FiniteOrdinal
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Foundation
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Successor
import YesMetaZFC.Logic.FirstOrder.Metatheory.Basic

/-!
# `ProofT` 的标准 numeral 算术

固定公理表的证书标签拒绝只需要区分两个外部自然数对应的对象 numeral。该接口
独立于自然数切分、quotation 和序列编码，避免有限表 verifier 依赖完整 `Core`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 闭句推导的显式上下文别名，避免空列表导致 free 上下文无法推断。 -/
private abbrev closed_derives (T : SetTheory) (formula : SetSentence) :=
  Derives T ([] : Context signature []) formula

/--
标准 numeral 的严格次序可由后继定义直接实现为成员关系。

归纳只发生在外部 `Nat` 上，因此不需要对象理论中的自然数集合或归纳模式。
-/
theorem numeral_mem_of_lt
    {T : SetTheory}
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    {free : SetContext}
    {m n : Nat}
    (h : m < n) :
    Derives T ([] : Context signature free) (
      numₘ(m) ∈ₘ numₘ(n)) := by
  induction n with
  | zero =>
      exact False.elim (Nat.not_lt_zero m h)
  | succ n ih =>
      by_cases hmn : m = n
      · subst m
        simpa [finite_numeral_term] using
          FirstOrder.Derives.theory_weaken
            hSuccessor
            (mem_successor_self
              (Γ := ([] : Context signature free))
              (numₘ(n)))
      · have hlt : m < n := by
          omega
        have hPrevious :
            Derives T ([] : Context signature free) (
              numₘ(m) ∈ₘ numₘ(n)) :=
          ih hlt
        have hLift :
        Derives T ([] : Context signature free) (
          (numₘ(m) ∈ₘ numₘ(n)) ⟶ₘ
            (numₘ(m) ∈ₘ Sₘ(numₘ(n)))) :=
          FirstOrder.Derives.theory_weaken
            hSuccessor
            (mem_successor_of_mem
              (Γ := ([] : Context signature free))
              (numₘ(n)) (numₘ(m)))
        simpa [finite_numeral_term] using
          FirstOrder.Derives.imp_elim
            hLift hPrevious

/--
严格较小的标准 numeral 不等于较大的标准 numeral。

证明只把严格次序解释为成员关系，再用成员反自反排除等式；不需要 `ω`、
对象自然数归纳或任何无限集合。
-/
theorem numeral_ne_of_lt
    {T : SetTheory}
    (hIrreflexive :
      ∀ {formula},
        membership_irreflexive_theory formula → T formula)
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    {m n : Nat}
    (h : m < n) :
    closed_derives T (
      ¬ₘ (numₘ(m) ≐ₘ numₘ(n))) := by
  let equality : SetSentence :=
    numₘ(m) ≐ₘ numₘ(n)
  apply FirstOrder.Derives.neg_intro
  have hEquality :
      [equality] ⊢ₘ[T] equality :=
    FirstOrder.Derives.assumption (by simp)
  have hMembership :
      [equality] ⊢ₘ[T]
        numₘ(m) ∈ₘ numₘ(n) :=
    FirstOrder.Derives.context_weaken_cons
      (numeral_mem_of_lt hSuccessor h)
  have hSelfMembership :
      [equality] ⊢ₘ[T]
        numₘ(m) ∈ₘ numₘ(m) :=
    FirstOrder.Derives.iff_elim_right
      (membership_right_iff_of_equality
        (numₘ(m)) (numₘ(m)) (numₘ(n))
        hEquality)
      hMembership
  exact FirstOrder.Derives.neg_elim
    hSelfMembership
    (FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken
        hIrreflexive
        (membership_irreflexive_instance_derives
          (numₘ(m))))

/-- 不同外部自然数对应的标准 numeral 互异，且整个证明与无穷公理无关。 -/
theorem numeral_ne
    {T : SetTheory}
    (hIrreflexive :
      ∀ {formula},
        membership_irreflexive_theory formula → T formula)
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    {m n : Nat}
    (h : m ≠ n) :
    closed_derives T (
      ¬ₘ (numₘ(m) ≐ₘ numₘ(n))) := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · exact numeral_ne_of_lt
      hIrreflexive hSuccessor hlt
  · have hReverse :=
      numeral_ne_of_lt
        hIrreflexive hSuccessor hgt
    let equality : SetSentence :=
      numₘ(m) ≐ₘ numₘ(n)
    apply FirstOrder.Derives.neg_intro
    have hEquality :
        [equality] ⊢ₘ[T] equality :=
      FirstOrder.Derives.assumption (by simp)
    have hReverseEquality :
        [equality] ⊢ₘ[T]
          numₘ(n) ≐ₘ numₘ(m) :=
      Metatheory.Derives.equality_symm hEquality
    exact FirstOrder.Derives.neg_elim
      hReverseEquality
      (FirstOrder.Derives.context_weaken_cons hReverse)

/-! 标准 numeral 的成员关系也需要反向的有限判定。 -/

theorem numeral_not_mem_of_not_lt
    {T : SetTheory}
    (hEmpty :
      ∀ {formula},
        empty_set_symbol_theory formula → T formula)
    (hIrreflexive :
      ∀ {formula},
        membership_irreflexive_theory formula → T formula)
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    {left right : Nat}
    (h : ¬ left < right) :
    Derives T ([] : Context signature [])
      (¬ₘ (numₘ(left) ∈ₘ numₘ(right))) := by
  induction right with
  | zero =>
      simpa [finite_numeral_term] using
        FirstOrder.Derives.theory_weaken
          hEmpty
          (empty_set_term_has_no_members
            (Γ := ([] : Context signature []))
            (numₘ(left) : SetOpenTerm []))
  | succ right ih =>
      have hNe : left ≠ right := by
        intro hEq
        subst left
        exact h (Nat.lt_succ_self right)
      have hPrevious : ¬ left < right := by
        intro hLt
        exact h (Nat.lt_trans hLt (Nat.lt_succ_self right))
      have hPreviousNeg := ih hPrevious
      let member : SetSentence := numₘ(left) ∈ₘ numₘ(right + 1)
      apply FirstOrder.Derives.neg_intro
      have hMember : [member] ⊢ₘ[T]
          numₘ(left) ∈ₘ numₘ(right + 1) :=
        FirstOrder.Derives.assumption (by simp [member])
      have hCases : [member] ⊢ₘ[T]
          (numₘ(left) ≐ₘ numₘ(right)) ∨ₘ
            (numₘ(left) ∈ₘ numₘ(right)) := by
        have hIff : [member] ⊢ₘ[T]
            (numₘ(left) ∈ₘ Sₘ(numₘ(right))) ↔ₘ
              ((numₘ(left) ≐ₘ numₘ(right)) ∨ₘ
                (numₘ(left) ∈ₘ numₘ(right))) :=
          FirstOrder.Derives.theory_weaken
            hSuccessor
            (successor_term_membership_iff
              (Γ := [member])
              (numₘ(right)) (numₘ(left)))
        exact FirstOrder.Derives.iff_elim_left hIff (by
          simpa [member, finite_numeral_term] using hMember)
      apply FirstOrder.Derives.disj_elim hCases
      · exact FirstOrder.Derives.neg_elim
          (FirstOrder.Derives.assumption (by simp [member]))
          (FirstOrder.Derives.context_weaken_cons
            (FirstOrder.Derives.context_weaken_cons
              (numeral_ne hIrreflexive hSuccessor hNe)))
      · exact FirstOrder.Derives.neg_elim
          (FirstOrder.Derives.assumption (by simp [member]))
          (FirstOrder.Derives.context_weaken_cons
            (FirstOrder.Derives.context_weaken_cons hPreviousNeg))

/-- 对象理论能够判定不同标准 numeral 互异。 -/
structure NumeralArithmetic (T : SetTheory) where
  numeral_ne :
    ∀ {left right : Nat},
      left ≠ right →
    closed_derives T (
      ¬ₘ (numₘ(left) ≐ₘ numₘ(right)))

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
