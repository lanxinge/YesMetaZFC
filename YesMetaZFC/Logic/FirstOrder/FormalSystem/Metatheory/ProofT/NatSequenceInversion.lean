import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceExtensionality
import YesMetaZFC.Logic.FirstOrder.Derivation.QuantifierBlock
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceConditionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSpaceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingInversionDirect
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion

/-!
# 内在自然数序列反演

本模块迁移自然数序列反演的有限归纳核心。对象项、轨迹项和递归步均使用内在
上下文；有限 numeral 的成员消去由 `CertificateCore` 提供，不再携带旧式
`Admissible`、自由支撑或变量编号参数。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open IntrinsicPairing

set_option autoImplicit false

/-! ## 外部列表辅助 -/

theorem list_snoc_induction
    {α : Type}
    (motive : List α → Prop)
    (hNil : motive [])
    (hSnoc : ∀ list item, motive list → motive (list ++ [item])) :
    ∀ list, motive list := by
  intro list
  have hReverse : ∀ (reverseList : List α), motive reverseList.reverse := by
    intro reverseList
    induction reverseList with
    | nil =>
        simpa using hNil
    | cons item reverseList ih =>
        simpa [List.reverse_cons] using
          hSnoc reverseList.reverse item ih
  simpa using hReverse list.reverse

/-! ## 地面递归步 -/

/-- 规范自然数递归步在对象层直接计算为一个 numeral。 -/
theorem nat_sequence_code_step_numeral_eq
    {T : SetTheory}
    (C : CertificateCore T)
    (accumulator item : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(item))) ≐ₘ
        numₘ(nat_sequence_code_step accumulator item) := by
  have hPair := C.pair_value accumulator item
  have hStep := successor_term_congr_of_equality
    (godel_pairₘ(numₘ(accumulator), numₘ(item)))
    (numₘ(godel_pair_value accumulator item)) hPair
  simpa [nat_sequence_code_step, finite_numeral_term, successor_term] using hStep

private theorem lift_closed
    {T : SetTheory} {free : SetContext}
    {formula : SetSentence}
    (hFormula :
      ([] : Context signature []) ⊢ₘ[T] formula) :
    ([] : Context signature free) ⊢ₘ[T]
      Formula.renameFree
        (VariableRenaming.empty : VariableRenaming [] free)
        formula := by
  simpa using
    FirstOrder.Derives.free_renaming
      (T := T)
      (ρ := (VariableRenaming.empty : VariableRenaming [] free))
      hFormula

theorem nat_sequence_code_step_numeral_at
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (accumulator item : Nat) :
    Γ ⊢ₘ[T]
      Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(item))) ≐ₘ
        numₘ(nat_sequence_code_step accumulator item) := by
  have hGround := nat_sequence_code_step_numeral_eq C accumulator item
  have hFree := lift_closed (free := free) hGround
  have hContext := FirstOrder.Derives.context_weaken
    (Γ := ([] : Context signature free))
    (Δ := Γ) (by simp) hFree
  simpa [Formula.renameFree, Formula.rename, Renaming.free,
    Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
    finite_numeral_term_renameMapped] using hContext

/-- 任意已求值的对象项共用同一个配数递推计算。 -/
theorem nat_sequence_code_step_of_values
    {T : SetTheory} (C : CertificateCore T)
    {free : SetContext} {Γ : Context signature free}
    {left right : SetOpenTerm free} {accumulator item : Nat}
    (hLeft : Γ ⊢ₘ[T] left ≐ₘ numₘ(accumulator))
    (hRight : Γ ⊢ₘ[T] right ≐ₘ numₘ(item)) :
    Γ ⊢ₘ[T] Sₘ(godel_pairₘ(left, right)) ≐ₘ
      numₘ(nat_sequence_code_step accumulator item) :=
  Metatheory.Derives.equality_trans
    (successor_term_congr_of_equality _ _
      (IntrinsicPairing.pair_congr_of_equalities _ _ _ _ hLeft hRight))
    (nat_sequence_code_step_numeral_at C accumulator item)

theorem numeral_ne_context
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    {left right : Nat}
    (hNe : left ≠ right) :
    Γ ⊢ₘ[T] ¬ₘ(numₘ(left) ≐ₘ numₘ(right)) := by
  have hClosed := C.numeral_ne hNe
  have hFree := FirstOrder.Derives.free_renaming
    (T := T)
    (ρ := (VariableRenaming.empty : VariableRenaming [] free))
    hClosed
  have hContext := FirstOrder.Derives.context_weaken
    (Γ := ([] : Context signature free))
    (Δ := Γ) (by simp) hFree
  simpa [Formula.renameFree, Formula.rename, Renaming.free,
    Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
    finite_numeral_term_renameMapped] using hContext

theorem falsum_of_numeral_equality
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    {left right : Nat}
    (hNe : left ≠ right)
    (hEquality : Γ ⊢ₘ[T] numₘ(left) ≐ₘ numₘ(right)) :
    Γ ⊢ₘ[T] Formula.falsum :=
  FirstOrder.Derives.neg_elim hEquality
    (numeral_ne_context C hNe)

/-! ## 有限前缀反演 -/

/-- 有限码域中的一步编码只需枚举一次；不匹配的 numeral 分支统一排除。 -/
theorem nat_sequence_step_value_elim
    {T : SetTheory} (C : CertificateCore T)
    {free : SetContext} {Γ : Context signature free}
    (previous value : SetOpenTerm free) (candidate bound : Nat)
    (conclusion : SetOpenFormula free)
    (hPrevious : Γ ⊢ₘ[T] previous ∈ₘ numₘ(bound + 1))
    (hValue : Γ ⊢ₘ[T] value ∈ₘ numₘ(bound))
    (hStep : Γ ⊢ₘ[T] numₘ(candidate) ≐ₘ Sₘ(godel_pairₘ(previous, value)))
    (hBranch : ∀ accumulator, accumulator < bound + 1 →
      ∀ item, item < bound → candidate = nat_sequence_code_step accumulator item →
        (value ≐ₘ numₘ(item)) :: (previous ≐ₘ numₘ(accumulator)) :: Γ ⊢ₘ[T]
          conclusion) :
    Γ ⊢ₘ[T] conclusion := by
  apply C.member_elim (bound + 1) previous conclusion hPrevious
  intro accumulator hAccumulator
  apply C.member_elim bound value conclusion
    (FirstOrder.Derives.context_weaken_cons hValue)
  intro item hItem
  have hPreviousEq : (value ≐ₘ numₘ(item)) :: (previous ≐ₘ numₘ(accumulator)) :: Γ
      ⊢ₘ[T] previous ≐ₘ numₘ(accumulator) :=
    FirstOrder.Derives.assumption (by simp)
  have hValueEq : (value ≐ₘ numₘ(item)) :: (previous ≐ₘ numₘ(accumulator)) :: Γ
      ⊢ₘ[T] value ≐ₘ numₘ(item) := FirstOrder.Derives.assumption List.mem_cons_self
  have hCode := FirstOrder.Derives.eq_trans
    (FirstOrder.Derives.context_weaken_cons
      (FirstOrder.Derives.context_weaken_cons hStep))
    (nat_sequence_code_step_of_values C hPreviousEq hValueEq)
  by_cases hMatch : candidate = nat_sequence_code_step accumulator item
  · exact hBranch accumulator hAccumulator item hItem hMatch
  · exact FirstOrder.Derives.falsum_elim (falsum_of_numeral_equality C hMatch hCode)

/-- 递归轨迹和末码共同决定自然数序列的有限前缀。 -/
theorem nat_sequence_code_prefix_unique
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace : SetOpenTerm free)
    (tokens : List Nat)
    (length bound : Nat)
    (hZero :
      Γ ⊢ₘ[T] (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep :
      ∀ index, index < length →
        Γ ⊢ₘ[T]
          nat_sequence_code_step_condition
            sequence trace (numₘ(index)))
    (hValueBound :
      ∀ index, index < length →
        Γ ⊢ₘ[T] (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound))
    (hTraceBound :
      ∀ index, index ≤ length →
        Γ ⊢ₘ[T] (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hFinal :
      Γ ⊢ₘ[T]
        numₘ(nat_sequence_code_value tokens) ≐ₘ
          (trace ·ₘ numₘ(length))) :
    (Γ ⊢ₘ[T] numₘ(length) ≐ₘ numₘ(tokens.length)) ∧
      (∀ index (hIndex : index < tokens.length),
        Γ ⊢ₘ[T]
          (sequence ·ₘ numₘ(index)) ≐ₘ
            numₘ(tokens[index]'hIndex)) := by
  induction tokens using list_snoc_induction generalizing Γ length with
  | hNil =>
      by_cases hLength : length = 0
      · subst length
        exact ⟨FirstOrder.Derives.eq_refl _, fun index hIndex => by simp at hIndex⟩
      · obtain ⟨prefixLength, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hLength
        have hFalse : Γ ⊢ₘ[T] Formula.falsum := by
          apply nat_sequence_step_value_elim C
            (trace ·ₘ numₘ(prefixLength)) (sequence ·ₘ numₘ(prefixLength)) 0 bound
            Formula.falsum (hTraceBound prefixLength (Nat.le_succ _))
            (hValueBound prefixLength (Nat.lt_succ_self _))
            (FirstOrder.Derives.eq_trans hFinal (hStep prefixLength (Nat.lt_succ_self _)))
          intro accumulator _ item _ hMatch
          simp [nat_sequence_code_step] at hMatch
        exact ⟨FirstOrder.Derives.falsum_elim hFalse,
          fun _ _ => FirstOrder.Derives.falsum_elim hFalse⟩
  | hSnoc xs item ih =>
      by_cases hLength : length = 0
      · subst length
        have hFalse := falsum_of_numeral_equality C
          (Nat.ne_of_gt (nat_sequence_code_value_pos_of_ne_nil (by simp)))
          (FirstOrder.Derives.eq_trans hFinal hZero)
        exact ⟨FirstOrder.Derives.falsum_elim hFalse,
          fun _ _ => FirstOrder.Derives.falsum_elim hFalse⟩
      · obtain ⟨prefixLength, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hLength
        have hLast : Γ ⊢ₘ[T]
            (numₘ(nat_sequence_code_value xs) ≐ₘ (trace ·ₘ numₘ(prefixLength))) ∧ₘ
              ((sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(item)) := by
          apply nat_sequence_step_value_elim C
            (trace ·ₘ numₘ(prefixLength)) (sequence ·ₘ numₘ(prefixLength))
            (nat_sequence_code_value (xs ++ [item])) bound _
            (hTraceBound prefixLength (Nat.le_succ _))
            (hValueBound prefixLength (Nat.lt_succ_self _))
            (FirstOrder.Derives.eq_trans hFinal (hStep prefixLength (Nat.lt_succ_self _)))
          intro accumulator _ itemAt _ hMatch
          have hPairMatch : godel_pair_value (nat_sequence_code_value xs) item =
              godel_pair_value accumulator itemAt := by
            apply Nat.succ.inj
            simpa [nat_sequence_code_value_append_singleton, nat_sequence_code_step] using hMatch
          rcases godel_pair_value_eq_iff.mp hPairMatch with ⟨rfl, rfl⟩
          exact FirstOrder.Derives.conj_intro
            (FirstOrder.Derives.eq_symm (FirstOrder.Derives.assumption (by simp)))
            (FirstOrder.Derives.assumption List.mem_cons_self)
        have hPrefix := ih (Γ := Γ) prefixLength hZero
          (fun index hIndex => hStep index (by omega))
          (fun index hIndex => hValueBound index (by omega))
          (fun index hIndex => hTraceBound index (by omega))
          (FirstOrder.Derives.conj_elim_left hLast)
        constructor
        · simpa [List.length_append, finite_numeral_term, successor_term] using
            successor_term_congr_of_equality _ _ hPrefix.1
        · intro index hIndex
          by_cases hPrefixIndex : index < xs.length
          · simpa [List.getElem_append, hPrefixIndex] using hPrefix.2 index hPrefixIndex
          · have hIndexEq : index = xs.length := by
              simp only [List.length_append, List.length_singleton] at hIndex
              omega
            subst index
            have hApplication := function_application_term_congr_argument_of_equality
              sequence _ _ hPrefix.1
            simpa [List.getElem_append] using FirstOrder.Derives.eq_trans
              (FirstOrder.Derives.eq_symm hApplication)
              (FirstOrder.Derives.conj_elim_right hLast)

/-! ## 完整自然数序列回放 -/

/-- 将递归轨迹数据直接回放为规范自然数有限图。 -/
theorem nat_sequence_code_replay_of_data
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace : SetOpenTerm free)
    (tokens : List Nat)
    (length bound : Nat)
    (hFunction : Γ ⊢ₘ[T] is_function_formula sequence)
    (hDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(length))
    (hZero : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep : ∀ index, index < length →
      Γ ⊢ₘ[T]
        nat_sequence_code_step_condition
          sequence trace (numₘ(index)))
    (hValueBound : ∀ index, index < length →
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound))
    (hTraceBound : ∀ index, index ≤ length →
      Γ ⊢ₘ[T]
        (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hFinal : Γ ⊢ₘ[T]
      numₘ(nat_sequence_code_value tokens) ≐ₘ
        (trace ·ₘ numₘ(length))) :
    Γ ⊢ₘ[T] sequence ≐ₘ nat_sequence_graph_term tokens := by
  have hUnique := nat_sequence_code_prefix_unique C sequence trace tokens
    length bound hZero hStep hValueBound hTraceBound hFinal
  apply function_equality_of_finite_values C.toFiniteCore S sequence
    (tokens.map (fun token => numₘ(token))) hFunction
  · simpa only [List.length_map] using FirstOrder.Derives.eq_trans hDomain hUnique.1
  · intro index hIndex
    simpa only [List.getElem_map] using hUnique.2 index
      (by simpa only [List.length_map] using hIndex)

/-! ## 自然数序列条件的直接唯一性 -/

/-- 内在自然数序列条件与规范 numeral 码直接决定规范有限图。 -/
theorem nat_sequence_code_condition_unique_of_code_equality
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (tokens : List Nat)
    (hCondition : Γ ⊢ₘ[T]
      nat_sequence_code_condition sequence code)
    (hCodeEquality : Γ ⊢ₘ[T]
      code ≐ₘ numₘ(nat_sequence_code_value tokens)) :
    Γ ⊢ₘ[T] sequence ≐ₘ nat_sequence_graph_term tokens := by
  let bound : Nat := nat_sequence_code_value tokens
  have hParts := nat_sequence_code_condition_parts sequence code hCondition
  have hOmegaNonempty : Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.theory_weaken S.toArithmeticSupport.contains_empty_set
        (member_implies_set_nonempty code ωₘ)) hParts.code_omega
  have hMemberCondition :=
    sequence_space_member_implies_member_condition
      S ωₘ sequence hOmegaNonempty hParts.sequence_space
  have hFiniteCondition :=
    finite_sequence_member_condition_implies_finite_sequence
      S ωₘ sequence hMemberCondition
  have hFunction : Γ ⊢ₘ[T] is_function_formula sequence := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conj_elim_left hFiniteCondition
  have hCodeEqualityBound : Γ ⊢ₘ[T] code ≐ₘ numₘ(bound) := by
    simpa [bound] using hCodeEquality
  have hSuccessorCodeEquality : Γ ⊢ₘ[T]
      Sₘ(code) ≐ₘ Sₘ(numₘ(bound)) :=
    successor_term_congr_of_equality code (numₘ(bound))
      hCodeEqualityBound
  have hDomainSuccessor : Γ ⊢ₘ[T]
      domₘ(sequence) ∈ₘ Sₘ(numₘ(bound)) :=
    FirstOrder.Derives.iff_elim_left
      (membership_right_iff_of_equality
        (domₘ(sequence)) (Sₘ(code)) (Sₘ(numₘ(bound)))
        hSuccessorCodeEquality)
      hParts.domain_code_bound
  have hDomainMember : Γ ⊢ₘ[T]
      domₘ(sequence) ∈ₘ numₘ(bound + 1) := by
    simpa [finite_numeral_term, successor_term] using hDomainSuccessor
  apply C.member_elim (bound + 1) (domₘ(sequence))
    (sequence ≐ₘ nat_sequence_graph_term tokens) hDomainMember
  intro length hLength
  let domainEquation : SetOpenFormula free :=
    domₘ(sequence) ≐ₘ numₘ(length)
  let Δ : Context signature free := domainEquation :: Γ
  change Δ ⊢ₘ[T] sequence ≐ₘ nat_sequence_graph_term tokens
  have hDomain : Δ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(length) := by
    simpa [Δ, domainEquation] using
      (FirstOrder.Derives.assumption
        (T := T) (Γ := Δ) (formula := domainEquation) (by simp [Δ]))
  have hTraceExists : Δ ⊢ₘ[T]
      (nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here)).existsE SetSort.set :=
    FirstOrder.Derives.context_weaken_cons hParts.trace_exists
  exact nat_sequence_code_trace_elim sequence code hTraceExists
    (conclusion := sequence ≐ₘ nat_sequence_graph_term tokens) (by
      intro P
      let Ξ : Context signature (SetSort.set :: free) :=
        nat_sequence_trace_context Δ sequence code
      change Ξ ⊢ₘ[T]
        (sequence ≐ₘ nat_sequence_graph_term tokens).weakenFree SetSort.set
      have lift_to_trace {formula : SetOpenFormula free} (h : Δ ⊢ₘ[T] formula) :
          Ξ ⊢ₘ[T] formula.weakenFree SetSort.set := by
        simpa [Ξ, nat_sequence_trace_context] using
          FirstOrder.Derives.context_weaken_cons (fresh_context_weaken h)
      have hFunctionXi : Ξ ⊢ₘ[T] is_function_formula (sequence.weakenFree SetSort.set) :=
        lift_to_trace (FirstOrder.Derives.context_weaken_cons hFunction)
      have hDomainXi : Ξ ⊢ₘ[T] domₘ(sequence.weakenFree SetSort.set) ≐ₘ numₘ(length) := by
        simpa using lift_to_trace hDomain
      have hCodeEqualityXi : Ξ ⊢ₘ[T] code.weakenFree SetSort.set ≐ₘ numₘ(bound) := by
        simpa using lift_to_trace (FirstOrder.Derives.context_weaken_cons hCodeEqualityBound)
      have hValueBoundXi : Ξ ⊢ₘ[T] nat_sequence_value_code_bound
          (sequence.weakenFree SetSort.set) (code.weakenFree SetSort.set) := by
        simpa [nat_sequence_value_code_bound, Formula.LevyBound.boundedForall,
          Formula.LevyBound.membership, Formula.weakenFree, Formula.rename,
          Renaming.weakenFree, Renaming.free, Formula.renameMapped,
          Term.renameMapped, Arguments.renameMapped, Term.weakenFree_weakenBound] using!
          lift_to_trace (FirstOrder.Derives.context_weaken_cons hParts.value_code_bound)
      have hStepReplay : ∀ index, index < length →
          Ξ ⊢ₘ[T] nat_sequence_code_step_condition
            (sequence.weakenFree SetSort.set)
            nat_sequence_trace_term (numₘ(index)) := by
        intro index hIndex
        have hIndexDomain := row_index_mem_of_domain S.toArithmeticSupport
          (sequence.weakenFree SetSort.set) length index hDomainXi hIndex
        exact nat_sequence_code_step_condition_at
          (sequence.weakenFree SetSort.set)
          nat_sequence_trace_term (numₘ(index)) P.step hIndexDomain
      have hValueReplay : ∀ index, index < length →
          Ξ ⊢ₘ[T]
            ((sequence.weakenFree SetSort.set) ·ₘ numₘ(index)) ∈ₘ numₘ(bound) := by
        intro index hIndex
        have hIndexDomain := row_index_mem_of_domain S.toArithmeticSupport
          (sequence.weakenFree SetSort.set) length index hDomainXi hIndex
        have hValueCode := nat_sequence_value_code_bound_at
          (sequence.weakenFree SetSort.set)
          (code.weakenFree SetSort.set) (numₘ(index))
          hValueBoundXi hIndexDomain
        exact FirstOrder.Derives.iff_elim_left
          (membership_right_iff_of_equality
            ((sequence.weakenFree SetSort.set) ·ₘ numₘ(index))
            (code.weakenFree SetSort.set) (numₘ(bound))
            hCodeEqualityXi)
          hValueCode
      have hTraceData := sequence_trace_numeral_data S.toArithmeticSupport
        (sequence.weakenFree SetSort.set) nat_sequence_trace_term
        (code.weakenFree SetSort.set) length bound hDomainXi hCodeEqualityXi
        P.domain_eq P.code_bound P.final_code
      have hReplay := nat_sequence_code_replay_of_data C
        S.toFiniteSequenceEvaluationSupport
          (sequence.weakenFree SetSort.set) nat_sequence_trace_term
        tokens length bound hFunctionXi hDomainXi P.zero_value
        hStepReplay hValueReplay hTraceData.1 hTraceData.2
      simpa [nat_sequence_graph_term, nat_sequence_graph_term,
        standard_sequence_from_weakenFree, finite_numeral_term_weakenFree,
        Function.comp_def] using! hReplay)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
