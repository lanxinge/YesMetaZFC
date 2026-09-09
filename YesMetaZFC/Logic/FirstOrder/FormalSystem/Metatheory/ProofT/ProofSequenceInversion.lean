import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatSequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows

/-!
# 内在二维证明序列反演

二维编码的行码和轨迹见证均由规范 free 上下文承载。本模块只保留有限码穷尽、
配对反演和行内自然数序列唯一性，不再引入变量编号、新鲜性或良构桥接。
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

/-! ## 单步有限反演 -/

/--
穷尽二维递推末步中的轨迹前值和行码；不匹配的标准码分支直接由 numeral 判异关闭。
-/
theorem proof_sequence_step_code_elim
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code : SetOpenTerm free)
    (targetCode index bound : Nat)
    {conclusion : SetOpenFormula free}
    (hCodeEquality : Γ ⊢ₘ[T] code ≐ₘ numₘ(bound))
    (hStep : Γ ⊢ₘ[T]
      proof_sequence_code_row_condition
        sequence trace code (numₘ(index)))
    (hTraceBound : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hFinal : Γ ⊢ₘ[T]
      numₘ(targetCode) ≐ₘ (trace ·ₘ numₘ(index + 1)))
    (hBranch :
      ∀ accumulator, accumulator < bound + 1 →
        ∀ item, item < bound →
          targetCode = nat_sequence_code_step accumulator item →
          (proof_sequence_row_code_term ≐ₘ numₘ(item)) ::
            ((trace.weakenFree SetSort.set ·ₘ numₘ(index)) ≐ₘ
              numₘ(accumulator)) ::
            proof_sequence_row_context Γ
              sequence trace code (numₘ(index))
              ⊢ₘ[T] nat_sequence_code_condition
                (sequence.weakenFree SetSort.set ·ₘ numₘ(index))
                proof_sequence_row_code_term →
          (proof_sequence_row_code_term ≐ₘ numₘ(item)) ::
            ((trace.weakenFree SetSort.set ·ₘ numₘ(index)) ≐ₘ
              numₘ(accumulator)) ::
            proof_sequence_row_context Γ
              sequence trace code (numₘ(index))
              ⊢ₘ[T] conclusion.weakenFree SetSort.set) :
    Γ ⊢ₘ[T] conclusion := by
  exact proof_sequence_code_row_elim
    sequence trace code (numₘ(index)) hStep (by
      intro P
      let Ξ : Context signature (SetSort.set :: free) :=
        proof_sequence_row_context Γ sequence trace code (numₘ(index))
      change Ξ ⊢ₘ[T] conclusion.weakenFree SetSort.set
      have lift_to_row :
          ∀ {formula : SetOpenFormula free},
            Γ ⊢ₘ[T] formula →
              Ξ ⊢ₘ[T] formula.weakenFree SetSort.set := by
        intro formula hFormula
        simpa [Ξ, proof_sequence_row_context] using
          FirstOrder.Derives.context_weaken_cons
            (fresh_context_weaken hFormula)
      have hCodeEqualityXi : Ξ ⊢ₘ[T]
          code.weakenFree SetSort.set ≐ₘ numₘ(bound) := by
        simpa using lift_to_row hCodeEquality
      have hRowCodeBound : Ξ ⊢ₘ[T]
          proof_sequence_row_code_term ∈ₘ numₘ(bound) :=
        FirstOrder.Derives.iff_elim_left
          (membership_right_iff_of_equality
            proof_sequence_row_code_term
            (code.weakenFree SetSort.set) (numₘ(bound))
            hCodeEqualityXi)
          P.row_code_mem
      have hTraceBoundXi : Ξ ⊢ₘ[T]
          (trace.weakenFree SetSort.set ·ₘ numₘ(index)) ∈ₘ
            numₘ(bound + 1) := by
        simpa using lift_to_row hTraceBound
      have hOuter : Ξ ⊢ₘ[T]
          (trace.weakenFree SetSort.set ·ₘ Sₘ(numₘ(index))) ≐ₘ
            Sₘ(godel_pairₘ(trace.weakenFree SetSort.set ·ₘ numₘ(index),
              proof_sequence_row_code_term)) := by
        simpa [proof_sequence_code_step_condition] using!
          FirstOrder.Derives.conj_elim_right P.row_condition
      have hFinalXi : Ξ ⊢ₘ[T] numₘ(targetCode) ≐ₘ
          (trace.weakenFree SetSort.set ·ₘ numₘ(index + 1)) := by
        simpa using lift_to_row hFinal
      apply nat_sequence_step_value_elim C
        (trace.weakenFree SetSort.set ·ₘ numₘ(index)) proof_sequence_row_code_term
        targetCode bound _ hTraceBoundXi hRowCodeBound
        (FirstOrder.Derives.eq_trans hFinalXi hOuter)
      intro accumulator hAccumulator item hItem hMatch
      apply hBranch accumulator hAccumulator item hItem hMatch
      simpa [proof_sequence_code_step_condition] using!
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons
            (FirstOrder.Derives.conj_elim_left P.row_condition)))

/-! ## 有限前缀反演 -/

/-- 二维递归轨迹和末码共同决定证明行序列的有限前缀。 -/
theorem proof_sequence_code_prefix_unique
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code : SetOpenTerm free)
    (rows : List (List Nat))
    (length bound : Nat)
    (hZero : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep : ∀ index, index < length →
      Γ ⊢ₘ[T]
        proof_sequence_code_row_condition
          sequence trace code (numₘ(index)))
    (hTraceBound : ∀ index, index ≤ length →
      Γ ⊢ₘ[T]
        (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hCodeEquality : Γ ⊢ₘ[T]
      code ≐ₘ numₘ(bound))
    (hFinal : Γ ⊢ₘ[T]
      numₘ(proof_sequence_code_value rows) ≐ₘ
        (trace ·ₘ numₘ(length))) :
    (Γ ⊢ₘ[T] numₘ(length) ≐ₘ numₘ(rows.length)) ∧
      (∀ index (hIndex : index < rows.length),
        Γ ⊢ₘ[T]
          (sequence ·ₘ numₘ(index)) ≐ₘ
            nat_sequence_graph_term (rows[index]'hIndex)) := by
  induction rows using list_snoc_induction generalizing Γ length with
  | hNil =>
      by_cases hLength : length = 0
      · subst length
        constructor
        · exact Metatheory.Derives.equality_refl
            (T := T) (Γ := Γ) (numₘ(0))
        · intro index hIndex
          simp at hIndex
      · obtain ⟨prefixLength, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero hLength
        have hFinalZero : Γ ⊢ₘ[T]
            numₘ(0) ≐ₘ (trace ·ₘ numₘ(prefixLength + 1)) := by
          simpa [proof_sequence_code_value,
            proof_sequence_code_from, nat_sequence_code_value] using! hFinal
        have hFalse : Γ ⊢ₘ[T] Formula.falsum := by
          apply proof_sequence_step_code_elim C sequence trace code
            0 prefixLength bound hCodeEquality
            (hStep prefixLength (Nat.lt_succ_self _))
            (hTraceBound prefixLength (Nat.le_succ _)) hFinalZero
          intro accumulator hAccumulator item hItem hMatch hInner
          exfalso
          simp [nat_sequence_code_step] at hMatch
        constructor
        · exact FirstOrder.Derives.falsum_elim hFalse
        · intro index hIndex
          exact FirstOrder.Derives.falsum_elim hFalse
  | hSnoc xs row ih =>
      by_cases hLength : length = 0
      · subst length
        have hFinalZero : Γ ⊢ₘ[T]
            numₘ(proof_sequence_code_value (xs ++ [row])) ≐ₘ numₘ(0) :=
          Metatheory.Derives.equality_trans hFinal hZero
        have hPositive : 0 < proof_sequence_code_value (xs ++ [row]) := by
          rw [proof_sequence_code_value_append_singleton]
          exact Nat.succ_pos _
        have hFalse : Γ ⊢ₘ[T] Formula.falsum :=
          falsum_of_numeral_equality C (Nat.ne_of_gt hPositive) hFinalZero
        constructor
        · exact FirstOrder.Derives.falsum_elim hFalse
        · intro index hIndex
          exact FirstOrder.Derives.falsum_elim hFalse
      · obtain ⟨prefixLength, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero hLength
        let lastConclusion : SetOpenFormula free :=
          (numₘ(proof_sequence_code_value xs) ≐ₘ
              (trace ·ₘ numₘ(prefixLength))) ∧ₘ
            ((sequence ·ₘ numₘ(prefixLength)) ≐ₘ
              nat_sequence_graph_term row)
        have hLast : Γ ⊢ₘ[T] lastConclusion := by
          apply proof_sequence_step_code_elim C sequence trace code
            (proof_sequence_code_value (xs ++ [row]))
            prefixLength bound hCodeEquality
            (hStep prefixLength (Nat.lt_succ_self _))
            (hTraceBound prefixLength (Nat.le_succ _)) hFinal
          intro accumulator hAccumulator item hItem hMatch hInner
          have hPairMatch :
              godel_pair_value
                  (proof_sequence_code_value xs)
                  (nat_sequence_code_value row) =
                godel_pair_value accumulator item := by
            apply Nat.succ.inj
            simpa [nat_sequence_code_step] using hMatch
          rcases godel_pair_value_eq_iff.mp hPairMatch with
            ⟨rfl, rfl⟩
          let Ξ : Context signature (SetSort.set :: free) :=
            proof_sequence_row_context Γ
              sequence trace code (numₘ(prefixLength))
          let Ε : Context signature (SetSort.set :: free) :=
            ((trace.weakenFree SetSort.set ·ₘ numₘ(prefixLength)) ≐ₘ
              numₘ(proof_sequence_code_value xs)) :: Ξ
          let Ζ : Context signature (SetSort.set :: free) :=
            (proof_sequence_row_code_term ≐ₘ
              numₘ(nat_sequence_code_value row)) :: Ε
          change Ζ ⊢ₘ[T] lastConclusion.weakenFree SetSort.set
          have hTraceEquality : Ζ ⊢ₘ[T]
              (trace.weakenFree SetSort.set ·ₘ numₘ(prefixLength)) ≐ₘ
                numₘ(proof_sequence_code_value xs) :=
            FirstOrder.Derives.assumption (by simp [Ζ, Ε])
          have hRowCodeEquality : Ζ ⊢ₘ[T]
              proof_sequence_row_code_term ≐ₘ
                numₘ(nat_sequence_code_value row) :=
            FirstOrder.Derives.assumption (by simp [Ζ])
          have hRow : Ζ ⊢ₘ[T]
              (sequence.weakenFree SetSort.set ·ₘ numₘ(prefixLength)) ≐ₘ
                nat_sequence_graph_term row :=
            nat_sequence_code_condition_unique_of_code_equality C S
              (sequence.weakenFree SetSort.set ·ₘ numₘ(prefixLength))
              proof_sequence_row_code_term row hInner hRowCodeEquality
          have hPrefixFinal : Ζ ⊢ₘ[T]
              numₘ(proof_sequence_code_value xs) ≐ₘ
                (trace.weakenFree SetSort.set ·ₘ numₘ(prefixLength)) :=
            Metatheory.Derives.equality_symm hTraceEquality
          simpa [lastConclusion, nat_sequence_graph_term,
            standard_sequence_from_weakenFree,
            finite_numeral_term_weakenFree, Function.comp_def] using
            FirstOrder.Derives.conj_intro hPrefixFinal hRow
        have hPrefixFinal : Γ ⊢ₘ[T]
            numₘ(proof_sequence_code_value xs) ≐ₘ
              (trace ·ₘ numₘ(prefixLength)) := by
          simpa [lastConclusion] using
            FirstOrder.Derives.conj_elim_left hLast
        have hLastRow : Γ ⊢ₘ[T]
            (sequence ·ₘ numₘ(prefixLength)) ≐ₘ
              nat_sequence_graph_term row := by
          simpa [lastConclusion] using
            FirstOrder.Derives.conj_elim_right hLast
        have hIH := ih (Γ := Γ) prefixLength hZero
          (fun index hIndex => hStep index (by omega))
          (fun index hIndex => hTraceBound index (by omega))
          hCodeEquality hPrefixFinal
        constructor
        · have hSuccessorLength :=
            successor_term_congr_of_equality
              (numₘ(prefixLength)) (numₘ(xs.length)) hIH.1
          simpa [List.length_append,
            finite_numeral_term, successor_term] using hSuccessorLength
        · intro index hIndex
          by_cases hPrefixIndex : index < xs.length
          · simpa [List.getElem_append, hPrefixIndex] using
              hIH.2 index hPrefixIndex
          · have hIndexEq : index = xs.length := by
              have hIndex' : index < xs.length + 1 := by
                simpa [List.length_append] using hIndex
              omega
            subst index
            have hApplication : Γ ⊢ₘ[T]
                (sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                  (sequence ·ₘ numₘ(xs.length)) :=
              function_application_term_congr_argument_of_equality
                sequence (numₘ(prefixLength)) (numₘ(xs.length)) hIH.1
            simpa [List.getElem_append] using
              Metatheory.Derives.equality_trans
                (Metatheory.Derives.equality_symm hApplication)
                hLastRow

/-! ## 回放数据到规范二维序列 -/

/-- 将已经打开的二维编码数据收束为规范行序列。 -/
theorem proof_sequence_code_replay_of_data
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code : SetOpenTerm free)
    (rows : List (List Nat))
    (length bound : Nat)
    (hFunction : Γ ⊢ₘ[T] is_function_formula sequence)
    (hDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(length))
    (hZero : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep : ∀ index, index < length →
      Γ ⊢ₘ[T]
        proof_sequence_code_row_condition
          sequence trace code (numₘ(index)))
    (hTraceBound : ∀ index, index ≤ length →
      Γ ⊢ₘ[T]
        (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hCodeEquality : Γ ⊢ₘ[T]
      code ≐ₘ numₘ(bound))
    (hFinal : Γ ⊢ₘ[T]
      numₘ(proof_sequence_code_value rows) ≐ₘ
        (trace ·ₘ numₘ(length))) :
    Γ ⊢ₘ[T] sequence ≐ₘ proof_sequence_graph_term rows := by
  have hUnique := proof_sequence_code_prefix_unique C S sequence trace code rows
    length bound hZero hStep hTraceBound hCodeEquality hFinal
  apply function_equality_of_finite_values C.toFiniteCore S.toFiniteSequenceEvaluationSupport
    sequence (rows.map (fun row => nat_sequence_graph_term row)) hFunction
  · simpa only [List.length_map] using FirstOrder.Derives.eq_trans hDomain hUnique.1
  · intro index hIndex
    simpa only [List.getElem_map] using hUnique.2 index
      (by simpa only [List.length_map] using hIndex)

/-- 内在证明序列条件与规范 numeral 码直接决定规范二维有限图。 -/
theorem proof_sequence_code_condition_unique_of_code_equality
    {T : SetTheory}
    (C : CertificateCore T)
    (S : IntrinsicProofRowSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (rows : List (List Nat))
    (hCondition : Γ ⊢ₘ[T]
      proof_sequence_code_condition sequence code)
    (hCodeEquality : Γ ⊢ₘ[T]
      code ≐ₘ numₘ(proof_sequence_code_value rows)) :
    Γ ⊢ₘ[T] sequence ≐ₘ proof_sequence_graph_term rows := by
  let bound : Nat := proof_sequence_code_value rows
  have hParts := proof_sequence_code_condition_parts sequence code hCondition
  have hFormulaCodeNonempty : Γ ⊢ₘ[T]
      syntax_formula_code_set_term ≠ₘ ∅ₘ :=
    intrinsic_proof_row_formula_code_nonempty S (Γ := Γ)
  have hOrdinary : Γ ⊢ₘ[T]
      sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term) :=
    hParts.sequence_space
  have hMemberCondition :=
    sequence_space_member_implies_member_condition
      S.toFiniteSequenceSpaceSupport syntax_formula_code_set_term sequence
      hFormulaCodeNonempty hOrdinary
  have hFiniteCondition :=
    finite_sequence_member_condition_implies_finite_sequence
      S.toFiniteSequenceSpaceSupport syntax_formula_code_set_term sequence
      hMemberCondition
  have hFunction : Γ ⊢ₘ[T] is_function_formula sequence := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conj_elim_left hFiniteCondition
  have hCodeEqualityBound : Γ ⊢ₘ[T]
      code ≐ₘ numₘ(bound) := by
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
    (sequence ≐ₘ proof_sequence_graph_term rows) hDomainMember
  intro length hLength
  let domainEquation : SetOpenFormula free :=
    domₘ(sequence) ≐ₘ numₘ(length)
  let Δ : Context signature free := domainEquation :: Γ
  change Δ ⊢ₘ[T] sequence ≐ₘ proof_sequence_graph_term rows
  have hDomain : Δ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(length) := by
    simpa [Δ, domainEquation] using
      (FirstOrder.Derives.assumption
        (T := T) (Γ := Δ) (formula := domainEquation) (by simp [Δ]))
  have hTrace : Δ ⊢ₘ[T]
      proof_sequence_code_trace_condition sequence code :=
    FirstOrder.Derives.context_weaken_cons hParts.trace_condition
  exact proof_sequence_code_trace_elim sequence code hTrace
    (conclusion := sequence ≐ₘ proof_sequence_graph_term rows) (by
      intro P
      let Ξ : Context signature (SetSort.set :: free) :=
        proof_sequence_trace_context Δ sequence code
      change Ξ ⊢ₘ[T]
        (sequence ≐ₘ proof_sequence_graph_term rows).weakenFree SetSort.set
      have lift_to_trace {formula : SetOpenFormula free} (h : Δ ⊢ₘ[T] formula) :
          Ξ ⊢ₘ[T] formula.weakenFree SetSort.set := by
        simpa [Ξ, proof_sequence_trace_context] using
          FirstOrder.Derives.context_weaken_cons (fresh_context_weaken h)
      have hFunctionXi : Ξ ⊢ₘ[T] is_function_formula (sequence.weakenFree SetSort.set) :=
        lift_to_trace (FirstOrder.Derives.context_weaken_cons hFunction)
      have hDomainXi : Ξ ⊢ₘ[T] domₘ(sequence.weakenFree SetSort.set) ≐ₘ numₘ(length) := by
        simpa using lift_to_trace hDomain
      have hCodeEqualityXi : Ξ ⊢ₘ[T] code.weakenFree SetSort.set ≐ₘ numₘ(bound) := by
        simpa using lift_to_trace (FirstOrder.Derives.context_weaken_cons hCodeEqualityBound)
      have hStepReplay : ∀ index, index < length →
          Ξ ⊢ₘ[T]
            proof_sequence_code_row_condition
              (sequence.weakenFree SetSort.set)
              proof_sequence_trace_term
              (code.weakenFree SetSort.set)
              (numₘ(index)) := by
        intro index hIndex
        have hIndexDomain : Ξ ⊢ₘ[T]
            numₘ(index) ∈ₘ domₘ(sequence.weakenFree SetSort.set) :=
          row_index_mem_of_domain
            S.toFiniteSequenceSpaceSupport.toArithmeticSupport
            (sequence.weakenFree SetSort.set)
            length index hDomainXi hIndex
        exact proof_sequence_code_row_condition_at
          (sequence.weakenFree SetSort.set)
          proof_sequence_trace_term
          (code.weakenFree SetSort.set)
          (numₘ(index)) P.pointwise hIndexDomain
      have hTraceData := sequence_trace_numeral_data S.toFiniteSequenceSpaceSupport.toArithmeticSupport
        (sequence.weakenFree SetSort.set) proof_sequence_trace_term
        (code.weakenFree SetSort.set) length bound hDomainXi hCodeEqualityXi
        P.domain_eq P.code_bound P.final_code
      have hReplay := proof_sequence_code_replay_of_data C
        S.toFiniteSequenceSpaceSupport
        (sequence.weakenFree SetSort.set)
        proof_sequence_trace_term
        (code.weakenFree SetSort.set)
        rows length bound hFunctionXi hDomainXi P.zero_value
        hStepReplay hTraceData.1 hCodeEqualityXi hTraceData.2
      simpa [proof_sequence_graph_term, nat_sequence_graph_term,
        standard_sequence_from_weakenFree, finite_numeral_term_weakenFree,
        Function.comp_def] using! hReplay)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
