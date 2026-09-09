import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ArithmeticEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatSequenceInversion

/-!
# 内在自然数序列编码的正向构造

本模块把外部 `List Nat` 直接装配为内在自然数序列编码条件。序列图、轨迹图和
有限穷尽均由宿主递归与类型化 bound 上下文承载，不恢复旧的自由变量编号或
`Admissible` 桥接层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open IntrinsicPairing
open ProofCode

set_option autoImplicit false

private theorem omega_nonempty_of_numeral_member
    {T : SetTheory}
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (number : Nat)
    (hNumber : Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ := by
  have hImp : Γ ⊢ₘ[T]
      (numₘ(number) ∈ₘ (ωₘ : SetOpenTerm free)) ⟶ₘ
        (ωₘ ≠ₘ (∅ₘ : SetOpenTerm free)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.toArithmeticSupport.contains_empty_set hSentence)
      (member_implies_set_nonempty
        (Γ := Γ)
        (numₘ(number) : SetOpenTerm free)
        (ωₘ : SetOpenTerm free))
  exact FirstOrder.Derives.imp_elim hImp hNumber

private theorem nat_sequence_code_step_condition_instantiateTop
    {free : SetContext}
    (sequence trace : SetOpenTerm free)
    (index : Nat) :
    Formula.instantiateTop (numₘ(index))
        (nat_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (.bvar .here)) =
      nat_sequence_code_step_condition sequence trace (numₘ(index)) := by
  unfold nat_sequence_code_step_condition
  rw [Formula.instantiateTop_equal]
  simp only [Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_app,
    Term.instantiateTop_weakenBound]
  repeat rw [Term.instantiateTop_bvar_here]

private theorem standard_nat_sequence_space
    {T : SetTheory}
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (hNumeralOmega : ∀ number,
      Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      nat_sequence_graph_term (bound := []) (free := free) tokens ∈ₘ
        seq_spaceₘ(ωₘ) := by
  let elements : List (SetOpenTerm free) :=
    tokens.map (fun token => numₘ(token))
  have hLengthOmega : Γ ⊢ₘ[T]
      numₘ(elements.length) ∈ₘ (ωₘ : SetOpenTerm free) := by
    simpa [elements] using hNumeralOmega tokens.length
  have hOmegaNonempty : Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ :=
    omega_nonempty_of_numeral_member S elements.length hLengthOmega
  have hSpace : Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ seq_spaceₘ(ωₘ) :=
    standard_sequence_mem_sequence_space
      S elements ωₘ hLengthOmega hOmegaNonempty (by
        intro element hElement
        rcases List.mem_map.mp hElement with ⟨number, _, rfl⟩
        exact hNumeralOmega number)
  simpa [elements, nat_sequence_graph_term, standard_sequence] using hSpace

private theorem standard_nat_sequence_value
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index < tokens.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free) tokens ·ₘ
        numₘ(index)) ≐ₘ
        numₘ(tokens[index]'hIndex) := by
  simpa only [nat_sequence_graph_term, standard_sequence, nat_sequence_code_trace] using
    standard_sequence_map_value S (fun value => (numₘ(value) : SetOpenTerm free))
      (List.getElem?_eq_getElem hIndex)

private theorem standard_nat_sequence_trace_value
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index ≤ tokens.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (nat_sequence_code_trace tokens) ·ₘ numₘ(index)) ≐ₘ
        numₘ(nat_sequence_code_from 0 (tokens.take index)) := by
  simpa only [nat_sequence_graph_term, standard_sequence, nat_sequence_code_trace] using
    standard_sequence_map_value S (fun value => (numₘ(value) : SetOpenTerm free))
      (nat_sequence_code_trace_from_getElem? 0 tokens index hIndex)

private theorem standard_nat_sequence_trace_last_value
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (nat_sequence_code_trace tokens) ·ₘ numₘ(tokens.length)) ≐ₘ
        numₘ(nat_sequence_code_value tokens) := by
  simpa only [nat_sequence_graph_term, standard_sequence, nat_sequence_code_trace] using
    standard_sequence_map_value S (fun value => (numₘ(value) : SetOpenTerm free))
      (nat_sequence_code_trace_last tokens)

private theorem standard_nat_sequence_step
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (index : Nat)
    (hIndex : index < tokens.length) :
    Γ ⊢ₘ[T]
      (nat_sequence_graph_term (bound := []) (free := free)
          (nat_sequence_code_trace tokens) ·ₘ Sₘ(numₘ(index))) ≐ₘ
        Sₘ(godel_pairₘ(
          nat_sequence_graph_term (bound := []) (free := free)
            (nat_sequence_code_trace tokens) ·ₘ numₘ(index),
          nat_sequence_graph_term (bound := []) (free := free) tokens ·ₘ
            numₘ(index))) := by
  have hNext := standard_sequence_map_value (Γ := Γ) S
    (fun value => (numₘ(value) : SetOpenTerm free))
    (nat_sequence_code_trace_step tokens index _ (List.getElem?_eq_getElem hIndex))
  have hRight := nat_sequence_code_step_of_values (Γ := Γ) C
    (standard_nat_sequence_trace_value S tokens index (Nat.le_of_lt hIndex))
    (standard_nat_sequence_value S tokens index hIndex)
  simpa only [nat_sequence_graph_term, standard_sequence,
    finite_numeral_term, successor_term] using
    (Metatheory.Derives.equality_trans hNext (FirstOrder.Derives.eq_symm hRight))

/-! ## 自然数序列总码 -/

theorem nat_sequence_code_condition_intro_standard
    {T : SetTheory}
    (C : CertificateCore T)
    (R : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (tokens : List Nat)
    (hNumeralOmega : ∀ number,
      Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      nat_sequence_code_condition
        (nat_sequence_graph_term (bound := []) (free := free) tokens)
        (numₘ(nat_sequence_code_value tokens)) := by
  let sequence : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free) tokens
  let code : SetOpenTerm free :=
    numₘ(nat_sequence_code_value tokens)
  let trace : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free)
      (nat_sequence_code_trace tokens)
  let sequenceElements : List (SetOpenTerm free) :=
    tokens.map (fun token => numₘ(token))
  let traceElements : List (SetOpenTerm free) :=
    (nat_sequence_code_trace tokens).map (fun value => numₘ(value))
  have hSequenceSpace : Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(ωₘ) := by
    simpa [sequence] using standard_nat_sequence_space R tokens hNumeralOmega
  have hCodeOmega : Γ ⊢ₘ[T] code ∈ₘ ωₘ := by
    simpa [code] using hNumeralOmega (nat_sequence_code_value tokens)
  have hSequenceDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(tokens.length) := by
    simpa [sequence, sequenceElements, nat_sequence_graph_term,
      standard_sequence] using
      (standard_sequence_domain_eq
        (Γ := Γ) R.toFiniteSequenceGraphSupport
        (elements := sequenceElements))
  have hSequenceDomainBound : Γ ⊢ₘ[T]
      domₘ(sequence) ∈ₘ Sₘ(code) := by
    have hLengthMember : Γ ⊢ₘ[T]
        numₘ(tokens.length) ∈ₘ
          Sₘ(numₘ(nat_sequence_code_value tokens)) := by
      simpa [code, finite_numeral_term, successor_term] using
        (FirstOrder.Derives.context_weaken
          (Γ := ([] : Context signature free))
          (Δ := Γ) (by simp)
          (numeral_mem_of_lt
            R.toArithmeticSupport.contains_successor
            (Nat.lt_succ_of_le (nat_sequence_length_le_code tokens))))
    exact FirstOrder.Derives.iff_elim_right
      (membership_left_iff_of_equality
        (domₘ(sequence)) (numₘ(tokens.length))
        (Sₘ(code)) hSequenceDomain)
      hLengthMember
  have hSequenceValueBound : Γ ⊢ₘ[T]
      nat_sequence_value_code_bound sequence code := by
    apply standard_sequence_values_mem C.toFiniteCore
      R.toFiniteSequenceEvaluationSupport sequenceElements code
    intro element hElement
    rcases List.mem_map.mp hElement with ⟨number, hNumber, rfl⟩
    exact FirstOrder.Derives.context_weaken (Γ := []) (by simp)
      (numeral_mem_of_lt R.toArithmeticSupport.contains_successor
        (mem_lt_nat_sequence_code_value hNumber))
  have hTraceSpace : Γ ⊢ₘ[T] trace ∈ₘ seq_spaceₘ(ωₘ) :=
    standard_nat_sequence_space R (nat_sequence_code_trace tokens) hNumeralOmega
  have hTraceDomain : Γ ⊢ₘ[T]
      domₘ(trace) ≐ₘ Sₘ(domₘ(sequence)) :=
    standard_sequence_trace_domain R.toFiniteSequenceGraphSupport
      sequenceElements traceElements (by
        simp only [sequenceElements, traceElements, List.length_map,
          nat_sequence_code_trace_length])
  have hTraceValueBound : Γ ⊢ₘ[T]
      sequence_trace_code_bound trace code := by
    apply standard_sequence_values_mem C.toFiniteCore
      R.toFiniteSequenceEvaluationSupport traceElements (Sₘ(code))
    intro element hElement
    rcases List.mem_map.mp hElement with ⟨number, hNumber, rfl⟩
    simpa only [code, finite_numeral_term, successor_term] using
      (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp)
        (numeral_mem_of_lt R.toArithmeticSupport.contains_successor
          (Nat.lt_succ_of_le (trace_mem_le_nat_sequence_code_value hNumber))))
  have hZero : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(0) ≐ₘ numₘ(0) := by
    apply standard_sequence_map_value R.toFiniteSequenceEvaluationSupport
      (fun value => (numₘ(value) : SetOpenTerm free))
    cases tokens <;> rfl
  have hStepNumeral : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (numₘ(tokens.length))
        (nat_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (.bvar .here)) :=
    bounded_forall_numeral_intro C.toFiniteCore tokens.length _ (by
      intro index hIndex
      have hStep := standard_nat_sequence_step (Γ := Γ) C
        R.toFiniteSequenceEvaluationSupport
        tokens index hIndex
      rw [nat_sequence_code_step_condition_instantiateTop sequence trace index]
      simpa [sequence, trace] using! hStep)
  have hStep : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (domₘ(sequence))
        (nat_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (.bvar .here)) :=
    bounded_forall_of_bound_eq hSequenceDomain hStepNumeral
  have hFinalTrace : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(tokens.length) ≐ₘ code := by
    simpa [trace, code] using
      (standard_nat_sequence_trace_last_value
        (Γ := Γ)
        R.toFiniteSequenceEvaluationSupport tokens)
  have hTraceAtDomain : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(tokens.length) ≐ₘ trace ·ₘ domₘ(sequence) :=
    function_application_term_congr_argument_of_equality
      trace (numₘ(tokens.length)) (domₘ(sequence))
      (Metatheory.Derives.equality_symm hSequenceDomain)
  have hFinal : Γ ⊢ₘ[T] code ≐ₘ trace ·ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hFinalTrace) hTraceAtDomain
  have hTraceBody : Γ ⊢ₘ[T]
      (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
          sequence_trace_code_bound trace code) ∧ₘ
          ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            (Formula.LevyBound.boundedForall set_levy_bound
              (domₘ(sequence))
              (nat_sequence_code_step_condition
                (sequence.weakenBound SetSort.set)
                (trace.weakenBound SetSort.set)
                (.bvar .here)) ∧ₘ
              (code ≐ₘ trace ·ₘ domₘ(sequence)))) := by
    exact FirstOrder.Derives.conj_intro hTraceSpace <|
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hTraceDomain hTraceValueBound)
        (FirstOrder.Derives.conj_intro hZero <|
          FirstOrder.Derives.conj_intro hStep hFinal)
  change Γ ⊢ₘ[T]
    ((((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
      sequence_domain_code_bound sequence code) ∧ₘ
      nat_sequence_value_code_bound sequence code) ∧ₘ
      ((nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here)).existsE SetSort.set)
  have hPrefix : Γ ⊢ₘ[T]
      ((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
        sequence_domain_code_bound sequence code :=
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hSequenceSpace hCodeOmega)
      hSequenceDomainBound
  have hCore : Γ ⊢ₘ[T]
      (((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
        sequence_domain_code_bound sequence code) ∧ₘ
        nat_sequence_value_code_bound sequence code :=
    FirstOrder.Derives.conj_intro hPrefix hSequenceValueBound
  apply FirstOrder.Derives.conj_intro hCore
  apply FirstOrder.Derives.exists_intro trace
  change Γ ⊢ₘ[T]
    Formula.instantiateTop trace
      (nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here))
  simpa [nat_sequence_code_trace_condition, sequence, code, trace,
    nat_sequence_code_step_condition, sequence_trace_code_bound,
    Formula.instantiateTop, Substitution.instantiateTop,
    Formula.substitute, Formula.substituteMapped,
    Term.instantiateTop, Term.substituteMapped,
    Arguments.instantiateTop, Arguments.substituteMapped,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    VariableSubstitution.instantiateTop, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftBound,
    VariableSubstitution.weakenBound,
    Term.substituteMapped_weakenBound,
    Arguments.substituteMapped_weakenBound] using hTraceBody

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
