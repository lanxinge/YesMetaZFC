import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.MultiplicationTrace

/-!
# 内在有限幂轨迹

幂的递归步复用内在乘法的有限 numeral 求值；对象层只验证有限图满足幂定义合同。
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

private def standard_exponentiation_trace_elements
    {free : SetContext} (base exponent : Nat) :
    List (SetOpenTerm free) :=
  (List.range (exponent + 1)).map (fun index => numₘ(base ^ index))

private theorem standard_exponentiation_trace_step
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (base exponent index : Nat) (hIndex : index < exponent) :
    Γ ⊢ₘ[T]
      (standard_sequence_from 0
          (standard_exponentiation_trace_elements base exponent) ·ₘ
        Sₘ(numₘ(index))) ≐ₘ
      ((standard_sequence_from 0
          (standard_exponentiation_trace_elements base exponent) ·ₘ
        numₘ(index)) *ₘ numₘ(base)) := by
  have hClosed := standard_sequence_finite_numeral_multiplication S (base ^ index) base
  have hLift := FirstOrder.Derives.context_weaken (Δ := Γ) (by simp)
    (FirstOrder.Derives.free_renaming
      (VariableRenaming.empty : VariableRenaming [] free) hClosed)
  have h := standard_numeral_trace_step (Γ := Γ) S.toFiniteSequenceEvaluationSupport
    (fun i => base ^ i) exponent index hIndex
    ((.bvar .here) *ₘ (numₘ(base) : SetOpenTerm free).weakenBound SetSort.set) (by
      simpa [Formula.renameFree, Formula.rename, Renaming.free,
        Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
        finite_numeral_term_renameMapped, Nat.add_mul, Nat.one_mul, Nat.pow_succ,
        Term.instantiateTop, Term.substitute, Substitution.instantiateTop,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop] using! hLift)
  simpa only [standard_exponentiation_trace_elements, Term.instantiateTop_app,
    Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound, Term.instantiateTop_bvar_here] using! h

private def standard_exponentiation_trace_step_formula
    (base exponent : Nat) : SetSentence :=
  let point : SetOpenTerm [SetSort.set] := .fvar .here
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0
      (standard_exponentiation_trace_elements
        (free := []) base exponent)
  ((point ∈ₘ (numₘ(exponent) : SetOpenTerm []).weakenFree SetSort.set) ⟶ₘ
      ((trace.weakenFree SetSort.set ·ₘ Sₘ(point)) ≐ₘ
        ((trace.weakenFree SetSort.set ·ₘ point) *ₘ
          (numₘ(base) : SetOpenTerm []).weakenFree SetSort.set))).forallFreeTop SetSort.set

private theorem standard_exponentiation_trace_step_forall
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (base exponent : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      standard_exponentiation_trace_step_formula base exponent := by
  let trace : SetOpenTerm [] := standard_sequence_from 0 (standard_exponentiation_trace_elements base exponent)
  let point : SetTerm [SetSort.set] [] := .bvar .here
  let body : SetFormula [SetSort.set] [] :=
    (trace.weakenBound SetSort.set ·ₘ Sₘ(point)) ≐ₘ ((trace.weakenBound SetSort.set ·ₘ point) *ₘ (numₘ(base) : SetOpenTerm []).weakenBound SetSort.set)
  have h := bounded_forall_numeral_intro
    (ArithmeticSupport.finite_core S.toArithmeticSupport) exponent body (by
      intro index hIndex
      simpa only [body, point, trace, Formula.instantiateTop_equal,
        Term.instantiateTop_app, Arguments.instantiateTop_cons,
        Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound,
        Term.instantiateTop_bvar_here] using!
        (standard_exponentiation_trace_step (Γ := []) S base exponent index hIndex))
  simpa only [body, point, trace, standard_exponentiation_trace_step_formula,
    Formula.LevyBound.boundedForall, Formula.forallFreeTop,
    Formula.abstractFreeTop, Formula.substitute, Substitution.abstractFreeTop,
    Formula.substituteMapped, Term.substituteMapped_abstractFreeTop_weakenFree,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.abstractFreeTop, VariableSubstitution.abstractBound,
    set_levy_bound, Formula.LevyBound.membership] using! h

theorem standard_sequence_finite_numeral_exponentiation
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (base exponent : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      numₘ(base ^ exponent) ≐ₘ
        (numₘ(base) ^ₘ numₘ(exponent)) := by
  let elements : List (SetOpenTerm []) :=
    standard_exponentiation_trace_elements
      (free := []) base exponent
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0 elements
  let result : SetOpenTerm [] := numₘ(base ^ exponent)
  have hTraceMapping : ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(exponent))) ωₘ :=
    standard_numeral_trace_mapping S (fun i => base ^ i) exponent
  have hInitial : ([] : Context signature []) ⊢ₘ[T]
      (trace ·ₘ ∅ₘ) ≐ₘ Sₘ(∅ₘ) := by
    simpa [trace, elements, standard_exponentiation_trace_elements, finite_numeral_term] using!
      (standard_numeral_trace_value (Γ := []) S.toFiniteSequenceEvaluationSupport
        (fun i => base ^ i) exponent 0 (Nat.zero_le _))
  have hStep : ([] : Context signature []) ⊢ₘ[T]
      standard_exponentiation_trace_step_formula base exponent :=
    standard_exponentiation_trace_step_forall S base exponent
  have hTerminal : ([] : Context signature []) ⊢ₘ[T]
      trace ·ₘ numₘ(exponent) ≐ₘ result := by
    simpa [trace, elements, result, standard_exponentiation_trace_elements, Nat.add_comm] using!
      (standard_numeral_trace_value (Γ := []) S.toFiniteSequenceEvaluationSupport
        (fun i => base ^ i) exponent exponent (Nat.le_refl _))
  have hGraph : ([] : Context signature []) ⊢ₘ[T]
      natural_exponentiation_graph_condition
        (numₘ(base) : SetOpenTerm [])
        (numₘ(exponent) : SetOpenTerm []) result trace := by
    change ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(exponent))) ωₘ ∧ₘ
        ((trace ·ₘ ∅ₘ ≐ₘ Sₘ(∅ₘ)) ∧ₘ
          (standard_exponentiation_trace_step_formula base exponent ∧ₘ
            (trace ·ₘ (numₘ(exponent) : SetOpenTerm []) ≐ₘ result)))
    exact FirstOrder.Derives.conj_intro hTraceMapping <|
      FirstOrder.Derives.conj_intro hInitial <|
        FirstOrder.Derives.conj_intro hStep hTerminal
  have hResultOmega : ([] : Context signature []) ⊢ₘ[T]
      result ∈ₘ ωₘ := by
    simpa [result] using S.finite_numeral_mem_omega (base ^ exponent)
  have hSpec : ([] : Context signature []) ⊢ₘ[T]
      natural_exponentiation_spec
        (numₘ(base) : SetOpenTerm [])
        (numₘ(exponent) : SetOpenTerm []) result := by
    unfold natural_exponentiation_spec natural_exponentiation_bound_graph_condition
    apply FirstOrder.Derives.conj_intro hResultOmega
    apply FirstOrder.Derives.existsFreePrefix_intro (.cons trace .nil)
    simpa [Arguments.substitutionWith, Formula.substituteFree,
      Substitution.free_map, Formula.substitute, Formula.substituteMapped,
      Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.liftFree, natural_exponentiation_graph_condition,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_id,
      Formula.instantiateFreeTop_forallFreeTop, result] using! hGraph
  exact FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.imp_elim
      (S.exponentiation_definition_instance_derives (numₘ(base)) (numₘ(exponent)) result)
      (FirstOrder.Derives.conj_intro
        (S.finite_numeral_mem_omega base) (S.finite_numeral_mem_omega exponent))) hSpec

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
