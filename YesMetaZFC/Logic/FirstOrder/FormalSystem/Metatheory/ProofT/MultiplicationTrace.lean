import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ArithmeticTrace

/-!
# 内在有限乘法轨迹

乘法只在外部 `Nat` 上生成有限轨迹；对象层仅验证轨迹图满足乘法定义合同。
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

private def standard_multiplication_trace_elements
    {free : SetContext} (left right : Nat) :
    List (SetOpenTerm free) :=
  (List.range (left + 1)).map (fun index => numₘ(index * right))

private theorem standard_multiplication_trace_step
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right index : Nat) (hIndex : index < left) :
    Γ ⊢ₘ[T]
      (standard_sequence_from 0
          (standard_multiplication_trace_elements left right) ·ₘ
        Sₘ(numₘ(index))) ≐ₘ
      ((standard_sequence_from 0
          (standard_multiplication_trace_elements left right) ·ₘ
        numₘ(index)) +ₘ numₘ(right)) := by
  have hClosed := standard_sequence_finite_numeral_addition S (index * right) right
  have hLift := FirstOrder.Derives.context_weaken (Δ := Γ) (by simp)
    (FirstOrder.Derives.free_renaming
      (VariableRenaming.empty : VariableRenaming [] free) hClosed)
  have h := standard_numeral_trace_step (Γ := Γ) S.toFiniteSequenceEvaluationSupport
    (fun i => i * right) left index hIndex
    ((.bvar .here) +ₘ (numₘ(right) : SetOpenTerm free).weakenBound SetSort.set) (by
      simpa [Formula.renameFree, Formula.rename, Renaming.free,
        Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
        finite_numeral_term_renameMapped, Nat.add_mul, Nat.one_mul, Nat.pow_succ,
        Term.instantiateTop, Term.substitute, Substitution.instantiateTop,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop] using! hLift)
  simpa only [standard_multiplication_trace_elements, Term.instantiateTop_app,
    Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound, Term.instantiateTop_bvar_here] using! h

private def standard_multiplication_trace_step_formula
    (left right : Nat) : SetSentence :=
  let point : SetOpenTerm [SetSort.set] := .fvar .here
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0
      (standard_multiplication_trace_elements (free := []) left right)
  ((point ∈ₘ (numₘ(left) : SetOpenTerm []).weakenFree SetSort.set) ⟶ₘ
      ((trace.weakenFree SetSort.set ·ₘ Sₘ(point)) ≐ₘ
        ((trace.weakenFree SetSort.set ·ₘ point) +ₘ
          (numₘ(right) : SetOpenTerm []).weakenFree SetSort.set))).forallFreeTop SetSort.set

private theorem standard_multiplication_trace_step_forall
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      standard_multiplication_trace_step_formula left right := by
  let trace : SetOpenTerm [] := standard_sequence_from 0 (standard_multiplication_trace_elements left right)
  let point : SetTerm [SetSort.set] [] := .bvar .here
  let body : SetFormula [SetSort.set] [] :=
    (trace.weakenBound SetSort.set ·ₘ Sₘ(point)) ≐ₘ ((trace.weakenBound SetSort.set ·ₘ point) +ₘ (numₘ(right) : SetOpenTerm []).weakenBound SetSort.set)
  have h := bounded_forall_numeral_intro
    (ArithmeticSupport.finite_core S.toArithmeticSupport) left body (by
      intro index hIndex
      simpa only [body, point, trace, Formula.instantiateTop_equal,
        Term.instantiateTop_app, Arguments.instantiateTop_cons,
        Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound,
        Term.instantiateTop_bvar_here] using!
        (standard_multiplication_trace_step (Γ := []) S left right index hIndex))
  simpa only [body, point, trace, standard_multiplication_trace_step_formula,
    Formula.LevyBound.boundedForall, Formula.forallFreeTop,
    Formula.abstractFreeTop, Formula.substitute, Substitution.abstractFreeTop,
    Formula.substituteMapped, Term.substituteMapped_abstractFreeTop_weakenFree,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.abstractFreeTop, VariableSubstitution.abstractBound,
    set_levy_bound, Formula.LevyBound.membership] using! h

theorem standard_sequence_finite_numeral_multiplication
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      numₘ(left * right) ≐ₘ
        (numₘ(left) *ₘ numₘ(right)) := by
  let elements : List (SetOpenTerm []) :=
    standard_multiplication_trace_elements (free := []) left right
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0 elements
  let result : SetOpenTerm [] := numₘ(left * right)
  have hTraceMapping : ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ :=
    standard_numeral_trace_mapping S (fun i => i * right) left
  have hInitial : ([] : Context signature []) ⊢ₘ[T]
      (trace ·ₘ ∅ₘ) ≐ₘ ∅ₘ := by
    simpa [trace, elements, standard_multiplication_trace_elements, finite_numeral_term] using!
      (standard_numeral_trace_value (Γ := []) S.toFiniteSequenceEvaluationSupport
        (fun i => i * right) left 0 (Nat.zero_le _))
  have hStep : ([] : Context signature []) ⊢ₘ[T]
      standard_multiplication_trace_step_formula left right :=
    standard_multiplication_trace_step_forall S left right
  have hTerminal : ([] : Context signature []) ⊢ₘ[T]
      trace ·ₘ numₘ(left) ≐ₘ result := by
    simpa [trace, elements, result, standard_multiplication_trace_elements, Nat.add_comm] using!
      (standard_numeral_trace_value (Γ := []) S.toFiniteSequenceEvaluationSupport
        (fun i => i * right) left left (Nat.le_refl _))
  have hGraph : ([] : Context signature []) ⊢ₘ[T]
      natural_multiplication_graph_condition
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) result trace := by
    change ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ ∧ₘ
        ((trace ·ₘ ∅ₘ ≐ₘ ∅ₘ) ∧ₘ
          (standard_multiplication_trace_step_formula left right ∧ₘ
            (trace ·ₘ (numₘ(left) : SetOpenTerm []) ≐ₘ result)))
    exact FirstOrder.Derives.conj_intro hTraceMapping <|
      FirstOrder.Derives.conj_intro hInitial <|
        FirstOrder.Derives.conj_intro hStep hTerminal
  have hResultOmega : ([] : Context signature []) ⊢ₘ[T]
      result ∈ₘ ωₘ := by
    simpa [result] using S.finite_numeral_mem_omega (left * right)
  have hSpec : ([] : Context signature []) ⊢ₘ[T]
      natural_multiplication_spec
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) result := by
    unfold natural_multiplication_spec natural_multiplication_bound_graph_condition
    apply FirstOrder.Derives.conj_intro hResultOmega
    apply FirstOrder.Derives.existsFreePrefix_intro (.cons trace .nil)
    simpa [Arguments.substitutionWith, Formula.substituteFree,
      Substitution.free_map, Formula.substitute, Formula.substituteMapped,
      Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.liftFree, natural_multiplication_graph_condition,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_id,
      Formula.instantiateFreeTop_forallFreeTop, result] using! hGraph
  exact FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.imp_elim
      (S.multiplication_definition_instance_derives (numₘ(left)) (numₘ(right)) result)
      (FirstOrder.Derives.conj_intro
        (S.finite_numeral_mem_omega left) (S.finite_numeral_mem_omega right))) hSpec

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
