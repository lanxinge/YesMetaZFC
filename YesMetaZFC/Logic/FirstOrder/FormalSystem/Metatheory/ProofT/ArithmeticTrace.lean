import YesMetaZFC.Logic.FirstOrder.Derivation.QuantifierBlock
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ArithmeticEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceMappingSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceConstruction

/-!
# 内在有限算术轨迹

本模块提供标准有限图的值域反演与算术轨迹计算。所有递归均在外部列表或
`Nat` 上进行；对象层只消费类型化的图成员和定义合同。
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

/-- 任意标准自然数值列的第 `index` 个图值。 -/
theorem standard_numeral_trace_value
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (values : Nat → Nat) (length index : Nat) (hIndex : index ≤ length) :
    Γ ⊢ₘ[T] (standard_sequence_from 0
      ((List.range (length + 1)).map (fun i => numₘ(values i))) ·ₘ numₘ(index)) ≐ₘ
        numₘ(values index) := by
  apply standard_sequence_getElem?_value S
  simp [Nat.lt_succ_iff.mpr hIndex]

/-- 标准自然数值列统一给出精确定义域和内部 ω 值域。 -/
theorem standard_numeral_trace_mapping
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (values : Nat → Nat) (length : Nat) :
    Γ ⊢ₘ[T] is_mapping_formula
      (standard_sequence_from 0
        ((List.range (length + 1)).map (fun i => numₘ(values i))))
      (Sₘ(numₘ(length))) ωₘ := by
  apply standard_sequence_from_is_mapping S.toFiniteSequenceEvaluationSupport
  · simpa [finite_numeral_term] using FirstOrder.Derives.eq_symm
      (standard_sequence_domain_eq (Γ := Γ) S.toFiniteSequenceGraphSupport
        (elements := (List.range (length + 1)).map (fun i => numₘ(values i))))
  · intro element hElement
    rcases List.mem_map.mp hElement with ⟨index, _, rfl⟩
    exact S.finite_numeral_mem_omega (values index)

/-- 递推验证只需当前值、下一值及算子的 numeral 方程；图求值和同余统一处理。 -/
theorem standard_numeral_trace_step
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (values : Nat → Nat) (length index : Nat) (hIndex : index < length)
    (step : SetTerm [SetSort.set] free)
    (hStep : Γ ⊢ₘ[T] numₘ(values (index + 1)) ≐ₘ
      step.instantiateTop (numₘ(values index))) :
    Γ ⊢ₘ[T] (standard_sequence_from 0
      ((List.range (length + 1)).map (fun i => numₘ(values i))) ·ₘ Sₘ(numₘ(index))) ≐ₘ
        step.instantiateTop (standard_sequence_from 0
          ((List.range (length + 1)).map (fun i => numₘ(values i))) ·ₘ numₘ(index)) := by
  have hCurrent := standard_numeral_trace_value (Γ := Γ) S values length index
    (Nat.le_of_lt hIndex)
  have hNext := standard_numeral_trace_value (Γ := Γ) S values length (index + 1)
    (Nat.succ_le_iff.mpr hIndex)
  exact FirstOrder.Derives.eq_trans hNext (FirstOrder.Derives.eq_trans hStep
    (FirstOrder.Derives.eq_symm
      (Metatheory.Derives.term_context_congr_of_equality step hCurrent)))

private def standard_addition_trace_elements
    {free : SetContext} (left right : Nat) :
    List (SetOpenTerm free) :=
  (List.range (left + 1)).map (fun index => numₘ(right + index))

private theorem standard_addition_trace_step
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right index : Nat) (hIndex : index < left) :
    Γ ⊢ₘ[T]
      (standard_sequence_from 0
          (standard_addition_trace_elements left right) ·ₘ
        Sₘ(numₘ(index))) ≐ₘ
      Sₘ(standard_sequence_from 0
          (standard_addition_trace_elements left right) ·ₘ
        numₘ(index)) := by
  simpa [standard_addition_trace_elements, Term.instantiateTop_app,
    Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
    Term.instantiateTop_bvar_here] using!
    standard_numeral_trace_step S.toFiniteSequenceEvaluationSupport
      (fun i => right + i) left index hIndex (Sₘ(.bvar .here))
      (FirstOrder.Derives.eq_refl _)

private def standard_addition_trace_step_formula
    (left right : Nat) : SetSentence :=
  let point : SetOpenTerm [SetSort.set] := .fvar .here
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0
      (standard_addition_trace_elements (free := []) left right)
  ((point ∈ₘ (numₘ(left) : SetOpenTerm []).weakenFree SetSort.set) ⟶ₘ
      ((trace.weakenFree SetSort.set ·ₘ Sₘ(point)) ≐ₘ
        Sₘ(trace.weakenFree SetSort.set ·ₘ point))).forallFreeTop SetSort.set

private theorem standard_addition_trace_step_forall
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      standard_addition_trace_step_formula left right := by
  let trace : SetOpenTerm [] := standard_sequence_from 0 (standard_addition_trace_elements left right)
  let point : SetTerm [SetSort.set] [] := .bvar .here
  let body : SetFormula [SetSort.set] [] :=
    (trace.weakenBound SetSort.set ·ₘ Sₘ(point)) ≐ₘ Sₘ(trace.weakenBound SetSort.set ·ₘ point)
  have h := bounded_forall_numeral_intro
    (ArithmeticSupport.finite_core S.toArithmeticSupport) left body (by
      intro index hIndex
      simpa only [body, point, trace, Formula.instantiateTop_equal,
        Term.instantiateTop_app, Arguments.instantiateTop_cons,
        Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound,
        Term.instantiateTop_bvar_here] using!
        (standard_addition_trace_step (Γ := []) S left right index hIndex))
  simpa only [body, point, trace, standard_addition_trace_step_formula,
    Formula.LevyBound.boundedForall, Formula.forallFreeTop,
    Formula.abstractFreeTop, Formula.substitute, Substitution.abstractFreeTop,
    Formula.substituteMapped, Term.substituteMapped_abstractFreeTop_weakenFree,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.abstractFreeTop, VariableSubstitution.abstractBound,
    set_levy_bound, Formula.LevyBound.membership] using! h

theorem standard_sequence_finite_numeral_addition
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      numₘ(left + right) ≐ₘ
        (numₘ(left) +ₘ numₘ(right)) := by
  let elements : List (SetOpenTerm []) :=
    standard_addition_trace_elements (free := []) left right
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0 elements
  let result : SetOpenTerm [] := numₘ(left + right)
  have hTraceMapping : ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ :=
    standard_numeral_trace_mapping S (fun i => right + i) left
  have hInitial : ([] : Context signature []) ⊢ₘ[T]
      (trace ·ₘ ∅ₘ) ≐ₘ numₘ(right) := by
    simpa [trace, elements, standard_addition_trace_elements, finite_numeral_term] using!
      (standard_numeral_trace_value (Γ := []) S.toFiniteSequenceEvaluationSupport
        (fun i => right + i) left 0 (Nat.zero_le _))
  have hStep : ([] : Context signature []) ⊢ₘ[T]
      standard_addition_trace_step_formula left right :=
    standard_addition_trace_step_forall S left right
  have hTerminal : ([] : Context signature []) ⊢ₘ[T]
      trace ·ₘ numₘ(left) ≐ₘ result := by
    simpa [trace, elements, result, standard_addition_trace_elements, Nat.add_comm] using!
      (standard_numeral_trace_value (Γ := []) S.toFiniteSequenceEvaluationSupport
        (fun i => right + i) left left (Nat.le_refl _))
  have hGraph : ([] : Context signature []) ⊢ₘ[T]
      natural_addition_graph_condition
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) result trace := by
    change ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ ∧ₘ
        ((trace ·ₘ ∅ₘ ≐ₘ (numₘ(right) : SetOpenTerm [])) ∧ₘ
          (standard_addition_trace_step_formula left right ∧ₘ
            (trace ·ₘ (numₘ(left) : SetOpenTerm []) ≐ₘ result)))
    exact FirstOrder.Derives.conj_intro hTraceMapping <|
      FirstOrder.Derives.conj_intro hInitial <|
        FirstOrder.Derives.conj_intro hStep hTerminal
  have hResultOmega : ([] : Context signature []) ⊢ₘ[T]
      result ∈ₘ ωₘ := by
    simpa [result] using S.finite_numeral_mem_omega (left + right)
  have hSpec : ([] : Context signature []) ⊢ₘ[T]
      natural_addition_spec
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) result := by
    unfold natural_addition_spec natural_addition_bound_graph_condition
    apply FirstOrder.Derives.conj_intro hResultOmega
    apply FirstOrder.Derives.existsFreePrefix_intro (.cons trace .nil)
    simpa [Arguments.substitutionWith, Formula.substituteFree,
      Substitution.free_map, Formula.substitute, Formula.substituteMapped,
      Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.liftFree, natural_addition_graph_condition,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_id,
      Formula.instantiateFreeTop_forallFreeTop, result] using! hGraph
  exact FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.imp_elim
      (S.addition_definition_instance_derives (numₘ(left)) (numₘ(right)) result)
      (FirstOrder.Derives.conj_intro
        (S.finite_numeral_mem_omega left) (S.finite_numeral_mem_omega right))) hSpec

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC

