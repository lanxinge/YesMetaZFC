import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSpaceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-!
# 有限序列构造的公共推导

列表查找、定义域运输和值域证明只依赖有限图合同，不依赖具体编码的行规格。
这些接口处理外部有限列表；列表中的对象项仍可表示任意模型内部自然数。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols Symbols

set_option autoImplicit false

/-- 有限定义域等式下，外部有效索引属于对象定义域。 -/
theorem row_index_mem_of_domain
    {T : SetTheory}
    (A : ArithmeticSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence : SetOpenTerm free)
    (length index : Nat)
    (hDomain : Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(length))
    (hIndex : index < length) :
    Γ ⊢ₘ[T] numₘ(index) ∈ₘ domₘ(sequence) := by
  have hNumeralMember :
      Γ ⊢ₘ[T] numₘ(index) ∈ₘ numₘ(length) :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature free))
      (Δ := Γ)
      (by simp)
      (numeral_mem_of_lt A.contains_successor hIndex)
  exact FirstOrder.Derives.iff_elim_right
    (membership_right_iff_of_equality
      (numₘ(index)) (domₘ(sequence)) (numₘ(length)) hDomain)
    hNumeralMember

/-- 按列表查找计算规范有限图的值，等式方向固定为图值在左。 -/
theorem standard_sequence_getElem?_value
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    {elements : List (SetOpenTerm free)} {index : Nat} {element : SetOpenTerm free}
    (hGet : elements[index]? = some element) :
    Γ ⊢ₘ[T] (standard_sequence elements ·ₘ numₘ(index)) ≐ₘ element := by
  simpa only [standard_sequence, Nat.zero_add] using
    FirstOrder.Derives.eq_symm (standard_sequence_from_getElem?_apply_eq S 0 hGet)

/-- 映射后的列表查找统一经过同一个有限图求值定理。 -/
theorem standard_sequence_map_value
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    {α : Type} (encode : α → SetOpenTerm free)
    {elements : List α} {index : Nat} {element : α}
    (hGet : elements[index]? = some element) :
    Γ ⊢ₘ[T]
      (standard_sequence (elements.map encode) ·ₘ numₘ(index)) ≐ₘ encode element := by
  apply standard_sequence_getElem?_value S
  simpa only [List.getElem?_map, Option.map_some] using congrArg (Option.map encode) hGet

/-- 有限图上的有界全称只要求各标准位置的实例。 -/
theorem standard_sequence_forall_intro
    {T : SetTheory} (C : FiniteCore T) (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free)) (body : SetFormula [SetSort.set] free)
    (hRows : ∀ index, index < elements.length →
      Γ ⊢ₘ[T] body.instantiateTop (numₘ(index))) :
    Γ ⊢ₘ[T] Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(standard_sequence elements)) body :=
  bounded_forall_of_bound_eq (standard_sequence_domain_eq S)
    (bounded_forall_numeral_intro C elements.length body hRows)

/-- 值域成员证明随列表求值传输，无须各编码构造重复处理 binder。 -/
theorem standard_sequence_values_mem
    {T : SetTheory} (C : FiniteCore T) (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free)) (bound : SetOpenTerm free)
    (hValues : ∀ element, element ∈ elements → Γ ⊢ₘ[T] element ∈ₘ bound) :
    Γ ⊢ₘ[T] Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(standard_sequence elements))
      (((standard_sequence elements).weakenBound SetSort.set ·ₘ
        (.bvar .here : SetTerm [SetSort.set] free)) ∈ₘ
        bound.weakenBound SetSort.set) := by
  apply standard_sequence_forall_intro C S.toFiniteSequenceGraphSupport
  intro index hIndex
  have hValue := standard_sequence_getElem?_value (Γ := Γ) S
    (List.getElem?_eq_getElem hIndex)
  have hMember := FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality _ _ bound hValue)
    (hValues elements[index] (List.getElem_mem hIndex))
  rw [Formula.instantiateTop_rel]
  simp only [Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_app,
    Term.instantiateTop_weakenBound]
  rw [Term.instantiateTop_bvar_here]
  exact hMember

/-- 轨迹比输入多一个位置时，两图的定义域相差一个后继。 -/
theorem standard_sequence_trace_domain
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements trace : List (SetOpenTerm free))
    (hLength : trace.length = elements.length + 1) :
    Γ ⊢ₘ[T] domₘ(standard_sequence trace) ≐ₘ
      Sₘ(domₘ(standard_sequence elements)) := by
  have hTrace : Γ ⊢ₘ[T] domₘ(standard_sequence trace) ≐ₘ
      Sₘ(numₘ(elements.length)) := by
    simpa only [hLength, finite_numeral_term, successor_term] using
      (standard_sequence_domain_eq (Γ := Γ) S (elements := trace))
  exact Metatheory.Derives.equality_trans hTrace
    (FirstOrder.Derives.eq_symm (successor_term_congr_of_equality _ _
      (standard_sequence_domain_eq S (elements := elements))))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
