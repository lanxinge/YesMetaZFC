import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomain

/-!
# 内在有限序列的定义域语义

本层只把有限图成员反演接到关系定义域接口；不重新展开分离规格，也不引入旧式
良构、自由支撑或变量编号证明。有效下标的定义域成员性由列表取值证书直接给出。
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

private theorem standard_sequence_pair_condition_index_mem
    {T : SetTheory} (A : ArithmeticSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (index value : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      standard_sequence_pair_member_condition
        start elements index value ⟶ₘ
        (index ∈ₘ numₘ(start + elements.length)) := by
  induction elements generalizing start Γ with
  | nil =>
      apply FirstOrder.Derives.imp_intro
      exact FirstOrder.Derives.falsum_elim
        (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head tail ih =>
      let headCondition : SetOpenFormula free :=
        (index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)
      let tailCondition : SetOpenFormula free :=
        standard_sequence_pair_member_condition
          (start + 1) tail index value
      change
        Γ ⊢ₘ[T] (headCondition ∨ₘ tailCondition) ⟶ₘ
          (index ∈ₘ numₘ(start + (head :: tail).length))
      apply FirstOrder.Derives.imp_intro
      let Δ : Context signature free :=
        (headCondition ∨ₘ tailCondition) :: Γ
      have hCases : Δ ⊢ₘ[T] headCondition ∨ₘ tailCondition :=
        FirstOrder.Derives.assumption List.mem_cons_self
      apply FirstOrder.Derives.disj_elim hCases
      · have hHead : headCondition :: Δ ⊢ₘ[T] headCondition :=
          FirstOrder.Derives.assumption List.mem_cons_self
        have hIndexEquality := FirstOrder.Derives.conj_elim_left hHead
        have hNumeralMember : headCondition :: Δ ⊢ₘ[T]
            numₘ(start) ∈ₘ numₘ(start + (head :: tail).length) := by
          apply FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature free))
            (Δ := headCondition :: Δ)
            (by simp)
          exact numeral_mem_of_lt A.contains_successor (by
            simp only [List.length_cons]
            omega)
        exact FirstOrder.Derives.iff_elim_right
          (membership_left_iff_of_equality
            (index) (numₘ(start))
            (numₘ(start + (head :: tail).length))
            hIndexEquality)
          hNumeralMember
      · have hTail : tailCondition :: Δ ⊢ₘ[T] tailCondition :=
          FirstOrder.Derives.assumption List.mem_cons_self
        have hTailResult := FirstOrder.Derives.imp_elim
          (ih (Γ := tailCondition :: Δ) (start + 1))
          hTail
        simpa [Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hTailResult

theorem standard_sequence_from_domain_mem_implies_numeral_mem
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (index : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (index ∈ₘ domₘ(standard_sequence_from start elements)) ⟶ₘ
        (index ∈ₘ numₘ(start + elements.length)) := by
  let sequence : SetOpenTerm free :=
    standard_sequence_from start elements
  let domainMembership : SetOpenFormula free :=
    index ∈ₘ domₘ(sequence)
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := domainMembership :: Γ
  have hDomainMembership : Δ ⊢ₘ[T] domainMembership :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hRelation : Δ ⊢ₘ[T] is_relation_formula sequence := by
    apply FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) (by
        intro candidate hCandidate
        simp [Δ, domainMembership, hCandidate])
    simpa [sequence] using
      (standard_sequence_from_is_relation (Γ := Γ) S start elements)
  have hDomainIff : Δ ⊢ₘ[T]
      domainMembership ↔ₘ
        ((index ∈ₘ double_union_term sequence) ∧ₘ
          relation_domain_member_condition sequence index) := by
    have hRule := FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_predicate
        (relation_domain_operator_theory_subset_function_predicate_theory
          hSentence))
      (is_relation_domain_member_iff (Γ := Γ) sequence index)
    have hRule' := FirstOrder.Derives.context_weaken_cons
      (assumption := domainMembership) hRule
    exact FirstOrder.Derives.imp_elim hRule' hRelation
  have hCoordinate : Δ ⊢ₘ[T]
      relation_domain_member_condition sequence index :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.iff_elim_left
        hDomainIff hDomainMembership)
  unfold relation_domain_member_condition
    relation_coordinate_member_condition at hCoordinate
  apply FirstOrder.Derives.exists_elim hCoordinate
  let liftedElements : List (SetOpenTerm (SetSort.set :: free)) :=
    elements.map (fun element => element.weakenFree SetSort.set)
  let sequenceLift : SetOpenTerm (SetSort.set :: free) :=
    standard_sequence_from start liftedElements
  let pair : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  let pairBody : SetOpenFormula (SetSort.set :: free) :=
    (pair ∈ₘ sequence.weakenFree SetSort.set) ∧ₘ
      (index.weakenFree SetSort.set ≐ₘ
        relation_coordinate_projection_term RelationCoordinate.domain pair)
  let Ξ : Context signature (SetSort.set :: free) :=
    pairBody :: FreshVariable.extendContext SetSort.set Δ
  have hPairBody : Ξ ⊢ₘ[T] pairBody :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hPairMember : Ξ ⊢ₘ[T] pair ∈ₘ sequenceLift := by
    simpa [pairBody, sequenceLift, sequence, liftedElements] using
      (FirstOrder.Derives.conj_elim_left hPairBody)
  have hIndexProjection : Ξ ⊢ₘ[T]
      index.weakenFree SetSort.set ≐ₘ (pair)₀ₘ :=
    by
      simpa [pairBody, relation_coordinate_projection_term] using
        (FirstOrder.Derives.conj_elim_right hPairBody)
  have hLiftedRelation : Ξ ⊢ₘ[T] is_relation_formula sequenceLift := by
    simpa [sequenceLift, liftedElements] using
      (standard_sequence_from_is_relation
        (Γ := Ξ) S start liftedElements)
  have hOrderedRule : Ξ ⊢ₘ[T]
      is_relation_formula sequenceLift ⟶ₘ
        (pair ∈ₘ sequenceLift) ⟶ₘ
          is_ordered_pair_formula pair :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_predicate
        (relation_predicate_theory_subset_function_predicate_theory
          hSentence))
      (is_relation_member_is_ordered_pair
        (Γ := Ξ) sequenceLift pair)
  have hOrdered := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim hOrderedRule hLiftedRelation)
    hPairMember
  have hPairRepresentation : Ξ ⊢ₘ[T]
      pair ≐ₘ ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.theory_weaken
        (show Theory.Extends T right_projection_operator_theory from by
          intro sentence hSentence; apply S.contains_function_predicate; theory_inclusion)
        (is_ordered_pair_eq_ordered_pair_projections
          (Γ := Ξ) pair))
      hOrdered
  have hExplicitMember : Ξ ⊢ₘ[T]
      (⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ ∈ₘ sequenceLift) :=
    FirstOrder.Derives.iff_elim_left
      (membership_left_iff_of_equality
        pair ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ sequenceLift
        hPairRepresentation)
      hPairMember
  have hPairCondition : Ξ ⊢ₘ[T]
      standard_sequence_pair_member_condition
        start liftedElements (pair)₀ₘ (pair)₁ₘ :=
    FirstOrder.Derives.iff_elim_left
      (standard_sequence_from_pair_member_iff
        (Γ := Ξ) S start (elements := liftedElements)
          (pair)₀ₘ (pair)₁ₘ)
      hExplicitMember
  have hProjectionBound :=
    standard_sequence_pair_condition_index_mem
      (Γ := Ξ) S.toArithmeticSupport start
        (elements := liftedElements) (pair)₀ₘ (pair)₁ₘ
  have hBound := FirstOrder.Derives.imp_elim
    hProjectionBound hPairCondition
  have hResult := FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality
      (index.weakenFree SetSort.set) (pair)₀ₘ
        ((numₘ(start + elements.length)).weakenFree SetSort.set)
        hIndexProjection)
    (by simpa [liftedElements] using hBound)
  change Ξ ⊢ₘ[T]
    (index ∈ₘ numₘ(start + elements.length)).weakenFree SetSort.set
  exact hResult

/-! ## 有效点进入定义域 -/

theorem standard_sequence_from_getElem?_domain_mem
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    {index : Nat} {element : SetOpenTerm free}
    (hGet : elements[index]? = some element) :
    Γ ⊢ₘ[T]
      numₘ(start + index) ∈ₘ
        domₘ(standard_sequence_from start elements) := by
  let sequence : SetOpenTerm free :=
    standard_sequence_from start elements
  let input : SetOpenTerm free := numₘ(start + index)
  have hRelation : Γ ⊢ₘ[T] is_relation_formula sequence := by
    simpa [sequence] using
      (standard_sequence_from_is_relation (Γ := Γ) S start elements)
  have hGraph : Γ ⊢ₘ[T]
      (⟨input, element⟩ₘ ∈ₘ sequence) := by
    simpa [sequence, input] using
      (standard_sequence_from_getElem?_graph_mem
        (Γ := Γ) S start hGet)
  have hCoordinateRule : Γ ⊢ₘ[T]
      is_relation_formula sequence ⟶ₘ
        ((⟨input, element⟩ₘ ∈ₘ sequence) ⟶ₘ
          (input ∈ₘ domₘ(sequence))) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_predicate hSentence)
      (relation_member_left_coordinate_mem_domain
        (Γ := Γ) sequence input element)
  have hGraphDomain : Γ ⊢ₘ[T]
      (⟨input, element⟩ₘ ∈ₘ sequence) ⟶ₘ
        (input ∈ₘ domₘ(sequence)) :=
    FirstOrder.Derives.imp_elim hCoordinateRule hRelation
  simpa [sequence, input] using
    (FirstOrder.Derives.imp_elim hGraphDomain hGraph)

theorem standard_sequence_from_index_domain_mem_of_lt
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (index : Nat) (hIndex : index < elements.length) :
    Γ ⊢ₘ[T]
      numₘ(start + index) ∈ₘ
        domₘ(standard_sequence_from start elements) := by
  have hGet : elements[index]? = some elements[index] :=
    List.getElem?_eq_getElem hIndex
  exact standard_sequence_from_getElem?_domain_mem
    (Γ := Γ) S start hGet

/-- 从零开始的规范有限图定义域恰为其外部列表区间。 -/
theorem standard_sequence_domain_eq
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    {elements : List (SetOpenTerm free)} :
    Γ ⊢ₘ[T]
      domₘ(standard_sequence elements) ≐ₘ numₘ(elements.length) := by
  let Γ' : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Γ
  let index : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  let liftedElements : List (SetOpenTerm (SetSort.set :: free)) :=
    elements.map (fun element => element.weakenFree SetSort.set)
  let sequenceLift : SetOpenTerm (SetSort.set :: free) :=
    standard_sequence liftedElements
  let length : Nat := elements.length
  have hForward : Γ' ⊢ₘ[T]
      (index ∈ₘ domₘ(sequenceLift)) ⟶ₘ
        (index ∈ₘ numₘ(length)) := by
    simpa [Γ', index, sequenceLift, liftedElements, length] using
      (standard_sequence_from_domain_mem_implies_numeral_mem
        (Γ := Γ') S 0
          (elements := liftedElements) index)
  have hReverse : Γ' ⊢ₘ[T]
      (index ∈ₘ numₘ(length)) ⟶ₘ
        (index ∈ₘ domₘ(sequenceLift)) := by
    apply FirstOrder.Derives.imp_intro
    let Δ : Context signature (SetSort.set :: free) :=
      (index ∈ₘ numₘ(length)) :: Γ'
    have hIndex : Δ ⊢ₘ[T] index ∈ₘ numₘ(length) :=
      FirstOrder.Derives.assumption List.mem_cons_self
    apply (ArithmeticSupport.finite_core S.toArithmeticSupport).member_elim
      length index (index ∈ₘ domₘ(sequenceLift)) hIndex
    intro coordinate hCoordinate
    let Ε : Context signature (SetSort.set :: free) :=
      (index ≐ₘ numₘ(coordinate)) :: Δ
    have hIndexEquality : Ε ⊢ₘ[T]
        index ≐ₘ numₘ(coordinate) :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hCoordinateDomain : Ε ⊢ₘ[T]
        numₘ(coordinate) ∈ₘ domₘ(sequenceLift) := by
      apply FirstOrder.Derives.context_weaken
        (Γ := Γ') (Δ := Ε) (by
          intro formula hFormula
          simp [Ε, Δ, hFormula])
      simpa [sequenceLift, liftedElements, length] using
        (standard_sequence_from_index_domain_mem_of_lt
            (Γ := Γ') S 0
            (elements := liftedElements) coordinate
            (by simpa [length, liftedElements] using hCoordinate))
    exact FirstOrder.Derives.iff_elim_right
      (membership_left_iff_of_equality
        index (numₘ(coordinate)) (domₘ(sequenceLift)) hIndexEquality)
      hCoordinateDomain
  have hPoint : Γ' ⊢ₘ[T]
      (index ∈ₘ domₘ(sequenceLift)) ↔ₘ
        (index ∈ₘ numₘ(length)) :=
    FirstOrder.Derives.iff_intro hForward hReverse
  have hAgreement : Γ ⊢ₘ[T]
      membership_agreement
        (domₘ(standard_sequence elements))
        (numₘ(elements.length)) := by
    unfold membership_agreement
    apply FirstOrder.Derives.forall_intro
    simpa [Γ', index, sequenceLift, liftedElements, length,
      standard_sequence_from_weakenFree,
      finite_numeral_term_weakenFree] using! hPoint
  have hExtensionality : Γ ⊢ₘ[T]
      extensionality_instance
        (domₘ(standard_sequence elements))
        (numₘ(elements.length)) := by
    exact FirstOrder.Derives.theory_weaken
      (show Theory.Extends T extensionality_theory from by
        intro sentence hSentence; apply S.contains_function_predicate; theory_inclusion)
      (extensionality_instance_derives
        (Γ := Γ)
        (domₘ(standard_sequence elements))
        (numₘ(elements.length)))
  exact FirstOrder.Derives.imp_elim hExtensionality hAgreement

/-! ## 有效点的函数值 -/

theorem standard_sequence_from_getElem?_apply_eq
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    {index : Nat} {element : SetOpenTerm free}
    (hGet : elements[index]? = some element) :
    Γ ⊢ₘ[T]
      element ≐ₘ
        (standard_sequence_from start elements ·ₘ
          numₘ(start + index)) := by
  let sequence : SetOpenTerm free :=
    standard_sequence_from start elements
  let input : SetOpenTerm free := numₘ(start + index)
  have hFunction : Γ ⊢ₘ[T] is_function_formula sequence := by
    simpa [sequence] using
      (standard_sequence_from_is_function
        (Γ := Γ) S.toFiniteSequenceGraphSupport start elements)
  have hDomain : Γ ⊢ₘ[T] input ∈ₘ domₘ(sequence) := by
    simpa [sequence, input] using
      (standard_sequence_from_getElem?_domain_mem
        (Γ := Γ) S.toFiniteSequenceGraphSupport start hGet)
  have hGraph : Γ ⊢ₘ[T]
      (⟨input, element⟩ₘ ∈ₘ sequence) := by
    simpa [sequence, input] using
      (standard_sequence_from_getElem?_graph_mem
        (Γ := Γ) S.toFiniteSequenceGraphSupport start hGet)
  have hContract : Γ ⊢ₘ[T]
      (is_function_formula sequence ∧ₘ
        (input ∈ₘ domₘ(sequence))) ⟶ₘ
        ((element ≐ₘ (sequence ·ₘ input)) ↔ₘ
          (⟨input, element⟩ₘ ∈ₘ sequence)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application hSentence)
      (function_application_eq_iff_graph
        (Γ := Γ) sequence input element)
  have hIff := FirstOrder.Derives.imp_elim hContract
    (FirstOrder.Derives.conj_intro hFunction hDomain)
  simpa [sequence, input] using
    (FirstOrder.Derives.iff_elim_right hIff hGraph)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
