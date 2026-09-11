import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSemantics

/-!
# 内在有限序列的值域与映射语义

本模块把规范有限图的值域约束和映射构造下沉到有限序列求值合同。证明只消费
函数图、关系投影与函数应用定义，不要求无穷公理、算术运算或 Quine 编码。
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

private theorem standard_sequence_pair_condition_value_mem
    {T : SetTheory}
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (target index value : SetOpenTerm free)
    (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target) :
    Γ ⊢ₘ[T]
      standard_sequence_pair_member_condition
        start elements index value ⟶ₘ value ∈ₘ target := by
  induction elements generalizing start Γ with
  | nil =>
      apply FirstOrder.Derives.imp_intro
      exact FirstOrder.Derives.falsum_elim
        (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head tail ih =>
      let headCase : SetOpenFormula free :=
        (index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)
      let tailCase : SetOpenFormula free :=
        standard_sequence_pair_member_condition
          (start + 1) tail index value
      have hHead : Γ ⊢ₘ[T] headCase ⟶ₘ value ∈ₘ target := by
        apply FirstOrder.Derives.imp_intro
        let Δ : Context signature free := headCase :: Γ
        have hHeadCase : Δ ⊢ₘ[T] headCase :=
          FirstOrder.Derives.assumption List.mem_cons_self
        have hValue : Δ ⊢ₘ[T] value ≐ₘ head :=
          FirstOrder.Derives.conj_elim_right hHeadCase
        have hTarget : Δ ⊢ₘ[T] head ∈ₘ target :=
          FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := Δ) (by
              intro candidate hCandidate
              exact List.mem_cons_of_mem headCase hCandidate)
            (hTargetMember head (by simp))
        exact FirstOrder.Derives.iff_elim_right
          (membership_left_iff_of_equality value head target hValue)
          hTarget
      have hTail : Γ ⊢ₘ[T] tailCase ⟶ₘ value ∈ₘ target := by
        have hTailMember : ∀ element, element ∈ tail →
            Γ ⊢ₘ[T] element ∈ₘ target := by
          intro element hElement
          exact hTargetMember element (by simp [hElement])
        simpa [tailCase] using
          ih (start + 1) hTailMember
      apply FirstOrder.Derives.imp_intro
      let source : SetOpenFormula free := headCase ∨ₘ tailCase
      let Δ : Context signature free := source :: Γ
      have hSource : Δ ⊢ₘ[T] source :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hCases : Δ ⊢ₘ[T] headCase ∨ₘ tailCase := by
        simpa [source] using hSource
      apply FirstOrder.Derives.disj_elim hCases
      · exact FirstOrder.Derives.imp_elim
          (hHead.context_weaken_prefix
            (initial := [headCase, source]))
          (FirstOrder.Derives.assumption List.mem_cons_self)
      · exact FirstOrder.Derives.imp_elim
          (hTail.context_weaken_prefix
            (initial := [tailCase, source]))
          (FirstOrder.Derives.assumption List.mem_cons_self)

private theorem standard_sequence_from_graph_value_mem
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (target index value : SetOpenTerm free)
    (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target)
    (hGraph : Γ ⊢ₘ[T]
      ⟨index, value⟩ₘ ∈ₘ standard_sequence_from start elements) :
    Γ ⊢ₘ[T] value ∈ₘ target := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (standard_sequence_from_pair_member_iff
      (Γ := Γ) S start (elements := elements) index value)
    hGraph
  exact FirstOrder.Derives.imp_elim
    (standard_sequence_pair_condition_value_mem
      (Γ := Γ) start (elements := elements) target index value
      hTargetMember)
    hCondition

theorem standard_sequence_from_range_subset
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (target : SetOpenTerm free)
    (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target) :
    Γ ⊢ₘ[T] ranₘ(standard_sequence_from start elements) ⊆ₘ target := by
  let sequence : SetOpenTerm free :=
    standard_sequence_from start elements
  let elements₁ : List (SetOpenTerm (SetSort.set :: free)) :=
    elements.map (fun element => element.weakenFree SetSort.set)
  let sequence₁ : SetOpenTerm (SetSort.set :: free) :=
    sequence.weakenFree SetSort.set
  let target₁ : SetOpenTerm (SetSort.set :: free) :=
    target.weakenFree SetSort.set
  apply subset_intro
    (fun {sentence} hSentence =>
      S.contains_function_predicate
        (relation_plane_theory_subset_function_predicate_theory
          (subset_theory_subset_relation_plane_theory hSentence)))
    (ranₘ(sequence)) target
  let Γ₁ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Γ
  let value₁ : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  change Γ₁ ⊢ₘ[T]
    (value₁ ∈ₘ ranₘ(sequence₁)) ⟶ₘ
      (value₁ ∈ₘ target₁)
  apply FirstOrder.Derives.imp_intro
  let membership₁ : SetOpenFormula (SetSort.set :: free) :=
    value₁ ∈ₘ ranₘ(sequence₁)
  let Δ₁ : Context signature (SetSort.set :: free) :=
    membership₁ :: Γ₁
  have hMembership : Δ₁ ⊢ₘ[T] membership₁ :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hRelation : Δ₁ ⊢ₘ[T] is_relation_formula sequence₁ := by
    have hBase : Γ₁ ⊢ₘ[T] is_relation_formula sequence₁ := by
      simpa [sequence₁, sequence, elements₁,
        standard_sequence_from_weakenFree] using
        (standard_sequence_from_is_relation
          (Γ := Γ₁) S.toFiniteSequenceGraphSupport start elements₁)
    exact FirstOrder.Derives.context_weaken_cons hBase
  have hRangeRule : Γ₁ ⊢ₘ[T]
      is_relation_formula sequence₁ ⟶ₘ
        ((value₁ ∈ₘ ranₘ(sequence₁)) ↔ₘ
          ((value₁ ∈ₘ double_union_term sequence₁) ∧ₘ
            relation_range_member_condition sequence₁ value₁)) := by
    simpa using
      (FirstOrder.Derives.theory_weaken
        (show Theory.Extends T relation_range_operator_theory from by
          intro sentence hSentence; apply S.contains_function_predicate; theory_inclusion)
        (is_relation_range_member_iff
          (Γ := Γ₁) sequence₁ value₁))
  have hRangeIff : Δ₁ ⊢ₘ[T]
      (value₁ ∈ₘ ranₘ(sequence₁)) ↔ₘ
        ((value₁ ∈ₘ double_union_term sequence₁) ∧ₘ
          relation_range_member_condition sequence₁ value₁) :=
    FirstOrder.Derives.imp_elim
      (hRangeRule.context_weaken_cons) hRelation
  have hRangeCondition : Δ₁ ⊢ₘ[T]
      relation_range_member_condition sequence₁ value₁ :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.iff_elim_left hRangeIff hMembership)
  unfold relation_range_member_condition
    relation_coordinate_member_condition at hRangeCondition
  apply FirstOrder.Derives.exists_elim hRangeCondition
  let elements₂ : List
      (SetOpenTerm (SetSort.set :: (SetSort.set :: free))) :=
    elements₁.map (fun element => element.weakenFree SetSort.set)
  let sequence₂ : SetOpenTerm
      (SetSort.set :: (SetSort.set :: free)) :=
    sequence₁.weakenFree SetSort.set
  let target₂ : SetOpenTerm
      (SetSort.set :: (SetSort.set :: free)) :=
    target₁.weakenFree SetSort.set
  let value₂ : SetOpenTerm
      (SetSort.set :: (SetSort.set :: free)) :=
    value₁.weakenFree SetSort.set
  let pair : SetOpenTerm (SetSort.set :: (SetSort.set :: free)) :=
    FreshVariable.newest (σ := signature)
      (free := SetSort.set :: free) SetSort.set
  let pairBody : SetOpenFormula
      (SetSort.set :: (SetSort.set :: free)) :=
    (pair ∈ₘ sequence₂) ∧ₘ
      (value₂ ≐ₘ
        relation_coordinate_projection_term
          RelationCoordinate.range pair)
  let Γ₂ : Context signature
      (SetSort.set :: (SetSort.set :: free)) :=
    FreshVariable.extendContext SetSort.set Γ₁
  let membership₂ : SetOpenFormula
      (SetSort.set :: (SetSort.set :: free)) :=
    membership₁.weakenFree SetSort.set
  let Ξ : Context signature (SetSort.set :: (SetSort.set :: free)) :=
    pairBody :: membership₂ :: Γ₂
  change Ξ ⊢ₘ[T] value₂ ∈ₘ target₂
  have hPairBody : Ξ ⊢ₘ[T] pairBody :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hPairMember : Ξ ⊢ₘ[T] pair ∈ₘ sequence₂ :=
    FirstOrder.Derives.conj_elim_left hPairBody
  have hPairRelation : Ξ ⊢ₘ[T] is_relation_formula sequence₂ := by
    simpa [sequence₂, sequence₁, sequence, elements₂, elements₁,
      standard_sequence_from_weakenFree] using
      (standard_sequence_from_is_relation
        (Γ := Ξ) S.toFiniteSequenceGraphSupport start
        elements₂)
  have hOrderedRule : Ξ ⊢ₘ[T]
      is_relation_formula sequence₂ ⟶ₘ
        (pair ∈ₘ sequence₂) ⟶ₘ
          is_ordered_pair_formula pair :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_predicate
        (relation_predicate_theory_subset_function_predicate_theory hSentence))
      (is_relation_member_is_ordered_pair
        (Γ := Ξ)
        ((sequence.weakenFree SetSort.set).weakenFree SetSort.set) pair)
  have hOrdered : Ξ ⊢ₘ[T] is_ordered_pair_formula pair :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hOrderedRule hPairRelation)
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
      ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ ∈ₘ sequence₂ :=
    FirstOrder.Derives.iff_elim_left
      (membership_left_iff_of_equality
        pair ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ
        sequence₂ hPairRepresentation)
      hPairMember
  have hTargetMember' : ∀ element, element ∈
      elements₂ → Ξ ⊢ₘ[T] element ∈ₘ target₂ := by
    intro element hElement
    rcases List.mem_map.mp hElement with ⟨element₁, hElement₁, rfl⟩
    rcases List.mem_map.mp hElement₁ with ⟨item, hItem, rfl⟩
    have hFirst : Γ₁ ⊢ₘ[T]
        item.weakenFree SetSort.set ∈ₘ target₁ := by
      simpa only [Γ₁, target₁, FreshVariable.extendContext,
        Formula.weakenFree, Formula.renameFree, Renaming.weakenFree] using!
        FirstOrder.Derives.free_renaming
          (T := T) (VariableRenaming.weaken SetSort.set)
          (hTargetMember item hItem)
    have hSecond : Γ₂ ⊢ₘ[T]
        (item.weakenFree SetSort.set).weakenFree SetSort.set ∈ₘ target₂ := by
      simpa only [Γ₂, target₂, FreshVariable.extendContext,
        Formula.weakenFree, Formula.renameFree, Renaming.weakenFree] using!
        FirstOrder.Derives.free_renaming
          (T := T) (VariableRenaming.weaken SetSort.set) hFirst
    exact FirstOrder.Derives.context_weaken
      (Γ := Γ₂) (Δ := Ξ)
      (by
        intro formula hFormula
        exact List.mem_cons_of_mem pairBody
          (List.mem_cons_of_mem membership₂ hFormula))
      hSecond
  have hValueTarget : Ξ ⊢ₘ[T] (pair)₁ₘ ∈ₘ target₂ :=
    standard_sequence_from_graph_value_mem
      (Γ := Ξ) S.toFiniteSequenceGraphSupport start
      (elements := elements₂) target₂
      (pair)₀ₘ (pair)₁ₘ hTargetMember' (by
        simpa [sequence₂, sequence₁, sequence, elements₂, elements₁,
          standard_sequence_from_weakenFree] using hExplicitMember)
  have hValueEquality : Ξ ⊢ₘ[T] value₂ ≐ₘ (pair)₁ₘ := by
    simpa [pairBody, relation_coordinate_projection_term] using
      (FirstOrder.Derives.conj_elim_right hPairBody)
  exact FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality
      value₂ (pair)₁ₘ target₂ hValueEquality)
    hValueTarget

theorem standard_sequence_from_is_mapping
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (source target : SetOpenTerm free)
    (hDomainEquality : Γ ⊢ₘ[T]
      source ≐ₘ domₘ(standard_sequence_from start elements))
    (hTargetMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ target) :
    Γ ⊢ₘ[T]
      is_mapping_formula (standard_sequence_from start elements)
        source target := by
  have hFunction : Γ ⊢ₘ[T]
      is_function_formula (standard_sequence_from start elements) :=
    standard_sequence_from_is_function
      (Γ := Γ) S.toFiniteSequenceGraphSupport start elements
  have hRangeSubset : Γ ⊢ₘ[T]
      ranₘ(standard_sequence_from start elements) ⊆ₘ target :=
    standard_sequence_from_range_subset
      (Γ := Γ) S start target hTargetMember
  have hCondition : Γ ⊢ₘ[T]
      is_mapping_condition
        (standard_sequence_from start elements) source target :=
    FirstOrder.Derives.conj_intro hFunction <|
      FirstOrder.Derives.conj_intro hDomainEquality hRangeSubset
  have hDefinition : Γ ⊢ₘ[T]
      is_mapping_formula (standard_sequence_from start elements)
          source target ↔ₘ
        is_mapping_condition
          (standard_sequence_from start elements) source target :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application
        (mapping_predicate_theory_subset_function_application_theory
          hSentence))
      (is_mapping_iff_condition
        (Γ := Γ) (standard_sequence_from start elements) source target)
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
