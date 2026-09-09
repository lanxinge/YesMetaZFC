import YesMetaZFC.Logic.FirstOrder.Hilbert.Equivalence
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction.Derived
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceGraph

/-!
# 内在有限序列的成员反演

本模块把规范有限图的成员关系直接反演为外部列表上的析取条件。列表、项、公式和
理论合同均由类型携带；这里不再引入旧层的 `Admissible`、裸变量编号或兼容桥接。
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

/-! ## 外部有限条件 -/

/-- 标准有限图的成员条件。 -/
def standard_sequence_member_condition {free : SetContext} (start : Nat) :
    List (SetOpenTerm free) → SetOpenTerm free → SetOpenFormula free :=
  fun elements member =>
    match elements with
    | [] => .falsum
    | element :: rest =>
        (member ≐ₘ ⟨numₘ(start), element⟩ₘ) ∨ₘ
          standard_sequence_member_condition (start + 1) rest member

/-- 标准有限图的坐标成员条件。 -/
def standard_sequence_pair_member_condition {free : SetContext} (start : Nat) :
    List (SetOpenTerm free) → SetOpenTerm free → SetOpenTerm free →
      SetOpenFormula free :=
  fun elements index value =>
    match elements with
    | [] => .falsum
    | element :: rest =>
        ((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ element)) ∨ₘ
          standard_sequence_pair_member_condition
            (start + 1) rest index value

namespace FiniteSequenceSemantics

private theorem empty_member_iff_falsum
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (member : SetOpenTerm free) :
    Γ ⊢ₘ[T] (member ∈ₘ (∅ₘ : SetOpenTerm free)) ↔ₘ
      (.falsum : SetOpenFormula free) := by
  have hEmpty : Γ ⊢ₘ[T] ¬ₘ (member ∈ₘ (∅ₘ : SetOpenTerm free)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_empty_set hSentence)
      (empty_set_term_has_no_members (Γ := Γ) member)
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.neg_elim
      (FirstOrder.Derives.assumption List.mem_cons_self)
      (FirstOrder.Derives.context_weaken_cons hEmpty)
  · exact FirstOrder.Derives.falsum_elim
      (FirstOrder.Derives.assumption List.mem_cons_self)

private theorem binary_union_member_iff_of_support
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right member : SetOpenTerm free) :
    Γ ⊢ₘ[T] (member ∈ₘ (left ∪ₘ right)) ↔ₘ
      ((member ∈ₘ left) ∨ₘ (member ∈ₘ right)) := by
  have hSpec : Γ ⊢ₘ[T]
      binary_union_spec left right (left ∪ₘ right) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_binary_union hSentence)
      (binary_union_term_spec_derives (Γ := Γ) left right)
  exact binary_union_spec_membership_iff
    left right (left ∪ₘ right) member hSpec

private theorem singleton_member_iff_of_support
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (element member : SetOpenTerm free) :
    Γ ⊢ₘ[T] (member ∈ₘ {element}ₘ) ↔ₘ (member ≐ₘ element) := by
  have hSpec : Γ ⊢ₘ[T]
      singleton_spec element {element}ₘ :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_ordered_pair <|
        singleton_operator_theory_subset_ordered_pair_operator_theory
          hSentence)
      (singleton_term_spec_derives (Γ := Γ) element)
  exact singleton_spec_membership_iff element {element}ₘ member hSpec

private theorem ordered_pair_eq_iff_coordinates_of_support
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left₁ right₁ left₂ right₂ : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (⟨left₁, right₁⟩ₘ ≐ₘ ⟨left₂, right₂⟩ₘ) ↔ₘ
        ((left₁ ≐ₘ left₂) ∧ₘ (right₁ ≐ₘ right₂)) :=
  FirstOrder.Derives.theory_weaken
    (fun hSentence => S.contains_ordered_pair hSentence)
    (ordered_pair_term_eq_iff_coordinates
      (Γ := Γ) left₁ right₁ left₂ right₂)

private theorem pair_condition_index_ne
    {T : SetTheory} (A : ArithmeticSupport T)
    {free : SetContext}
    (start previous : Nat) (hPrevious : previous < start)
    {elements : List (SetOpenTerm free)}
    (index value : SetOpenTerm free) :
    ([] : Context signature free) ⊢ₘ[T]
      standard_sequence_pair_member_condition
        start elements index value ⟶ₘ
          ¬ₘ (index ≐ₘ numₘ(previous)) := by
  induction elements generalizing start with
  | nil =>
      apply FirstOrder.Derives.imp_intro
      apply FirstOrder.Derives.falsum_elim
      have hFalse :
          (Formula.falsum :: ([] : Context signature free)) ⊢ₘ[T]
            Formula.falsum :=
        FirstOrder.Derives.assumption List.mem_cons_self
      simpa [standard_sequence_pair_member_condition] using hFalse
  | cons head tail ih =>
      let headCase : SetOpenFormula free :=
        (index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)
      let tailCase : SetOpenFormula free :=
        standard_sequence_pair_member_condition
          (start + 1) tail index value
      have hNumeralNe : ([] : Context signature free) ⊢ₘ[T]
          ¬ₘ (numₘ(previous) ≐ₘ numₘ(start)) :=
        by
          simpa [Formula.renameFree, Formula.rename,
            Renaming.free, Formula.renameMapped,
            Arguments.renameMapped,
            finite_numeral_term_renameMapped] using
            (FirstOrder.Derives.free_renaming
              (T := T)
              (ρ := (VariableRenaming.empty :
                VariableRenaming [] free))
              (A.numeral_arithmetic.numeral_ne
                (Nat.ne_of_lt hPrevious)))
      have hHead : ([] : Context signature free) ⊢ₘ[T]
          headCase ⟶ₘ ¬ₘ (index ≐ₘ numₘ(previous)) := by
        apply FirstOrder.Derives.imp_intro
        apply FirstOrder.Derives.neg_intro
        let Δ : Context signature free :=
          (index ≐ₘ numₘ(previous)) :: headCase :: []
        have hHeadCase : Δ ⊢ₘ[T] headCase :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hIndexStart : Δ ⊢ₘ[T] index ≐ₘ numₘ(start) :=
          FirstOrder.Derives.conj_elim_left hHeadCase
        have hIndexPrevious : Δ ⊢ₘ[T]
            index ≐ₘ numₘ(previous) :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hPreviousStart : Δ ⊢ₘ[T]
            numₘ(previous) ≐ₘ numₘ(start) :=
          Metatheory.Derives.equality_trans
            (Metatheory.Derives.equality_symm hIndexPrevious)
            hIndexStart
        exact FirstOrder.Derives.neg_elim hPreviousStart
          (FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature free)) (Δ := Δ)
            (by simp [Δ])
            hNumeralNe)
      have hTail : ([] : Context signature free) ⊢ₘ[T]
          tailCase ⟶ₘ ¬ₘ (index ≐ₘ numₘ(previous)) := by
        simpa [tailCase] using
          ih (start + 1)
            (Nat.lt_trans hPrevious (Nat.lt_succ_self start))
      apply FirstOrder.Derives.imp_intro
      have hCondition :
          (standard_sequence_pair_member_condition
            start (head :: tail) index value ::
              ([] : Context signature free)) ⊢ₘ[T]
            standard_sequence_pair_member_condition
              start (head :: tail) index value :=
        FirstOrder.Derives.assumption List.mem_cons_self
      apply FirstOrder.Derives.disj_elim
        (by simpa [headCase, tailCase,
          standard_sequence_pair_member_condition] using hCondition)
      · simpa [headCase, tailCase,
          standard_sequence_pair_member_condition] using
          FirstOrder.Derives.imp_elim
            (hHead.context_weaken_prefix
              (initial := [headCase,
                standard_sequence_pair_member_condition
                  start (head :: tail) index value]))
            (FirstOrder.Derives.assumption List.mem_cons_self)
      · simpa [headCase, tailCase,
          standard_sequence_pair_member_condition] using
          FirstOrder.Derives.imp_elim
            (hTail.context_weaken_prefix
              (initial := [tailCase,
                standard_sequence_pair_member_condition
                  start (head :: tail) index value]))
            (FirstOrder.Derives.assumption List.mem_cons_self)

private theorem disj_conj_imp
    {T : SetTheory} {free : SetContext}
    {left₁ left₂ right₁ right₂ conclusion : SetOpenFormula free}
    (h₁₁ : ([] : Context signature free) ⊢ₘ[T]
      (left₁ ∧ₘ right₁) ⟶ₘ conclusion)
    (h₁₂ : ([] : Context signature free) ⊢ₘ[T]
      (left₁ ∧ₘ right₂) ⟶ₘ conclusion)
    (h₂₁ : ([] : Context signature free) ⊢ₘ[T]
      (left₂ ∧ₘ right₁) ⟶ₘ conclusion)
    (h₂₂ : ([] : Context signature free) ⊢ₘ[T]
      (left₂ ∧ₘ right₂) ⟶ₘ conclusion) :
    ([] : Context signature free) ⊢ₘ[T]
      ((left₁ ∨ₘ left₂) ∧ₘ (right₁ ∨ₘ right₂)) ⟶ₘ conclusion := by

  derive_prop

private theorem pair_condition_unique
    {T : SetTheory} (A : ArithmeticSupport T)
    {free : SetContext}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (index first second : SetOpenTerm free) :
    ([] : Context signature free) ⊢ₘ[T]
      (standard_sequence_pair_member_condition
        start elements index first ∧ₘ
        standard_sequence_pair_member_condition
          start elements index second) ⟶ₘ
            (first ≐ₘ second) := by
  induction elements generalizing start with
  | nil =>
      apply FirstOrder.Derives.imp_intro
      let source : SetOpenFormula free :=
        standard_sequence_pair_member_condition
          start [] index first ∧ₘ
          standard_sequence_pair_member_condition
            start [] index second
      have hSource : [source] ⊢ₘ[T] source :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hFalse : [source] ⊢ₘ[T] Formula.falsum := by
        simpa [source, standard_sequence_pair_member_condition] using
          FirstOrder.Derives.conj_elim_left hSource
      exact FirstOrder.Derives.falsum_elim hFalse
  | cons head tail ih =>
      let headFirst : SetOpenFormula free :=
        (index ≐ₘ numₘ(start)) ∧ₘ (first ≐ₘ head)
      let headSecond : SetOpenFormula free :=
        (index ≐ₘ numₘ(start)) ∧ₘ (second ≐ₘ head)
      let tailFirst : SetOpenFormula free :=
        standard_sequence_pair_member_condition
          (start + 1) tail index first
      let tailSecond : SetOpenFormula free :=
        standard_sequence_pair_member_condition
          (start + 1) tail index second
      have hHeadNeFirst := pair_condition_index_ne
        A (start + 1) start (Nat.lt_succ_self start)
          (elements := tail) index first
      have hHeadNeSecond := pair_condition_index_ne
        A (start + 1) start (Nat.lt_succ_self start)
          (elements := tail) index second
      have hHeadHead : ([] : Context signature free) ⊢ₘ[T]
          (headFirst ∧ₘ headSecond) ⟶ₘ (first ≐ₘ second) := by
        apply FirstOrder.Derives.imp_intro
        let source : SetOpenFormula free := headFirst ∧ₘ headSecond
        have hSource : [source] ⊢ₘ[T] source :=
          FirstOrder.Derives.assumption List.mem_cons_self
        have hFirstHead : [source] ⊢ₘ[T] first ≐ₘ head :=
          FirstOrder.Derives.conj_elim_right
            (FirstOrder.Derives.conj_elim_left hSource)
        have hSecondHead : [source] ⊢ₘ[T] second ≐ₘ head :=
          FirstOrder.Derives.conj_elim_right
            (FirstOrder.Derives.conj_elim_right hSource)
        exact Metatheory.Derives.equality_trans hFirstHead
          (Metatheory.Derives.equality_symm hSecondHead)
      have hHeadTail : ([] : Context signature free) ⊢ₘ[T]
          (headFirst ∧ₘ tailSecond) ⟶ₘ (first ≐ₘ second) := by
        apply FirstOrder.Derives.imp_intro
        let source : SetOpenFormula free := headFirst ∧ₘ tailSecond
        have hSource : [source] ⊢ₘ[T] source :=
          FirstOrder.Derives.assumption List.mem_cons_self
        have hIndexStart : [source] ⊢ₘ[T]
            index ≐ₘ numₘ(start) :=
          FirstOrder.Derives.conj_elim_left
            (FirstOrder.Derives.conj_elim_left hSource)
        have hTailCase : [source] ⊢ₘ[T] tailSecond :=
          FirstOrder.Derives.conj_elim_right hSource
        have hTailNe := FirstOrder.Derives.imp_elim
          hHeadNeSecond.context_weaken_cons hTailCase
        exact FirstOrder.Derives.falsum_elim
          (FirstOrder.Derives.neg_elim hIndexStart hTailNe)
      have hTailHead : ([] : Context signature free) ⊢ₘ[T]
          (tailFirst ∧ₘ headSecond) ⟶ₘ (first ≐ₘ second) := by
        apply FirstOrder.Derives.imp_intro
        let source : SetOpenFormula free := tailFirst ∧ₘ headSecond
        have hSource : [source] ⊢ₘ[T] source :=
          FirstOrder.Derives.assumption List.mem_cons_self
        have hTailCase : [source] ⊢ₘ[T] tailFirst :=
          FirstOrder.Derives.conj_elim_left hSource
        have hIndexStart : [source] ⊢ₘ[T]
            index ≐ₘ numₘ(start) :=
          FirstOrder.Derives.conj_elim_left
            (FirstOrder.Derives.conj_elim_right hSource)
        have hTailNe := FirstOrder.Derives.imp_elim
          hHeadNeFirst.context_weaken_cons hTailCase
        exact FirstOrder.Derives.falsum_elim
          (FirstOrder.Derives.neg_elim hIndexStart hTailNe)
      have hTailTail : ([] : Context signature free) ⊢ₘ[T]
          (tailFirst ∧ₘ tailSecond) ⟶ₘ (first ≐ₘ second) := by
        simpa [tailFirst, tailSecond] using ih (start + 1)
      have hCombined := disj_conj_imp
        (T := T) hHeadHead hHeadTail hTailHead hTailTail
      simpa [headFirst, headSecond, tailFirst, tailSecond,
        standard_sequence_pair_member_condition] using hCombined

private theorem ordered_pair_of_equality
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (member left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] member ≐ₘ ⟨left, right⟩ₘ) :
    Γ ⊢ₘ[T] is_ordered_pair_formula member := by
  have hDefinition : Γ ⊢ₘ[T]
      is_ordered_pair_definition_instance member :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_predicate
        (relation_function_theory_subset_function_predicate_theory hSentence))
      (is_ordered_pair_definition_instance_derives
        (Γ := Γ) member)
  have hCondition : Γ ⊢ₘ[T] is_ordered_pair_condition member :=
    is_ordered_pair_condition_intro member left right hEquality
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

private theorem standard_sequence_member_condition_is_ordered_pair
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (member : SetOpenTerm free) :
    ([] : Context signature free) ⊢ₘ[T]
      standard_sequence_member_condition start elements member ⟶ₘ
        is_ordered_pair_formula member := by
  induction elements generalizing start with
  | nil =>
      apply FirstOrder.Derives.imp_intro
      exact FirstOrder.Derives.falsum_elim
        (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head tail ih =>
      let headCase : SetOpenFormula free :=
        member ≐ₘ ⟨numₘ(start), head⟩ₘ
      let tailCase : SetOpenFormula free :=
        standard_sequence_member_condition (start + 1) tail member
      have hHead : ([] : Context signature free) ⊢ₘ[T]
          headCase ⟶ₘ is_ordered_pair_formula member := by
        apply FirstOrder.Derives.imp_intro
        have hEquality : [headCase] ⊢ₘ[T]
            member ≐ₘ ⟨numₘ(start), head⟩ₘ :=
          FirstOrder.Derives.assumption List.mem_cons_self
        exact ordered_pair_of_equality S member
          (numₘ(start)) head hEquality
      have hTail : ([] : Context signature free) ⊢ₘ[T]
          tailCase ⟶ₘ is_ordered_pair_formula member := by
        simpa [tailCase] using ih (start + 1)
      apply FirstOrder.Derives.imp_intro
      let source : SetOpenFormula free := headCase ∨ₘ tailCase
      have hSource : [source] ⊢ₘ[T] source :=
        FirstOrder.Derives.assumption List.mem_cons_self
      apply FirstOrder.Derives.disj_elim
        (by simpa [source, headCase, tailCase,
          standard_sequence_member_condition] using hSource)
      · simpa [source, headCase, tailCase] using!
          FirstOrder.Derives.imp_elim
            (hHead.context_weaken_prefix
              (initial := [headCase, source]))
            (FirstOrder.Derives.assumption List.mem_cons_self)
      · simpa [source, headCase, tailCase] using!
          FirstOrder.Derives.imp_elim
            (hTail.context_weaken_prefix
              (initial := [tailCase, source]))
            (FirstOrder.Derives.assumption List.mem_cons_self)

end FiniteSequenceSemantics

/-! ## 成员反演 -/

theorem standard_sequence_from_member_iff
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (member : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (member ∈ₘ standard_sequence_from start elements) ↔ₘ
        standard_sequence_member_condition start elements member := by
  induction elements generalizing start with
  | nil =>
      simpa [standard_sequence_from, standard_sequence_member_condition] using
        (FiniteSequenceSemantics.empty_member_iff_falsum S member)
  | cons head tail ih =>
      let pair : SetOpenTerm free := ⟨numₘ(start), head⟩ₘ
      let singleton : SetOpenTerm free := {pair}ₘ
      let tailSequence : SetOpenTerm free :=
        standard_sequence_from (start + 1) tail
      have hSingleton :=
        FiniteSequenceSemantics.singleton_member_iff_of_support
          (Γ := Γ) S pair member
      have hTail := ih (start + 1)
      have hUnion :=
        FiniteSequenceSemantics.binary_union_member_iff_of_support
          (Γ := Γ) S singleton tailSequence member
      have hDisjunction :=
        DerivationEquivalent.disj_congr
          (DerivationEquivalent.of_iff hSingleton)
          (DerivationEquivalent.of_iff hTail)
      have hStep : Γ ⊢ₘ[T]
          (member ∈ₘ (singleton ∪ₘ tailSequence)) ↔ₘ
            ((member ≐ₘ pair) ∨ₘ
              standard_sequence_member_condition (start + 1) tail member) :=
        ((DerivationEquivalent.of_iff hUnion).trans hDisjunction).to_iff
      simpa [standard_sequence_from, standard_sequence_member_condition,
        pair, singleton, tailSequence] using hStep

/-! ## 关系性 -/

theorem standard_sequence_from_is_relation
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) (elements : List (SetOpenTerm free)) :
    Γ ⊢ₘ[T] is_relation_formula (standard_sequence_from start elements) := by
  apply is_relation_intro
    (hRelationTheory := fun hSentence =>
      S.contains_function_predicate
        (relation_predicate_theory_subset_function_predicate_theory hSentence))
    (standard_sequence_from start elements)
  let Γ' : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Γ
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  let liftedElements : List (SetOpenTerm (SetSort.set :: free)) :=
    elements.map (fun element => element.weakenFree SetSort.set)
  have hMemberIff : Γ' ⊢ₘ[T]
      (member ∈ₘ standard_sequence_from start liftedElements) ↔ₘ
        standard_sequence_member_condition start liftedElements member :=
    standard_sequence_from_member_iff (Γ := Γ') S start
      (elements := liftedElements) member
  have hCondition : ([] : Context signature (SetSort.set :: free)) ⊢ₘ[T]
      standard_sequence_member_condition start liftedElements member ⟶ₘ
        is_ordered_pair_formula member :=
    FiniteSequenceSemantics.standard_sequence_member_condition_is_ordered_pair
      S start (elements := liftedElements) member
  have hCondition' : Γ' ⊢ₘ[T]
      standard_sequence_member_condition start liftedElements member ⟶ₘ
        is_ordered_pair_formula member :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature (SetSort.set :: free)))
      (Δ := Γ') (by simp [Γ']) hCondition
  have hPoint' : Γ' ⊢ₘ[T]
      (member ∈ₘ standard_sequence_from start liftedElements) ⟶ₘ
        is_ordered_pair_formula member := by
    apply FirstOrder.Derives.imp_intro
    let Δ : Context signature (SetSort.set :: free) :=
      (member ∈ₘ standard_sequence_from start liftedElements) :: Γ'
    have hMember : Δ ⊢ₘ[T]
        member ∈ₘ standard_sequence_from start liftedElements :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hConditionAt : Δ ⊢ₘ[T]
        standard_sequence_member_condition start liftedElements member :=
      FirstOrder.Derives.iff_elim_left
        (hMemberIff.context_weaken_cons) hMember
    exact FirstOrder.Derives.imp_elim
      (hCondition'.context_weaken_prefix (initial :=
        [member ∈ₘ standard_sequence_from start liftedElements]))
      hConditionAt
  simpa [Γ', member, liftedElements] using hPoint'

/-! ## 坐标反演 -/

theorem standard_sequence_from_pair_member_iff
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (index value : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (⟨index, value⟩ₘ ∈ₘ standard_sequence_from start elements) ↔ₘ
        standard_sequence_pair_member_condition
          start elements index value := by
  induction elements generalizing start with
  | nil =>
      simpa [standard_sequence_from,
        standard_sequence_pair_member_condition] using!
        (standard_sequence_from_member_iff S start
          (elements := []) (⟨index, value⟩ₘ))
  | cons head tail ih =>
      let pair : SetOpenTerm free := ⟨numₘ(start), head⟩ₘ
      let singleton : SetOpenTerm free := {pair}ₘ
      let tailSequence : SetOpenTerm free :=
        standard_sequence_from (start + 1) tail
      let member : SetOpenTerm free := ⟨index, value⟩ₘ
      have hSingleton :=
        FiniteSequenceSemantics.singleton_member_iff_of_support
          (Γ := Γ) S pair member
      have hCoordinates :=
        FiniteSequenceSemantics.ordered_pair_eq_iff_coordinates_of_support
          (Γ := Γ) S index value (numₘ(start)) head
      have hSingletonCoordinates : Γ ⊢ₘ[T]
          (member ∈ₘ singleton) ↔ₘ
            ((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)) :=
        ((DerivationEquivalent.of_iff hSingleton).trans
          (DerivationEquivalent.of_iff hCoordinates)).to_iff
      have hTail := ih (start + 1)
      have hUnion :=
        FiniteSequenceSemantics.binary_union_member_iff_of_support
          (Γ := Γ) S singleton tailSequence member
      have hDisjunction :=
        DerivationEquivalent.disj_congr
          (DerivationEquivalent.of_iff hSingletonCoordinates)
          (DerivationEquivalent.of_iff hTail)
      have hStep : Γ ⊢ₘ[T]
          (member ∈ₘ (singleton ∪ₘ tailSequence)) ↔ₘ
            (((index ≐ₘ numₘ(start)) ∧ₘ (value ≐ₘ head)) ∨ₘ
              standard_sequence_pair_member_condition
                (start + 1) tail index value) :=
        ((DerivationEquivalent.of_iff hUnion).trans hDisjunction).to_iff
      simpa [standard_sequence_from,
        standard_sequence_pair_member_condition, pair, singleton,
        tailSequence, member] using hStep

private theorem standard_sequence_from_pair_member_unique
    {T : SetTheory} (A : ArithmeticSupport T)
    (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (index first second : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      ((⟨index, first⟩ₘ ∈ₘ standard_sequence_from start elements) ∧ₘ
        (⟨index, second⟩ₘ ∈ₘ standard_sequence_from start elements)) ⟶ₘ
      (first ≐ₘ second) := by
  have hFirst := standard_sequence_from_pair_member_iff
    (Γ := Γ) S start (elements := elements) index first
  have hSecond := standard_sequence_from_pair_member_iff
    (Γ := Γ) S start (elements := elements) index second
  have hUnique := FiniteSequenceSemantics.pair_condition_unique
    A start (elements := elements) index first second
  have hUnique' : Γ ⊢ₘ[T]
      (standard_sequence_pair_member_condition
          start elements index first ∧ₘ
        standard_sequence_pair_member_condition
          start elements index second) ⟶ₘ
          (first ≐ₘ second) :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature free)) (Δ := Γ) (by simp) hUnique
  apply FirstOrder.Derives.imp_intro
  let source : SetOpenFormula free :=
    (⟨index, first⟩ₘ ∈ₘ standard_sequence_from start elements) ∧ₘ
      (⟨index, second⟩ₘ ∈ₘ standard_sequence_from start elements)
  let Δ : Context signature free := source :: Γ
  have hSource : Δ ⊢ₘ[T] source :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hFirstMember : Δ ⊢ₘ[T]
      ⟨index, first⟩ₘ ∈ₘ standard_sequence_from start elements :=
    FirstOrder.Derives.conj_elim_left hSource
  have hSecondMember : Δ ⊢ₘ[T]
      ⟨index, second⟩ₘ ∈ₘ standard_sequence_from start elements :=
    FirstOrder.Derives.conj_elim_right hSource
  have hFirstCondition : Δ ⊢ₘ[T]
      standard_sequence_pair_member_condition start elements index first :=
    FirstOrder.Derives.iff_elim_left
      (hFirst.context_weaken_cons) hFirstMember
  have hSecondCondition : Δ ⊢ₘ[T]
      standard_sequence_pair_member_condition start elements index second :=
    FirstOrder.Derives.iff_elim_left
      (hSecond.context_weaken_cons) hSecondMember
  exact FirstOrder.Derives.imp_elim
    (hUnique'.context_weaken_cons)
    (FirstOrder.Derives.conj_intro hFirstCondition hSecondCondition)

theorem standard_sequence_from_is_function
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) (elements : List (SetOpenTerm free)) :
    Γ ⊢ₘ[T] is_function_formula (standard_sequence_from start elements) := by
  have hRelation := standard_sequence_from_is_relation
    (Γ := Γ) S start elements
  have hSingle : Γ ⊢ₘ[T]
      function_single_valued_condition
        (standard_sequence_from start elements) := by
    unfold function_single_valued_condition
      function_single_valued_at_input
      function_single_valued_at_left
      function_single_valued_at_values
    apply FirstOrder.Derives.forall_intro
    apply FirstOrder.Derives.forall_intro
    apply FirstOrder.Derives.forall_intro
    let Γ₃ : Context signature (SetSort.set :: SetSort.set ::
        SetSort.set :: free) :=
      FreshVariable.extendContext SetSort.set
        (FreshVariable.extendContext SetSort.set
          (FreshVariable.extendContext SetSort.set Γ))
    let input : SetOpenTerm (SetSort.set :: SetSort.set ::
        SetSort.set :: free) :=
      .fvar (.there (.there .here))
    let left : SetOpenTerm (SetSort.set :: SetSort.set ::
        SetSort.set :: free) :=
      .fvar (.there .here)
    let right : SetOpenTerm (SetSort.set :: SetSort.set ::
        SetSort.set :: free) :=
      .fvar .here
    let liftedElements : List (SetOpenTerm (SetSort.set :: SetSort.set ::
        SetSort.set :: free)) :=
      elements.map (fun element =>
        (element.weakenFree SetSort.set).weakenFree SetSort.set |>.weakenFree
          SetSort.set)
    have hUnique := standard_sequence_from_pair_member_unique
      S.toArithmeticSupport S (Γ := Γ₃) start
        (elements := liftedElements) input left right
    simpa [Γ₃, input, left, right, liftedElements] using! hUnique
  have hCondition : Γ ⊢ₘ[T]
      is_function_condition (standard_sequence_from start elements) :=
    FirstOrder.Derives.conj_intro hRelation hSingle
  have hDefinition : Γ ⊢ₘ[T]
      is_function_definition_instance
        (standard_sequence_from start elements) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_predicate hSentence)
      (is_function_definition_instance_derives
        (Γ := Γ) (standard_sequence_from start elements))
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

/-! ## 列表取值 -/

/-- 列表取出的元素在规范有限图中位于对应坐标。 -/
theorem standard_sequence_from_getElem?_graph_mem
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    {index : Nat} {element : SetOpenTerm free}
    (hGet : elements[index]? = some element) :
    Γ ⊢ₘ[T]
      ⟨numₘ(start + index), element⟩ₘ ∈ₘ
        standard_sequence_from start elements := by
  induction elements generalizing start index with
  | nil =>
      simp at hGet
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hGet
          subst element
          have hPair := standard_sequence_from_pair_member_iff
            (Γ := Γ) S start (elements := head :: tail) (numₘ(start)) head
          have hCondition : Γ ⊢ₘ[T]
              standard_sequence_pair_member_condition
                start (head :: tail) (numₘ(start)) head := by
            simp only [standard_sequence_pair_member_condition]
            exact FirstOrder.Derives.disj_intro_left
              (FirstOrder.Derives.conj_intro
                (Metatheory.Derives.equality_refl
                  (T := T) (Γ := Γ) (numₘ(start)))
                (Metatheory.Derives.equality_refl
                  (T := T) (Γ := Γ) head))
          simpa [standard_sequence_from] using
            FirstOrder.Derives.iff_elim_right hPair hCondition
      | succ index =>
          simp only [List.getElem?_cons_succ] at hGet
          have hTailGraph := ih (start + 1) hGet
          let fullIndex : Nat := start + Nat.succ index
          have hTailGraph' : Γ ⊢ₘ[T]
              ⟨numₘ(fullIndex), element⟩ₘ ∈ₘ
                standard_sequence_from (start + 1) tail := by
            simpa [fullIndex, Nat.succ_eq_add_one, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using hTailGraph
          have hTailPair := standard_sequence_from_pair_member_iff
            (Γ := Γ) S (start + 1) (elements := tail)
              (numₘ(fullIndex)) element
          have hTailCondition :=
            FirstOrder.Derives.iff_elim_left hTailPair hTailGraph'
          have hFullPair := standard_sequence_from_pair_member_iff
            (Γ := Γ) S start (elements := head :: tail)
              (numₘ(fullIndex)) element
          have hFullCondition : Γ ⊢ₘ[T]
              standard_sequence_pair_member_condition
                start (head :: tail) (numₘ(fullIndex)) element := by
            simp only [standard_sequence_pair_member_condition]
            exact FirstOrder.Derives.disj_intro_right
              (by simpa [fullIndex, Nat.succ_eq_add_one, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hTailCondition)
          simpa [fullIndex, standard_sequence_from] using
            FirstOrder.Derives.iff_elim_right hFullPair hFullCondition

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
