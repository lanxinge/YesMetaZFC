import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FunctionProperties

/-!
# 自然离散线性序

本模块只保留内在类型语法、定义公理与理论嵌入。良构性和闭句性由语法类型与
`SetSentence` 定义保证，不再重复维护 proof-carrying 边界。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 线性序 -/

def linear_order_irreflexive_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((element ∈ₘ carrier.weakenFree SetSort.set) ⟶ₘ
      (¬ₘ (⟨element, element⟩ₘ ∈ₘ relation.weakenFree SetSort.set)))
    |>.forallFreeTop SetSort.set

def linear_order_transitive_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  let first : SetTerm bound (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
    .fvar (.there (.there .here))
  let second : SetTerm bound (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let third : SetTerm bound (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
    .fvar .here
  let relation' := relation.weakenFree SetSort.set |>.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let carrier' := carrier.weakenFree SetSort.set |>.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  (((first ∈ₘ carrier') ∧ₘ ((second ∈ₘ carrier') ∧ₘ (third ∈ₘ carrier'))) ⟶ₘ
      (((⟨first, second⟩ₘ ∈ₘ relation') ∧ₘ (⟨second, third⟩ₘ ∈ₘ relation')) ⟶ₘ
        (⟨first, third⟩ₘ ∈ₘ relation')))
    |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

def linear_order_connex_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let right : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let relation' := relation.weakenFree SetSort.set |>.weakenFree SetSort.set
  let carrier' := carrier.weakenFree SetSort.set |>.weakenFree SetSort.set
  (((left ∈ₘ carrier') ∧ₘ (right ∈ₘ carrier')) ⟶ₘ
      ((¬ₘ (⟨left, right⟩ₘ ∈ₘ relation')) ⟶ₘ
        ((¬ₘ (left ≐ₘ right)) ⟶ₘ (⟨right, left⟩ₘ ∈ₘ relation'))))
    |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

def is_linear_order_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  is_relation_formula relation ∧ₘ
    ((relation ⊆ₘ (carrier ×ₘ carrier)) ∧ₘ
      ((linear_order_irreflexive_condition relation carrier ∧ₘ
          linear_order_transitive_condition relation carrier) ∧ₘ
        linear_order_connex_condition relation carrier))

def is_linear_order_definition_instance {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  is_linear_order_formula relation carrier ↔ₘ
    is_linear_order_condition relation carrier

def is_linear_order_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_linear_order_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 序同构与序嵌入 -/

def order_preservation_condition {bound free : SetContext}
    (function sourceRelation sourceCarrier targetRelation : SetTerm bound free) :
    SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let right : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let function' := function.weakenFree SetSort.set |>.weakenFree SetSort.set
  let sourceRelation' := sourceRelation.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let sourceCarrier' := sourceCarrier.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let targetRelation' := targetRelation.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  (((left ∈ₘ sourceCarrier') ∧ₘ (right ∈ₘ sourceCarrier')) ⟶ₘ
      ((⟨left, right⟩ₘ ∈ₘ sourceRelation') ↔ₘ
        (⟨function' ·ₘ left, function' ·ₘ right⟩ₘ ∈ₘ targetRelation')))
    |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

def is_order_isomorphism_condition {bound free : SetContext}
    (function sourceRelation sourceCarrier targetRelation targetCarrier :
      SetTerm bound free) : SetFormula bound free :=
  is_linear_order_formula sourceRelation sourceCarrier ∧ₘ
    ((is_linear_order_formula targetRelation targetCarrier ∧ₘ
        is_bijection_formula function sourceCarrier targetCarrier) ∧ₘ
      order_preservation_condition function sourceRelation sourceCarrier targetRelation)

def is_order_isomorphism_definition_instance {bound free : SetContext}
    (function sourceRelation sourceCarrier targetRelation targetCarrier :
      SetTerm bound free) : SetFormula bound free :=
  is_order_isomorphism_formula
      function sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_isomorphism_condition
      function sourceRelation sourceCarrier targetRelation targetCarrier

def is_order_isomorphism_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_order_isomorphism_definition_instance
      (.fvar (.there (.there (.there (.there .here)))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

def is_order_isomorphic_condition {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm bound free) :
    SetFormula bound free :=
  let function : SetTerm bound (SetSort.set :: free) := .fvar .here
  (is_order_isomorphism_formula function
      (sourceRelation.weakenFree SetSort.set)
      (sourceCarrier.weakenFree SetSort.set)
      (targetRelation.weakenFree SetSort.set)
      (targetCarrier.weakenFree SetSort.set)).existsFreeTop SetSort.set

def is_order_isomorphic_definition_instance {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm bound free) :
    SetFormula bound free :=
  is_order_isomorphic_formula
      sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_isomorphic_condition
      sourceRelation sourceCarrier targetRelation targetCarrier

def is_order_isomorphic_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_order_isomorphic_definition_instance
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

def is_order_embedding_condition {bound free : SetContext}
    (function sourceRelation sourceCarrier targetRelation targetCarrier :
      SetTerm bound free) : SetFormula bound free :=
  is_linear_order_formula sourceRelation sourceCarrier ∧ₘ
    ((is_linear_order_formula targetRelation targetCarrier ∧ₘ
        is_injective_formula function sourceCarrier targetCarrier) ∧ₘ
      order_preservation_condition function sourceRelation sourceCarrier targetRelation)

def is_order_embedding_definition_instance {bound free : SetContext}
    (function sourceRelation sourceCarrier targetRelation targetCarrier :
      SetTerm bound free) : SetFormula bound free :=
  is_order_embedding_formula
      function sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_embedding_condition
      function sourceRelation sourceCarrier targetRelation targetCarrier

def is_order_embedding_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_order_embedding_definition_instance
      (.fvar (.there (.there (.there (.there .here)))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

def is_order_embeddable_condition {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm bound free) :
    SetFormula bound free :=
  let function : SetTerm bound (SetSort.set :: free) := .fvar .here
  (is_order_embedding_formula function
      (sourceRelation.weakenFree SetSort.set)
      (sourceCarrier.weakenFree SetSort.set)
      (targetRelation.weakenFree SetSort.set)
      (targetCarrier.weakenFree SetSort.set)).existsFreeTop SetSort.set

def is_order_embeddable_definition_instance {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm bound free) :
    SetFormula bound free :=
  is_order_embeddable_formula
      sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_embeddable_condition
      sourceRelation sourceCarrier targetRelation targetCarrier

def is_order_embeddable_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_order_embeddable_definition_instance
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

/-! ## 自然离散性 -/

def natural_order_greatest_element_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  let subset : SetTerm bound (SetSort.set :: free) := .fvar .here
  let witness : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let element : SetTerm bound
      (SetSort.set :: SetSort.set :: SetSort.set :: free) := .fvar .here
  let relation' := relation.weakenFree SetSort.set |>.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let carrier' := carrier.weakenFree SetSort.set
  let subset' := subset.weakenFree SetSort.set
  let witness' := witness.weakenFree SetSort.set
  let inner :=
    ((element ∈ₘ subset'.weakenFree SetSort.set) ⟶ₘ
      ((¬ₘ (witness' ≐ₘ element)) ⟶ₘ
        (⟨element, witness'⟩ₘ ∈ₘ relation')))
      |>.forallFreeTop SetSort.set
  let witness_exists :=
    ((witness ∈ₘ subset.weakenFree SetSort.set) ∧ₘ inner)
      |>.existsFreeTop SetSort.set
  (((subset ∈ₘ 𝒫ₘ(carrier')) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ))) ⟶ₘ witness_exists)
    |>.forallFreeTop SetSort.set

def natural_order_least_element_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  let subset : SetTerm bound (SetSort.set :: free) := .fvar .here
  let witness : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let element : SetTerm bound
      (SetSort.set :: SetSort.set :: SetSort.set :: free) := .fvar .here
  let relation' := relation.weakenFree SetSort.set |>.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let carrier' := carrier.weakenFree SetSort.set
  let subset' := subset.weakenFree SetSort.set
  let witness' := witness.weakenFree SetSort.set
  let inner :=
    ((element ∈ₘ subset'.weakenFree SetSort.set) ⟶ₘ
      ((¬ₘ (witness' ≐ₘ element)) ⟶ₘ
        (⟨witness', element⟩ₘ ∈ₘ relation')))
      |>.forallFreeTop SetSort.set
  let witness_exists :=
    ((witness ∈ₘ subset.weakenFree SetSort.set) ∧ₘ inner)
      |>.existsFreeTop SetSort.set
  (((subset ∈ₘ 𝒫ₘ(carrier')) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ))) ⟶ₘ witness_exists)
    |>.forallFreeTop SetSort.set

def is_natural_discrete_linear_order_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  is_linear_order_formula relation carrier ∧ₘ
    (natural_order_greatest_element_condition relation carrier ∧ₘ
      natural_order_least_element_condition relation carrier)

def is_natural_discrete_linear_order_definition_instance {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  is_natural_discrete_linear_order_formula relation carrier ↔ₘ
    is_natural_discrete_linear_order_condition relation carrier

def is_natural_discrete_linear_order_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_natural_discrete_linear_order_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 理论组合与嵌入 -/

def linear_order_theory : SetTheory :=
  Theory.insert is_linear_order_definition_axiom
    membership_relation_operator_theory

def order_isomorphism_theory : SetTheory :=
  Theory.insert is_order_isomorphism_definition_axiom linear_order_theory

def order_isomorphic_theory : SetTheory :=
  Theory.insert is_order_isomorphic_definition_axiom order_isomorphism_theory

def order_embedding_theory : SetTheory :=
  Theory.insert is_order_embedding_definition_axiom order_isomorphic_theory

def order_embeddable_theory : SetTheory :=
  Theory.insert is_order_embeddable_definition_axiom order_embedding_theory

def natural_discrete_linear_order_theory : SetTheory :=
  Theory.insert is_natural_discrete_linear_order_definition_axiom
    order_embeddable_theory

derive_theory_subset membership_relation_operator_theory ⊆ linear_order_theory

derive_theory_subset linear_order_theory ⊆ order_isomorphism_theory

derive_theory_subset order_isomorphism_theory ⊆ order_isomorphic_theory

derive_theory_subset order_isomorphic_theory ⊆ order_embedding_theory

derive_theory_subset order_embedding_theory ⊆ order_embeddable_theory

derive_theory_subset order_embeddable_theory ⊆ natural_discrete_linear_order_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
