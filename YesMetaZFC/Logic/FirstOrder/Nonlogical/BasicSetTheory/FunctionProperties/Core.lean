import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Function

/-!
# 关系与函数的属性层：核心

单射、满射、双射、恒等映射、映射收集、传递集与成员关系限制全部建立在内在
类型语法上。三个集合构造统一使用参数化分离 schema，不再保存一次性闭分离公理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 单射、满射与双射 -/

/-- 固定像值的两个逆像必相等。 -/
def injectivity_condition {bound free : SetContext}
    (function : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: free) := .fvar .here
  let right : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let value : SetTerm bound
      (SetSort.set :: SetSort.set :: SetSort.set :: free) := .fvar .here
  let left' := (left.weakenFree SetSort.set).weakenFree SetSort.set
  let right' := right.weakenFree SetSort.set
  let function' := ((function.weakenFree SetSort.set).weakenFree
    SetSort.set).weakenFree SetSort.set
  (((((⟨left', value⟩ₘ ∈ₘ function') ∧ₘ
        (⟨right', value⟩ₘ ∈ₘ function')) ⟶ₘ (left' ≐ₘ right'))
    |>.forallFreeTop SetSort.set)
    |>.forallFreeTop SetSort.set)
    |>.forallFreeTop SetSort.set

def is_injective_condition {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_mapping_formula function source target ∧ₘ injectivity_condition function

def is_injective_definition_instance {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_injective_formula function source target ↔ₘ
    is_injective_condition function source target

def is_injective_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_injective_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

def is_surjective_condition {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_function_formula function ∧ₘ
    ((source ≐ₘ domₘ(function)) ∧ₘ (target ≐ₘ ranₘ(function)))

def is_surjective_definition_instance {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_surjective_formula function source target ↔ₘ
    is_surjective_condition function source target

def is_surjective_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_surjective_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

def is_bijection_condition {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_injective_formula function source target ∧ₘ
    is_surjective_formula function source target

def is_bijection_definition_instance {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_bijection_formula function source target ↔ₘ
    is_bijection_condition function source target

def is_bijection_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_bijection_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 恒等映射 -/

def identity_graph_condition {bound free : SetContext}
    (source element : SetTerm bound free) : SetFormula bound free :=
  let x : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((x ∈ₘ source.weakenFree SetSort.set) ∧ₘ
    (element.weakenFree SetSort.set ≐ₘ ⟨x, x⟩ₘ))
    |>.existsFreeTop SetSort.set

def identity_member_condition {bound free : SetContext}
    (source element : SetTerm bound free) : SetFormula bound free :=
  (element ∈ₘ (source ×ₘ source)) ∧ₘ
    identity_graph_condition source element

def identity_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (identity_member_condition
      (source.weakenFree SetSort.set) element)

def identity_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (identity_spec (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

def identity_predicate {free : SetContext}
    (source : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (identity_graph_condition
      (source.weakenFree SetSort.set) element).abstractFreeTop

def identity_definition_instance {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ Idₘ(source)) ↔ₘ identity_spec source candidate

def identity_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (identity_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 映射收集 -/

abbrev mapping_collection_bound_term {bound free : SetContext}
    (source target : SetTerm bound free) : SetTerm bound free :=
  𝒫ₘ(source ×ₘ target)

def mapping_collection_member_condition {bound free : SetContext}
    (source target element : SetTerm bound free) : SetFormula bound free :=
  (element ∈ₘ mapping_collection_bound_term source target) ∧ₘ
    is_mapping_formula element source target

def mapping_collection_spec {bound free : SetContext}
    (source target candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (mapping_collection_member_condition
      (source.weakenFree SetSort.set)
      (target.weakenFree SetSort.set) element)

def mapping_collection_exists {bound free : SetContext}
    (source target : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (mapping_collection_spec
    (source.weakenFree SetSort.set)
    (target.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

def mapping_collection_predicate {free : SetContext}
    (source target : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (is_mapping_formula element
      (source.weakenFree SetSort.set)
      (target.weakenFree SetSort.set)).abstractFreeTop

def mapping_collection_definition_instance {bound free : SetContext}
    (source target candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ Mapₘ(source, target)) ↔ₘ
    mapping_collection_spec source target candidate

def mapping_collection_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (mapping_collection_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 传递集与成员关系限制 -/

def is_transitive_set_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  let container : SetTerm bound (SetSort.set :: free) := .fvar .here
  let element : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar .here
  let set₁ := set.weakenFree SetSort.set
  let container₂ := container.weakenFree SetSort.set
  let set₂ := set₁.weakenFree SetSort.set
  (((container ∈ₘ set₁) ⟶ₘ
      (((element ∈ₘ container₂) ⟶ₘ (element ∈ₘ set₂))
        |>.forallFreeTop SetSort.set))
    |>.forallFreeTop SetSort.set)

def is_transitive_set_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  is_transitive_set_formula set ↔ₘ is_transitive_set_condition set

def is_transitive_set_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_transitive_set_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

def membership_relation_graph_condition {bound free : SetContext}
    (element : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: free) := .fvar .here
  let right : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  (((element.weakenFree SetSort.set).weakenFree SetSort.set ≐ₘ
      ⟨left.weakenFree SetSort.set, right⟩ₘ) ∧ₘ
    (left.weakenFree SetSort.set ∈ₘ right))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def membership_relation_member_condition {bound free : SetContext}
    (source element : SetTerm bound free) : SetFormula bound free :=
  (element ∈ₘ (source ×ₘ source)) ∧ₘ
    membership_relation_graph_condition element

def membership_relation_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (membership_relation_member_condition
      (source.weakenFree SetSort.set) element)

def membership_relation_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (membership_relation_spec (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

def membership_relation_predicate : SetPredicate [] where
  body :=
    let element : SetOpenTerm [SetSort.set] :=
      FreshVariable.newest
        (σ := signature) (free := []) SetSort.set
    (membership_relation_graph_condition element).abstractFreeTop

def membership_relation_definition_instance {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  is_transitive_set_formula source ⟶ₘ
    ((candidate ≐ₘ εₘ(source)) ↔ₘ
      membership_relation_spec source candidate)

def membership_relation_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (membership_relation_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 理论组合 -/

def injective_predicate_theory : SetTheory :=
  Theory.insert is_injective_definition_axiom function_application_theory

def surjective_predicate_theory : SetTheory :=
  Theory.insert is_surjective_definition_axiom injective_predicate_theory

def bijection_predicate_theory : SetTheory :=
  Theory.insert is_bijection_definition_axiom surjective_predicate_theory

def identity_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (source : SetOpenTerm free),
      sentence = (identity_predicate source).separation_axiom) ∨
    bijection_predicate_theory sentence

def identity_operator_theory : SetTheory :=
  Theory.insert identity_definition_axiom identity_theory

def mapping_collection_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (source target : SetOpenTerm free),
      sentence =
        (mapping_collection_predicate source target).separation_axiom) ∨
    identity_operator_theory sentence

def mapping_collection_operator_theory : SetTheory :=
  Theory.insert mapping_collection_definition_axiom mapping_collection_theory

def transitive_set_theory : SetTheory :=
  Theory.insert is_transitive_set_definition_axiom
    mapping_collection_operator_theory

def membership_relation_theory : SetTheory :=
  Theory.insert membership_relation_predicate.separation_axiom
    transitive_set_theory

def membership_relation_operator_theory : SetTheory :=
  Theory.insert membership_relation_definition_axiom
    membership_relation_theory

derive_theory_subset function_application_theory ⊆ injective_predicate_theory

derive_theory_subset injective_predicate_theory ⊆ surjective_predicate_theory

derive_theory_subset surjective_predicate_theory ⊆ bijection_predicate_theory

derive_theory_subset bijection_predicate_theory ⊆ identity_theory

derive_theory_subset identity_theory ⊆ identity_operator_theory

derive_theory_subset bijection_predicate_theory ⊆ identity_operator_theory

derive_theory_subset identity_operator_theory ⊆ mapping_collection_theory

derive_theory_subset mapping_collection_theory ⊆ mapping_collection_operator_theory

derive_theory_subset identity_operator_theory ⊆ mapping_collection_operator_theory

derive_theory_subset mapping_collection_operator_theory ⊆ transitive_set_theory

derive_theory_subset transitive_set_theory ⊆ membership_relation_theory

derive_theory_subset membership_relation_theory ⊆ membership_relation_operator_theory

derive_theory_subset transitive_set_theory ⊆ membership_relation_operator_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
