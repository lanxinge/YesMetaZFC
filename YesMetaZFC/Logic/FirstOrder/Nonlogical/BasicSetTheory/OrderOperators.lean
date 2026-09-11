import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FiniteOrdinal

/-!
# 映像、限制与序算子

本模块把关系像、函数限制以及良序极值算子统一写成内在类型规格。存在性使用
参数化分离接口，定义公理只保留对象语言中的数学条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 关系像 -/

def relation_image_member_condition {bound free : SetContext}
    (relation source element : SetTerm bound free) : SetFormula bound free :=
  let preimage : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((preimage ∈ₘ source.weakenFree SetSort.set) ∧ₘ
      (⟨preimage, element.weakenFree SetSort.set⟩ₘ ∈ₘ
        relation.weakenFree SetSort.set))
    |>.existsFreeTop SetSort.set

def relation_image_separation_spec {bound free : SetContext}
    (relation source target candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ target.weakenFree SetSort.set) ∧ₘ
      relation_image_member_condition
        (relation.weakenFree SetSort.set)
        (source.weakenFree SetSort.set) element)

def relation_image_separation_exists {bound free : SetContext}
    (relation source target : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (relation_image_separation_spec
    (relation.weakenFree SetSort.set)
    (source.weakenFree SetSort.set)
    (target.weakenFree SetSort.set)
    candidate).existsFreeTop SetSort.set

def relation_image_separation_predicate {free : SetContext}
    (relation source target : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    ((element ∈ₘ target.weakenFree SetSort.set) ∧ₘ
      relation_image_member_condition
        (relation.weakenFree SetSort.set)
        (source.weakenFree SetSort.set) element).abstractFreeTop

def relation_image_separation_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (relation_image_separation_exists
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 映像与限制 -/

def image_spec {bound free : SetContext}
    (function subset target candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ target.weakenFree SetSort.set) ∧ₘ
      relation_image_member_condition
        (function.weakenFree SetSort.set)
        (subset.weakenFree SetSort.set) element)

def image_definition_instance {bound free : SetContext}
    (function source target subset candidate : SetTerm bound free) :
    SetFormula bound free :=
  is_mapping_formula function source target ⟶ₘ
    ((subset ⊆ₘ source) ⟶ₘ
      ((candidate ≐ₘ imgₘ(function, subset)) ↔ₘ
        image_spec function subset target candidate))

def image_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (image_definition_instance
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

def restriction_member_condition {bound free : SetContext}
    (subset element : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let right : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let subset' := subset.weakenFree SetSort.set |>.weakenFree SetSort.set
  let element' := element.weakenFree SetSort.set |>.weakenFree SetSort.set
  (((left ∈ₘ subset') ∧ₘ (element' ≐ₘ ⟨left, right⟩ₘ))
      |>.existsFreeTop SetSort.set)
    |>.existsFreeTop SetSort.set

def restriction_spec {bound free : SetContext}
    (function subset candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ function.weakenFree SetSort.set) ∧ₘ
      restriction_member_condition
        (subset.weakenFree SetSort.set) element)

def restriction_definition_instance {bound free : SetContext}
    (function source target subset candidate : SetTerm bound free) :
    SetFormula bound free :=
  is_mapping_formula function source target ⟶ₘ
    ((subset ⊆ₘ source) ⟶ₘ
      ((candidate ≐ₘ restrictₘ(function, subset)) ↔ₘ
        restriction_spec function subset candidate))

def restriction_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (restriction_definition_instance
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

/-! ## 极值 -/

def minimum_spec {bound free : SetContext}
    (relation subset candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  let candidate' := candidate.weakenFree SetSort.set
  let subset' := subset.weakenFree SetSort.set
  let relation' := relation.weakenFree SetSort.set
  let body :=
    (candidate' ∈ₘ subset') ∧ₘ
      ((element ∈ₘ subset') ⟶ₘ
        ((¬ₘ (candidate' ≐ₘ element)) ⟶ₘ
          (⟨candidate', element⟩ₘ ∈ₘ relation')))
  body.forallFreeTop SetSort.set

def minimum_linear_order_definition_instance {bound free : SetContext}
    (relation carrier subset candidate : SetTerm bound free) : SetFormula bound free :=
  ((is_well_order_formula relation carrier ∧ₘ
      ((subset ⊆ₘ carrier) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ
    ((candidate ≐ₘ minₘ(relation, subset)) ↔ₘ
      minimum_spec relation subset candidate))

def minimum_linear_order_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (minimum_linear_order_definition_instance
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

def minimum_natural_order_definition_instance {bound free : SetContext}
    (relation carrier subset candidate : SetTerm bound free) : SetFormula bound free :=
  ((is_natural_discrete_linear_order_formula relation carrier ∧ₘ
      ((subset ⊆ₘ carrier) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ
    ((candidate ≐ₘ minₘ(relation, subset)) ↔ₘ
      minimum_spec relation subset candidate))

def minimum_natural_order_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (minimum_natural_order_definition_instance
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

def maximum_spec {bound free : SetContext}
    (relation subset candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  let candidate' := candidate.weakenFree SetSort.set
  let subset' := subset.weakenFree SetSort.set
  let relation' := relation.weakenFree SetSort.set
  let body :=
    (candidate' ∈ₘ subset') ∧ₘ
      ((element ∈ₘ subset') ⟶ₘ
        ((¬ₘ (candidate' ≐ₘ element)) ⟶ₘ
          (⟨element, candidate'⟩ₘ ∈ₘ relation')))
  body.forallFreeTop SetSort.set

def maximum_natural_order_definition_instance {bound free : SetContext}
    (relation carrier subset candidate : SetTerm bound free) : SetFormula bound free :=
  ((is_natural_discrete_linear_order_formula relation carrier ∧ₘ
      ((subset ⊆ₘ carrier) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ
    ((candidate ≐ₘ maxₘ(relation, subset)) ↔ₘ
      maximum_spec relation subset candidate))

def maximum_natural_order_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (maximum_natural_order_definition_instance
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

/-! ## 理论组合与嵌入 -/

def relation_image_separation_theory : SetTheory :=
  Theory.insert relation_image_separation_axiom finite_ordinal_theory

def image_operator_theory : SetTheory :=
  Theory.insert image_definition_axiom relation_image_separation_theory

def restriction_operator_theory : SetTheory :=
  Theory.insert restriction_definition_axiom image_operator_theory

def minimum_linear_order_theory : SetTheory :=
  Theory.insert minimum_linear_order_definition_axiom restriction_operator_theory

def minimum_natural_order_theory : SetTheory :=
  Theory.insert minimum_natural_order_definition_axiom minimum_linear_order_theory

def order_operator_theory : SetTheory :=
  Theory.insert maximum_natural_order_definition_axiom minimum_natural_order_theory

derive_theory_subset finite_ordinal_theory ⊆ relation_image_separation_theory

derive_theory_subset relation_image_separation_theory ⊆ image_operator_theory

derive_theory_subset image_operator_theory ⊆ restriction_operator_theory

derive_theory_subset restriction_operator_theory ⊆ minimum_linear_order_theory

derive_theory_subset minimum_linear_order_theory ⊆ minimum_natural_order_theory

derive_theory_subset minimum_natural_order_theory ⊆ order_operator_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
