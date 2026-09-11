import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.WellOrderComparison

/-!
# 序数、自然数与良序比较映射

本模块只保留比较映射、序数/自然数谓词以及成员序极值的内在定义设施。对象语言
项的良构性由 `SetTerm` 类型携带，理论成员由闭句类型携带。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 良序比较映射 -/

def well_order_comparison_map_definition_instance {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier candidate :
      SetTerm bound free) : SetFormula bound free :=
  (is_well_order_formula sourceRelation sourceCarrier ∧ₘ
      is_well_order_formula targetRelation targetCarrier) ⟶ₘ
    ((candidate ≐ₘ wo_compareₘ(
        sourceRelation, sourceCarrier, targetRelation, targetCarrier)) ↔ₘ
      (maximal_order_isomorphism_spec
        sourceRelation sourceCarrier targetRelation targetCarrier candidate ∧ₘ
        (sourceCarrier ≐ₘ domₘ(candidate))))

def well_order_comparison_map_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (well_order_comparison_map_definition_instance
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

/-! ## 序数与自然数谓词 -/

def is_ordinal_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  is_transitive_set_formula set ∧ₘ
    is_well_order_formula (εₘ(set)) set

def is_ordinal_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  is_ordinal_formula set ↔ₘ is_ordinal_condition set

def is_ordinal_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_ordinal_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

def is_natural_number_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  is_transitive_set_formula set ∧ₘ
    is_natural_discrete_linear_order_formula (εₘ(set)) set

def is_natural_number_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  is_natural_number_formula set ↔ₘ is_natural_number_condition set

def is_natural_number_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_natural_number_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-! ## 成员序极值 -/

def ordinal_membership_minimum_spec {bound free : SetContext}
    (subset candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  let subset' := subset.weakenFree SetSort.set
  let candidate' := candidate.weakenFree SetSort.set
  ((candidate' ∈ₘ subset') ∧ₘ
      ((element ∈ₘ subset') ⟶ₘ (candidate' ∈ₘ Sₘ(element))))
    |>.forallFreeTop SetSort.set

def ordinal_membership_minimum_definition_instance {bound free : SetContext}
    (ordinal subset candidate : SetTerm bound free) : SetFormula bound free :=
  (is_ordinal_formula ordinal ∧ₘ
      ((subset ⊆ₘ ordinal) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ
    ((candidate ≐ₘ minεₘ(ordinal, subset)) ↔ₘ
      ordinal_membership_minimum_spec subset candidate)

def ordinal_membership_minimum_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (ordinal_membership_minimum_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

def natural_membership_maximum_spec {bound free : SetContext}
    (subset candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  let subset' := subset.weakenFree SetSort.set
  let candidate' := candidate.weakenFree SetSort.set
  ((candidate' ∈ₘ subset') ∧ₘ
      ((element ∈ₘ subset') ⟶ₘ (element ∈ₘ Sₘ(candidate'))))
    |>.forallFreeTop SetSort.set

def natural_membership_maximum_definition_instance {bound free : SetContext}
    (natural subset candidate : SetTerm bound free) : SetFormula bound free :=
  (is_natural_number_formula natural ∧ₘ
      ((subset ⊆ₘ natural) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ
    ((candidate ≐ₘ maxεₘ(natural, subset)) ↔ₘ
      natural_membership_maximum_spec subset candidate)

def natural_membership_maximum_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (natural_membership_maximum_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 理论组合与嵌入 -/

def well_order_comparison_map_theory : SetTheory :=
  Theory.insert well_order_comparison_map_definition_axiom
    well_order_comparison_theory

def ordinal_predicate_theory : SetTheory :=
  Theory.insert is_ordinal_definition_axiom
    well_order_comparison_map_theory

def natural_number_predicate_theory : SetTheory :=
  Theory.insert is_natural_number_definition_axiom
    ordinal_predicate_theory

def ordinal_membership_minimum_theory : SetTheory :=
  Theory.insert ordinal_membership_minimum_definition_axiom
    natural_number_predicate_theory

def ordinal_natural_theory : SetTheory :=
  Theory.insert natural_membership_maximum_definition_axiom
    ordinal_membership_minimum_theory

derive_theory_subset well_order_comparison_theory ⊆ well_order_comparison_map_theory

derive_theory_subset well_order_comparison_map_theory ⊆ ordinal_predicate_theory

derive_theory_subset ordinal_predicate_theory ⊆ natural_number_predicate_theory

derive_theory_subset natural_number_predicate_theory ⊆ ordinal_membership_minimum_theory

derive_theory_subset ordinal_membership_minimum_theory ⊆ ordinal_natural_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
