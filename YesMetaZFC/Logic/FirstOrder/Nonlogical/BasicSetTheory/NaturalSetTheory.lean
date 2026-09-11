import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Infinity

/-!
# 自然数集合基础设施

本模块用内在类型语法定义有界、无界及自然数子集序型。所有定义公理直接构造为
`SetSentence`，不再为对象语言项维护 admissibility、检查证书或闭句证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 有界与无界子集 -/

def unbounded_subset_condition {bound free : SetContext}
    (subset relation carrier : SetTerm bound free) : SetFormula bound free :=
  let boundElement : SetTerm bound (SetSort.set :: free) := .fvar .here
  let element : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let subset' := subset.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let relation' := relation.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let witness :=
    ((element ∈ₘ subset') ∧ₘ
      (⟨boundElement.weakenFree SetSort.set, element⟩ₘ ∈ₘ relation')).existsFreeTop
      SetSort.set
  (subset ⊆ₘ carrier) ∧ₘ
    ((boundElement ∈ₘ carrier.weakenFree SetSort.set ⟶ₘ witness).forallFreeTop
      SetSort.set)

def unbounded_subset_definition_instance {bound free : SetContext}
    (subset relation carrier : SetTerm bound free) : SetFormula bound free :=
  unboundedₘ(subset, relation, carrier) ↔ₘ
    unbounded_subset_condition subset relation carrier

def unbounded_subset_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let subset : SetOpenTerm free := .fvar (.there (.there .here))
  let relation : SetOpenTerm free := .fvar (.there .here)
  let carrier : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (unbounded_subset_definition_instance subset relation carrier)

def bounded_subset_condition {bound free : SetContext}
    (subset relation carrier : SetTerm bound free) : SetFormula bound free :=
  let boundElement : SetTerm bound (SetSort.set :: free) := .fvar .here
  let element : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let subset' := subset.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let relation' := relation.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let boundBody :=
    (boundElement ∈ₘ carrier.weakenFree SetSort.set) ∧ₘ
      ((element ∈ₘ subset') ⟶ₘ
        (⟨element, boundElement.weakenFree SetSort.set⟩ₘ ∈ₘ relation')).forallFreeTop
        SetSort.set
  (subset ⊆ₘ carrier) ∧ₘ boundBody.existsFreeTop SetSort.set

def bounded_subset_definition_instance {bound free : SetContext}
    (subset relation carrier : SetTerm bound free) : SetFormula bound free :=
  boundedₘ(subset, relation, carrier) ↔ₘ
    bounded_subset_condition subset relation carrier

def bounded_subset_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let subset : SetOpenTerm free := .fvar (.there (.there .here))
  let relation : SetOpenTerm free := .fvar (.there .here)
  let carrier : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (bounded_subset_definition_instance subset relation carrier)

/-! ## 自然离散线性序的序型 -/

def natural_order_type_condition {bound free : SetContext}
    (relation carrier candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ∈ₘ ωₘ) ∧ₘ
    is_order_isomorphic_formula
      relation carrier (εₘ(candidate)) candidate

def natural_order_type_definition_instance {bound free : SetContext}
    (relation carrier candidate : SetTerm bound free) : SetFormula bound free :=
  is_natural_discrete_linear_order_formula relation carrier ⟶ₘ
    ((candidate ≐ₘ ord_typeₘ(relation, carrier)) ↔ₘ
      natural_order_type_condition relation carrier candidate)

def natural_order_type_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let relation : SetOpenTerm free := .fvar (.there (.there .here))
  let carrier : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_order_type_definition_instance relation carrier candidate)

/-! ## 自然数子集的序型 -/

def natural_subset_type_condition {bound free : SetContext}
    (subset candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ∈ₘ Sₘ(ωₘ)) ∧ₘ
    ((boundedₘ(subset, εₘ(ωₘ), ωₘ) ⟶ₘ
        ((candidate ∈ₘ ωₘ) ∧ₘ
          is_order_isomorphic_formula
            (εₘ(subset)) subset (εₘ(candidate)) candidate)) ∧ₘ
      (¬ₘ boundedₘ(subset, εₘ(ωₘ), ωₘ) ⟶ₘ
        (candidate ≐ₘ ωₘ)))

def natural_subset_type_definition_instance {bound free : SetContext}
    (subset candidate : SetTerm bound free) : SetFormula bound free :=
  (subset ⊆ₘ ωₘ) ⟶ₘ
    ((candidate ≐ₘ nat_subset_typeₘ(subset)) ↔ₘ
      natural_subset_type_condition subset candidate)

def natural_subset_type_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set]
  let subset : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_subset_type_definition_instance subset candidate)

/-! ## 理论组合与嵌入 -/

def unbounded_subset_theory : SetTheory :=
  Theory.insert unbounded_subset_definition_axiom infinity_theory

def bounded_subset_theory : SetTheory :=
  Theory.insert bounded_subset_definition_axiom unbounded_subset_theory

def natural_order_type_theory : SetTheory :=
  Theory.insert natural_order_type_definition_axiom bounded_subset_theory

def natural_subset_type_theory : SetTheory :=
  Theory.insert natural_subset_type_definition_axiom natural_order_type_theory

def natural_set_theory : SetTheory :=
  natural_subset_type_theory

derive_theory_subset infinity_theory ⊆ unbounded_subset_theory

derive_theory_subset unbounded_subset_theory ⊆ bounded_subset_theory

derive_theory_subset bounded_subset_theory ⊆ natural_order_type_theory

derive_theory_subset natural_order_type_theory ⊆ natural_subset_type_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
