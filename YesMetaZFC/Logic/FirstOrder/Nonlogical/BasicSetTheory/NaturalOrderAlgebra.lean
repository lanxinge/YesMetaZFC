import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Foundation

/-!
# 自然离散线性序下的代数运算

本模块建立带载体的序和与词典序积。两者的对象语言参数全部显式保留，词典序积
的存在性采用参数化分离 schema，不再维护一次性闭分离公理及其检查边界。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 线性序和 -/

def order_sum_guard {bound free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier : SetTerm bound free) :
    SetFormula bound free :=
  is_linear_order_formula firstRelation firstCarrier ∧ₘ
    (is_linear_order_formula secondRelation secondCarrier ∧ₘ
      ((firstCarrier ∩ₘ secondCarrier) ≐ₘ ∅ₘ))

def order_sum_witness {bound free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier : SetTerm bound free) :
    SetTerm bound free :=
  (firstRelation ∪ₘ secondRelation) ∪ₘ
    (firstCarrier ×ₘ secondCarrier)

def order_sum_definition_instance {bound free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier : SetTerm bound free) :
    SetFormula bound free :=
  order_sum_guard firstRelation firstCarrier secondRelation secondCarrier ⟶ₘ
    (ord_sumₘ(firstRelation, firstCarrier, secondRelation, secondCarrier) ≐ₘ
      order_sum_witness firstRelation firstCarrier secondRelation secondCarrier)

def order_sum_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (order_sum_definition_instance
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

/-! ## 词典序积 -/

def order_product_coordinate_condition {bound free : SetContext}
    (firstRelation secondRelation left right : SetTerm bound free) :
    SetFormula bound free :=
  (⟨(left)₀ₘ, (right)₀ₘ⟩ₘ ∈ₘ firstRelation) ∨ₘ
    (((left)₀ₘ ≐ₘ (right)₀ₘ) ∧ₘ
      (⟨(left)₁ₘ, (right)₁ₘ⟩ₘ ∈ₘ secondRelation))

def order_product_member_condition {bound free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier element :
      SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let right : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let element' := element.weakenFree SetSort.set |>.weakenFree SetSort.set
  let firstProduct :=
    (firstCarrier.weakenFree SetSort.set |>.weakenFree SetSort.set) ×ₘ
      (secondCarrier.weakenFree SetSort.set |>.weakenFree SetSort.set)
  let firstRelation' := firstRelation.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let secondRelation' := secondRelation.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  ((((left ∈ₘ firstProduct) ∧ₘ (right ∈ₘ firstProduct)) ∧ₘ
      ((element' ≐ₘ ⟨left, right⟩ₘ) ∧ₘ
        order_product_coordinate_condition firstRelation' secondRelation' left right))
      |>.existsFreeTop SetSort.set)
    |>.existsFreeTop SetSort.set

def order_product_spec {bound free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier candidate :
      SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (order_product_member_condition
      (firstRelation.weakenFree SetSort.set)
      (firstCarrier.weakenFree SetSort.set)
      (secondRelation.weakenFree SetSort.set)
      (secondCarrier.weakenFree SetSort.set)
      element)

def order_product_exists {bound free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier : SetTerm bound free) :
    SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (order_product_spec
    (firstRelation.weakenFree SetSort.set)
    (firstCarrier.weakenFree SetSort.set)
    (secondRelation.weakenFree SetSort.set)
    (secondCarrier.weakenFree SetSort.set)
    candidate).existsFreeTop SetSort.set

def order_product_predicate {free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier : SetOpenTerm free) :
    SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (order_product_member_condition
      (firstRelation.weakenFree SetSort.set)
      (firstCarrier.weakenFree SetSort.set)
      (secondRelation.weakenFree SetSort.set)
      (secondCarrier.weakenFree SetSort.set)
      element).abstractFreeTop

def order_product_definition_instance {bound free : SetContext}
    (firstRelation firstCarrier secondRelation secondCarrier candidate :
      SetTerm bound free) : SetFormula bound free :=
  (is_linear_order_formula firstRelation firstCarrier ∧ₘ
      is_linear_order_formula secondRelation secondCarrier) ⟶ₘ
    ((candidate ≐ₘ ord_prodₘ(
        firstRelation, firstCarrier, secondRelation, secondCarrier)) ↔ₘ
      order_product_spec
        firstRelation firstCarrier secondRelation secondCarrier candidate)

def order_product_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (order_product_definition_instance
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

/-! ## 理论组合与嵌入 -/

def natural_order_algebra_base_theory : SetTheory :=
  foundation_theory

def order_sum_theory : SetTheory :=
  Theory.insert order_sum_definition_axiom natural_order_algebra_base_theory

def order_product_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext)
      (firstRelation firstCarrier secondRelation secondCarrier : SetOpenTerm free),
      sentence =
        (order_product_predicate firstRelation firstCarrier
          secondRelation secondCarrier).separation_axiom) ∨
    order_sum_theory sentence

def order_product_theory : SetTheory :=
  Theory.insert order_product_definition_axiom
    order_product_separation_theory

derive_theory_subset foundation_theory ⊆ natural_order_algebra_base_theory

derive_theory_subset natural_order_algebra_base_theory ⊆ order_sum_theory

derive_theory_subset order_sum_theory ⊆ order_product_separation_theory

derive_theory_subset order_product_separation_theory ⊆ order_product_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
