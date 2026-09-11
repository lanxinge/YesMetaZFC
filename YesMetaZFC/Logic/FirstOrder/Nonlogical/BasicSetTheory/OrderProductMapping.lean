import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalOrderAlgebra

/-!
# 映射直积基础设施

映射直积的成员由两个源坐标及其函数值直接生成。分离母集显式取源直积到目标
直积的笛卡尔平方，分离实例通过参数化 `SetPredicate` 提供。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

def mapping_product_member_condition {bound free : SetContext}
    (firstFunction firstSource secondFunction secondSource element :
      SetTerm bound free) : SetFormula bound free :=
  let first : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let second : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let element' := element.weakenFree SetSort.set |>.weakenFree SetSort.set
  let firstSource' := firstSource.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let secondSource' := secondSource.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let firstFunction' := firstFunction.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let secondFunction' := secondFunction.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  ((((first ∈ₘ firstSource') ∧ₘ (second ∈ₘ secondSource')) ∧ₘ
      (element' ≐ₘ
        ⟨⟨first, second⟩ₘ,
          ⟨firstFunction' ·ₘ first, secondFunction' ·ₘ second⟩ₘ⟩ₘ))
      |>.existsFreeTop SetSort.set)
    |>.existsFreeTop SetSort.set

def mapping_product_spec {bound free : SetContext}
    (firstFunction firstSource secondFunction secondSource candidate :
      SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (mapping_product_member_condition
      (firstFunction.weakenFree SetSort.set)
      (firstSource.weakenFree SetSort.set)
      (secondFunction.weakenFree SetSort.set)
      (secondSource.weakenFree SetSort.set)
      element)

def mapping_product_separation_spec {bound free : SetContext}
    (firstFunction firstSource firstTarget secondFunction secondSource secondTarget
      candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  let firstProduct := firstSource.weakenFree SetSort.set ×ₘ
    secondSource.weakenFree SetSort.set
  let secondProduct := firstTarget.weakenFree SetSort.set ×ₘ
    secondTarget.weakenFree SetSort.set
  membership_specification candidate
    ((element ∈ₘ (firstProduct ×ₘ secondProduct)) ∧ₘ
      mapping_product_member_condition
        (firstFunction.weakenFree SetSort.set)
        (firstSource.weakenFree SetSort.set)
        (secondFunction.weakenFree SetSort.set)
        (secondSource.weakenFree SetSort.set)
        element)

def mapping_product_separation_exists {bound free : SetContext}
    (firstFunction firstSource firstTarget secondFunction secondSource secondTarget :
      SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (mapping_product_separation_spec
    (firstFunction.weakenFree SetSort.set)
    (firstSource.weakenFree SetSort.set)
    (firstTarget.weakenFree SetSort.set)
    (secondFunction.weakenFree SetSort.set)
    (secondSource.weakenFree SetSort.set)
    (secondTarget.weakenFree SetSort.set)
    candidate).existsFreeTop SetSort.set

def mapping_product_predicate {free : SetContext}
    (firstFunction firstSource firstTarget secondFunction secondSource secondTarget :
      SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    ((element ∈ₘ
        ((firstSource.weakenFree SetSort.set ×ₘ secondSource.weakenFree SetSort.set) ×ₘ
          (firstTarget.weakenFree SetSort.set ×ₘ secondTarget.weakenFree SetSort.set))) ∧ₘ
      mapping_product_member_condition
        (firstFunction.weakenFree SetSort.set)
        (firstSource.weakenFree SetSort.set)
        (secondFunction.weakenFree SetSort.set)
        (secondSource.weakenFree SetSort.set)
        element).abstractFreeTop

def mapping_product_definition_instance {bound free : SetContext}
    (firstFunction firstSource firstTarget secondFunction secondSource secondTarget candidate :
      SetTerm bound free) : SetFormula bound free :=
  (is_mapping_formula firstFunction firstSource firstTarget ∧ₘ
      is_mapping_formula secondFunction secondSource secondTarget) ⟶ₘ
    ((candidate ≐ₘ map_prodₘ(firstFunction, secondFunction)) ↔ₘ
      mapping_product_spec firstFunction firstSource
        secondFunction secondSource candidate)

def mapping_product_definition_axiom : SetSentence :=
  let free :=
    [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
      SetSort.set, SetSort.set, SetSort.set]
  let firstFunction : SetOpenTerm free :=
    .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let firstSource : SetOpenTerm free :=
    .fvar (.there (.there (.there (.there (.there .here)))))
  let firstTarget : SetOpenTerm free :=
    by exact .fvar (.there (.there (.there (.there .here))))
  let secondFunction : SetOpenTerm free :=
    .fvar (.there (.there (.there .here)))
  let secondSource : SetOpenTerm free :=
    .fvar (.there (.there .here))
  let secondTarget : SetOpenTerm free :=
    .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (mapping_product_definition_instance
      firstFunction firstSource firstTarget
      secondFunction secondSource secondTarget candidate)

def mapping_product_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext)
      (firstFunction firstSource firstTarget secondFunction secondSource secondTarget :
        SetOpenTerm free),
      sentence =
        (mapping_product_predicate firstFunction firstSource firstTarget
          secondFunction secondSource secondTarget).separation_axiom) ∨
    order_product_theory sentence

def mapping_product_theory : SetTheory :=
  Theory.insert mapping_product_definition_axiom
    mapping_product_separation_theory

derive_theory_subset order_product_theory ⊆ mapping_product_separation_theory

derive_theory_subset mapping_product_separation_theory ⊆ mapping_product_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
