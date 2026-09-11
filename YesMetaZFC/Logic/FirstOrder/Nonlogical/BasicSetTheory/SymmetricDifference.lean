import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.PowerSetCoding

/-!
# 对称差运算

本模块用逐元素异或规格定义对称差项。存在性采用参数化分离 schema，定义项由闭
定义公理给出，不再维护 admissibility、检查证书或手工变量展开接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

def symmetric_difference_member_condition {bound free : SetContext}
    (left right element : SetTerm bound free) : SetFormula bound free :=
  ((element ∈ₘ left) ∧ₘ ¬ₘ (element ∈ₘ right)) ∨ₘ
    ((element ∈ₘ right) ∧ₘ ¬ₘ (element ∈ₘ left))

def symmetric_difference_spec {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ (left.weakenFree SetSort.set ∪ₘ
        right.weakenFree SetSort.set)) ∧ₘ
      symmetric_difference_member_condition
        (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)
        element)

def symmetric_difference_separation_exists {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (symmetric_difference_spec
    (left.weakenFree SetSort.set)
    (right.weakenFree SetSort.set)
    candidate).existsFreeTop SetSort.set

def symmetric_difference_predicate {free : SetContext}
    (left right : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    ((element ∈ₘ (left.weakenFree SetSort.set ∪ₘ
        right.weakenFree SetSort.set)) ∧ₘ
      symmetric_difference_member_condition
        (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)
        element).abstractFreeTop

def symmetric_difference_definition_instance {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ sym_diffₘ(left, right)) ↔ₘ
    symmetric_difference_spec left right candidate

def symmetric_difference_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let left : SetOpenTerm free := .fvar (.there (.there .here))
  let right : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (symmetric_difference_definition_instance left right candidate)

/-! ## 理论组合与嵌入 -/

def symmetric_difference_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (left right : SetOpenTerm free),
      sentence =
        (symmetric_difference_predicate left right).separation_axiom) ∨
    power_set_bijection_theory sentence

def symmetric_difference_theory : SetTheory :=
  Theory.insert symmetric_difference_definition_axiom
    symmetric_difference_separation_theory

derive_theory_subset power_set_bijection_theory ⊆ symmetric_difference_separation_theory

derive_theory_subset symmetric_difference_separation_theory ⊆ symmetric_difference_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
