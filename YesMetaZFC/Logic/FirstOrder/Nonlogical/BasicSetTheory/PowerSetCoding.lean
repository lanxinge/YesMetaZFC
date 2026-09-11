import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.IndexOrder

/-!
# 幂集的二值函数编码

本模块直接用内在类型语法刻画幂集到二值函数空间的规范编码。编码图的存在性
采用参数化分离 schema，定义项则由闭定义公理给出。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 二值编码规格 -/

def binary_value_set_term {bound free : SetContext} : SetTerm bound free :=
  {numₘ(0), numₘ(1)}ₘ

def power_set_bijection_member_condition {bound free : SetContext}
    (natural element : SetTerm bound free) : SetFormula bound free :=
  let natural' := natural.weakenFree SetSort.set
  let element' := element.weakenFree SetSort.set
  let coordinate : SetTerm bound (SetSort.set :: free) :=
    .fvar .here
  let subset := (element')₀ₘ
  let function := (element')₁ₘ
  let coordinate_in_subset := coordinate ∈ₘ subset
  let coordinate_in_natural := coordinate ∈ₘ natural'
  let function_at_coordinate := ⟨coordinate, numₘ(1)⟩ₘ ∈ₘ function
  let zero_function_at_coordinate := ⟨coordinate, numₘ(0)⟩ₘ ∈ₘ function
  let pointwise_condition :=
    (coordinate_in_natural ⟶ₘ
      ((coordinate_in_subset ↔ₘ function_at_coordinate) ∧ₘ
        ((¬ₘ coordinate_in_subset) ↔ₘ zero_function_at_coordinate))).forallFreeTop
      SetSort.set
  (element ∈ₘ (𝒫ₘ(natural) ×ₘ
      Mapₘ(natural, binary_value_set_term))) ∧ₘ pointwise_condition

def power_set_bijection_spec {bound free : SetContext}
    (natural candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (power_set_bijection_member_condition
      (natural.weakenFree SetSort.set) element)

def power_set_bijection_separation_exists {bound free : SetContext}
    (natural : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (power_set_bijection_spec
    (natural.weakenFree SetSort.set) candidate).existsFreeTop SetSort.set

def power_set_bijection_predicate {free : SetContext}
    (natural : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (power_set_bijection_member_condition
      (natural.weakenFree SetSort.set) element).abstractFreeTop

def power_set_bijection_definition_instance {bound free : SetContext}
    (natural candidate : SetTerm bound free) : SetFormula bound free :=
  is_natural_number_formula natural ⟶ₘ
    ((candidate ≐ₘ chiₘ(natural)) ↔ₘ
      power_set_bijection_spec natural candidate)

def power_set_bijection_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set]
  let natural : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (power_set_bijection_definition_instance natural candidate)

/-! ## 理论组合与嵌入 -/

def power_set_bijection_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (natural : SetOpenTerm free),
      sentence = (power_set_bijection_predicate natural).separation_axiom) ∨
    index_order_theory sentence

def power_set_bijection_theory : SetTheory :=
  Theory.insert power_set_bijection_definition_axiom
    power_set_bijection_separation_theory

derive_theory_subset index_order_theory ⊆ power_set_bijection_separation_theory

derive_theory_subset power_set_bijection_separation_theory ⊆ power_set_bijection_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
