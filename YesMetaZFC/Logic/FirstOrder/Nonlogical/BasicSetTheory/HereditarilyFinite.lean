import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.HypertransfiniteRecursion
/-!
# 彻底有限集合

本模块只保留彻底有限集合相关的对象语言定义、闭定义公理和理论组合。所有项与公式
均由内在上下文记录排序和作用域；不再生成变量编号，也不再携带 `Admissible`、
`Sentence` 或理论良构性证明。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 传递闭包 -/

def transitive_closure_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let lower : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((source ⊆ₘ candidate) ∧ₘ is_transitive_set_formula candidate) ∧ₘ
    (((source.weakenFree SetSort.set ⊆ₘ lower) ∧ₘ
      is_transitive_set_formula lower) ⟶ₘ
      (candidate.weakenFree SetSort.set ⊆ₘ lower)).forallFreeTop SetSort.set

def transitive_closure_definition_instance {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ tcₘ(source)) ↔ₘ transitive_closure_spec source candidate

def transitive_closure_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (transitive_closure_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 有限层级与 `V_ω` -/

def finite_hierarchy_step_body :
    SetOpenFormula [SetSort.set, SetSort.set, SetSort.set] :=
  let next : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] := .fvar .here
  let current : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] :=
    .fvar (.there .here)
  next ≐ₘ 𝒫ₘ(current)

def finite_hierarchy_step : RecursiveStep where
  parameterContext := []
  body := finite_hierarchy_step_body

def finite_hierarchy_spec (sequence : SetOpenTerm []) : SetOpenFormula [] :=
  transfinite_recursion_spec finite_hierarchy_step ∅ₘ sequence

def finite_hierarchy_definition_axiom : SetSentence :=
  finite_hierarchy_spec Vseqₘ

def finite_universe_spec (universeSet : SetOpenTerm []) : SetOpenFormula [] :=
  universeSet ≐ₘ ⋃ₘ(ranₘ(Vseqₘ))

def finite_universe_definition_axiom : SetSentence :=
  finite_universe_spec Vωₘ

def finite_universe_successor_term {bound free : SetContext} : Nat → SetTerm bound free
  | 0 => Vωₘ
  | level + 1 => 𝒫ₘ(finite_universe_successor_term level)

abbrev finite_hierarchy_value_term {bound free : SetContext}
    (index : SetTerm bound free) : SetTerm bound free :=
  Vseqₘ ·ₘ index

namespace Symbols

scoped notation:max "Vₘ(" index ")" => finite_hierarchy_value_term index
scoped notation:max "Vω⁺ₘ[" level "]" => finite_universe_successor_term level

end Symbols

/-! ## 自然数上的成员序 -/

abbrev natural_membership_order_term : SetOpenTerm [] := εₘ(ωₘ)

def natural_membership_order_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ∈ₘ ωₘ) ∧ₘ ((right ∈ₘ ωₘ) ∧ₘ (left ∈ₘ right))

def natural_membership_order_spec {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  let relationDeep : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    @Term.weakenFree signature bound (SetSort.set :: free)
      SetSort.set SetSort.set
      (@Term.weakenFree signature bound free
        SetSort.set SetSort.set relation)
  (((⟨left, right⟩ₘ ∈ₘ relationDeep) ↔ₘ
    natural_membership_order_condition
      (bound := bound) (free := [SetSort.set, SetSort.set] ++ free)
      left right).forallFreeTop SetSort.set)
    |>.forallFreeTop SetSort.set

/-! ## 遗传有限集 -/

def hereditarily_finite_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  finiteₘ(tcₘ(set))

def hereditarily_finite_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  hereditarily_finiteₘ(set) ↔ₘ hereditarily_finite_condition set

def hereditarily_finite_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (hereditarily_finite_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-! ## 有限子集收集 -/

def finite_subset_collection_member_condition {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound (SetSort.set :: free) :=
  let subset : SetTerm bound (SetSort.set :: free) := .fvar .here
  (subset ∈ₘ 𝒫ₘ(source.weakenFree SetSort.set)) ∧ₘ finiteₘ(subset)

def finite_subset_collection_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  membership_specification candidate
    (finite_subset_collection_member_condition source)

def finite_subset_collection_separation_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (finite_subset_collection_spec
      (source.weakenFree SetSort.set) candidate).existsFreeTop SetSort.set

def finite_subset_collection_separation_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (finite_subset_collection_separation_exists
      (.fvar .here : SetOpenTerm [SetSort.set]))

def finite_subset_collection_definition_instance {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ FinSubₘ(source)) ↔ₘ
    finite_subset_collection_spec source candidate

def finite_subset_collection_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (finite_subset_collection_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 理论组合 -/

def transitive_closure_operator_theory : SetTheory :=
  Theory.insert transitive_closure_definition_axiom natural_arithmetic_theory

def finite_hierarchy_operator_theory : SetTheory :=
  Theory.insert finite_hierarchy_definition_axiom transitive_closure_operator_theory

def finite_universe_operator_theory : SetTheory :=
  Theory.insert finite_universe_definition_axiom finite_hierarchy_operator_theory

def hereditarily_finite_predicate_theory : SetTheory :=
  Theory.insert hereditarily_finite_definition_axiom finite_universe_operator_theory

def finite_subset_collection_separation_theory : SetTheory :=
  Theory.insert finite_subset_collection_separation_axiom
    hereditarily_finite_predicate_theory

def finite_subset_collection_operator_theory : SetTheory :=
  Theory.insert finite_subset_collection_definition_axiom
    finite_subset_collection_separation_theory

def hereditarily_finite_theory : SetTheory :=
  finite_subset_collection_operator_theory

derive_theory_subset natural_arithmetic_theory ⊆ transitive_closure_operator_theory

derive_theory_subset transitive_closure_operator_theory ⊆ finite_hierarchy_operator_theory

derive_theory_subset finite_hierarchy_operator_theory ⊆ finite_universe_operator_theory

derive_theory_subset finite_universe_operator_theory ⊆ hereditarily_finite_predicate_theory

derive_theory_subset hereditarily_finite_predicate_theory ⊆ finite_subset_collection_separation_theory

derive_theory_subset finite_subset_collection_separation_theory ⊆ hereditarily_finite_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
