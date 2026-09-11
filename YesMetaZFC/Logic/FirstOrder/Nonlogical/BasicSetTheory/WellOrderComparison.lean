import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.OrderOperators
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection

/-!
# 良序初始段与比较基础设施

严格初始段与关系限制均采用内在类型规格。初始段分离使用参数化 schema，关系
限制直接定义为关系与笛卡尔平方的交，不再携带章节性的良序护栏。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 理论基座 -/

def well_order_comparison_base_theory : SetTheory :=
  fun sentence =>
    order_operator_theory sentence ∨ binary_intersection_operator_theory sentence

/-! ## 严格初始段 -/

def strict_initial_segment_member_condition {bound free : SetContext}
    (point relation element : SetTerm bound free) : SetFormula bound free :=
  ⟨element, point⟩ₘ ∈ₘ relation

def strict_initial_segment_spec {bound free : SetContext}
    (point relation carrier candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ carrier.weakenFree SetSort.set) ∧ₘ
      strict_initial_segment_member_condition
        (point.weakenFree SetSort.set)
        (relation.weakenFree SetSort.set)
        element)

def strict_initial_segment_exists {bound free : SetContext}
    (point relation carrier : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (strict_initial_segment_spec
    (point.weakenFree SetSort.set)
    (relation.weakenFree SetSort.set)
    (carrier.weakenFree SetSort.set)
    candidate).existsFreeTop SetSort.set

def strict_initial_segment_predicate {free : SetContext}
    (point relation carrier : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    ((element ∈ₘ carrier.weakenFree SetSort.set) ∧ₘ
      strict_initial_segment_member_condition
        (point.weakenFree SetSort.set)
        (relation.weakenFree SetSort.set)
        element).abstractFreeTop

def strict_initial_segment_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (point relation carrier : SetOpenTerm free),
      sentence =
        (strict_initial_segment_predicate point relation carrier).separation_axiom) ∨
    well_order_comparison_base_theory sentence

def initial_segment_definition_instance {bound free : SetContext}
    (point relation carrier candidate : SetTerm bound free) : SetFormula bound free :=
  (is_well_order_formula relation carrier ∧ₘ
      (point ∈ₘ carrier)) ⟶ₘ
    ((candidate ≐ₘ segₘ(point, relation, carrier)) ↔ₘ
      strict_initial_segment_spec point relation carrier candidate)

def initial_segment_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (initial_segment_definition_instance
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

/-! ## 关系限制 -/

abbrev relation_restriction_witness_term {bound free : SetContext}
    (relation subset : SetTerm bound free) : SetTerm bound free :=
  relation ∩ₘ (subset ×ₘ subset)

def relation_restriction_definition_instance {bound free : SetContext}
    (relation subset : SetTerm bound free) : SetFormula bound free :=
  rel_restrictₘ(relation, subset) ≐ₘ
    relation_restriction_witness_term relation subset

def relation_restriction_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (relation_restriction_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 最大序同构规格 -/

def corresponding_initial_segments_condition {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier pair : SetTerm bound free) :
    SetFormula bound free :=
  is_order_isomorphic_formula
    (rel_restrictₘ(sourceRelation,
      segₘ((pair)₀ₘ, sourceRelation, sourceCarrier)))
    (segₘ((pair)₀ₘ, sourceRelation, sourceCarrier))
    (rel_restrictₘ(targetRelation,
      segₘ((pair)₁ₘ, targetRelation, targetCarrier)))
    (segₘ((pair)₁ₘ, targetRelation, targetCarrier))

def maximal_order_isomorphism_spec {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier candidate :
      SetTerm bound free) : SetFormula bound free :=
  is_well_order_formula sourceRelation sourceCarrier ∧ₘ
    (is_well_order_formula targetRelation targetCarrier ∧ₘ
      let pair : SetTerm bound (SetSort.set :: free) := .fvar .here
      membership_specification candidate
        ((pair ∈ₘ (sourceCarrier.weakenFree SetSort.set ×ₘ
            targetCarrier.weakenFree SetSort.set)) ∧ₘ
          corresponding_initial_segments_condition
            (sourceRelation.weakenFree SetSort.set)
            (sourceCarrier.weakenFree SetSort.set)
            (targetRelation.weakenFree SetSort.set)
            (targetCarrier.weakenFree SetSort.set)
            pair))

/-! ## 理论组合与嵌入 -/

def initial_segment_operator_theory : SetTheory :=
  Theory.insert initial_segment_definition_axiom
    strict_initial_segment_separation_theory

def well_order_comparison_theory : SetTheory :=
  Theory.insert relation_restriction_definition_axiom
    initial_segment_operator_theory

derive_theory_subset order_operator_theory ⊆ well_order_comparison_base_theory

derive_theory_subset binary_intersection_operator_theory ⊆ well_order_comparison_base_theory

derive_theory_subset well_order_comparison_base_theory ⊆ strict_initial_segment_separation_theory

derive_theory_subset strict_initial_segment_separation_theory ⊆ initial_segment_operator_theory

derive_theory_subset initial_segment_operator_theory ⊆ well_order_comparison_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
