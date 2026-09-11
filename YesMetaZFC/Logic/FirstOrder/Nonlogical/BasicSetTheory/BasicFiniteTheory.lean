import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.SymmetricDifference

/-!
# 基本有穷理论

本模块直接用内在类型语法定义有穷性、等势、基数比较和戴德金有限性。闭定义公理
由 `SetSentence` 类型保证闭合，理论不再携带 admissibility 或 sentence 证明链。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 有穷性 -/

def is_finite_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  let orderRelation : SetTerm bound (SetSort.set :: free) := .fvar .here
  (is_natural_discrete_linear_order_formula
    orderRelation (set.weakenFree SetSort.set)).existsFreeTop SetSort.set

def is_finite_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  finiteₘ(set) ↔ₘ is_finite_condition set

def is_finite_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_finite_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-! ## 等势与基数比较 -/

def is_equinumerous_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let function : SetTerm bound (SetSort.set :: free) := .fvar .here
  (is_bijection_formula
    function (left.weakenFree SetSort.set) (right.weakenFree SetSort.set)).existsFreeTop
    SetSort.set

def is_equinumerous_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ≈ₘ right) ↔ₘ is_equinumerous_condition left right

def is_equinumerous_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_equinumerous_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def cardinality_leq_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let function : SetTerm bound (SetSort.set :: free) := .fvar .here
  (left ≠ₘ ∅ₘ) ⟶ₘ
    (is_injective_formula
      function (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)).existsFreeTop SetSort.set

def cardinality_leq_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ≼ₘ right) ↔ₘ cardinality_leq_condition left right

def cardinality_leq_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (cardinality_leq_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def cardinality_strict_less_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ≼ₘ right) ∧ₘ ¬ₘ (left ≈ₘ right)

def cardinality_strict_less_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ≺ₘ right) ↔ₘ cardinality_strict_less_condition left right

def cardinality_strict_less_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (cardinality_strict_less_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 戴德金有限 -/

def is_dedekind_finite_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  let function : SetTerm bound (SetSort.set :: free) := .fvar .here
  (is_injective_formula
      function (set.weakenFree SetSort.set) (set.weakenFree SetSort.set) ⟶ₘ
    is_surjective_formula
      function (set.weakenFree SetSort.set) (set.weakenFree SetSort.set)).forallFreeTop
      SetSort.set

def is_dedekind_finite_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  dedekind_finiteₘ(set) ↔ₘ is_dedekind_finite_condition set

def is_dedekind_finite_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_dedekind_finite_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

def dedekind_finiteness_principle : SetSentence :=
  let free := [SetSort.set]
  let set : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (finiteₘ(set) ⟶ₘ dedekind_finiteₘ(set))

/-! ## 理论组合 -/

def finite_predicate_theory : SetTheory :=
  Theory.insert is_finite_definition_axiom symmetric_difference_theory

def equinumerous_predicate_theory : SetTheory :=
  Theory.insert is_equinumerous_definition_axiom finite_predicate_theory

def cardinality_leq_predicate_theory : SetTheory :=
  Theory.insert cardinality_leq_definition_axiom
    equinumerous_predicate_theory

def cardinality_strict_less_predicate_theory : SetTheory :=
  Theory.insert cardinality_strict_less_definition_axiom
    cardinality_leq_predicate_theory

def dedekind_finite_predicate_theory : SetTheory :=
  Theory.insert is_dedekind_finite_definition_axiom
    cardinality_strict_less_predicate_theory

def basic_finite_theory : SetTheory :=
  dedekind_finite_predicate_theory

/-! ## 理论嵌入 -/

derive_theory_subset symmetric_difference_theory ⊆ finite_predicate_theory

derive_theory_subset finite_predicate_theory ⊆ equinumerous_predicate_theory

derive_theory_subset equinumerous_predicate_theory ⊆ cardinality_leq_predicate_theory

derive_theory_subset cardinality_leq_predicate_theory ⊆ cardinality_strict_less_predicate_theory

derive_theory_subset cardinality_strict_less_predicate_theory ⊆ dedekind_finite_predicate_theory

derive_theory_subset dedekind_finite_predicate_theory ⊆ basic_finite_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
