import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalSetTheory
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 基础无穷集合与自然数算术设施

本模块用内在类型语法定义自然数算术、有限序列、递归序列、基数分类、`ω × ω`
上的典型序以及 Gödel 配对。定义公理直接构造为 `SetSentence`，不再维护对象语言
项的 admissibility、检查证书或闭句证明链。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 自然数算术 -/

def natural_addition_graph_condition {bound free : SetContext}
    (left right result graph : SetTerm bound free) : SetFormula bound free :=
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let left' := left.weakenFree SetSort.set
  let graph' := graph.weakenFree SetSort.set
  (is_mapping_formula graph (Sₘ(left)) ωₘ) ∧ₘ
    ((graph ·ₘ ∅ₘ ≐ₘ right) ∧ₘ
      ((((index ∈ₘ left') ⟶ₘ
          ((graph' ·ₘ Sₘ(index)) ≐ₘ Sₘ(graph' ·ₘ index))).forallFreeTop
            SetSort.set) ∧ₘ
        (graph ·ₘ left ≐ₘ result)))

def natural_addition_bound_graph_condition {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  let graph : SetTerm bound (SetSort.set :: free) := .fvar .here
  (natural_addition_graph_condition
    (left.weakenFree SetSort.set)
    (right.weakenFree SetSort.set)
    (result.weakenFree SetSort.set)
    graph).existsFreeTop SetSort.set

def natural_addition_spec {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  (result ∈ₘ ωₘ) ∧ₘ
    natural_addition_bound_graph_condition left right result

def natural_addition_definition_instance {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ
    ((result ≐ₘ (left +ₘ right)) ↔ₘ
      natural_addition_spec left right result)

def natural_addition_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let left : SetOpenTerm free := .fvar (.there (.there .here))
  let right : SetOpenTerm free := .fvar (.there .here)
  let result : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_addition_definition_instance left right result)

def natural_multiplication_graph_condition {bound free : SetContext}
    (left right result graph : SetTerm bound free) : SetFormula bound free :=
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let left' := left.weakenFree SetSort.set
  let graph' := graph.weakenFree SetSort.set
  (is_mapping_formula graph (Sₘ(left)) ωₘ) ∧ₘ
    ((graph ·ₘ ∅ₘ ≐ₘ ∅ₘ) ∧ₘ
      ((((index ∈ₘ left') ⟶ₘ
          ((graph' ·ₘ Sₘ(index)) ≐ₘ
            ((graph' ·ₘ index) +ₘ (right.weakenFree SetSort.set)))).forallFreeTop SetSort.set) ∧ₘ
        (graph ·ₘ left ≐ₘ result)))

def natural_multiplication_bound_graph_condition {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  let graph : SetTerm bound (SetSort.set :: free) := .fvar .here
  (natural_multiplication_graph_condition
    (left.weakenFree SetSort.set)
    (right.weakenFree SetSort.set)
    (result.weakenFree SetSort.set)
    graph).existsFreeTop SetSort.set

def natural_multiplication_spec {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  (result ∈ₘ ωₘ) ∧ₘ
    natural_multiplication_bound_graph_condition left right result

def natural_multiplication_definition_instance {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ
    ((result ≐ₘ (left *ₘ right)) ↔ₘ
      natural_multiplication_spec left right result)

def natural_multiplication_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let left : SetOpenTerm free := .fvar (.there (.there .here))
  let right : SetOpenTerm free := .fvar (.there .here)
  let result : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_multiplication_definition_instance left right result)

def natural_exponentiation_graph_condition {bound free : SetContext}
    (base exponent result graph : SetTerm bound free) : SetFormula bound free :=
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let exponent' := exponent.weakenFree SetSort.set
  let graph' := graph.weakenFree SetSort.set
  (is_mapping_formula graph (Sₘ(exponent)) ωₘ) ∧ₘ
    ((graph ·ₘ ∅ₘ ≐ₘ Sₘ(∅ₘ)) ∧ₘ
      ((((index ∈ₘ exponent') ⟶ₘ
          ((graph' ·ₘ Sₘ(index)) ≐ₘ
            ((graph' ·ₘ index) *ₘ (base.weakenFree SetSort.set)))).forallFreeTop SetSort.set) ∧ₘ
        (graph ·ₘ exponent ≐ₘ result)))

def natural_exponentiation_bound_graph_condition {bound free : SetContext}
    (base exponent result : SetTerm bound free) : SetFormula bound free :=
  let graph : SetTerm bound (SetSort.set :: free) := .fvar .here
  (natural_exponentiation_graph_condition
    (base.weakenFree SetSort.set)
    (exponent.weakenFree SetSort.set)
    (result.weakenFree SetSort.set)
    graph).existsFreeTop SetSort.set

def natural_exponentiation_spec {bound free : SetContext}
    (base exponent result : SetTerm bound free) : SetFormula bound free :=
  (result ∈ₘ ωₘ) ∧ₘ
    natural_exponentiation_bound_graph_condition base exponent result

def natural_exponentiation_definition_instance {bound free : SetContext}
    (base exponent result : SetTerm bound free) : SetFormula bound free :=
  ((base ∈ₘ ωₘ) ∧ₘ (exponent ∈ₘ ωₘ)) ⟶ₘ
    ((result ≐ₘ base ^ₘ exponent) ↔ₘ
      natural_exponentiation_spec base exponent result)

def natural_exponentiation_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let base : SetOpenTerm free := .fvar (.there (.there .here))
  let exponent : SetOpenTerm free := .fvar (.there .here)
  let result : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_exponentiation_definition_instance base exponent result)

def natural_difference_step_condition {bound free : SetContext}
    (graph index : SetTerm bound free) : SetFormula bound free :=
  let previous : SetTerm bound (SetSort.set :: free) := .fvar .here
  let graph' := graph.weakenFree SetSort.set
  let index' := index.weakenFree SetSort.set
  (((graph ·ₘ index) ≐ₘ ∅ₘ) ∧ₘ
      ((graph ·ₘ Sₘ(index)) ≐ₘ ∅ₘ)) ∨ₘ
    ((((graph' ·ₘ index') ≐ₘ Sₘ(previous)) ∧ₘ
        ((graph' ·ₘ Sₘ(index')) ≐ₘ previous)).existsFreeTop SetSort.set)

def natural_difference_graph_condition {bound free : SetContext}
    (left right result graph : SetTerm bound free) : SetFormula bound free :=
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let graph' := graph.weakenFree SetSort.set
  let right' := right.weakenFree SetSort.set
  (is_mapping_formula graph (Sₘ(right)) ωₘ) ∧ₘ
    ((graph ·ₘ ∅ₘ ≐ₘ left) ∧ₘ
      ((((index ∈ₘ right') ⟶ₘ natural_difference_step_condition graph' index).forallFreeTop SetSort.set) ∧ₘ
        (graph ·ₘ right ≐ₘ result)))

def natural_difference_spec {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  (result ∈ₘ ωₘ) ∧ₘ
    (let graph : SetTerm bound (SetSort.set :: free) := .fvar .here
     (natural_difference_graph_condition
       (left.weakenFree SetSort.set)
       (right.weakenFree SetSort.set)
       (result.weakenFree SetSort.set)
       graph).existsFreeTop SetSort.set)

def natural_difference_definition_instance {bound free : SetContext}
    (left right result : SetTerm bound free) : SetFormula bound free :=
  ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ
    ((result ≐ₘ (left -ₘ right)) ↔ₘ
      natural_difference_spec left right result)

def natural_difference_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let left : SetOpenTerm free := .fvar (.there (.there .here))
  let right : SetOpenTerm free := .fvar (.there .here)
  let result : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_difference_definition_instance left right result)

/-! ## 有限序列与递归序列 -/

def finite_sequence_member_condition {bound free : SetContext}
    (source sequence : SetTerm bound free) : SetFormula bound free :=
  let length : SetTerm bound (SetSort.set :: free) := .fvar .here
  (length ∈ₘ ωₘ ∧ₘ
    is_mapping_formula
      (sequence.weakenFree SetSort.set) length (source.weakenFree SetSort.set)).existsFreeTop
      SetSort.set

def finite_sequence_space_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let sequence : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((sequence ∈ₘ candidate.weakenFree SetSort.set) ↔ₘ
    finite_sequence_member_condition
      (source.weakenFree SetSort.set) sequence).forallFreeTop SetSort.set

def finite_sequence_space_definition_instance {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  (source ≠ₘ ∅ₘ) ⟶ₘ
    ((candidate ≐ₘ seq_spaceₘ(source)) ↔ₘ
      finite_sequence_space_spec source candidate)

def finite_sequence_space_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set]
  let source : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (finite_sequence_space_definition_instance source candidate)

def recursive_sequence_step_condition {bound free : SetContext}
    (source seed recursion sequence : SetTerm bound free) : SetFormula bound free :=
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let firstValue : SetTerm bound
      (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
    .fvar .here
  let secondValue : SetTerm bound
      (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let index' : SetTerm bound
      (SetSort.set :: SetSort.set :: SetSort.set :: free) := .fvar (.there (.there .here))
  let source' := source.weakenFree SetSort.set
    |>.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let sequence' := sequence.weakenFree SetSort.set
    |>.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let recursion' := recursion.weakenFree SetSort.set
    |>.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let witness :=
    ((firstValue ∈ₘ source') ∧ₘ
      ((secondValue ∈ₘ source') ∧ₘ
        ((⟨index', secondValue⟩ₘ ∈ₘ sequence') ∧ₘ
          ((⟨Sₘ(index'), firstValue⟩ₘ ∈ₘ sequence') ∧ₘ
            (⟨⟨secondValue, index'⟩ₘ, firstValue⟩ₘ ∈ₘ recursion'))))).existsFreeTop
      SetSort.set |>.existsFreeTop SetSort.set
  (⟨∅ₘ, seed⟩ₘ ∈ₘ sequence) ∧ₘ
    ((((index ∈ₘ domₘ(sequence.weakenFree SetSort.set)) ∧ₘ
        (Sₘ(index) ∈ₘ domₘ(sequence.weakenFree SetSort.set))) ⟶ₘ
      witness).forallFreeTop SetSort.set)

def recursive_sequence_member_condition {bound free : SetContext}
    (source seed recursion sequence : SetTerm bound free) : SetFormula bound free :=
  finite_sequence_member_condition source sequence ∧ₘ
    recursive_sequence_step_condition source seed recursion sequence

def recursive_sequence_space_spec {bound free : SetContext}
    (source seed recursion candidate : SetTerm bound free) : SetFormula bound free :=
  let sequence : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((sequence ∈ₘ candidate.weakenFree SetSort.set) ↔ₘ
    recursive_sequence_member_condition
      (source.weakenFree SetSort.set)
      (seed.weakenFree SetSort.set)
      (recursion.weakenFree SetSort.set)
      sequence).forallFreeTop SetSort.set

def recursive_sequence_space_definition_instance {bound free : SetContext}
    (source seed recursion candidate : SetTerm bound free) : SetFormula bound free :=
  ((seed ∈ₘ source) ∧ₘ
      is_mapping_formula recursion (source ×ₘ ωₘ) source) ⟶ₘ
    ((candidate ≐ₘ rec_seq_spaceₘ(source, seed, recursion)) ↔ₘ
      recursive_sequence_space_spec source seed recursion candidate)

def recursive_sequence_space_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
  let source : SetOpenTerm free := .fvar (.there (.there (.there .here)))
  let seed : SetOpenTerm free := .fvar (.there (.there .here))
  let recursion : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (recursive_sequence_space_definition_instance
      source seed recursion candidate)

def omega_recursive_sequence_spec {bound free : SetContext}
    (source seed recursion candidate : SetTerm bound free) : SetFormula bound free :=
  candidate ≐ₘ (⋃ₘ rec_seq_spaceₘ(source, seed, recursion))

def omega_recursive_sequence_definition_instance {bound free : SetContext}
    (source seed recursion candidate : SetTerm bound free) : SetFormula bound free :=
  ((seed ∈ₘ source) ∧ₘ
      is_mapping_formula recursion (source ×ₘ ωₘ) source) ⟶ₘ
    ((candidate ≐ₘ ω_rec_seqₘ(source, seed, recursion)) ↔ₘ
      omega_recursive_sequence_spec source seed recursion candidate)

def omega_recursive_sequence_definition_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
  let source : SetOpenTerm free := .fvar (.there (.there (.there .here)))
  let seed : SetOpenTerm free := .fvar (.there (.there .here))
  let recursion : SetOpenTerm free := .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (omega_recursive_sequence_definition_instance
      source seed recursion candidate)

/-! ## 无限性与可数性 -/

def is_infinite_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  let natural : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((natural ∈ₘ ωₘ) ⟶ₘ ¬ₘ (set.weakenFree SetSort.set ≈ₘ natural)).forallFreeTop
    SetSort.set

def is_countable_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  let function : SetTerm bound (SetSort.set :: free) := .fvar .here
  (is_surjective_formula function ωₘ (set.weakenFree SetSort.set)).existsFreeTop
    SetSort.set

def is_uncountable_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  ¬ₘ is_countable_condition set

def is_countably_infinite_condition {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  set ≈ₘ ωₘ

def is_infinite_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  infiniteₘ(set) ↔ₘ is_infinite_condition set

def is_countable_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  countableₘ(set) ↔ₘ is_countable_condition set

def is_uncountable_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  uncountableₘ(set) ↔ₘ is_uncountable_condition set

def is_countably_infinite_definition_instance {bound free : SetContext}
    (set : SetTerm bound free) : SetFormula bound free :=
  countably_infiniteₘ(set) ↔ₘ is_countably_infinite_condition set

def is_infinite_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_infinite_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

def is_countable_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_countable_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

def is_uncountable_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_uncountable_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

def is_countably_infinite_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_countably_infinite_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-! ## `ω × ω` 的典型序与 Gödel 编码 -/

def natural_leq_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ≐ₘ right) ∨ₘ (left ∈ₘ right)

def omega_pair_less_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  ((left ∈ₘ (ωₘ ×ₘ ωₘ)) ∧ₘ (right ∈ₘ (ωₘ ×ₘ ωₘ))) ⟶ₘ
    ((¬ₘ (maxεₘ(ωₘ, left) ∈ₘ maxεₘ(ωₘ, right))) ⟶ₘ
      ((¬ₘ ((maxεₘ(ωₘ, left) ≐ₘ maxεₘ(ωₘ, right)) ∧ₘ
          ((left)₀ₘ ∈ₘ (right)₀ₘ))) ⟶ₘ
        ((maxεₘ(ωₘ, left) ≐ₘ maxεₘ(ωₘ, right)) ∧ₘ
          (((left)₀ₘ ≐ₘ (right)₀ₘ) ∧ₘ
            ((left)₁ₘ ∈ₘ (right)₁ₘ)))))

def omega_pair_less_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  omega_pair_less_formula left right ↔ₘ
    omega_pair_less_condition left right

def omega_pair_less_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (omega_pair_less_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def godel_pairing_condition {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ∈ₘ ωₘ) ∧ₘ
    (((left ∈ₘ right) ⟶ₘ
        (candidate ≐ₘ ((right ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ left))) ∧ₘ
      ((natural_leq_condition right left) ⟶ₘ
        (candidate ≐ₘ (((left ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ left) +ₘ right))))

def godel_pairing_definition_instance {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ
    ((candidate ≐ₘ godel_pairₘ(left, right)) ↔ₘ
      godel_pairing_condition left right candidate)

def godel_pairing_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (godel_pairing_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 理论组合与嵌入 -/

def natural_addition_theory : SetTheory :=
  Theory.insert natural_addition_definition_axiom natural_set_theory

def natural_multiplication_theory : SetTheory :=
  Theory.insert natural_multiplication_definition_axiom
    natural_addition_theory

def natural_exponentiation_theory : SetTheory :=
  Theory.insert natural_exponentiation_definition_axiom
    natural_multiplication_theory

/-- 只携带配数定义及其真正依赖的最弱算术理论。 -/
def godel_pairing_core_theory : SetTheory :=
  Theory.insert godel_pairing_definition_axiom
    natural_exponentiation_theory

def infinite_predicate_theory : SetTheory :=
  Theory.insert is_infinite_definition_axiom natural_exponentiation_theory

def countable_predicate_theory : SetTheory :=
  Theory.insert is_countable_definition_axiom infinite_predicate_theory

def uncountable_predicate_theory : SetTheory :=
  Theory.insert is_uncountable_definition_axiom countable_predicate_theory

def countably_infinite_predicate_theory : SetTheory :=
  Theory.insert is_countably_infinite_definition_axiom
    uncountable_predicate_theory

def cardinality_classification_theory : SetTheory :=
  countably_infinite_predicate_theory

def finite_sequence_space_theory : SetTheory :=
  Theory.insert finite_sequence_space_definition_axiom
    cardinality_classification_theory

def recursive_sequence_space_theory : SetTheory :=
  Theory.insert recursive_sequence_space_definition_axiom
    finite_sequence_space_theory

def omega_recursive_sequence_theory : SetTheory :=
  Theory.insert omega_recursive_sequence_definition_axiom
    recursive_sequence_space_theory

def natural_difference_theory : SetTheory :=
  Theory.insert natural_difference_definition_axiom
    omega_recursive_sequence_theory

def omega_pair_order_theory : SetTheory :=
  Theory.insert omega_pair_less_definition_axiom natural_difference_theory

def godel_pairing_theory : SetTheory :=
  Theory.insert godel_pairing_definition_axiom omega_pair_order_theory

def natural_arithmetic_theory : SetTheory :=
  godel_pairing_theory

/-! ## 算术定义合同 -/

private theorem natural_addition_axiom_derives :
    ([] : Context signature []) ⊢ₘ[natural_addition_theory]
      Formula.fromSentence natural_addition_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

/-- 加法定义可在任意开放上下文中直接实例化。 -/
theorem natural_addition_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right result : SetOpenTerm free) :
    Γ ⊢ₘ[natural_addition_theory]
      natural_addition_definition_instance left right result := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    natural_addition_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons result
      (VariableSubstitution.cons right
        (VariableSubstitution.cons left VariableSubstitution.empty))
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [natural_addition_definition_axiom, body] using
        natural_addition_axiom_derives)
  simpa [body, τ, natural_addition_definition_instance,
    natural_addition_spec, natural_addition_bound_graph_condition,
    natural_addition_graph_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

private theorem natural_multiplication_axiom_derives :
    ([] : Context signature []) ⊢ₘ[natural_multiplication_theory]
      Formula.fromSentence natural_multiplication_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

/-- 乘法定义可在任意开放上下文中直接实例化。 -/
theorem natural_multiplication_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right result : SetOpenTerm free) :
    Γ ⊢ₘ[natural_multiplication_theory]
      natural_multiplication_definition_instance left right result := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    natural_multiplication_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons result
      (VariableSubstitution.cons right
        (VariableSubstitution.cons left VariableSubstitution.empty))
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [natural_multiplication_definition_axiom, body] using
        natural_multiplication_axiom_derives)
  simpa [body, τ, natural_multiplication_definition_instance,
    natural_multiplication_spec,
    natural_multiplication_bound_graph_condition,
    natural_multiplication_graph_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

private theorem natural_exponentiation_axiom_derives :
    ([] : Context signature []) ⊢ₘ[natural_exponentiation_theory]
      Formula.fromSentence natural_exponentiation_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

/-- 幂定义可在任意开放上下文中直接实例化。 -/
theorem natural_exponentiation_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (base exponent result : SetOpenTerm free) :
    Γ ⊢ₘ[natural_exponentiation_theory]
      natural_exponentiation_definition_instance base exponent result := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    natural_exponentiation_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons result
      (VariableSubstitution.cons exponent
        (VariableSubstitution.cons base VariableSubstitution.empty))
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [natural_exponentiation_definition_axiom, body] using
        natural_exponentiation_axiom_derives)
  simpa [body, τ, natural_exponentiation_definition_instance,
    natural_exponentiation_spec,
    natural_exponentiation_bound_graph_condition,
    natural_exponentiation_graph_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-! ## Gödel 配数定义合同 -/

private theorem godel_pairing_core_axiom_derives :
    ([] : Context signature []) ⊢ₘ[godel_pairing_core_theory]
      Formula.fromSentence godel_pairing_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

/-- 配数定义可在任意开放上下文中直接实例化。 -/
theorem godel_pairing_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[godel_pairing_core_theory]
      godel_pairing_definition_instance left right candidate := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    godel_pairing_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons right
        (VariableSubstitution.cons left VariableSubstitution.empty))
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [godel_pairing_definition_axiom, body] using
        godel_pairing_core_axiom_derives)
  simpa [body, τ, godel_pairing_definition_instance,
    godel_pairing_condition, natural_leq_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- 两个自然数的配数仍属于 `ω`。 -/
theorem godel_pairing_mem_omega
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeft : Γ ⊢ₘ[godel_pairing_core_theory] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[godel_pairing_core_theory] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[godel_pairing_core_theory] godel_pairₘ(left, right) ∈ₘ ωₘ := by
  have hDefinition := FirstOrder.Derives.imp_elim
    (godel_pairing_definition_instance_derives
      (Γ := Γ) left right godel_pairₘ(left, right))
    (FirstOrder.Derives.conj_intro hLeft hRight)
  have hCondition := FirstOrder.Derives.iff_elim_left hDefinition
    (Metatheory.Derives.equality_refl godel_pairₘ(left, right))
  exact FirstOrder.Derives.conj_elim_left hCondition

/-- 任意包含配数核心公理的理论都保持自然数对配数封闭。 -/
theorem godel_pairing_mem_omega_of_extends
    {T : SetTheory}
    (hT : Theory.Extends T godel_pairing_core_theory)
    {free : SetContext}
    {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeft : Γ ⊢ₘ[T] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[T] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] godel_pairₘ(left, right) ∈ₘ ωₘ := by
  have hDefinition := FirstOrder.Derives.theory_weaken hT
    (godel_pairing_definition_instance_derives
      (Γ := Γ) left right godel_pairₘ(left, right))
  have hCondition := FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.imp_elim hDefinition
      (FirstOrder.Derives.conj_intro hLeft hRight))
    (Metatheory.Derives.equality_refl godel_pairₘ(left, right))
  exact FirstOrder.Derives.conj_elim_left hCondition

/-! ## 理论嵌入 -/

derive_theory_subset natural_set_theory ⊆ natural_addition_theory

derive_theory_subset natural_addition_theory ⊆ natural_multiplication_theory

derive_theory_subset natural_multiplication_theory ⊆ natural_exponentiation_theory

derive_theory_subset natural_exponentiation_theory ⊆ infinite_predicate_theory

derive_theory_subset infinite_predicate_theory ⊆ countable_predicate_theory

derive_theory_subset countable_predicate_theory ⊆ uncountable_predicate_theory

derive_theory_subset uncountable_predicate_theory ⊆ countably_infinite_predicate_theory

derive_theory_subset cardinality_classification_theory ⊆ finite_sequence_space_theory

derive_theory_subset finite_sequence_space_theory ⊆ recursive_sequence_space_theory

derive_theory_subset recursive_sequence_space_theory ⊆ omega_recursive_sequence_theory

derive_theory_subset omega_recursive_sequence_theory ⊆ natural_difference_theory

derive_theory_subset natural_difference_theory ⊆ omega_pair_order_theory

derive_theory_subset omega_pair_order_theory ⊆ godel_pairing_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
