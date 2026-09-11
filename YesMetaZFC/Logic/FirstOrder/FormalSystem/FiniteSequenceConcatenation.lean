import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.HereditarilyFinite

/-!
# 有限序列合并与有限折叠

本模块只保留有限序列层的内在类型对象语言规格、闭定义公理与理论组合。项和公式的
作用域由类型直接记录；不再生成变量编号，也不再维护良构性、句子性或兼容桥接证明。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols

/-! ## 有限序列与顺序合并 -/

def finite_sequence_condition {bound free : SetContext}
    (sequence : SetTerm bound free) : SetFormula bound free :=
  is_function_formula sequence ∧ₘ domₘ(sequence) ∈ₘ ωₘ

def finite_sequence_concatenation_left_condition {bound free : SetContext}
    (left candidate index : SetTerm bound free) : SetFormula bound free :=
  (index ∈ₘ domₘ(left)) ⟶ₘ
    ((index ∈ₘ domₘ(candidate)) ∧ₘ
      ((candidate ·ₘ index) ≐ₘ (left ·ₘ index)))

def finite_sequence_concatenation_right_condition {bound free : SetContext}
    (left right candidate index : SetTerm bound free) : SetFormula bound free :=
  (index ∈ₘ domₘ(right)) ⟶ₘ
    (((domₘ(left) +ₘ index) ∈ₘ domₘ(candidate)) ∧ₘ
      ((candidate ·ₘ (domₘ(left) +ₘ index)) ≐ₘ (right ·ₘ index)))

def finite_sequence_concatenation_spec {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  let leftDeep : SetTerm bound (SetSort.set :: free) := left.weakenFree SetSort.set
  let rightDeep : SetTerm bound (SetSort.set :: free) := right.weakenFree SetSort.set
  let candidateDeep : SetTerm bound (SetSort.set :: free) :=
    candidate.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  finite_sequence_condition candidate ∧ₘ
    ((domₘ(candidate) ≐ₘ (domₘ(left) +ₘ domₘ(right))) ∧ₘ
      ((finite_sequence_concatenation_left_condition
          leftDeep candidateDeep index).forallFreeTop SetSort.set ∧ₘ
        (finite_sequence_concatenation_right_condition
          leftDeep rightDeep candidateDeep index).forallFreeTop SetSort.set))

def finite_sequence_concatenation_definition_instance
    {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  (finite_sequence_condition left ∧ₘ finite_sequence_condition right) ⟶ₘ
    ((candidate ≐ₘ (left ⌢ₘ right)) ↔ₘ
      finite_sequence_concatenation_spec left right candidate)

def finite_sequence_concatenation_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (finite_sequence_concatenation_definition_instance
      (.fvar (.there (.there .here)) : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 非空有限序列空间 -/

def nonempty_finite_sequence_member_condition {bound free : SetContext}
    (source : SetTerm bound free)
    (sequence : SetTerm bound (SetSort.set :: free)) :
    SetFormula bound (SetSort.set :: free) :=
  (sequence ∈ₘ seq_spaceₘ(source.weakenFree SetSort.set)) ∧ₘ
    (numₘ(0) ∈ₘ domₘ(sequence))

def nonempty_finite_sequence_space_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let sequence : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (nonempty_finite_sequence_member_condition source sequence)

def nonempty_finite_sequence_space_separation_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (nonempty_finite_sequence_space_spec
      (source.weakenFree SetSort.set) candidate).existsFreeTop SetSort.set

def nonempty_finite_sequence_space_separation_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (nonempty_finite_sequence_space_separation_exists
      (.fvar .here : SetOpenTerm [SetSort.set]))

def nonempty_finite_sequence_space_definition_instance
    {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  (source ≠ₘ ∅ₘ) ⟶ₘ
    ((candidate ≐ₘ seq₊_spaceₘ(source)) ↔ₘ
      nonempty_finite_sequence_space_spec source candidate)

def nonempty_finite_sequence_space_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (nonempty_finite_sequence_space_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 有限序列族的有限折叠 -/

def finite_sequence_family_condition {bound free : SetContext}
    (family : SetTerm bound free) : SetFormula bound free :=
  let familyDeep : SetTerm bound (SetSort.set :: free) := family.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  finite_sequence_condition family ∧ₘ
    ((index ∈ₘ domₘ(familyDeep)) ⟶ₘ
      finite_sequence_condition (familyDeep ·ₘ index)).forallFreeTop SetSort.set

def finite_sequence_flatten_step_condition {bound free : SetContext}
    (family accumulator index : SetTerm bound free) : SetFormula bound free :=
  (index ∈ₘ domₘ(family)) ⟶ₘ
    ((accumulator ·ₘ Sₘ(index)) ≐ₘ
      ((accumulator ·ₘ index) ⌢ₘ (family ·ₘ index)))

def finite_sequence_flatten_spec {bound free : SetContext}
    (family result : SetTerm bound free) : SetFormula bound free :=
  let familyOne : SetTerm bound (SetSort.set :: free) := family.weakenFree SetSort.set
  let resultOne : SetTerm bound (SetSort.set :: free) := result.weakenFree SetSort.set
  let accumulator : SetTerm bound (SetSort.set :: free) := .fvar .here
  let familyDeep : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    familyOne.weakenFree SetSort.set
  let resultDeep : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    resultOne.weakenFree SetSort.set
  let accumulatorDeep : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    accumulator.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let stepAndResult : SetFormula bound (SetSort.set :: SetSort.set :: free) :=
    finite_sequence_flatten_step_condition familyDeep accumulatorDeep index ∧ₘ
      (resultDeep ≐ₘ (accumulatorDeep ·ₘ domₘ(familyDeep)))
  let stepClosed : SetFormula bound (SetSort.set :: free) :=
    stepAndResult.forallFreeTop SetSort.set
  let accumulatorSpec : SetFormula bound (SetSort.set :: free) :=
    finite_sequence_condition accumulator ∧ₘ
      ((domₘ(accumulator) ≐ₘ Sₘ(domₘ(familyOne))) ∧ₘ
        (((accumulator ·ₘ numₘ(0)) ≐ₘ ∅ₘ) ∧ₘ stepClosed))
  finite_sequence_condition result ∧ₘ accumulatorSpec.existsFreeTop SetSort.set

def finite_sequence_flatten_definition_instance {bound free : SetContext}
    (family result : SetTerm bound free) : SetFormula bound free :=
  finite_sequence_family_condition family ⟶ₘ
    ((result ≐ₘ flattenₘ(family)) ↔ₘ finite_sequence_flatten_spec family result)

def finite_sequence_flatten_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (finite_sequence_flatten_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 理论组合 -/

def finite_sequence_concatenation_theory : SetTheory :=
  Theory.insert finite_sequence_concatenation_definition_axiom hereditarily_finite_theory

def nonempty_finite_sequence_space_separation_theory : SetTheory :=
  Theory.insert nonempty_finite_sequence_space_separation_axiom
    finite_sequence_concatenation_theory

def nonempty_finite_sequence_space_theory : SetTheory :=
  Theory.insert nonempty_finite_sequence_space_definition_axiom
    nonempty_finite_sequence_space_separation_theory

def finite_sequence_flatten_theory : SetTheory :=
  Theory.insert finite_sequence_flatten_definition_axiom
    nonempty_finite_sequence_space_theory

def finite_sequence_formal_system_theory : SetTheory :=
  finite_sequence_flatten_theory

/-! ## 理论嵌入 -/

derive_theory_subset hereditarily_finite_theory ⊆ finite_sequence_concatenation_theory

derive_theory_subset finite_sequence_concatenation_theory ⊆ nonempty_finite_sequence_space_separation_theory => finite_sequence_concatenation_theory_subset_nonempty_sequence_separation_theory

derive_theory_subset nonempty_finite_sequence_space_separation_theory ⊆ nonempty_finite_sequence_space_theory => nonempty_sequence_separation_theory_subset_nonempty_sequence_space_theory

derive_theory_subset nonempty_finite_sequence_space_theory ⊆ finite_sequence_flatten_theory => nonempty_sequence_space_theory_subset_finite_sequence_flatten_theory

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
