import YesMetaZFC.Automation.TheoryInclusion
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Language

/-!
# 基本集合论的首组非逻辑公理

外延性、子集定义与真子集定义直接构造成内在良构闭句。公式参数对 bound/free
上下文多态；进入量词体时只做结构 weakening，不再产生 admissibility、scope、
freshness 或“该理论只含闭公式”的旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

universe u v w

/-- 两个集合具有完全相同的元素。 -/
def membership_agreement {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((element ∈ₘ left.weakenFree SetSort.set) ↔ₘ
    (element ∈ₘ right.weakenFree SetSort.set)).forallFreeTop SetSort.set

/-- 等式推出成员外延一致。 -/
def equality_to_agreement {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ≐ₘ right) ⟶ₘ membership_agreement left right

/-- 成员外延一致推出等式。 -/
def agreement_to_equality {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  membership_agreement left right ⟶ₘ (left ≐ₘ right)

/-- 外延公理的双参数实例。 -/
def extensionality_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  agreement_to_equality left right

/-- 子集关系的成员条件。 -/
def subset_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((element ∈ₘ left.weakenFree SetSort.set) ⟶ₘ
    (element ∈ₘ right.weakenFree SetSort.set)).forallFreeTop SetSort.set

/-- 子集关系符号的定义实例。 -/
def subset_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ⊆ₘ right) ↔ₘ subset_condition left right

/-- 真子集关系的成员条件。 -/
def proper_subset_condition {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  (left ⊆ₘ right) ∧ₘ
    (((element ∈ₘ right.weakenFree SetSort.set) ∧ₘ
      ¬ₘ (element ∈ₘ left.weakenFree SetSort.set)).existsFreeTop SetSort.set)

/-- 真子集关系符号的定义实例。 -/
def proper_subset_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ⊂ₘ right) ↔ₘ proper_subset_condition left right

/-- 外延公理。 -/
def extensionality_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (extensionality_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 子集关系符号的定义公理。 -/
def subset_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (subset_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 真子集关系符号的定义公理。 -/
def proper_subset_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (proper_subset_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 只含外延公理的首个具体理论。 -/
def extensionality_theory : SetTheory :=
  Theory.singleton extensionality_axiom

/-- 在外延理论上加入子集定义公理。 -/
def subset_theory : SetTheory :=
  Theory.insert subset_definition_axiom extensionality_theory

/-- 在子集理论上再加入真子集定义公理。 -/
def proper_subset_theory : SetTheory :=
  Theory.insert proper_subset_definition_axiom subset_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
