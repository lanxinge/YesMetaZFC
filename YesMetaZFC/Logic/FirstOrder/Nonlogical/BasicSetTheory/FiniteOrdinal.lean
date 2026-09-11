import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalDiscreteLinearOrder

/-!
# 良序与有限自然数基础设施

本模块把良序建立在自然离散线性序之上，并把有限自然数直接递归为内在类型项。
不再为对象语言项维护额外的 admissibility、certificate 或 sentence 边界。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 良序 -/

def well_order_condition {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  is_linear_order_formula relation carrier ∧ₘ
    natural_order_least_element_condition relation carrier

def well_order_definition_instance {bound free : SetContext}
    (relation carrier : SetTerm bound free) : SetFormula bound free :=
  is_well_order_formula relation carrier ↔ₘ
    well_order_condition relation carrier

def well_order_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (well_order_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def well_order_theory : SetTheory :=
  Theory.insert well_order_definition_axiom
    natural_discrete_linear_order_theory

/-! ## 有限自然数项 -/

def finite_numeral_term {bound free : SetContext} : Nat → SetTerm bound free
  | 0 => (∅ₘ : SetTerm bound free)
  | number + 1 => Sₘ(finite_numeral_term number)

scoped notation:max "numₘ(" number ")" =>
  finite_numeral_term number

/-- 有限数码不含变量，任意类型化替换都在根节点命中闭项快路径。 -/
@[simp] theorem finite_numeral_term_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree)
    (number : Nat) :
    (finite_numeral_term
      (bound := sourceBound) (free := sourceFree) number).substituteMapped
        boundSubstitution freeSubstitution =
      finite_numeral_term
        (bound := targetBound) (free := targetFree) number := by
  induction number with
  | zero =>
      rfl
  | succ number ih =>
      simp [finite_numeral_term, Term.substituteMapped,
        Arguments.substituteMapped, ih]

@[simp] theorem finite_numeral_term_weakenBound
    {bound free : SetContext}
    (introduced : SetSort)
    (number : Nat) :
    (finite_numeral_term
      (bound := bound) (free := free) number).weakenBound introduced =
      finite_numeral_term
        (bound := introduced :: bound) (free := free) number := by
  induction number with
  | zero =>
      rfl
  | succ number ih =>
      simp [finite_numeral_term, ih]

@[simp] theorem finite_numeral_term_weakenFree
    {bound free : SetContext}
    (introduced : SetSort)
    (number : Nat) :
    (finite_numeral_term
      (bound := bound) (free := free) number).weakenFree introduced =
      finite_numeral_term
        (bound := bound) (free := introduced :: free) number := by
  induction number with
  | zero =>
      rfl
  | succ number ih =>
      simp [finite_numeral_term, ih]

@[simp] theorem finite_numeral_term_renameMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (number : Nat) :
    (finite_numeral_term
      (bound := sourceBound) (free := sourceFree) number).renameMapped
        boundRenaming freeRenaming =
      finite_numeral_term
        (bound := targetBound) (free := targetFree) number := by
  induction number with
  | zero =>
      rfl
  | succ number ih =>
      simp [finite_numeral_term, Term.renameMapped,
        Arguments.renameMapped, ih]

/-! ## 理论嵌入 -/

def finite_ordinal_theory : SetTheory :=
  well_order_theory

derive_theory_subset natural_discrete_linear_order_theory ⊆ well_order_theory

derive_theory_subset well_order_theory ⊆ finite_ordinal_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
