import YesMetaZFC.Logic.FirstOrder.FormalSystem.FiniteSequenceConcatenation

/-!
# 内在有限序列语法

有限列表直接递归为对象集合论中的有限函数图。列表元素、绑定上下文和自由上下文
全部由 `SetTerm` 的类型携带；本层只负责可计算的语法构造，不引入对象层良构谓词、
变量编号或停机旁证。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 列表到有限函数图 -/

/-- 从给定自然数位置开始，把列表实现为有限函数图。 -/
def standard_sequence_from {bound free : SetContext} (start : Nat) :
    List (SetTerm bound free) → SetTerm bound free
  | [] => ∅ₘ
  | element :: rest =>
      {⟨numₘ(start), element⟩ₘ}ₘ ∪ₘ
        standard_sequence_from (start + 1) rest

/-- 从零开始的规范有限函数图。 -/
abbrev standard_sequence {bound free : SetContext}
    (elements : List (SetTerm bound free)) : SetTerm bound free :=
  standard_sequence_from 0 elements

@[simp] theorem standard_sequence_from_nil
    {bound free : SetContext} (start : Nat) :
    standard_sequence_from start ([] : List (SetTerm bound free)) = ∅ₘ :=
  rfl

@[simp] theorem standard_sequence_from_cons
    {bound free : SetContext}
    (start : Nat) (element : SetTerm bound free)
    (rest : List (SetTerm bound free)) :
    standard_sequence_from start (element :: rest) =
      {⟨numₘ(start), element⟩ₘ}ₘ ∪ₘ
        standard_sequence_from (start + 1) rest :=
  rfl

@[simp] theorem standard_sequence_eq_from_zero
    {bound free : SetContext} (elements : List (SetTerm bound free)) :
    standard_sequence elements = standard_sequence_from 0 elements :=
  rfl

@[simp] theorem standard_sequence_from_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (start : Nat) (elements : List (SetTerm bound free)) :
    (standard_sequence_from start elements).weakenFree introduced =
      standard_sequence_from start
        (elements.map fun element => element.weakenFree introduced) := by
  induction elements generalizing start with
  | nil =>
      rfl
  | cons head tail ih =>
      exact (congrArg
        (fun index =>
          {⟨index, head.weakenFree introduced⟩ₘ}ₘ ∪ₘ
            (standard_sequence_from (start + 1) tail).weakenFree introduced)
        (finite_numeral_term_weakenFree introduced start)).trans
          (congrArg
            (fun rest => {⟨numₘ(start), head.weakenFree introduced⟩ₘ}ₘ ∪ₘ rest)
            (ih (start + 1)))

/-- 标准序列逐项弱化后再实例化顶部 free 槽，直接恢复原有限图。 -/
@[simp] theorem standard_sequence_from_instantiateFreeTop_map_weakenFree
    {bound free : SetContext}
    (replacement : SetTerm bound free)
    (start : Nat) (elements : List (SetTerm bound free)) :
    (standard_sequence_from start
        (elements.map fun element => element.weakenFree SetSort.set)).instantiateFreeTop
      replacement =
        standard_sequence_from start elements := by
  rw [← standard_sequence_from_weakenFree]
  exact Term.instantiateFreeTop_weakenFree replacement _

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
