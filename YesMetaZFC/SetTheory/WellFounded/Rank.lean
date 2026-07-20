import YesMetaZFC.SetTheory.WellFounded.Recursion

/-!
# 良基关系的秩函数

本文件把秩递归所需的序数后继与上确界抽象成值域接口。给定这些运算后，任意良基关系
都存在唯一函数 `ρ`，满足

`ρ current = sup {succ (ρ predecessor) | E predecessor current}`。

该层刻画定理的良基递归骨架；具体序数实现只需提供对应的后继与集合大小上确界。
-/

namespace YesMetaZFC
namespace SetTheory
namespace WellFounded
namespace Rank

universe u v

/-- 秩值域所需的运算：序数后继及任意同宇宙索引族的上确界。 -/
structure SuccessorSupremum (OrdinalValue : Type v) where
  successor : OrdinalValue → OrdinalValue
  supremum : {ι : Type u} → (ι → OrdinalValue) → OrdinalValue

/-- 当前秩是所有前驱秩的后继之上确界。 -/
def step {P : Type u} {OrdinalValue : Type v}
    (E : P → P → Prop)
    (operations : SuccessorSupremum.{u, v} OrdinalValue)
    (current : P)
    (previous : ∀ predecessor,
      E predecessor current → OrdinalValue) :
    OrdinalValue :=
  operations.supremum fun predecessor :
      Recursion.Predecessor E current =>
    operations.successor
      (previous predecessor.1 predecessor.2)

/-- `ρ` 满足良基关系的秩递归方程。 -/
def IsRankFunction {P : Type u} {OrdinalValue : Type v}
    (E : P → P → Prop)
    (operations : SuccessorSupremum.{u, v} OrdinalValue)
    (ρ : P → OrdinalValue) : Prop :=
  Recursion.SatisfiesEquation (step E operations) ρ

/-- 秩函数定义直接展开为前驱秩后继的上确界方程。 -/
theorem isRankFunction_iff
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    {operations : SuccessorSupremum.{u, v} OrdinalValue}
    {ρ : P → OrdinalValue} :
    IsRankFunction E operations ρ ↔
      ∀ current,
        ρ current =
          operations.supremum
            (fun predecessor :
                Recursion.Predecessor E current =>
              operations.successor (ρ predecessor.1)) :=
  Iff.rfl

/-- 由 Lean 良基证据确定的规范秩函数。 -/
noncomputable def functionOfWellFounded
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : _root_.WellFounded E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue) :
    P → OrdinalValue :=
  Recursion.solve hE (step E operations)

/-- 规范秩函数满足秩递归方程。 -/
theorem functionOfWellFounded_isRankFunction
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : _root_.WellFounded E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue) :
    IsRankFunction E operations
      (functionOfWellFounded hE operations) :=
  Recursion.solve_satisfiesEquation hE
    (step E operations)

/-- 规范秩函数在每一点等于所有前驱秩后继的上确界。 -/
theorem functionOfWellFounded_apply
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : _root_.WellFounded E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue)
    (current : P) :
    functionOfWellFounded hE operations current =
      operations.supremum
        (fun predecessor :
            Recursion.Predecessor E current =>
          operations.successor
            (functionOfWellFounded hE operations predecessor.1)) :=
  isRankFunction_iff.mp
    (functionOfWellFounded_isRankFunction hE operations)
    current

/-- 任意满足方程的秩函数都等于规范秩函数。 -/
theorem eq_functionOfWellFounded
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : _root_.WellFounded E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue)
    {ρ : P → OrdinalValue}
    (hρ : IsRankFunction E operations ρ) :
    ρ = functionOfWellFounded hE operations :=
  Recursion.eq_of_satisfiesEquation hE
    (step E operations) hρ
    (functionOfWellFounded_isRankFunction hE operations)

/-- 由纸面极小元定义确定的规范秩函数。 -/
noncomputable def function
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop} (hE : HasMinimalElements E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue) :
    P → OrdinalValue :=
  functionOfWellFounded
    (wellFounded_of_hasMinimalElements hE) operations

/-- 纸面定义下的规范秩函数满足秩递归方程。 -/
theorem function_isRankFunction
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : HasMinimalElements E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue) :
    IsRankFunction E operations (function hE operations) :=
  functionOfWellFounded_isRankFunction
    (wellFounded_of_hasMinimalElements hE) operations

/-- 纸面定义下的规范秩函数逐点满足上确界方程。 -/
theorem function_apply
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : HasMinimalElements E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue)
    (current : P) :
    function hE operations current =
      operations.supremum
        (fun predecessor :
            Recursion.Predecessor E current =>
          operations.successor
            (function hE operations predecessor.1)) :=
  functionOfWellFounded_apply
    (wellFounded_of_hasMinimalElements hE) operations current

/-- 纸面定义下的任意秩函数都等于规范秩函数。 -/
theorem eq_function
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : HasMinimalElements E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue)
    {ρ : P → OrdinalValue}
    (hρ : IsRankFunction E operations ρ) :
    ρ = function hE operations :=
  eq_functionOfWellFounded
    (wellFounded_of_hasMinimalElements hE) operations hρ

/-- Lean 良基关系具有唯一的秩函数。 -/
theorem existsUnique_of_wellFounded
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop}
    (hE : _root_.WellFounded E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue) :
    ∃ ρ,
      IsRankFunction E operations ρ ∧
        ∀ other, IsRankFunction E operations other →
          other = ρ := by
  refine
    ⟨functionOfWellFounded hE operations,
      functionOfWellFounded_isRankFunction hE operations, ?_⟩
  intro other hOther
  exact eq_functionOfWellFounded hE operations hOther

/-- 纸面意义下的良基关系具有唯一的秩函数。 -/
theorem existsUnique
    {P : Type u} {OrdinalValue : Type v}
    {E : P → P → Prop} (hE : HasMinimalElements E)
    (operations : SuccessorSupremum.{u, v} OrdinalValue) :
    ∃ ρ,
      IsRankFunction E operations ρ ∧
        ∀ other, IsRankFunction E operations other →
          other = ρ := by
  refine
    ⟨function hE operations,
      function_isRankFunction hE operations, ?_⟩
  intro other hOther
  exact eq_function hE operations hOther

end Rank
end WellFounded
end SetTheory
end YesMetaZFC
