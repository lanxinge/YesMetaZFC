import YesMetaZFC.SetTheory.WellFounded.Basic

/-!
# 良基递归

本文件在任意良基关系上建立依赖型递归方程的规范解，并用良基归纳证明解的唯一性。
后续秩函数及一般关系递归都只需给出一步算子。
-/

namespace YesMetaZFC
namespace SetTheory
namespace WellFounded
namespace Recursion

universe u v

/-- `current` 的所有 `E`-前驱组成的索引类型。 -/
def Predecessor {P : Type u} (E : P → P → Prop)
    (current : P) : Type u :=
  {predecessor // E predecessor current}

/-- 将一个全域函数限制到 `current` 的所有前驱。 -/
def restrict {P : Type u} {E : P → P → Prop}
    {C : P → Sort v} (solution : ∀ current, C current)
    (current : P) :
    ∀ predecessor : Predecessor E current, C predecessor.1 :=
  fun predecessor => solution predecessor.1

/-- `solution` 满足由 `step` 指定的良基递归方程。 -/
def SatisfiesEquation {P : Type u} {E : P → P → Prop}
    {C : P → Sort v}
    (step : ∀ current,
      (∀ predecessor, E predecessor current → C predecessor) →
        C current)
    (solution : ∀ current, C current) : Prop :=
  ∀ current,
    solution current =
      step current (fun predecessor _ => solution predecessor)

/-- 良基递归方程的规范解。 -/
noncomputable def solve {P : Type u} {E : P → P → Prop}
    {C : P → Sort v} (hE : _root_.WellFounded E)
    (step : ∀ current,
      (∀ predecessor, E predecessor current → C predecessor) →
        C current) :
    ∀ current, C current :=
  hE.fix step

/-- 规范解满足对应的递归方程。 -/
theorem solve_satisfiesEquation {P : Type u}
    {E : P → P → Prop} {C : P → Sort v}
    (hE : _root_.WellFounded E)
    (step : ∀ current,
      (∀ predecessor, E predecessor current → C predecessor) →
        C current) :
    SatisfiesEquation step (solve hE step) := by
  intro current
  exact hE.fix_eq step current

/-- 同一良基递归方程的两个解相等。 -/
theorem eq_of_satisfiesEquation {P : Type u}
    {E : P → P → Prop} {C : P → Sort v}
    (hE : _root_.WellFounded E)
    (step : ∀ current,
      (∀ predecessor, E predecessor current → C predecessor) →
        C current)
    {left right : ∀ current, C current}
    (hLeft : SatisfiesEquation step left)
    (hRight : SatisfiesEquation step right) :
    left = right := by
  funext current
  apply hE.induction current
  intro value hPrevious
  rw [hLeft value, hRight value]
  apply congrArg (step value)
  funext predecessor
  funext hRelation
  exact hPrevious predecessor hRelation

/-- 每个良基递归方程都存在唯一解。 -/
theorem existsUnique {P : Type u} {E : P → P → Prop}
    {C : P → Sort v} (hE : _root_.WellFounded E)
    (step : ∀ current,
      (∀ predecessor, E predecessor current → C predecessor) →
        C current) :
    ∃ solution,
      SatisfiesEquation step solution ∧
        ∀ other, SatisfiesEquation step other →
          other = solution := by
  refine
    ⟨solve hE step, solve_satisfiesEquation hE step, ?_⟩
  intro other hOther
  exact eq_of_satisfiesEquation hE step hOther
    (solve_satisfiesEquation hE step)

/-- 纸面极小元定义下的良基递归方程同样存在唯一解。 -/
theorem existsUnique_of_hasMinimalElements
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (hE : HasMinimalElements E)
    (step : ∀ current,
      (∀ predecessor, E predecessor current → C predecessor) →
        C current) :
    ∃ solution,
      SatisfiesEquation step solution ∧
        ∀ other, SatisfiesEquation step other →
          other = solution :=
  existsUnique (wellFounded_of_hasMinimalElements hE) step

/-- 把消费前驱限制函数的算子转成 Lean 核心良基递归所需的一步算子。 -/
def restrictionStep {P : Type u} {E : P → P → Prop}
    {C : P → Sort v}
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current)
    (current : P)
    (previous : ∀ predecessor,
      E predecessor current → C predecessor) :
    C current :=
  G current fun predecessor =>
    previous predecessor.1 predecessor.2

/-- `solution` 在每一点由 `G` 作用于其前驱限制得到。 -/
def SatisfiesRestrictionEquation
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current)
    (solution : ∀ current, C current) : Prop :=
  ∀ current,
    solution current =
      G current (restrict solution current)

/-- 前驱限制方程等价于对应的一般良基递归方程。 -/
theorem satisfiesRestrictionEquation_iff
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    {G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current}
    {solution : ∀ current, C current} :
    SatisfiesRestrictionEquation G solution ↔
      SatisfiesEquation (restrictionStep G) solution :=
  Iff.rfl

/-- 前驱限制型良基递归的规范解。 -/
noncomputable def solveRestriction
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (hE : _root_.WellFounded E)
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current) :
    ∀ current, C current :=
  solve hE (restrictionStep G)

/-- 规范解满足前驱限制型递归方程。 -/
theorem solveRestriction_satisfiesEquation
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (hE : _root_.WellFounded E)
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current) :
    SatisfiesRestrictionEquation G (solveRestriction hE G) :=
  satisfiesRestrictionEquation_iff.mpr <|
    solve_satisfiesEquation hE (restrictionStep G)

/-- 规范解逐点满足习题 2.15 的前驱限制方程。 -/
theorem solveRestriction_apply
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (hE : _root_.WellFounded E)
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current)
    (current : P) :
    solveRestriction hE G current =
      G current (restrict (solveRestriction hE G) current) :=
  solveRestriction_satisfiesEquation hE G current

/-- 任意满足前驱限制方程的函数都等于规范解。 -/
theorem eq_solveRestriction
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (hE : _root_.WellFounded E)
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current)
    {solution : ∀ current, C current}
    (hSolution : SatisfiesRestrictionEquation G solution) :
    solution = solveRestriction hE G :=
  eq_of_satisfiesEquation hE (restrictionStep G)
    (satisfiesRestrictionEquation_iff.mp hSolution)
    (satisfiesRestrictionEquation_iff.mp <|
      solveRestriction_satisfiesEquation hE G)

/-- 习题 2.15：前驱限制型良基递归方程存在唯一解。 -/
theorem restriction_existsUnique
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (hE : _root_.WellFounded E)
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current) :
    ∃ solution,
      SatisfiesRestrictionEquation G solution ∧
        ∀ other, SatisfiesRestrictionEquation G other →
          other = solution := by
  refine
    ⟨solveRestriction hE G,
      solveRestriction_satisfiesEquation hE G, ?_⟩
  intro other hOther
  exact eq_solveRestriction hE G hOther

/-- 纸面极小元定义下的前驱限制型递归方程存在唯一解。 -/
theorem restriction_existsUnique_of_hasMinimalElements
    {P : Type u} {E : P → P → Prop} {C : P → Sort v}
    (hE : HasMinimalElements E)
    (G : ∀ current,
      (∀ predecessor : Predecessor E current, C predecessor.1) →
        C current) :
    ∃ solution,
      SatisfiesRestrictionEquation G solution ∧
        ∀ other, SatisfiesRestrictionEquation G other →
          other = solution :=
  restriction_existsUnique
    (wellFounded_of_hasMinimalElements hE) G

end Recursion
end WellFounded
end SetTheory
end YesMetaZFC
