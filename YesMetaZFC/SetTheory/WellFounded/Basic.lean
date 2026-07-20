import YesMetaZFC.SetTheory.Binding

/-!
# 良基关系的基础接口

本文件把“每个非空子集都有极小元”的纸面定义整理为普通 Lean 谓词，并证明它与
Lean 核心的可达性定义 `WellFounded` 等价。关系方向统一为 `E predecessor current`。
-/

namespace YesMetaZFC
namespace SetTheory
namespace WellFounded

universe u

/-- `candidate` 是谓词子集 `part` 关于 `E` 的极小元。 -/
def IsMinimal {P : Type u} (E : P → P → Prop)
    (part : P → Prop) (candidate : P) : Prop :=
  part candidate ∧
    ∀ predecessor, part predecessor → ¬ E predecessor candidate

/-- 每个非空谓词子集都具有关于 `E` 的极小元。 -/
def HasMinimalElements {P : Type u} (E : P → P → Prop) : Prop :=
  ∀ part : P → Prop, (∃ value, part value) →
    ∃ candidate, IsMinimal E part candidate

/-- `sequence` 沿关系 `E` 严格下降。 -/
def IsDescendingSequence {P : Type u} (E : P → P → Prop)
    (sequence : Nat → P) : Prop :=
  ∀ index, E (sequence index.succ) (sequence index)

/-- Lean 良基关系满足纸面的极小元定义。 -/
theorem hasMinimalElements_of_wellFounded {P : Type u}
    {E : P → P → Prop} (hE : _root_.WellFounded E) :
    HasMinimalElements E := by
  classical
  intro part hNonempty
  rcases hNonempty with ⟨start, hStart⟩
  let property : P → Prop := fun value =>
    part value → ∃ candidate, IsMinimal E part candidate
  have hProperty : property start := by
    apply hE.induction start
    intro current hPrevious
    change part current →
      ∃ candidate, IsMinimal E part candidate
    intro hCurrent
    by_cases hPredecessor :
        ∃ predecessor, part predecessor ∧ E predecessor current
    · rcases hPredecessor with
        ⟨predecessor, hPart, hRelation⟩
      exact hPrevious predecessor hRelation hPart
    · exact
        ⟨current, hCurrent, fun predecessor hPart hRelation =>
          hPredecessor ⟨predecessor, hPart, hRelation⟩⟩
  exact hProperty hStart

/-- 纸面的极小元定义推出 Lean 的可达性良基定义。 -/
theorem wellFounded_of_hasMinimalElements {P : Type u}
    {E : P → P → Prop} (hE : HasMinimalElements E) :
    _root_.WellFounded E := by
  classical
  refine ⟨?_⟩
  intro start
  apply Classical.byContradiction
  intro hStart
  rcases hE (fun value => ¬ Acc E value) ⟨start, hStart⟩ with
    ⟨minimal, hMinimal, hNoPredecessor⟩
  apply hMinimal
  exact Acc.intro minimal fun predecessor hRelation => by
    apply Classical.byContradiction
    intro hPredecessor
    exact hNoPredecessor predecessor hPredecessor hRelation

/-- 纸面的极小元定义与 Lean 核心良基定义等价。 -/
theorem wellFounded_iff_hasMinimalElements {P : Type u}
    {E : P → P → Prop} :
    _root_.WellFounded E ↔ HasMinimalElements E :=
  ⟨hasMinimalElements_of_wellFounded,
    wellFounded_of_hasMinimalElements⟩

/-- 由纸面良基定义得到的良基归纳原理。 -/
theorem induction {P : Type u} {E : P → P → Prop}
    (hE : HasMinimalElements E) (property : P → Prop)
    (hProgressive : ∀ current,
      (∀ predecessor, E predecessor current → property predecessor) →
        property current) :
    ∀ current, property current :=
  fun current =>
    (wellFounded_of_hasMinimalElements hE).induction
      current hProgressive

/-- Lean 良基关系上没有给定的无限下降序列。 -/
theorem not_isDescendingSequence_of_wellFounded
    {P : Type u} {E : P → P → Prop}
    (hE : _root_.WellFounded E) (sequence : Nat → P) :
    ¬ IsDescendingSequence E sequence := by
  intro hDescending
  let property : P → Prop := fun current =>
    ∀ index, sequence index = current → False
  have hProperty : property (sequence 0) := by
    apply hE.induction (sequence 0)
    intro current hPrevious
    change ∀ index, sequence index = current → False
    intro index hCurrent
    have hRelation :
        E (sequence index.succ) current := by
      simpa [hCurrent] using hDescending index
    exact hPrevious (sequence index.succ) hRelation
      index.succ rfl
  exact hProperty 0 rfl

/-- Lean 良基关系上不存在任何无限下降序列。 -/
theorem noInfiniteDescendingSequence_of_wellFounded
    {P : Type u} {E : P → P → Prop}
    (hE : _root_.WellFounded E) :
    ¬ ∃ sequence, IsDescendingSequence E sequence := by
  rintro ⟨sequence, hDescending⟩
  exact
    not_isDescendingSequence_of_wellFounded
      hE sequence hDescending

/-- 纸面极小元定义下的良基关系不存在无限下降序列。 -/
theorem noInfiniteDescendingSequence
    {P : Type u} {E : P → P → Prop}
    (hE : HasMinimalElements E) :
    ¬ ∃ sequence, IsDescendingSequence E sequence :=
  noInfiniteDescendingSequence_of_wellFounded
    (wellFounded_of_hasMinimalElements hE)

end WellFounded
end SetTheory
end YesMetaZFC
