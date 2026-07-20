import YesMetaZFC.Automation.Data.StableIdLiveness

/-!
# AVATAR 模型轮增量前沿

该工作区只保存 selector assignment 的紧凑快照、selector 到稳定 clause id 的追加式依赖
journal，以及当前模型下的可见位。模型变化时只枚举发生变化的 selector 所影响的字句；
Active/Passive 的语义迁移由上层饱和状态消费这里产生的 affected id。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

private def assignmentUnknown : UInt8 := 0
private def assignmentFalse : UInt8 := 1
private def assignmentTrue : UInt8 := 2

@[inline]
private def encodeAssignmentValue : Option Bool → UInt8
  | none => assignmentUnknown
  | some false => assignmentFalse
  | some true => assignmentTrue

/-- 把公开 assignment 压成与 selector id 对齐的三态字节数组。 -/
def encodeModelAssignment (assignment : Array (Option Bool)) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity assignment.size
  for value in assignment do
    out := out.push (encodeAssignmentValue value)
  return out

@[inline]
private def byteAt (values : ByteArray) (index : Nat) : UInt8 :=
  values[index]?.getD 0

/--
跨模型轮持久保留的 guard 依赖与可见状态。

`dependencyHeads[var]` 与 `dependencyNext` 使用 1-based journal slot；`0` 表示链尾。
dependency journal 永不删除，永久删除由上层 tombstone 过滤。`registered` 防止稳定 clause
id 重复登记，`affectedStamps` 只负责一次 assignment delta 内的去重。
-/
structure ModelRoundWorkspace where
  previousAssignment : ByteArray := ByteArray.empty
  dependencyHeads : Array Nat := #[]
  dependencyClauseIds : Array Nat := #[]
  dependencyNext : Array Nat := #[]
  registered : ByteArray := ByteArray.empty
  registeredClauseIds : Array Nat := #[]
  visible : ByteArray := ByteArray.empty
  affectedStamps : Array Nat := #[]
  affectedGeneration : Nat := 1
  initialized : Bool := false
  deriving Repr, Inhabited, BEq, Lean.ToExpr

namespace ModelRoundWorkspace

/-- 稳定 clause id 是否已经登记 guard 依赖。 -/
@[inline]
def contains (workspace : ModelRoundWorkspace) (clauseId : Nat) : Bool :=
  byteAt workspace.registered clauseId != 0

/-- 当前模型是否支持该稳定 clause id。 -/
@[inline]
def isVisible (workspace : ModelRoundWorkspace) (clauseId : Nat) : Bool :=
  byteAt workspace.visible clauseId != 0

/-- 按稳定 id 一次登记 guard 中出现的 selector 变量。 -/
def registerClause (workspace : ModelRoundWorkspace) (clauseId : Nat)
    (selectorVars : Array Nat) : ModelRoundWorkspace :=
  if workspace.contains clauseId then
    workspace
  else
    Id.run do
      let mut dependencyHeads := workspace.dependencyHeads
      let mut dependencyClauseIds := workspace.dependencyClauseIds
      let mut dependencyNext := workspace.dependencyNext
      for var in selectorVars do
        dependencyHeads := ensureArraySize dependencyHeads (var + 1) 0
        let previousHead := dependencyHeads.getD var 0
        let rawSlot := dependencyClauseIds.size + 1
        dependencyClauseIds := dependencyClauseIds.push clauseId
        dependencyNext := dependencyNext.push previousHead
        dependencyHeads := dependencyHeads.set! var rawSlot
      return {
        workspace with
        dependencyHeads := dependencyHeads
        dependencyClauseIds := dependencyClauseIds
        dependencyNext := dependencyNext
        registered :=
          setByteArrayD workspace.registered clauseId 1 0
        registeredClauseIds := workspace.registeredClauseIds.push clauseId
        visible := ensureByteArraySize workspace.visible (clauseId + 1) 0
        affectedStamps :=
          ensureArraySize workspace.affectedStamps (clauseId + 1) 0
      }

/-- 写入当前模型下的可见位。 -/
@[inline]
def setVisible (workspace : ModelRoundWorkspace) (clauseId : Nat) (value : Bool) :
    ModelRoundWorkspace :=
  {
    workspace with
    visible :=
      setByteArrayD workspace.visible clauseId (if value then 1 else 0) 0
  }

/-- 永久删除时同步清除可见位；依赖 journal 保留 tombstone 槽。 -/
def deleteMany (workspace : ModelRoundWorkspace) (clauseIds : Array Nat) :
    ModelRoundWorkspace :=
  Id.run do
    let mut workspace := workspace
    for clauseId in clauseIds do
      workspace := workspace.setVisible clauseId false
    return workspace

/--
进入新 assignment，并返回所有可能改变 support 的稳定 clause id。

首轮需要初始化全部已登记字句；后续只遍历 changed selector 的依赖链。affected journal
按稳定登记顺序的链内顺序产生，上层不依赖该顺序决定 given 调度。
-/
def beginAssignment (workspace : ModelRoundWorkspace)
    (assignment : Array (Option Bool)) :
    ModelRoundWorkspace × Array Nat := Id.run do
  let current := encodeModelAssignment assignment
  if !workspace.initialized then
    return ({
      workspace with
      previousAssignment := current
      initialized := true
    }, workspace.registeredClauseIds)
  let generation := workspace.affectedGeneration + 1
  let mut affectedStamps := workspace.affectedStamps
  let mut affected := #[]
  let width := Nat.max workspace.previousAssignment.size current.size
  for var in [:width] do
    if byteAt workspace.previousAssignment var != byteAt current var then
      let mut rawSlot := workspace.dependencyHeads.getD var 0
      while rawSlot != 0 do
        let slot := rawSlot - 1
        let clauseId := workspace.dependencyClauseIds.getD slot 0
        affectedStamps := ensureArraySize affectedStamps (clauseId + 1) 0
        if affectedStamps.getD clauseId 0 != generation then
          affectedStamps := affectedStamps.set! clauseId generation
          affected := affected.push clauseId
        rawSlot := workspace.dependencyNext.getD slot 0
  return ({
    workspace with
    previousAssignment := current
    affectedStamps := affectedStamps
    affectedGeneration := generation
  }, affected)

end ModelRoundWorkspace

end Data
end Automation
end YesMetaZFC
