import Lean
import YesMetaZFC.Automation.Data.Util

/-!
# Given-clause 持久调度工作区

Passive 的 age/weight 调度使用同一批稳定条目。age 侧保留插入顺序和前缀游标，
weight 侧使用平坦二叉最小堆；稳定编号状态戳统一判断当前 generation 的 Passive/Active
成员资格。两个 queue stamp 另行记录物理载荷是否仍待消费，使 assignment 暂时失活后
可以复用原槽，也不会让已经弹出的 stale 载荷重新生效。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- Given-clause 调度使用的稳定条目。 -/
structure GivenEntry where
  clauseId : Nat
  age : Nat
  weight : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace GivenEntry

/-- Age 队列比较：更老的条目优先。 -/
@[inline]
def betterByAge (left right : GivenEntry) : Bool :=
  left.age < right.age ||
    (left.age == right.age && left.clauseId < right.clauseId)

/-- Weight 队列比较：更轻的条目优先，同权时更老者优先。 -/
@[inline]
def betterByWeight (left right : GivenEntry) : Bool :=
  left.weight < right.weight ||
    (left.weight == right.weight && betterByAge left right)

end GivenEntry

/--
一个 saturation 生命周期内的 Given-clause 工作区。

`passiveStamps/activeStamps` 与稳定 clause id 对齐；`0` 保留为未登记或已删除标记，
只有等于当前非零 `generation` 的槽才属于当前集合。普通一阶 saturation 可以用
`beginRound` 开启全量 generation；AVATAR 模型切换保持 generation、队列与 cursor，
只更新受 assignment delta 影响的成员资格。
-/
structure GivenWorkspace where
  generation : Nat := 1
  ageItems : Array GivenEntry := #[]
  ageHead : Nat := 0
  weightHeap : Array GivenEntry := #[]
  passiveStamps : Array Nat := #[]
  activeStamps : Array Nat := #[]
  ageQueueStamps : Array Nat := #[]
  weightQueueStamps : Array Nat := #[]
  passiveCount : Nat := 0
  deriving Repr, Inhabited, BEq, Lean.ToExpr

namespace GivenWorkspace

private def heapParent (index : Nat) : Nat := (index - 1) / 2
private def heapLeft (index : Nat) : Nat := 2 * index + 1
private def heapRight (index : Nat) : Nat := 2 * index + 2

private partial def siftUp (heap : Array GivenEntry) (index : Nat) :
    Array GivenEntry :=
  if index == 0 then
    heap
  else
    let parent := heapParent index
    match heap[index]?, heap[parent]? with
    | some child, some parentEntry =>
        if child.betterByWeight parentEntry then
          siftUp (swapArray? heap index parent) parent
        else
          heap
    | _, _ => heap

private partial def siftDown (heap : Array GivenEntry) (index : Nat) :
    Array GivenEntry :=
  let left := heapLeft index
  let right := heapRight index
  match heap[left]? with
  | none => heap
  | some leftEntry =>
      let best :=
        match heap[right]? with
        | some rightEntry => if rightEntry.betterByWeight leftEntry then right else left
        | none => left
      match heap[best]?, heap[index]? with
      | some bestEntry, some current =>
          if bestEntry.betterByWeight current then
            siftDown (swapArray? heap index best) best
          else
            heap
      | _, _ => heap

private def heapify (entries : Array GivenEntry) : Array GivenEntry := Id.run do
  let mut heap := entries
  let mut index := heap.size / 2
  while index > 0 do
    index := index - 1
    heap := siftDown heap index
  return heap

private def heapPush (heap : Array GivenEntry) (entry : GivenEntry) :
    Array GivenEntry :=
  let heap := heap.push entry
  siftUp heap (heap.size - 1)

private def heapPop? (heap : Array GivenEntry) :
    Option (GivenEntry × Array GivenEntry) :=
  match heap[0]? with
  | none => none
  | some root =>
      if heap.size == 1 then
        some (root, #[])
      else
        match heap.back? with
        | some last =>
            let heap := (heap.set! 0 last).pop
            some (root, siftDown heap 0)
        | none => none

/--
把重新可见的旧字句插回尚未消费的 age 后缀。

正常派生字句的 age 单调递增，因此走尾部追加；模型轮重激活只在少量旧 age 上承担后缀
移动成本，同时保持既有 cursor 与 age 语义。
-/
private def insertAgeEntry (items : Array GivenEntry) (head : Nat)
    (entry : GivenEntry) : Array GivenEntry := Id.run do
  let mut index := Nat.min head items.size
  while h : index < items.size do
    if entry.betterByAge items[index] then
      return items.insertIdx index entry
    index := index + 1
  return items.push entry

@[inline]
private def stampAt (stamps : Array Nat) (id generation : Nat) : Bool :=
  stamps[id]? == some generation

@[inline]
private def setStamp (stamps : Array Nat) (id stamp : Nat) : Array Nat :=
  (ensureArraySize stamps (id + 1) 0).set! id stamp

/-- 稳定编号当前是否仍在 Passive。 -/
@[inline]
def isPassive (workspace : GivenWorkspace) (id : Nat) : Bool :=
  stampAt workspace.passiveStamps id workspace.generation

/-- 稳定编号当前是否已经进入 Active。 -/
@[inline]
def isActive (workspace : GivenWorkspace) (id : Nat) : Bool :=
  stampAt workspace.activeStamps id workspace.generation

/-- 当前 Passive 条目数量。 -/
@[inline]
def size (workspace : GivenWorkspace) : Nat :=
  workspace.passiveCount

/-- 当前 Passive 是否为空。 -/
@[inline]
def isEmpty (workspace : GivenWorkspace) : Bool :=
  workspace.passiveCount == 0

private def markNotPassive (workspace : GivenWorkspace) (id : Nat) :
    GivenWorkspace :=
  if workspace.isPassive id then
    {
      workspace with
      passiveStamps := workspace.passiveStamps.set! id 0
      passiveCount := workspace.passiveCount - 1
    }
  else
    workspace

/-- 开启全量 generation，并用插入顺序稳定的条目重建双队列。 -/
def beginRound (workspace : GivenWorkspace) (entries : Array GivenEntry) :
    GivenWorkspace :=
  Id.run do
    let generation := workspace.generation + 1
    let mut passiveStamps := workspace.passiveStamps
    let mut ageQueueStamps := workspace.ageQueueStamps
    let mut weightQueueStamps := workspace.weightQueueStamps
    for entry in entries do
      passiveStamps := setStamp passiveStamps entry.clauseId generation
      ageQueueStamps := setStamp ageQueueStamps entry.clauseId generation
      weightQueueStamps := setStamp weightQueueStamps entry.clauseId generation
    return {
      generation := generation
      ageItems := entries
      ageHead := 0
      weightHeap := heapify entries
      passiveStamps := passiveStamps
      activeStamps := workspace.activeStamps
      ageQueueStamps := ageQueueStamps
      weightQueueStamps := weightQueueStamps
      passiveCount := entries.size
    }

/-- 向当前 generation 的两个调度队列加入一个稳定条目。 -/
def push (workspace : GivenWorkspace) (entry : GivenEntry) : GivenWorkspace :=
  if workspace.isPassive entry.clauseId then
    workspace
  else
    Id.run do
      let generation := workspace.generation
      let ageQueued :=
        stampAt workspace.ageQueueStamps entry.clauseId generation
      let weightQueued :=
        stampAt workspace.weightQueueStamps entry.clauseId generation
      return {
        workspace with
        ageItems :=
          if ageQueued then workspace.ageItems
          else insertAgeEntry workspace.ageItems workspace.ageHead entry
        weightHeap :=
          if weightQueued then workspace.weightHeap
          else heapPush workspace.weightHeap entry
        passiveStamps :=
          setStamp workspace.passiveStamps entry.clauseId generation
        ageQueueStamps :=
          if ageQueued then workspace.ageQueueStamps
          else setStamp workspace.ageQueueStamps entry.clauseId generation
        weightQueueStamps :=
          if weightQueued then workspace.weightQueueStamps
          else setStamp workspace.weightQueueStamps entry.clauseId generation
        passiveCount := workspace.passiveCount + 1
      }

/-- 按 age 顺序弹出下一个 live 条目；stale 前缀只推进游标。 -/
def popAge? (workspace : GivenWorkspace) :
    Option (GivenEntry × GivenWorkspace) := Id.run do
  let mut workspace := workspace
  while workspace.ageHead < workspace.ageItems.size do
    let entry := workspace.ageItems[workspace.ageHead]!
    workspace := {
      workspace with
      ageHead := workspace.ageHead + 1
      ageQueueStamps := workspace.ageQueueStamps.set! entry.clauseId 0
    }
    if workspace.isPassive entry.clauseId then
      return some (entry, workspace.markNotPassive entry.clauseId)
  return none

/-- 按 weight 顺序弹出下一个 live 条目；另一队列已消费的条目在堆顶 lazy 跳过。 -/
def popWeight? (workspace : GivenWorkspace) :
    Option (GivenEntry × GivenWorkspace) := Id.run do
  let mut workspace := workspace
  while !workspace.weightHeap.isEmpty do
    let some (entry, heap) := heapPop? workspace.weightHeap | return none
    workspace := {
      workspace with
      weightHeap := heap
      weightQueueStamps := workspace.weightQueueStamps.set! entry.clauseId 0
    }
    if workspace.isPassive entry.clauseId then
      return some (entry, workspace.markNotPassive entry.clauseId)
  return none

/-- 标记一个稳定编号已经进入当前 Active。 -/
def markActive (workspace : GivenWorkspace) (id : Nat) : GivenWorkspace :=
  {
    workspace with
    activeStamps := setStamp workspace.activeStamps id workspace.generation
  }

/-- assignment 切换时暂时移除不可见字句；物理队列载荷由后续 lazy pop 回收。 -/
def deactivateMany (workspace : GivenWorkspace) (ids : Array Nat) : GivenWorkspace :=
  Id.run do
    let mut workspace := workspace
    for id in ids do
      workspace := workspace.markNotPassive id
      if workspace.isActive id then
        workspace := {
          workspace with
          activeStamps := workspace.activeStamps.set! id 0
        }
    return workspace

/-- 删除一组稳定编号；双队列中的旧载荷由后续 pop lazy 跳过。 -/
def deleteMany (workspace : GivenWorkspace) (ids : Array Nat) : GivenWorkspace :=
  workspace.deactivateMany ids

/-- 按旧 Passive 数组的插入顺序物化当前 live 条目。 -/
def liveEntries (workspace : GivenWorkspace) : Array GivenEntry := Id.run do
  let mut entries := Array.mkEmpty workspace.passiveCount
  for h : index in [workspace.ageHead:workspace.ageItems.size] do
    let entry := workspace.ageItems[index]
    if workspace.isPassive entry.clauseId then
      entries := entries.push entry
  return entries

/-- 按旧 Passive 数组顺序物化当前 live clause id。 -/
def liveClauseIds (workspace : GivenWorkspace) : Array Nat :=
  workspace.liveEntries.map (·.clauseId)

end GivenWorkspace

end Data
end Automation
end YesMetaZFC
