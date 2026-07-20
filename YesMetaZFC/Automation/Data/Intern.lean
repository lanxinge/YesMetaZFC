import YesMetaZFC.Automation.Data.Arena
import YesMetaZFC.Automation.Data.OpenAddress

/-!
# Arena-backed intern table

Intern 表不再把富结构对象直接作为 persistent `Std.HashMap` key。对象只存入 arena 一次，
哈希层保存 `fingerprint → collision chain`，链节点只包含 arena handle。这样热插入只会
更新开放寻址槽位和追加数组，不会因为 map 快照共享而复制整棵哈希结构。

冻结的 `InternTable` 用于只读边界；所有新增对象都通过 `InternTable.Builder` 完成。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 冻结的 hash-consing 表。链和 handle 均使用 1-based 索引，`0` 表示空。 -/
structure InternTable (tag : Type) (α : Type) [BEq α] [Hashable α] where
  arena : Arena tag α := Arena.empty
  buckets : NatMap Nat := NatMap.empty
  ids : Array (Id tag) := #[]
  next : Array Nat := #[]

namespace InternTable

variable {tag α : Type} [BEq α] [Hashable α]

/-- 空 intern table。 -/
def empty : InternTable tag α := {}

/-- 已 intern 的元素数量。 -/
@[inline]
def size (table : InternTable tag α) : Nat :=
  table.arena.size

/-- 按 id 读取对象。 -/
@[inline]
def get? (table : InternTable tag α) (id : Id tag) : Option α :=
  table.arena.get? id

/-- 结构哈希指纹；哈希命中后仍需沿冲突链做结构确认。 -/
@[inline]
def fingerprint (_table : InternTable tag α) (value : α) : UInt64 :=
  Hashable.hash value

/-- 查找已有 id。 -/
def lookup? (table : InternTable tag α) (value : α) : Option (Id tag) := Id.run do
  let hash := hashNat value
  let mut link := table.buckets.getD hash 0
  while link != 0 do
    let index := link - 1
    match table.ids[index]? with
    | some id =>
        match table.arena.get? id with
        | some candidate =>
            if candidate == value then
              return some id
        | none => pure ()
    | none => pure ()
    link := table.next.getD index 0
  return none

end InternTable

/-!
## ST builder
-/

/-- ST 生命周期内可变的 intern table。 -/
structure InternTable.Builder (σ : Type) (tag : Type) (α : Type)
    [BEq α] [Hashable α] where
  arena : Arena.Builder σ tag α
  buckets : NatMap.Builder σ Nat
  ids : MutArray σ (Id tag)
  next : MutArray σ Nat

namespace InternTable.Builder

variable {σ tag α : Type} [BEq α] [Hashable α]

/-- 创建空 builder。 -/
def empty (capacity : Nat := 16) : ST σ (InternTable.Builder σ tag α) := do
  return {
    arena := ← Arena.Builder.empty (σ := σ) (tag := tag) (α := α) capacity
    buckets := ← NatMap.Builder.empty (σ := σ) (α := Nat) (Nat.max 16 (capacity * 2))
    ids := ← MutArray.emptyWithCapacity (σ := σ) (α := Id tag) capacity
    next := ← MutArray.emptyWithCapacity (σ := σ) (α := Nat) capacity
  }

/-- 从冻结表创建 builder。 -/
def ofTable (table : InternTable tag α) : ST σ (InternTable.Builder σ tag α) := do
  return {
    arena := ← Arena.Builder.ofArena (σ := σ) table.arena
    buckets := ← NatMap.Builder.ofMap (σ := σ) table.buckets
    ids := ← MutArray.mk (σ := σ) table.ids
    next := ← MutArray.mk (σ := σ) table.next
  }

/-- 已 intern 的元素数量。 -/
@[inline]
def size (builder : InternTable.Builder σ tag α) : ST σ Nat :=
  builder.arena.size

/-- 按 id 读取对象。 -/
@[inline]
def get? (builder : InternTable.Builder σ tag α) (id : Id tag) : ST σ (Option α) :=
  builder.arena.get? id

/-- 查找已有 id。 -/
def lookup? (builder : InternTable.Builder σ tag α) (value : α) :
    ST σ (Option (Id tag)) := do
  let hash := hashNat value
  let mut link ← builder.buckets.getD hash 0
  while link != 0 do
    let index := link - 1
    let id ← builder.ids.getD index Id.invalid
    if id.isValid then
      match ← builder.arena.get? id with
      | some candidate =>
          if candidate == value then
            return some id
      | none => pure ()
    link ← builder.next.getD index 0
  return none

/-- intern 一个对象，返回稳定 arena handle。 -/
def intern (builder : InternTable.Builder σ tag α) (value : α) : ST σ (Id tag) := do
  match ← builder.lookup? value with
  | some id => return id
  | none =>
      let hash := hashNat value
      let head ← builder.buckets.getD hash 0
      let id ← builder.arena.push value
      let link := (← builder.ids.pushGetIndex id) + 1
      builder.next.push head
      builder.buckets.insert hash link
      return id

/-- 冻结为只读 intern table。调用后不应继续修改 builder。 -/
def freeze (builder : InternTable.Builder σ tag α) : ST σ (InternTable tag α) := do
  return {
    arena := ← builder.arena.freeze
    buckets := ← builder.buckets.freeze
    ids := ← builder.ids.freeze
    next := ← builder.next.freeze
  }

end InternTable.Builder

end Data
end Automation
end YesMetaZFC
