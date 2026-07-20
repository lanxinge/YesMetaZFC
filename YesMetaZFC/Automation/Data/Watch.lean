import YesMetaZFC.Automation.Data.Packed

/-!
# Watched buckets

泛化 two-watched literals 的桶表。具体 SAT/CDCL 后端负责解释 watch position 和传播语义；
这里仅维护 `slot → item` 列表。item 自身的 watch 位置应与其固定头部放在同一处。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- watched bucket 表。`items` 通常是 clause id。 -/
structure WatchTable where
  buckets : Array (Array Nat) := #[]
  deriving Repr, BEq, Inhabited

namespace WatchTable

/-- 构造指定槽位数量的空 watch table。 -/
def empty (slotCount : Nat := 0) : WatchTable :=
  { buckets := filledArray slotCount #[] }

/-- 确保 slot 存在。 -/
def ensureSlot (table : WatchTable) (slot : Nat) : WatchTable :=
  { table with buckets := ensureArraySize table.buckets (slot + 1) #[] }

/-- 读取 slot 的 bucket。 -/
def bucket (table : WatchTable) (slot : Nat) : Array Nat :=
  table.buckets.getD slot #[]

/-- 设置 slot 的 bucket。 -/
def setBucket (table : WatchTable) (slot : Nat) (items : Array Nat) : WatchTable :=
  let table := table.ensureSlot slot
  { table with buckets := table.buckets.set! slot items }

/-- 向 slot 追加 item。 -/
def pushBucket (table : WatchTable) (slot item : Nat) : WatchTable :=
  let table := table.ensureSlot slot
  { table with buckets := table.buckets.set! slot ((table.bucket slot).push item) }

/-- 清空并返回一个 bucket，适合传播时重建保留列表。 -/
def drainBucket (table : WatchTable) (slot : Nat) : Array Nat × WatchTable :=
  (table.bucket slot, table.setBucket slot #[])

/-- 对 bucket 做一次压缩过滤。 -/
def compactBucket (table : WatchTable) (slot : Nat) (keep : Nat → Bool) : WatchTable :=
  let kept := (table.bucket slot).filter keep
  table.setBucket slot kept

/-- literal 编码下的取反 bucket。 -/
def negLiteralBucket (table : WatchTable) (slot : Nat) : Array Nat :=
  table.bucket (negLiteralSlot slot)

end WatchTable

/-!
## ST builder

热传播循环通过 builder 更新 watch table。冻结的 `WatchTable` 只作为循环边界快照，
不要把 builder 内部数组写入 trace 或历史列表。
-/

/-- ST 内的可变 watched bucket 表。 -/
structure WatchTable.Builder (σ : Type) where
  buckets : MutArray σ (Array Nat)

namespace WatchTable.Builder

/-- 从冻结表创建 builder。 -/
def ofTable {σ : Type} (table : WatchTable) : ST σ (WatchTable.Builder σ) := do
  let buckets ← MutArray.mk (σ := σ) table.buckets
  return { buckets := buckets }

/-- 创建指定槽位数的空 builder。 -/
def empty {σ : Type} (slotCount : Nat := 0) : ST σ (WatchTable.Builder σ) :=
  ofTable (WatchTable.empty slotCount)

/-- 冻结 builder。冻结值只应在热循环边界长期保存。 -/
def freeze {σ : Type} (builder : WatchTable.Builder σ) : ST σ WatchTable := do
  let buckets ← builder.buckets.freeze
  return { buckets := buckets }

/-- 读取 slot 的 bucket。 -/
def bucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) : ST σ (Array Nat) :=
  builder.buckets.getD slot #[]

/-- 设置 slot 的 bucket。 -/
def setBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat)
    (items : Array Nat) : ST σ Unit :=
  builder.buckets.setD slot items #[]

/-- 向 slot 追加 item。 -/
@[inline]
def pushBucket {σ : Type} (builder : WatchTable.Builder σ) (slot item : Nat) : ST σ Unit :=
  builder.buckets.modifyNestedD slot #[] (fun items => items.push item)

/-- 清空并返回一个 bucket，适合传播时重建保留列表。 -/
def drainBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) :
    ST σ (Array Nat) :=
  builder.buckets.takeD slot #[]

/-- 对 bucket 做一次压缩过滤。 -/
def compactBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat)
    (keep : Nat → Bool) : ST σ Unit := do
  let items ← builder.drainBucket slot
  builder.setBucket slot (items.filter keep)

/-- literal 编码下的取反 bucket。 -/
def negLiteralBucket {σ : Type} (builder : WatchTable.Builder σ) (slot : Nat) :
    ST σ (Array Nat) :=
  builder.bucket (negLiteralSlot slot)

end WatchTable.Builder

end Data
end Automation
end YesMetaZFC
