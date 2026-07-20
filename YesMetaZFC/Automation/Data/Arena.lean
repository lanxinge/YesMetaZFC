import YesMetaZFC.Automation.Data.Packed

/-!
# Arena 和 Slab

`Arena` 用 1-based handle 管理固定元素；`Slab` 用连续切片管理可变长度载荷。
这两者是后续 term/literal/clause intern 的基础，避免热路径复制递归 AST。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 连续数组切片。 -/
structure Slice where
  start : Nat := 0
  len : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Slice

/-- 空切片。 -/
def empty : Slice := {}

/-- 切片终点。 -/
def stop (slice : Slice) : Nat := slice.start + slice.len

/-- 切片是否为空。 -/
def isEmpty (slice : Slice) : Bool := slice.len == 0

end Slice

/-- 通过类型标签化 handle 访问的冻结 arena。 -/
structure Arena (tag : Type) (α : Type) where
  values : Array α := #[]
  deriving Repr, Inhabited

namespace Arena

variable {tag α : Type}

/-- 空 arena。 -/
def empty : Arena tag α := {}

/-- 元素数量。 -/
def size (arena : Arena tag α) : Nat := arena.values.size

/-- 下一个将被分配的 handle。 -/
def nextId (arena : Arena tag α) : Id tag :=
  Id.ofIndex arena.values.size

/-- 追加元素并返回新 handle。 -/
def push (arena : Arena tag α) (value : α) : Id tag × Arena tag α :=
  (arena.nextId, { values := arena.values.push value })

/-- 按 handle 读取元素。 -/
def get? (arena : Arena tag α) (id : Id tag) : Option α :=
  match id.index? with
  | some index => arena.values[index]?
  | none => none

/-- 按 handle 读取元素，越界时返回默认值。 -/
def getD (arena : Arena tag α) (id : Id tag) (default : α) : α :=
  match arena.get? id with
  | some value => value
  | none => default

/-- 按 handle 写入；越界时保持不变。 -/
def set? (arena : Arena tag α) (id : Id tag) (value : α) : Arena tag α :=
  match id.index? with
  | some index =>
      if index < arena.values.size then
        { arena with values := arena.values.set! index value }
      else
        arena
  | none => arena

/-- 按 handle 修改；越界时保持不变。 -/
def modify? (arena : Arena tag α) (id : Id tag) (f : α → α) : Arena tag α :=
  match arena.get? id, id.index? with
  | some value, some index => { arena with values := arena.values.set! index (f value) }
  | _, _ => arena

/-- 顺序折叠 arena 中的元素。 -/
def foldl {β : Type w} (f : β → Id tag → α → β) (init : β) (arena : Arena tag α) :
    β := Id.run do
  let mut acc := init
  for h : i in [:arena.values.size] do
    acc := f acc (Id.ofIndex i) arena.values[i]
  return acc

end Arena

/-- ST 生命周期内可变的 arena。 -/
structure Arena.Builder (σ : Type) (tag : Type) (α : Type) where
  values : MutArray σ α

namespace Arena.Builder

/-- 从冻结 arena 创建 builder。 -/
def ofArena {σ : Type} {tag α : Type} (arena : Arena tag α) :
    ST σ (Arena.Builder σ tag α) := do
  return { values := ← MutArray.mk (σ := σ) arena.values }

/-- 创建空 builder，可预留元素容量。 -/
def empty {σ : Type} {tag α : Type} (capacity : Nat := 0) :
    ST σ (Arena.Builder σ tag α) := do
  return { values := ← MutArray.emptyWithCapacity (σ := σ) (α := α) capacity }

/-- 冻结 arena。调用后不应继续修改 builder。 -/
def freeze {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) :
    ST σ (Arena tag α) := do
  return { values := ← builder.values.freeze }

/-- 当前元素数量。 -/
@[inline]
def size {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) : ST σ Nat :=
  builder.values.size

/-- 下一个将被分配的 handle。 -/
@[inline]
def nextId {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) :
    ST σ (Id tag) := do
  return Id.ofIndex (← builder.size)

/-- 追加元素并返回稳定 handle。 -/
def push {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (value : α) :
    ST σ (Id tag) := do
  return Id.ofIndex (← builder.values.pushGetIndex value)

/-- 按 handle 读取元素。 -/
def get? {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag) :
    ST σ (Option α) := do
  let some index := id.index? | return none
  builder.values.get? index

/-- 按 handle 读取元素，缺失时返回默认值。 -/
def getD {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag)
    (default : α) : ST σ α := do
  return (← builder.get? id).getD default

/-- 按 handle 写回元素；无效 handle 保持不变。 -/
def set? {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag)
    (value : α) : ST σ Bool := do
  let some index := id.index? | return false
  builder.values.setAt? index value

/-- 按 handle 修改元素；无效 handle 保持不变。 -/
def modify? {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag)
    (f : α → α) : ST σ Bool := do
  let some index := id.index? | return false
  builder.values.modifyAt? index f

/-- 修改嵌套 RC 值；先断开 arena 槽位对旧值的引用。 -/
def modifyNested? {σ : Type} {tag α : Type} [Inhabited α]
    (builder : Arena.Builder σ tag α) (id : Id tag) (f : α → α) : ST σ Bool := do
  let some index := id.index? | return false
  builder.values.modifyNestedAt? index f

/-- 清空 arena，并在线性持有时保留容量。 -/
def clear {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) : ST σ Unit :=
  builder.values.clear

end Arena.Builder

/-- 连续存放可变长度载荷的 slab。 -/
structure Slab (α : Type) where
  data : Array α := #[]
  deriving Repr, Inhabited

namespace Slab

/-- 空 slab。 -/
def empty : Slab α := {}

/-- 当前载荷长度。 -/
def size (slab : Slab α) : Nat := slab.data.size

/-- 追加一个数组切片。 -/
def pushSlice (slab : Slab α) (items : Array α) : Slice × Slab α :=
  let slice : Slice := { start := slab.data.size, len := items.size }
  (slice, { data := appendArray slab.data items })

/-- 追加一个列表切片。 -/
def pushList (slab : Slab α) (items : List α) : Slice × Slab α :=
  slab.pushSlice items.toArray

/-- 取出切片视图。 -/
def getSlice (slab : Slab α) (slice : Slice) : Array α :=
  slab.data.extract slice.start slice.stop

/-- 折叠切片中的元素。 -/
def foldSlice (slab : Slab α) (slice : Slice) (init : β) (f : β → α → β) : β :=
  slab.data.foldl f init slice.start slice.stop

end Slab

/-- ST 生命周期内可变的连续 slab。 -/
structure Slab.Builder (σ : Type) (α : Type) where
  data : MutArray σ α

namespace Slab.Builder

/-- 从冻结 slab 创建 builder。 -/
def ofSlab {σ : Type} {α : Type} (slab : Slab α) : ST σ (Slab.Builder σ α) := do
  return { data := ← MutArray.mk (σ := σ) slab.data }

/-- 创建空 builder，可预留载荷容量。 -/
def empty {σ : Type} {α : Type} (capacity : Nat := 0) : ST σ (Slab.Builder σ α) := do
  return { data := ← MutArray.emptyWithCapacity (σ := σ) (α := α) capacity }

/-- 冻结 slab。调用后不应继续修改 builder。 -/
def freeze {σ : Type} {α : Type} (builder : Slab.Builder σ α) : ST σ (Slab α) := do
  return { data := ← builder.data.freeze }

/-- 当前载荷长度。 -/
@[inline]
def size {σ : Type} {α : Type} (builder : Slab.Builder σ α) : ST σ Nat :=
  builder.data.size

/-- 追加数组切片并返回稳定 slice。 -/
def pushSlice {σ : Type} {α : Type} (builder : Slab.Builder σ α)
    (items : @& Array α) : ST σ Slice := do
  let start ← builder.data.appendGetStart items
  return { start := start, len := items.size }

/-- 读取一个位置。 -/
def get? {σ : Type} {α : Type} (builder : Slab.Builder σ α) (index : Nat) :
    ST σ (Option α) :=
  builder.data.get? index

/-- 读取一个位置，越界时返回默认值。 -/
def getD {σ : Type} {α : Type} (builder : Slab.Builder σ α) (index : Nat)
    (default : α) : ST σ α :=
  builder.data.getD index default

/-- 读取一个位置；调用方必须保证位置有效。 -/
@[inline]
def get! {σ : Type} {α : Type} [Inhabited α] (builder : Slab.Builder σ α) (index : Nat) :
    ST σ α :=
  builder.data.get! index

/-- 清空 slab，并在线性持有时保留容量。 -/
def clear {σ : Type} {α : Type} (builder : Slab.Builder σ α) : ST σ Unit :=
  builder.data.clear

end Slab.Builder

end Data
end Automation
end YesMetaZFC
