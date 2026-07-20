import YesMetaZFC.Automation.Data.Util

/-!
# Binary heap

给 given-clause passive 队列、agenda 和优先级调度共用的最小堆。比较函数由调用方提供，
因此底层不依赖任何自动化语法。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 由调用方比较函数驱动的冻结二叉最小堆。 -/
structure BinaryHeap (α : Type) where
  data : Array α := #[]
  less : α → α → Bool

namespace BinaryHeap

/-- 空堆。 -/
def empty (less : α → α → Bool) : BinaryHeap α :=
  { less := less }

/-- 元素数量。 -/
def size (heap : BinaryHeap α) : Nat := heap.data.size

/-- 是否为空。 -/
def isEmpty (heap : BinaryHeap α) : Bool := heap.data.isEmpty

/-- 查看堆顶。 -/
def peek? (heap : BinaryHeap α) : Option α := heap.data[0]?

private def parent (index : Nat) : Nat := (index - 1) / 2
private def leftChild (index : Nat) : Nat := 2 * index + 1
private def rightChild (index : Nat) : Nat := 2 * index + 2

private partial def siftUpArray (less : α → α → Bool) (data : Array α) (index : Nat) :
    Array α :=
  if index == 0 then
    data
  else
    let parentIndex := parent index
    match data[index]?, data[parentIndex]? with
    | some child, some parentValue =>
        if less child parentValue then
          siftUpArray less (swapArray? data index parentIndex) parentIndex
        else
          data
    | _, _ => data

private partial def siftDownArray (less : α → α → Bool) (data : Array α) (index : Nat) :
    Array α :=
  let left := leftChild index
  let right := rightChild index
  match data[left]? with
  | none =>
    data
  | some leftValue =>
    let best :=
      match data[right]? with
      | some rightValue => if less rightValue leftValue then right else left
      | none => left
    match data[best]?, data[index]? with
    | some bestValue, some current =>
        if less bestValue current then
          siftDownArray less (swapArray? data index best) best
        else
          data
    | _, _ => data

/-- Floyd bottom-up heapify。每个非叶节点只向下筛一次，总复杂度为 O(n)。 -/
private def heapifyArray (less : α → α → Bool) (items : Array α) : Array α := Id.run do
  let mut data := items
  let mut index := data.size / 2
  while index > 0 do
    index := index - 1
    data := siftDownArray less data index
  return data

/-- 插入元素。 -/
def push (heap : BinaryHeap α) (value : α) : BinaryHeap α :=
  let data := heap.data.push value
  { heap with data := siftUpArray heap.less data (data.size - 1) }

/-- 弹出堆顶。 -/
def popMin? (heap : BinaryHeap α) : Option (α × BinaryHeap α) :=
  match heap.data[0]? with
  | none => none
  | some root =>
      if heap.data.size == 1 then
        some (root, { heap with data := #[] })
      else
        match heap.data.back? with
        | some last =>
            let data := (heap.data.set! 0 last).pop
            some (root, { heap with data := siftDownArray heap.less data 0 })
        | none => none

/-- 用 bottom-up heapify 从数组线性重建堆。 -/
def ofArray (less : α → α → Bool) (items : Array α) : BinaryHeap α :=
  { data := heapifyArray less items, less := less }

/-- 合并一个数组中的元素。 -/
def pushMany (heap : BinaryHeap α) (items : Array α) : BinaryHeap α :=
  items.foldl (fun heap item => heap.push item) heap

end BinaryHeap

/-!
## ST builder
-/

/-- ST 生命周期内可变的二叉最小堆。 -/
structure BinaryHeap.Builder (σ : Type) (α : Type) where
  data : MutArray σ α
  less : α → α → Bool

namespace BinaryHeap.Builder

/-- 从冻结堆创建 builder。 -/
def ofHeap {σ : Type} {α : Type} (heap : BinaryHeap α) :
    ST σ (BinaryHeap.Builder σ α) := do
  return {
    data := ← MutArray.mk (σ := σ) heap.data
    less := heap.less
  }

/-- 创建空堆，可预留容量。 -/
def empty {σ : Type} {α : Type} (less : α → α → Bool) (capacity : Nat := 0) :
    ST σ (BinaryHeap.Builder σ α) := do
  return {
    data := ← MutArray.emptyWithCapacity (σ := σ) (α := α) capacity
    less := less
  }

/-- 冻结堆。调用后不应继续修改 builder。 -/
def freeze {σ : Type} {α : Type} (builder : BinaryHeap.Builder σ α) :
    ST σ (BinaryHeap α) := do
  return { data := ← builder.data.freeze, less := builder.less }

/-- 元素数量。 -/
@[inline]
def size {σ : Type} {α : Type} (builder : BinaryHeap.Builder σ α) : ST σ Nat :=
  builder.data.size

/-- 堆是否为空。 -/
@[inline]
def isEmpty {σ : Type} {α : Type} (builder : BinaryHeap.Builder σ α) : ST σ Bool := do
  return (← builder.size) == 0

/-- 查看堆顶。 -/
def peek? {σ : Type} {α : Type} (builder : BinaryHeap.Builder σ α) :
    ST σ (Option α) :=
  builder.data.get? 0

private def swap {σ : Type} {α : Type} [Inhabited α]
    (builder : BinaryHeap.Builder σ α) (left right : Nat) : ST σ Unit := do
  if left != right then
    let leftValue ← builder.data.get! left
    let rightValue ← builder.data.get! right
    builder.data.set! left rightValue
    builder.data.set! right leftValue

private partial def siftUp {σ : Type} {α : Type} [Inhabited α]
    (builder : BinaryHeap.Builder σ α) (index : Nat) : ST σ Unit := do
  if index == 0 then
    return
  let parentIndex := (index - 1) / 2
  let child ← builder.data.get! index
  let parentValue ← builder.data.get! parentIndex
  if builder.less child parentValue then
    builder.swap index parentIndex
    builder.siftUp parentIndex

private partial def siftDown {σ : Type} {α : Type} [Inhabited α]
    (builder : BinaryHeap.Builder σ α) (index : Nat) : ST σ Unit := do
  let size ← builder.size
  let left := 2 * index + 1
  if left >= size then
    return
  let right := left + 1
  let mut best := left
  if right < size then
    let leftValue ← builder.data.get! left
    let rightValue ← builder.data.get! right
    if builder.less rightValue leftValue then
      best := right
  let current ← builder.data.get! index
  let bestValue ← builder.data.get! best
  if builder.less bestValue current then
    builder.swap index best
    builder.siftDown best

/-- 对当前底层数组执行 Floyd bottom-up heapify。 -/
private def heapify {σ : Type} {α : Type} [Inhabited α]
    (builder : BinaryHeap.Builder σ α) : ST σ Unit := do
  let mut index := (← builder.size) / 2
  while index > 0 do
    index := index - 1
    builder.siftDown index

/-- 插入元素。 -/
def push {σ : Type} {α : Type} [Inhabited α]
    (builder : BinaryHeap.Builder σ α) (value : α) : ST σ Unit := do
  let index ← builder.data.pushGetIndex value
  builder.siftUp index

/-- 弹出堆顶。 -/
def popMin? {σ : Type} {α : Type} [Inhabited α]
    (builder : BinaryHeap.Builder σ α) : ST σ (Option α) := do
  let size ← builder.size
  if size == 0 then
    return none
  let root ← builder.data.get! 0
  let some last ← builder.data.pop? | return some root
  if size > 1 then
    builder.data.set! 0 last
    builder.siftDown 0
  return some root

/-- 追加一批元素。 -/
def pushMany {σ : Type} {α : Type} [Inhabited α]
    (builder : BinaryHeap.Builder σ α) (items : @& Array α) : ST σ Unit := do
  for item in items do
    builder.push item

/-- 用 bottom-up heapify 从数组线性创建堆 builder。 -/
def ofArray {σ : Type} {α : Type} [Inhabited α]
    (less : α → α → Bool) (items : @& Array α) : ST σ (BinaryHeap.Builder σ α) := do
  let data ← MutArray.mk (σ := σ) items
  let builder : BinaryHeap.Builder σ α := { data := data, less := less }
  builder.heapify
  return builder

/-- 清空堆并保留容量。 -/
def clear {σ : Type} {α : Type} (builder : BinaryHeap.Builder σ α) : ST σ Unit :=
  builder.data.clear

end BinaryHeap.Builder

end Data
end Automation
end YesMetaZFC
