import YesMetaZFC.Automation.Data.Util

/-!
# Sparse set/map

SAT/ATP 热路径常用 sparse-dense 表示：membership、插入、删除和清空都避免线性扫描。
这里先支持 `Nat` key，后续 packed handle 可通过 `Id.toNat` 接入。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- `Nat` sparse set。 -/
structure SparseSet where
  dense : Array Nat := #[]
  sparse : Array Nat := #[]
  deriving Repr, BEq, Inhabited

namespace SparseSet

/-- 空集合。 -/
def empty : SparseSet := {}

/-- 元素数量。 -/
def size (set : SparseSet) : Nat := set.dense.size

/-- O(1) membership。 -/
def contains (set : SparseSet) (value : Nat) : Bool :=
  let pos := set.sparse.getD value 0
  pos < set.dense.size && set.dense[pos]! == value

/-- 插入元素。 -/
def insert (set : SparseSet) (value : Nat) : SparseSet :=
  if set.contains value then
    set
  else
    {
      dense := set.dense.push value
      sparse := setArrayD set.sparse value set.dense.size 0
    }

/-- 删除元素；用最后一个元素填洞。 -/
def erase (set : SparseSet) (value : Nat) : SparseSet :=
  if !set.contains value then
    set
  else
    let pos := set.sparse.getD value 0
    let lastIndex := set.dense.size - 1
    let last := set.dense[lastIndex]!
    let dense :=
      if pos == lastIndex then
        set.dense.pop
      else
        (set.dense.set! pos last).pop
    let sparse :=
      if pos == lastIndex then
        set.sparse
      else
        setArrayD set.sparse last pos 0
    { dense := dense, sparse := sparse }

/-- O(1) 清空；保留 sparse 容量供后续复用。 -/
def clear (set : SparseSet) : SparseSet :=
  { set with dense := #[] }

/-- 当前成员数组。 -/
def members (set : SparseSet) : Array Nat := set.dense

/-- 折叠当前成员。 -/
def fold (set : SparseSet) (init : β) (f : β → Nat → β) : β :=
  set.dense.foldl f init

end SparseSet

/-- ST 生命周期内可变的 sparse set。 -/
structure SparseSet.Builder (σ : Type) where
  dense : MutArray σ Nat
  sparse : MutArray σ Nat

namespace SparseSet.Builder

/-- 从冻结 sparse set 创建 builder。 -/
def ofSet {σ : Type} (set : SparseSet) : ST σ (SparseSet.Builder σ) := do
  return {
    dense := ← MutArray.mk (σ := σ) set.dense
    sparse := ← MutArray.mk (σ := σ) set.sparse
  }

/-- 创建空 builder。 -/
def empty {σ : Type} (capacity : Nat := 0) : ST σ (SparseSet.Builder σ) := do
  return {
    dense := ← MutArray.emptyWithCapacity (σ := σ) (α := Nat) capacity
    sparse := ← MutArray.mk (σ := σ) (#[] : Array Nat)
  }

/-- 冻结 sparse set。调用后不应继续修改 builder。 -/
def freeze {σ : Type} (builder : SparseSet.Builder σ) : ST σ SparseSet := do
  return {
    dense := ← builder.dense.freeze
    sparse := ← builder.sparse.freeze
  }

/-- 当前元素数量。 -/
@[inline]
def size {σ : Type} (builder : SparseSet.Builder σ) : ST σ Nat :=
  builder.dense.size

/-- O(1) membership。 -/
def contains {σ : Type} (builder : SparseSet.Builder σ) (value : Nat) : ST σ Bool := do
  let pos ← builder.sparse.getD value 0
  let size ← builder.size
  if pos < size then
    return (← builder.dense.get! pos) == value
  return false

/-- 插入元素。 -/
def insert {σ : Type} (builder : SparseSet.Builder σ) (value : Nat) : ST σ Bool := do
  if ← builder.contains value then
    return false
  let pos ← builder.dense.pushGetIndex value
  builder.sparse.setD value pos 0
  return true

/-- 删除元素；用最后一个元素填洞。 -/
def erase {σ : Type} (builder : SparseSet.Builder σ) (value : Nat) : ST σ Bool := do
  if !(← builder.contains value) then
    return false
  let pos ← builder.sparse.getD value 0
  let size ← builder.size
  let lastIndex := size - 1
  let last ← builder.dense.get! lastIndex
  let _ ← builder.dense.pop?
  if pos != lastIndex then
    builder.dense.set! pos last
    builder.sparse.setD last pos 0
  return true

/-- 清空 dense 成员并保留 sparse 定位表。 -/
def clear {σ : Type} (builder : SparseSet.Builder σ) : ST σ Unit :=
  builder.dense.clear

end SparseSet.Builder

/-- `Nat ↦ α` sparse map。 -/
structure SparseMap (α : Type) where
  keys : Array Nat := #[]
  values : Array α := #[]
  sparse : Array Nat := #[]
  deriving Repr, Inhabited

namespace SparseMap

/-- 空映射。 -/
def empty : SparseMap α := {}

/-- 键数量。 -/
def size (map : SparseMap α) : Nat := map.keys.size

/-- key 对应 dense 位置。 -/
def position? (map : SparseMap α) (key : Nat) : Option Nat :=
  let pos := map.sparse.getD key 0
  if pos < map.keys.size && map.keys[pos]! == key then some pos else none

/-- 是否包含 key。 -/
def contains (map : SparseMap α) (key : Nat) : Bool :=
  (map.position? key).isSome

/-- 读取 key。 -/
def get? (map : SparseMap α) (key : Nat) : Option α := do
  let pos ← map.position? key
  map.values[pos]?

/-- 插入或更新 key。 -/
def insert (map : SparseMap α) (key : Nat) (value : α) : SparseMap α :=
  match map.position? key with
  | some pos => { map with values := map.values.set! pos value }
  | none =>
      {
        keys := map.keys.push key
        values := map.values.push value
        sparse := setArrayD map.sparse key map.keys.size 0
      }

/-- 删除 key；用最后一个键值对填洞。 -/
def erase (map : SparseMap α) (key : Nat) : SparseMap α :=
  match map.position? key with
  | none => map
  | some pos =>
      let lastIndex := map.keys.size - 1
      match map.keys[lastIndex]?, map.values[lastIndex]? with
      | some lastKey, some lastValue =>
          let keys :=
            if pos == lastIndex then map.keys.pop else (map.keys.set! pos lastKey).pop
          let values :=
            if pos == lastIndex then map.values.pop else (map.values.set! pos lastValue).pop
          let sparse :=
            if pos == lastIndex then map.sparse else setArrayD map.sparse lastKey pos 0
          { keys := keys, values := values, sparse := sparse }
      | _, _ => map

/-- O(1) 清空；保留 sparse 容量。 -/
def clear (map : SparseMap α) : SparseMap α :=
  { map with keys := #[], values := #[] }

/-- 折叠键值对。 -/
def fold (map : SparseMap α) (init : β) (f : β → Nat → α → β) : β := Id.run do
  let mut acc := init
  for h : i in [:map.keys.size] do
    match map.values[i]? with
    | some value => acc := f acc map.keys[i] value
    | none => pure ()
  return acc

end SparseMap

/-- ST 生命周期内可变的 sparse map。 -/
structure SparseMap.Builder (σ : Type) (α : Type) where
  keys : MutArray σ Nat
  values : MutArray σ α
  sparse : MutArray σ Nat

namespace SparseMap.Builder

/-- 从冻结 sparse map 创建 builder。 -/
def ofMap {σ : Type} {α : Type} (map : SparseMap α) :
    ST σ (SparseMap.Builder σ α) := do
  return {
    keys := ← MutArray.mk (σ := σ) map.keys
    values := ← MutArray.mk (σ := σ) map.values
    sparse := ← MutArray.mk (σ := σ) map.sparse
  }

/-- 创建空 builder。 -/
def empty {σ : Type} {α : Type} (capacity : Nat := 0) :
    ST σ (SparseMap.Builder σ α) := do
  return {
    keys := ← MutArray.emptyWithCapacity (σ := σ) (α := Nat) capacity
    values := ← MutArray.emptyWithCapacity (σ := σ) (α := α) capacity
    sparse := ← MutArray.mk (σ := σ) (#[] : Array Nat)
  }

/-- 冻结 sparse map。调用后不应继续修改 builder。 -/
def freeze {σ : Type} {α : Type} (builder : SparseMap.Builder σ α) :
    ST σ (SparseMap α) := do
  return {
    keys := ← builder.keys.freeze
    values := ← builder.values.freeze
    sparse := ← builder.sparse.freeze
  }

/-- 当前键数量。 -/
@[inline]
def size {σ : Type} {α : Type} (builder : SparseMap.Builder σ α) : ST σ Nat :=
  builder.keys.size

/-- key 对应的 dense 位置。 -/
def position? {σ : Type} {α : Type} (builder : SparseMap.Builder σ α) (key : Nat) :
    ST σ (Option Nat) := do
  let pos ← builder.sparse.getD key 0
  if pos < (← builder.size) && (← builder.keys.get! pos) == key then
    return some pos
  return none

/-- 是否包含 key。 -/
@[inline]
def contains {σ : Type} {α : Type} (builder : SparseMap.Builder σ α) (key : Nat) :
    ST σ Bool := do
  return (← builder.position? key).isSome

/-- 读取 key。 -/
def get? {σ : Type} {α : Type} (builder : SparseMap.Builder σ α) (key : Nat) :
    ST σ (Option α) := do
  let some pos ← builder.position? key | return none
  builder.values.get? pos

/-- 插入或更新 key。返回值表示是否新增。 -/
def insert {σ : Type} {α : Type} (builder : SparseMap.Builder σ α)
    (key : Nat) (value : α) : ST σ Bool := do
  match ← builder.position? key with
  | some pos =>
      builder.values.set! pos value
      return false
  | none =>
      let pos ← builder.keys.pushGetIndex key
      builder.values.push value
      builder.sparse.setD key pos 0
      return true

/-- 删除 key；用最后一个键值对填洞。 -/
def erase {σ : Type} {α : Type} (builder : SparseMap.Builder σ α) (key : Nat) :
    ST σ Bool := do
  let some pos ← builder.position? key | return false
  let size ← builder.size
  let lastIndex := size - 1
  let lastKey ← builder.keys.get! lastIndex
  let some lastValue ← builder.values.pop? | return false
  let _ ← builder.keys.pop?
  if pos != lastIndex then
    builder.keys.set! pos lastKey
    builder.values.set! pos lastValue
    builder.sparse.setD lastKey pos 0
  return true

/-- 清空 dense 键值并保留 sparse 定位表。 -/
def clear {σ : Type} {α : Type} (builder : SparseMap.Builder σ α) : ST σ Unit := do
  builder.keys.clear
  builder.values.clear

end SparseMap.Builder

end Data
end Automation
end YesMetaZFC
