import Std

/-!
# 自动化底层数据结构公共工具

本文件只放与具体证明语法无关的小工具。后续 ATP 数据结构都从这里取得数组扩容、
安全写入和轻量哈希组合，避免每个模块重复写一份线性辅助函数。

性能约定：
* 纯 `Array` 更新函数只适合冷路径、构造小对象或已经能保证线性传递的管道。
* 饱和循环、CDCL 传播和索引批量构造应使用下面的 `MutArray`/`ST.Ref` 入口。
* trace/debug 历史只能保存摘要或冻结快照，不要保存正在热循环中继续更新的状态对象。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/--
热路径 fold 的提前停止协议。

`next` 继续遍历，`done` 立即返回当前结果。该协议只控制搜索遍历，不携带任何证明语义。
-/
inductive FoldStep (α : Type) where
  | next (state : α)
  | done (result : α)
  deriving Nonempty

namespace FoldStep

/-- 提取提前停止 fold 的最终状态。 -/
@[inline]
def value : FoldStep α → α
  | next state => state
  | done result => result

end FoldStep

/-- 对数组做可提前停止的稳定顺序 fold，并保留是否提前停止。 -/
def foldArrayUntilStep (values : Array α) (initial : β)
    (visit : β → α → FoldStep β) : FoldStep β :=
  Id.run do
    let mut state := initial
    for value in values do
      match visit state value with
      | .next next => state := next
      | .done result => return .done result
    return .next state

/-- 对数组做可提前停止的稳定顺序 fold。 -/
def foldArrayUntil (values : Array α) (initial : β)
    (visit : β → α → FoldStep β) : β :=
  (foldArrayUntilStep values initial visit).value

/-- 对自然数半开区间 `[start, stop)` 做可提前停止的 fold。 -/
def foldNatRangeUntil (start stop : Nat) (initial : α)
    (visit : α → Nat → FoldStep α) : α :=
  Id.run do
    let mut state := initial
    for index in [start:stop] do
      match visit state index with
      | .next next => state := next
      | .done result => return result
    return state

/-- 构造长度为 `n`、元素全为 `value` 的数组。 -/
def filledArray {α : Type u} (n : Nat) (value : α) : Array α := Id.run do
  let mut out := #[]
  for _ in [:n] do
    out := out.push value
  return out

/-- 把数组扩到至少 `target` 长；已有元素保持不变。 -/
def ensureArraySize {α : Type u} (xs : Array α) (target : Nat) (default : α) : Array α :=
  if xs.size >= target then
    xs
  else
    Id.run do
      let mut out := xs
      for _ in [:target - xs.size] do
        out := out.push default
      return out

/-- 在可能越界的位置写入；必要时先用 `default` 扩容。 -/
def setArrayD {α : Type u} (xs : Array α) (index : Nat) (value default : α) : Array α :=
  (ensureArraySize xs (index + 1) default).set! index value

/-- 在可能越界的位置修改；必要时先用 `default` 扩容。 -/
def modifyArrayD {α : Type u} (xs : Array α) (index : Nat) (default : α)
    (f : α → α) : Array α :=
  let xs := ensureArraySize xs (index + 1) default
  xs.set! index (f (xs.getD index default))

/-- 构造长度为 `n`、元素全为 `value` 的紧凑字节数组。 -/
def filledByteArray (n : Nat) (value : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [:n] do
    out := out.push value
  return out

/-- 把字节数组扩到至少 `target` 长；已有字节保持不变。 -/
def ensureByteArraySize (xs : ByteArray) (target : Nat) (default : UInt8) : ByteArray :=
  if xs.size >= target then
    xs
  else
    Id.run do
      let mut out := xs
      for _ in [:target - xs.size] do
        out := out.push default
      return out

/-- 在可能越界的位置写入字节；必要时先用 `default` 扩容。 -/
def setByteArrayD (xs : ByteArray) (index : Nat) (value default : UInt8) : ByteArray :=
  (ensureByteArraySize xs (index + 1) default).set! index value

/-- 用 ST 句柄把右侧数组追加到左侧数组后。适合替代热路径里的 `++`。 -/
def appendArray {α : Type} (left : Array α) (right : @& Array α) : Array α :=
  if right.isEmpty then
    left
  else
    runST fun σ => do
      let out ← ST.mkRef (σ := σ) left
      for value in right do
        out.modify (fun xs => xs.push value)
      out.get

/-- 交换两个数组位置；越界时保持原数组。 -/
def swapArray? {α : Type u} (xs : Array α) (i j : Nat) : Array α :=
  if hi : i < xs.size then
    if hj : j < xs.size then
      let vi := xs[i]
      let vj := xs[j]
      (xs.set! i vj).set! j vi
    else
      xs
  else
    xs

/-- `Hashable.hash` 的 `Nat` 视图。 -/
def hashNat [Hashable α] (value : α) : Nat :=
  (Hashable.hash value).toNat

/-- 把一个自然数压到固定槽位；`width = 0` 时稳定返回 `0`。 -/
def slotOfHash (width value : Nat) : Nat :=
  if width == 0 then 0 else value % width

/-!
## ST mutable array façade

`ST.Ref.modify` 让数组在 ref 内以线性方式流动。调用方不要在一次修改前后同时持有
同一个大数组快照；需要输出日志时先提取标量摘要，最终结果再 `freeze`。
-/

/-- 热路径使用的 ST 数组句柄。 -/
abbrev MutArray (σ : Type) (α : Type) := ST.Ref σ (Array α)

namespace MutArray

/-- 新建可变数组句柄。 -/
def mk {σ : Type} {α : Type} (initial : Array α := #[]) : ST σ (MutArray σ α) :=
  ST.mkRef (σ := σ) initial

/-- 用指定容量创建空数组句柄。 -/
def emptyWithCapacity {σ : Type} {α : Type} (capacity : Nat) : ST σ (MutArray σ α) :=
  ST.mkRef (σ := σ) (Array.emptyWithCapacity capacity)

/-- 读取冻结快照。不要在后续继续更新同一 ref 时长期保存这个数组。 -/
def freeze {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ (Array α) :=
  ref.get

/-- 整体替换底层数组。旧数组在调用后不应继续作为热状态使用。 -/
@[inline]
def replace {σ : Type} {α : Type} (ref : MutArray σ α) (values : Array α) : ST σ Unit :=
  ref.set values

/-- 读取当前元素数量，不把数组快照带出调用边界。 -/
@[inline]
def size {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ Nat := do
  let xs ← ref.get
  return xs.size

/-- 原地风格追加。 -/
def push {σ : Type} {α : Type} (ref : MutArray σ α) (value : α) : ST σ Unit :=
  ref.modify (fun xs => xs.push value)

/--
追加元素并返回追加前的长度。

必须把 size 读取和 push 放在同一次 `modifyGet` 中；若先 `get` 长度再调用 `push`，
生成代码可能让旧数组快照跨过 push 存活，使本应唯一的数组退化为复制更新。
-/
@[inline]
def pushGetIndex {σ : Type} {α : Type} (ref : MutArray σ α) (value : α) : ST σ Nat :=
  ref.modifyGet fun xs =>
    (xs.size, xs.push value)

/-- 弹出尾元素；通过 `modifyGet` 同时返回元素并把缩短后的数组放回 ref。 -/
@[inline]
def pop? {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ (Option α) :=
  ref.modifyGet fun xs =>
    match xs.back? with
    | some value => (some value, xs.pop)
    | none => (none, xs)

/-- 把数组原地截断到至多 `target` 个元素。 -/
@[inline]
def truncate {σ : Type} {α : Type} (ref : MutArray σ α) (target : Nat) : ST σ Unit :=
  ref.modify (fun xs => xs.shrink target)

/--
丢弃指定长度的前缀。

整个操作放在一次 `modify` 中，避免调用方先冻结数组再替换同一个 ref，导致旧快照
跨过清空或压缩操作存活。全部丢弃时使用 `shrink 0`，在线性持有时继续复用容量。
-/
def discardPrefix {σ : Type} {α : Type} (ref : MutArray σ α) (count : Nat) :
    ST σ Unit :=
  ref.modify fun xs =>
    if count == 0 then
      xs
    else if count >= xs.size then
      xs.shrink 0
    else
      xs.extract count xs.size

/-- 原地风格追加一个冻结数组。 -/
def appendArray {σ : Type} {α : Type} (ref : MutArray σ α) (values : @& Array α) :
    ST σ Unit := do
  for value in values do
    ref.push value

/-- 原子地返回旧长度并追加整个数组。 -/
def appendGetStart {σ : Type} {α : Type} (ref : MutArray σ α) (values : @& Array α) :
    ST σ Nat :=
  ref.modifyGet fun xs =>
    let start := xs.size
    let out := values.foldl (fun out value => out.push value) xs
    (start, out)

/-- 原地风格扩容到至少 `target`。 -/
def ensureSize {σ : Type} {α : Type} (ref : MutArray σ α) (target : Nat) (default : α) :
    ST σ Unit :=
  ref.modify (fun xs => ensureArraySize xs target default)

/-- 固定宽度热路径写入；越界时保持数组不变。 -/
@[inline]
def set! {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (value : α) :
    ST σ Unit :=
  ref.modify (fun xs => xs.set! index value)

/-- 固定宽度写入，并返回位置是否有效。 -/
@[inline]
def setAt? {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (value : α) :
    ST σ Bool :=
  ref.modifyGet fun xs =>
    if index < xs.size then
      (true, xs.set! index value)
    else
      (false, xs)

/-- 固定宽度修改，并返回位置是否有效。 -/
@[inline]
def modifyAt? {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat)
    (f : α → α) : ST σ Bool :=
  ref.modifyGet fun xs =>
    match xs[index]? with
    | some value => (true, xs.set! index (f value))
    | none => (false, xs)

/--
固定宽度修改嵌套 RC 值；先写入占位值，再把旧值交给更新函数。
-/
@[inline]
def modifyNestedAt? {σ : Type} {α : Type} [Inhabited α]
    (ref : MutArray σ α) (index : Nat) (f : α → α) : ST σ Bool :=
  ref.modifyGet fun xs =>
    match xs[index]? with
    | some value =>
        let xs := xs.set! index default
        (true, xs.set! index (f value))
    | none => (false, xs)

/-- 原地风格写入；必要时先扩容。 -/
def setD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (value default : α) :
    ST σ Unit :=
  ref.modify (fun xs => setArrayD xs index value default)

/-- 原地风格修改；必要时先扩容。 -/
def modifyD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α)
    (f : α → α) : ST σ Unit :=
  ref.modify (fun xs => modifyArrayD xs index default f)

/--
修改嵌套 RC 值；调用 `f` 前先用占位值断开外层数组对旧值的引用。

当槽位里存放 `Array`、`HashMap` 等 RC 容器时，普通 `modifyD` 会在读取旧值后仍让
外层数组持有它，使后续 `push`/`insert` 失去唯一性并复制整个容器。这里额外做一次
占位写入，让旧值有机会恢复唯一所有权。`default` 应选用廉价且不与旧值共享的空值。
-/
@[inline]
def modifyNestedD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α)
    (f : α → α) : ST σ Unit :=
  ref.modify fun xs =>
    let xs := ensureArraySize xs (index + 1) default
    let current := xs.getD index default
    let xs := xs.set! index default
    xs.set! index (f current)

/--
从嵌套槽位中取出旧值，并立即写入占位值。

与先 `getD` 再 `setD` 不同，这个操作在同一次 `modifyGet` 中断开外层数组对旧值的
引用。调用方随后可以线性修改返回的 `Array`、`HashMap` 等 RC 容器。
-/
@[inline]
def takeD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α) :
    ST σ α :=
  ref.modifyGet fun xs =>
    let xs := ensureArraySize xs (index + 1) default
    let current := xs.getD index default
    (current, xs.set! index default)

/-- 在 ST 内只读一个位置。 -/
def get? {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) : ST σ (Option α) := do
  let xs ← ref.get
  return xs[index]?

/-- 在 ST 内只读一个位置，越界时返回默认值。 -/
def getD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α) : ST σ α := do
  let xs ← ref.get
  return xs.getD index default

/-- 固定宽度热路径读取；越界时触发 `get!` 的 panic 默认值。 -/
@[inline]
def get! {σ : Type} {α : Type} [Inhabited α] (ref : MutArray σ α) (index : Nat) : ST σ α := do
  let xs ← ref.get
  return xs[index]!

/-- 清空数组，并在线性持有时复用底层容量。 -/
def clear {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ Unit :=
  ref.modify (·.shrink 0)

end MutArray

/-!
## ST mutable byte array façade

固定宽度状态表优先使用该表示，避免 `Array (Option Bool)` 一类装箱元素在热路径中
引入额外内存和 RC 流量。
-/

/-- 热路径使用的紧凑字节数组句柄。 -/
abbrev MutByteArray (σ : Type) := ST.Ref σ ByteArray

namespace MutByteArray

/-- 新建可变字节数组句柄。 -/
def mk {σ : Type} (initial : ByteArray := ByteArray.empty) : ST σ (MutByteArray σ) :=
  ST.mkRef (σ := σ) initial

/-- 整体替换底层字节数组。 -/
@[inline]
def replace {σ : Type} (ref : MutByteArray σ) (values : ByteArray) : ST σ Unit :=
  ref.set values

/-- 读取冻结快照。 -/
def freeze {σ : Type} (ref : MutByteArray σ) : ST σ ByteArray :=
  ref.get

/-- 读取当前字节数。 -/
@[inline]
def size {σ : Type} (ref : MutByteArray σ) : ST σ Nat := do
  let xs ← ref.get
  return xs.size

/-- 在 ST 内读取一个字节，越界时返回 `default`。 -/
@[inline]
def getD {σ : Type} (ref : MutByteArray σ) (index : Nat) (default : UInt8) :
    ST σ UInt8 := do
  let xs ← ref.get
  if index < xs.size then
    return xs.get! index
  return default

/-- 固定宽度热路径读取；越界时触发 `ByteArray.get!` 的 panic 默认值。 -/
@[inline]
def get! {σ : Type} (ref : MutByteArray σ) (index : Nat) : ST σ UInt8 := do
  let xs ← ref.get
  return xs.get! index

/-- 固定宽度热路径写入；越界时保持字节数组不变。 -/
@[inline]
def set! {σ : Type} (ref : MutByteArray σ) (index : Nat) (value : UInt8) :
    ST σ Unit :=
  ref.modify (fun xs => xs.set! index value)

/-- 原地风格写入字节；必要时先扩容。 -/
@[inline]
def setD {σ : Type} (ref : MutByteArray σ) (index : Nat) (value default : UInt8) :
    ST σ Unit :=
  ref.modify (fun xs => setByteArrayD xs index value default)

end MutByteArray

end Data
end Automation
end YesMetaZFC
