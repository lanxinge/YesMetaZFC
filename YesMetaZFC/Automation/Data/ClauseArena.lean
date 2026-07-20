import YesMetaZFC.Automation.Data.Arena
import Lean

/-!
# 命题字句 arena

CDCL 热数据库使用连续 literal slab 和单层 header 数组。逻辑边界的结构化 literal
只在输入、最终 SAT assignment 和对象层 replay 时物化；传播、冲突分析和证书 journal
统一传递 `ClauseId` 与 `PackedLit`。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 紧凑 literal：低位保存极性，其余位保存变量编号。 -/
abbrev PackedLit := Nat

namespace PackedLit

/-- 从变量编号与极性打包 literal。 -/
@[inline]
def pack (var : Nat) (positive : Bool) : PackedLit :=
  (var <<< 1) ||| if positive then 1 else 0

/-- 变量编号。 -/
@[inline]
def var (lit : PackedLit) : Nat :=
  lit >>> 1

/-- 极性。 -/
@[inline]
def positive (lit : PackedLit) : Bool :=
  lit &&& 1 == 1

/-- 取反。 -/
@[inline]
def neg (lit : PackedLit) : PackedLit :=
  lit ^^^ 1

end PackedLit

/-- 单个 arena 字句的固定头部。 -/
structure ClauseHeader where
  start : Nat := 0
  length : Nat := 0
  watch0 : Nat := 0
  watch1 : Nat := 0
  hash : UInt64 := 0
  activity : Nat := 0
  lbd : Nat := 0
  flags : UInt8 := 0
  deriving Repr, BEq, DecidableEq, Inhabited, Lean.ToExpr

namespace ClauseHeader

/-- literal 切片。 -/
def slice (header : ClauseHeader) : Slice :=
  { start := header.start, len := header.length }

/-- 当前两个 watch 位置。 -/
def watches (header : ClauseHeader) : Nat × Nat :=
  (header.watch0, header.watch1)

/-- 更新 watch 位置。 -/
def withWatches (header : ClauseHeader) (first second : Nat) : ClauseHeader :=
  { header with watch0 := first, watch1 := second }

end ClauseHeader

/-- learned clause 标志位。 -/
def learnedClauseFlag : UInt8 := 1

/-- 紧凑 literal 数组的稳定哈希。 -/
def hashPackedClause (clause : Array PackedLit) : UInt64 :=
  clause.foldl
    (fun hash lit => mixHash hash (Hashable.hash lit))
    (1469598103934665603 : UInt64)

/-- 冻结的命题字句 arena。 -/
structure ClauseArena where
  literals : Array PackedLit := #[]
  headers : Array ClauseHeader := #[]
  deriving Repr, BEq, Inhabited, Lean.ToExpr

namespace ClauseArena

/-- 空 arena。 -/
def empty : ClauseArena := {}

/-- 字句数量。 -/
@[inline]
def size (arena : ClauseArena) : Nat :=
  arena.headers.size

/-- 下一个字句 id。 -/
@[inline]
def nextId (arena : ClauseArena) : ClauseId :=
  Id.ofIndex arena.headers.size

/-- 读取 header。 -/
@[inline]
def header? (arena : ClauseArena) (id : ClauseId) : Option ClauseHeader := do
  let index ← id.index?
  arena.headers[index]?

/-- 读取字句长度。 -/
@[inline]
def clauseSize (arena : ClauseArena) (id : ClauseId) : Nat :=
  match arena.header? id with
  | some header => header.length
  | none => 0

/-- 读取字句中的 packed literal。 -/
@[inline]
def lit? (arena : ClauseArena) (id : ClauseId) (position : Nat) : Option PackedLit := do
  let header ← arena.header? id
  if position < header.length then
    arena.literals[header.start + position]?
  else
    none

/-- 物化一个 packed clause。只在冷路径或 replay 边界使用。 -/
def packedClause (arena : ClauseArena) (id : ClauseId) : Array PackedLit :=
  match arena.header? id with
  | some header => arena.literals.extract header.start (header.start + header.length)
  | none => #[]

/-- arena 字句是否等于给定 packed clause。 -/
def clauseEqPacked (arena : ClauseArena) (id : ClauseId)
    (clause : Array PackedLit) : Bool :=
  match arena.header? id with
  | none => false
  | some header =>
      if header.length != clause.size || header.hash != hashPackedClause clause then
        false
      else
        Id.run do
          for position in [:header.length] do
            if arena.literals[header.start + position]? != clause[position]? then
              return false
          return true

/-- arena 字句是否为空。 -/
@[inline]
def clauseIsEmpty (arena : ClauseArena) (id : ClauseId) : Bool :=
  arena.clauseSize id == 0

/-!
## ST builder
-/

/-- CDCL 生命周期内的可变 arena。 -/
structure Builder (σ : Type) where
  literals : Slab.Builder σ PackedLit
  headers : Arena.Builder σ ClauseTag ClauseHeader
  /-- 哈希命中后仍按 arena 正文确认，避免哈希碰撞。 -/
  buckets : ST.Ref σ (Std.HashMap UInt64 (Array Nat))

namespace Builder

/-- clause interning 的稳定结果。 -/
inductive InternResult where
  | inserted (id : ClauseId)
  | existing (id : ClauseId)

namespace InternResult

/-- 无论是否新插入，都取得稳定 ClauseId。 -/
@[inline]
def id : InternResult → ClauseId
  | .inserted id | .existing id => id

/-- 是否真的扩展了 arena。 -/
@[inline]
def isNew : InternResult → Bool
  | .inserted _ => true
  | .existing _ => false

end InternResult

/-- 把 ClauseId 登记进对应哈希碰撞桶。 -/
private def registerClauseId {σ : Type} (builder : Builder σ)
    (hash : UInt64) (id : ClauseId) : ST σ Unit :=
  builder.buckets.modify fun table =>
    table.insert hash (((table.get? hash).getD #[]).push id.raw)

/-- 创建空 builder。 -/
def empty {σ : Type} : ST σ (Builder σ) := do
  let literals ← Slab.Builder.empty (σ := σ) (α := PackedLit)
  let headers ← Arena.Builder.empty (σ := σ) (tag := ClauseTag) (α := ClauseHeader)
  let buckets ← ST.mkRef (σ := σ)
    (Std.HashMap.emptyWithCapacity : Std.HashMap UInt64 (Array Nat))
  return { literals := literals, headers := headers, buckets := buckets }

/-- 从冻结 arena 创建 builder。 -/
def ofArena {σ : Type} (arena : ClauseArena) : ST σ (Builder σ) := do
  let builder : Builder σ := {
    literals := ← Slab.Builder.ofSlab (σ := σ) { data := arena.literals }
    headers := ← Arena.Builder.ofArena (σ := σ) { values := arena.headers }
    buckets := ← ST.mkRef (σ := σ)
      (Std.HashMap.emptyWithCapacity : Std.HashMap UInt64 (Array Nat))
  }
  for h : index in [:arena.headers.size] do
    let id : ClauseId := Id.ofIndex index
    builder.registerClauseId arena.headers[index].hash id
  return builder

/-- 冻结 arena。调用后不应继续修改 builder。 -/
def freeze {σ : Type} (builder : Builder σ) : ST σ ClauseArena := do
  let literals ← builder.literals.freeze
  let headers ← builder.headers.freeze
  return {
    literals := literals.data
    headers := headers.values
  }

/-- 字句数量。 -/
@[inline]
def size {σ : Type} (builder : Builder σ) : ST σ Nat :=
  builder.headers.size

/-- 读取 header。 -/
@[inline]
def header? {σ : Type} (builder : Builder σ) (id : ClauseId) :
    ST σ (Option ClauseHeader) :=
  builder.headers.get? id

/-- 固定宽度写回 header。 -/
@[inline]
def setHeader {σ : Type} (builder : Builder σ) (id : ClauseId)
    (header : ClauseHeader) : ST σ Unit := do
  let _ ← builder.headers.set? id header
  pure ()

/-- 修改 header。 -/
@[inline]
def modifyHeader {σ : Type} (builder : Builder σ) (id : ClauseId)
    (f : ClauseHeader → ClauseHeader) : ST σ Unit := do
  match ← builder.header? id with
  | some header => builder.setHeader id (f header)
  | none => pure ()

/-- 更新 watch 位置。 -/
@[inline]
def setWatches {σ : Type} (builder : Builder σ) (id : ClauseId)
    (first second : Nat) : ST σ Unit :=
  builder.modifyHeader id (fun header => header.withWatches first second)

/-- 读取字句长度。 -/
@[inline]
def clauseSize {σ : Type} (builder : Builder σ) (id : ClauseId) : ST σ Nat := do
  return (← builder.header? id).map (·.length) |>.getD 0

/-- 读取 packed literal；越界时返回 `0`。 -/
@[inline]
def litAt! {σ : Type} (builder : Builder σ) (header : ClauseHeader) (position : Nat) :
    ST σ PackedLit := do
  if position < header.length then
    return ← builder.literals.get! (header.start + position)
  return 0

/-- 按 ClauseId 读取 packed literal；越界时返回 `0`。 -/
@[inline]
def lit! {σ : Type} (builder : Builder σ) (id : ClauseId) (position : Nat) :
    ST σ PackedLit := do
  let some header ← builder.header? id | return 0
  builder.litAt! header position

/-- arena 字句是否等于给定 packed clause。 -/
def clauseEqPacked {σ : Type} (builder : Builder σ) (id : ClauseId)
    (clause : @& Array PackedLit) : ST σ Bool := do
  let some header ← builder.header? id | return false
  if header.length != clause.size || header.hash != hashPackedClause clause then
    return false
  for position in [:header.length] do
    if (← builder.literals.get! (header.start + position)) != clause[position]! then
      return false
  return true

/-- 查找正文完全相等的已有字句。 -/
def lookupClause? {σ : Type} (builder : Builder σ)
    (clause : @& Array PackedLit) : ST σ (Option ClauseId) := do
  let hash := hashPackedClause clause
  let candidates := ((← builder.buckets.get).get? hash).getD #[]
  for rawId in candidates do
    let id : ClauseId := Id.ofNat rawId
    if ← builder.clauseEqPacked id clause then
      return some id
  return none

/-- 追加 packed clause，并返回稳定 ClauseId。 -/
def pushClause {σ : Type} (builder : Builder σ) (clause : @& Array PackedLit)
    (flags : UInt8 := 0) : ST σ ClauseId := do
  let slice ← builder.literals.pushSlice clause
  let secondWatch := if clause.size > 1 then 1 else 0
  let hash := hashPackedClause clause
  let id ← builder.headers.push {
    start := slice.start
    length := clause.size
    watch0 := 0
    watch1 := secondWatch
    hash := hash
    flags := flags
  }
  builder.registerClauseId hash id
  return id

/--
Intern 一个 packed clause。

初始输入仍可使用 `pushClause` 保留逐槽编号；learned 与外部 theory clause 使用本接口，
正文重复时复用最早登记的稳定 ClauseId。
-/
def internClause {σ : Type} (builder : Builder σ) (clause : @& Array PackedLit)
    (flags : UInt8 := 0) : ST σ InternResult := do
  match ← builder.lookupClause? clause with
  | some id => return .existing id
  | none => return .inserted (← builder.pushClause clause flags)

end Builder

end ClauseArena

end Data
end Automation
end YesMetaZFC
