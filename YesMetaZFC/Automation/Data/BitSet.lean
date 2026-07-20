import YesMetaZFC.Automation.Data.Util

/-!
# UInt64 BitSet

位集是包含检查、subsumption signature、变量集和删除标记的公共底层表示。
纯 `BitSet` 接口用于冻结快照和冷路径；热循环应使用 `BitSet.Builder`，让底层数组
留在 `ST.Ref` 中原地风格更新。若后续需要 native SIMD/FFI，只替换本文件实现即可。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

namespace UInt64Bits

/-- 每个机器字的位数。 -/
def wordBits : Nat := 64

/-- `1 <<< offset`，其中 `offset` 只看低 6 位。 -/
def mask (offset : Nat) : UInt64 :=
  UInt64.shiftLeft (1 : UInt64) (UInt64.ofNat (offset % wordBits))

/-- 从 offset 到最高位全部置一。 -/
@[inline]
def suffixMask (offset : Nat) : UInt64 :=
  UInt64.complement (mask offset - 1)

/-- SWAR popcount；只执行固定数量的机器字位运算。 -/
@[inline]
def popcount (word : UInt64) : Nat :=
  let word := word - ((word >>> 1) &&& (0x5555555555555555 : UInt64))
  let word := (word &&& (0x3333333333333333 : UInt64)) +
    ((word >>> 2) &&& (0x3333333333333333 : UInt64))
  let word := (word + (word >>> 4)) &&& (0x0F0F0F0F0F0F0F0F : UInt64)
  let word := word + (word >>> 8)
  let word := word + (word >>> 16)
  let word := word + (word >>> 32)
  (word &&& (0x7F : UInt64)).toNat

/-- 非零机器字最低置位的位置；零字返回 64。 -/
@[inline]
def trailingZeros (word : UInt64) : Nat := Id.run do
  if word == 0 then
    return wordBits
  let mut current := word
  let mut count : UInt64 := 0
  if (current &&& 0xFFFFFFFF) == 0 then
    current := current >>> 32
    count := count + 32
  if (current &&& 0xFFFF) == 0 then
    current := current >>> 16
    count := count + 16
  if (current &&& 0xFF) == 0 then
    current := current >>> 8
    count := count + 8
  if (current &&& 0xF) == 0 then
    current := current >>> 4
    count := count + 4
  if (current &&& 0x3) == 0 then
    current := current >>> 2
    count := count + 2
  if (current &&& 0x1) == 0 then
    count := count + 1
  return count.toNat

end UInt64Bits

/-- 小型可扩容位集。 -/
structure BitSet where
  words : Array UInt64 := #[]
  deriving Repr, BEq, Inhabited

namespace BitSet

/-- 空位集。 -/
def empty : BitSet := {}

/-- 位所属 word。 -/
def wordIndex (bit : Nat) : Nat := bit / UInt64Bits.wordBits

/-- 位在 word 内的偏移。 -/
def bitOffset (bit : Nat) : Nat := bit % UInt64Bits.wordBits

/-- 确保位集能容纳给定 bit。 -/
def ensureBit (set : BitSet) (bit : Nat) : BitSet :=
  { words := ensureArraySize set.words (wordIndex bit + 1) 0 }

/-- 测试 bit 是否存在。 -/
def test (set : @& BitSet) (bit : Nat) : Bool :=
  let wi := wordIndex bit
  if wi < set.words.size then
    (set.words[wi]! &&& UInt64Bits.mask (bitOffset bit)) != 0
  else
    false

/-- 加入 bit。 -/
def insert (set : BitSet) (bit : Nat) : BitSet :=
  let set := set.ensureBit bit
  let wi := wordIndex bit
  let word := set.words[wi]! ||| UInt64Bits.mask (bitOffset bit)
  { words := set.words.set! wi word }

/-- 删除 bit。 -/
def erase (set : BitSet) (bit : Nat) : BitSet :=
  let wi := wordIndex bit
  if wi < set.words.size then
    let word := set.words[wi]! &&& UInt64.complement (UInt64Bits.mask (bitOffset bit))
    { words := set.words.set! wi word }
  else
    set

/-- 翻转 bit。 -/
def toggle (set : BitSet) (bit : Nat) : BitSet :=
  if set.test bit then set.erase bit else set.insert bit

/-- 由自然数数组构造位集。 -/
def ofArray (bits : Array Nat) : BitSet :=
  bits.foldl (fun set bit => set.insert bit) empty

/-- 两个位集逐 word 合并。 -/
def union (left : @& BitSet) (right : @& BitSet) : BitSet := Id.run do
  let size := Nat.max left.words.size right.words.size
  let mut out := #[]
  for i in [:size] do
    out := out.push (left.words.getD i 0 ||| right.words.getD i 0)
  return { words := out }

/-- 两个位集求交。 -/
def inter (left : @& BitSet) (right : @& BitSet) : BitSet := Id.run do
  let size := Nat.min left.words.size right.words.size
  let mut out := #[]
  for i in [:size] do
    out := out.push (left.words.getD i 0 &&& right.words.getD i 0)
  return { words := out }

/-- 从 `left` 中去掉 `right`。 -/
def diff (left : @& BitSet) (right : @& BitSet) : BitSet := Id.run do
  let mut out := #[]
  for i in [:left.words.size] do
    out := out.push (left.words[i]! &&& UInt64.complement (right.words.getD i 0))
  return { words := out }

/-- 位集是否为空。 -/
def isEmpty (set : @& BitSet) : Bool :=
  set.words.all (fun word => word == 0)

/-- 两个位集是否有交。 -/
def intersects (left : @& BitSet) (right : @& BitSet) : Bool := Id.run do
  let size := Nat.min left.words.size right.words.size
  for i in [:size] do
    if (left.words[i]! &&& right.words[i]!) != 0 then
      return true
  return false

/-- 两个位集是否不相交。 -/
def disjoint (left : @& BitSet) (right : @& BitSet) : Bool :=
  !left.intersects right

/-- `left ⊆ right` 的可计算预筛。 -/
def subset (left : @& BitSet) (right : @& BitSet) : Bool := Id.run do
  for i in [:left.words.size] do
    if (left.words[i]! &&& UInt64.complement (right.words.getD i 0)) != 0 then
      return false
  return true

/-- 统计置位数量。 -/
def popcount (set : @& BitSet) : Nat :=
  set.words.foldl (fun acc word => acc + UInt64Bits.popcount word) 0

/-- 从 `start` 开始找下一个置位。 -/
def nextSetBit? (set : @& BitSet) (start : Nat := 0) : Option Nat := Id.run do
  let startWord := wordIndex start
  if startWord >= set.words.size then
    return none
  let first := set.words[startWord]! &&& UInt64Bits.suffixMask (bitOffset start)
  if first != 0 then
    return some (startWord * UInt64Bits.wordBits + UInt64Bits.trailingZeros first)
  for wordIndex in [startWord + 1:set.words.size] do
    let word := set.words[wordIndex]!
    if word != 0 then
      return some (wordIndex * UInt64Bits.wordBits + UInt64Bits.trailingZeros word)
  return none

/-- 对每个置位执行折叠。 -/
def foldSetBits (set : @& BitSet) (init : β) (f : β → Nat → β) : β := Id.run do
  let mut acc := init
  for wordIndex in [:set.words.size] do
    let mut word := set.words[wordIndex]!
    while word != 0 do
      let offset := UInt64Bits.trailingZeros word
      acc := f acc (wordIndex * UInt64Bits.wordBits + offset)
      word := word &&& (word - 1)
  return acc

/-!
## ST builder

`Builder` 是饱和循环和 CDCL 传播应使用的入口。它只保存 `ST.Ref σ (Array UInt64)`；
更新函数全部通过 `ST.Ref.modify` 执行，避免把整个 `BitSet` 状态存入 trace 或闭包后
继续 `set!` 导致 RC 升高。
-/

/-- ST 内的可变 bitset builder。 -/
structure Builder (σ : Type) where
  words : MutArray σ UInt64

namespace Builder

/-- 从冻结位集创建 builder。 -/
def ofBitSet {σ : Type} (initial : BitSet := BitSet.empty) : ST σ (Builder σ) := do
  let words ← MutArray.mk (σ := σ) initial.words
  return { words := words }

/-- 创建空 builder。 -/
def empty {σ : Type} : ST σ (Builder σ) :=
  ofBitSet BitSet.empty

/-- 冻结为普通 `BitSet`。冻结结果只应在热循环结束后长期保存。 -/
def freeze {σ : Type} (builder : Builder σ) : ST σ BitSet := do
  let words ← builder.words.freeze
  return { words := words }

private def insertWord (words : Array UInt64) (bit : Nat) : Array UInt64 :=
  let wi := wordIndex bit
  let words := ensureArraySize words (wi + 1) 0
  let word := words[wi]! ||| UInt64Bits.mask (bitOffset bit)
  words.set! wi word

private def eraseWord (words : Array UInt64) (bit : Nat) : Array UInt64 :=
  let wi := wordIndex bit
  if wi < words.size then
    let word := words[wi]! &&& UInt64.complement (UInt64Bits.mask (bitOffset bit))
    words.set! wi word
  else
    words

private def toggleWord (words : Array UInt64) (bit : Nat) : Array UInt64 :=
  let wi := wordIndex bit
  let words := ensureArraySize words (wi + 1) 0
  let mask := UInt64Bits.mask (bitOffset bit)
  let word := words[wi]! ^^^ mask
  words.set! wi word

/-- 原地风格加入 bit。 -/
def insert {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Unit :=
  builder.words.modify (fun words => insertWord words bit)

/-- 原地风格删除 bit。 -/
def erase {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Unit :=
  builder.words.modify (fun words => eraseWord words bit)

/-- 原地风格翻转 bit。 -/
def toggle {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Unit :=
  builder.words.modify (fun words => toggleWord words bit)

/-- 只读测试 builder 当前状态。不要在返回数组快照后继续保存它。 -/
def test {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Bool := do
  let wi := wordIndex bit
  if wi < (← builder.words.size) then
    return ((← builder.words.get! wi) &&& UInt64Bits.mask (bitOffset bit)) != 0
  return false

/-- 原地风格并入一个冻结 bitset。 -/
def unionInto {σ : Type} (builder : Builder σ) (other : @& BitSet) : ST σ Unit :=
  builder.words.modify fun words => Id.run do
    let size := Nat.max words.size other.words.size
    let mut out := ensureArraySize words size 0
    for i in [:size] do
      out := out.set! i (out.getD i 0 ||| other.words.getD i 0)
    return out

/-- 原地风格求交；超出 `other` 的 word 直接清零。 -/
def intersectWith {σ : Type} (builder : Builder σ) (other : @& BitSet) : ST σ Unit :=
  builder.words.modify fun words => Id.run do
    let mut out := words
    for i in [:out.size] do
      out := out.set! i (out.getD i 0 &&& other.words.getD i 0)
    return out

/-- 原地风格差集。 -/
def diffWith {σ : Type} (builder : Builder σ) (other : @& BitSet) : ST σ Unit :=
  builder.words.modify fun words => Id.run do
    let mut out := words
    for i in [:out.size] do
      out := out.set! i (out.getD i 0 &&& UInt64.complement (other.words.getD i 0))
    return out

/-- 原地风格清空。 -/
def clear {σ : Type} (builder : Builder σ) : ST σ Unit :=
  builder.words.clear

end Builder

end BitSet

end Data
end Automation
end YesMetaZFC
