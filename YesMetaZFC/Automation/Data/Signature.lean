import Lean
import YesMetaZFC.Automation.Data.BitSet

/-!
# ATP signatures

签名是低成本的必要条件过滤器：subsumption、resolution、rewrite 候选都可以先用位集
快速拒绝，再进入昂贵的结构检查或合一。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 固定宽度的哈希签名。 -/
structure Signature where
  width : Nat := 256
  bits : BitSet := BitSet.empty
  deriving Repr, BEq, Inhabited

namespace Signature

/-- 空签名。 -/
def empty (width : Nat := 256) : Signature :=
  { width := width }

/-- 把任意自然数压入签名。 -/
def insertNat (sig : Signature) (value : Nat) : Signature :=
  { sig with bits := sig.bits.insert (slotOfHash sig.width value) }

/-- 把可哈希对象压入签名。 -/
def insertHash [Hashable α] (sig : Signature) (value : α) : Signature :=
  sig.insertNat (hashNat value)

/-- 从自然数数组构造签名。 -/
def ofNats (width : Nat) (values : Array Nat) : Signature :=
  values.foldl (fun sig value => sig.insertNat value) (empty width)

/-- 合并两个签名，宽度取较大者。 -/
def union (left right : Signature) : Signature :=
  { width := Nat.max left.width right.width, bits := left.bits.union right.bits }

/-- 是否可能满足 `left ⊆ right`。 -/
def subset (left right : Signature) : Bool :=
  left.bits.subset right.bits

/-- 是否可能有公共特征。 -/
def overlaps (left right : Signature) : Bool :=
  left.bits.intersects right.bits

/-- subsumption 的必要条件：subsumer 的签名必须包含在 target 中。 -/
def maySubsume (subsumer target : Signature) : Bool :=
  subsumer.subset target

/-- resolution/superposition 这类候选的廉价重叠测试。 -/
def mayInteract (left right : Signature) : Bool :=
  left.overlaps right

end Signature

/-- ST 生命周期内可变的动态签名。 -/
structure Signature.Builder (σ : Type) where
  width : Nat
  bits : BitSet.Builder σ

namespace Signature.Builder

/-- 从冻结签名创建 builder。 -/
def ofSignature {σ : Type} (signature : Signature := Signature.empty) :
    ST σ (Signature.Builder σ) := do
  return {
    width := signature.width
    bits := ← BitSet.Builder.ofBitSet signature.bits
  }

/-- 创建指定宽度的空签名。 -/
def empty {σ : Type} (width : Nat := 256) : ST σ (Signature.Builder σ) :=
  ofSignature (Signature.empty width)

/-- 插入自然数特征。 -/
@[inline]
def insertNat {σ : Type} (builder : Signature.Builder σ) (value : Nat) : ST σ Unit :=
  builder.bits.insert (slotOfHash builder.width value)

/-- 插入可哈希特征。 -/
@[inline]
def insertHash {σ : Type} [Hashable α] (builder : Signature.Builder σ) (value : α) :
    ST σ Unit :=
  builder.insertNat (hashNat value)

/-- 清空签名并保留 bitset 容量。 -/
def clear {σ : Type} (builder : Signature.Builder σ) : ST σ Unit :=
  builder.bits.clear

/-- 冻结签名。调用后不应继续修改 builder。 -/
def freeze {σ : Type} (builder : Signature.Builder σ) : ST σ Signature := do
  return { width := builder.width, bits := ← builder.bits.freeze }

end Signature.Builder

/-!
## 固定 256 位签名

subsumption 与 term feature 预筛通常使用固定宽度。四个机器字直接放在结构中，不再让
每条 clause 持有独立的动态 `Array UInt64`。
-/

/-- 无嵌套 RC 容器的 256 位签名。 -/
structure Signature256 where
  word0 : UInt64 := 0
  word1 : UInt64 := 0
  word2 : UInt64 := 0
  word3 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Inhabited, Lean.ToExpr

namespace Signature256

/-- 空签名。 -/
def empty : Signature256 := {}

/-- 插入已经混合过的自然数特征。 -/
def insertNat (signature : Signature256) (value : Nat) : Signature256 :=
  let slot := slotOfHash 256 value
  let mask := UInt64Bits.mask slot
  match slot / 64 with
  | 0 => { signature with word0 := signature.word0 ||| mask }
  | 1 => { signature with word1 := signature.word1 ||| mask }
  | 2 => { signature with word2 := signature.word2 ||| mask }
  | _ => { signature with word3 := signature.word3 ||| mask }

/-- 插入可哈希特征。 -/
@[inline]
def insertHash [Hashable α] (signature : Signature256) (value : α) : Signature256 :=
  signature.insertNat (hashNat value)

/-- 合并两个签名。 -/
def union (left right : Signature256) : Signature256 := {
  word0 := left.word0 ||| right.word0
  word1 := left.word1 ||| right.word1
  word2 := left.word2 ||| right.word2
  word3 := left.word3 ||| right.word3
}

/-- `left ⊆ right` 的必要条件检查。 -/
def subset (left right : Signature256) : Bool :=
  (left.word0 &&& UInt64.complement right.word0) == 0 &&
    (left.word1 &&& UInt64.complement right.word1) == 0 &&
      (left.word2 &&& UInt64.complement right.word2) == 0 &&
        (left.word3 &&& UInt64.complement right.word3) == 0

/-- 两个签名是否共享至少一个特征位。 -/
def overlaps (left right : Signature256) : Bool :=
  (left.word0 &&& right.word0) != 0 ||
    (left.word1 &&& right.word1) != 0 ||
      (left.word2 &&& right.word2) != 0 ||
        (left.word3 &&& right.word3) != 0

/-- subsumption 的必要条件。 -/
@[inline]
def maySubsume (subsumer target : Signature256) : Bool :=
  subsumer.subset target

/-- resolution/superposition 的低成本交互预筛。 -/
@[inline]
def mayInteract (left right : Signature256) : Bool :=
  left.overlaps right

end Signature256

end Data
end Automation
end YesMetaZFC
