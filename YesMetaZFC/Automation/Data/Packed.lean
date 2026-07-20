import YesMetaZFC.Automation.Data.Util

/-!
# Packed handles

底层搜索结构统一用小型 handle 互相引用。`Id tag` 是一层类型标签，运行时只保存
`Nat`，但不同用途的 id 不会在 Lean 类型层被误混。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 类型标签化的紧凑 id。`0` 约定为 invalid，其余值可作为 1-based handle。 -/
@[unbox]
structure Id (tag : Type u) where
  raw : Nat := 0

namespace Id

/-- handle 的可读表示。显式实例保证跨模块导入时可见。 -/
instance {tag : Type u} : Repr (Id tag) where
  reprPrec id precedence := reprPrec id.raw precedence

/-- handle 的布尔相等只比较底层自然数。 -/
instance {tag : Type u} : BEq (Id tag) where
  beq left right := left.raw == right.raw

/-- handle 的可判定相等只比较底层自然数。 -/
instance {tag : Type u} : DecidableEq (Id tag)
  | ⟨left⟩, ⟨right⟩ =>
      if h : left = right then
        isTrue (by cases h; rfl)
      else
        isFalse fun hId => by
          cases hId
          exact h rfl

instance {tag : Type u} : Inhabited (Id tag) where
  default := ⟨0⟩

instance {tag : Type u} : Hashable (Id tag) where
  hash id := Hashable.hash id.raw

/-- 无效 handle。 -/
def invalid {tag : Type u} : Id tag := ⟨0⟩

/-- 从原始自然数构造 handle。 -/
def ofNat {tag : Type u} (n : Nat) : Id tag := ⟨n⟩

/-- 提取原始自然数。 -/
def toNat {tag : Type u} (id : Id tag) : Nat := id.raw

/-- handle 是否有效。 -/
def isValid {tag : Type u} (id : Id tag) : Bool := id.raw != 0

/-- 下一个 handle。 -/
def succ {tag : Type u} (id : Id tag) : Id tag := ⟨id.raw + 1⟩

/-- 1-based handle 对应的 0-based 数组位置。 -/
def index? {tag : Type u} (id : Id tag) : Option Nat :=
  match id.raw with
  | 0 => none
  | n + 1 => some n

/-- 从 0-based 数组位置生成 1-based handle。 -/
def ofIndex {tag : Type u} (index : Nat) : Id tag := ⟨index + 1⟩

/-- handle 的稳定排序键。 -/
def less {tag : Type u} (left right : Id tag) : Bool := left.raw < right.raw

end Id

/-- 常用 handle 标签。 -/
inductive ClauseTag
inductive LiteralTag
inductive TermTag
inductive VarTag
inductive NodeTag

abbrev ClauseId := Id ClauseTag
abbrev LiteralId := Id LiteralTag
abbrev TermId := Id TermTag
abbrev PackedVarId := Id VarTag
abbrev NodeId := Id NodeTag

/-- SAT/ATP 常用 literal 槽位编码：负文字偶数槽，正文字奇数槽。 -/
def literalSlot (var : Nat) (positive : Bool) : Nat :=
  2 * var + if positive then 1 else 0

/-- literal 槽位取反。 -/
def negLiteralSlot (slot : Nat) : Nat :=
  if slot % 2 == 0 then slot + 1 else slot - 1

/-- 从 literal 槽位还原变量编号与极性。 -/
def decodeLiteralSlot (slot : Nat) : Nat × Bool :=
  (slot / 2, slot % 2 == 1)

/-- 给二元 key 做无分配组合，适合 root/predicate/side 这类小型键。 -/
def pairKey (left right : Nat) : Nat :=
  left * 1315423911 + right + 2654435761

end Data
end Automation
end YesMetaZFC
