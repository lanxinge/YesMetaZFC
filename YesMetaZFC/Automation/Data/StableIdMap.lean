import YesMetaZFC.Automation.Data.Util

/-!
# 稳定编号表

为 arena 或证明 DAG 的稳定自然数编号提供直接寻址表。缺失槽位保存 `none`；按编号追加时
保持底层数组的独占更新路径，稀疏编号才补齐中间空槽。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 由稳定自然数编号直接索引的可选值表。 -/
structure StableIdMap (α : Type) where
  values : Array (Option α) := #[]
  deriving Repr, Inhabited

namespace StableIdMap

/-- 空表，并为预期编号范围预留容量。 -/
def emptyWithCapacity (capacity : Nat := 0) : StableIdMap α :=
  { values := Array.emptyWithCapacity capacity }

/-- 按稳定编号读取值。 -/
@[inline]
def get? (map : StableIdMap α) (id : Nat) : Option α :=
  (map.values[id]?).join

/-- 插入或更新稳定编号；连续编号走单次 `push`。 -/
def insert (map : StableIdMap α) (id : Nat) (value : α) : StableIdMap α :=
  if id == map.values.size then
    { values := map.values.push (some value) }
  else
    { values := setArrayD map.values id (some value) none }

end StableIdMap

end Data
end Automation
end YesMetaZFC
