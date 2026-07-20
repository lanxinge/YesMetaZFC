import Lean
import YesMetaZFC.Automation.Data.StableIdLiveness
import YesMetaZFC.Automation.Data.Util

/-!
# 稳定编号注册表

追加式 arena 可以用一张紧凑位图记录某个稳定编号是否已经完成一次性登记。该结构不处理
删除；永久删除仍由 `StableIdLiveness` 独立维护。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- 与稳定编号对齐的一次性注册位图；`1` 表示已经登记。 -/
structure StableIdRegistry where
  states : ByteArray := ByteArray.empty
  count : Nat := 0
  deriving Repr, Inhabited, BEq, Lean.ToExpr

namespace StableIdRegistry

/-- 指定稳定编号是否已经登记。 -/
@[inline]
def contains (registry : StableIdRegistry) (id : Nat) : Bool :=
  id < registry.states.size && registry.states.get! id == 1

/-- 登记一个稳定编号；重复登记保持原结构。 -/
@[inline]
def insert (registry : StableIdRegistry) (id : Nat) : StableIdRegistry :=
  if registry.contains id then
    registry
  else
    {
      states := setByteArrayD registry.states id 1 0
      count := registry.count + 1
    }

end StableIdRegistry

end Data
end Automation
end YesMetaZFC
