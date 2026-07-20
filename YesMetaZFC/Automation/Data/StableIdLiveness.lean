import Lean
import YesMetaZFC.Automation.Data.Util

/-!
# 稳定编号存活位图

追加式 arena 和索引可以保留旧载荷，只在查询边界按稳定编号过滤删除项。该结构统一持有
紧凑 `ByteArray`，删除不触碰索引的平坦节点、边或 payload 数组。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

deriving instance Repr, Lean.ToExpr for ByteArray

/-- 与稳定编号对齐的紧凑删除位图；`1` 表示 tombstone，缺失或 `0` 表示 live。 -/
structure StableIdLiveness where
  states : ByteArray := ByteArray.empty
  tombstones : Nat := 0
  deriving Repr, Inhabited, BEq, Lean.ToExpr

namespace StableIdLiveness

/-- 指定稳定编号当前是否 live。未写入的编号默认没有被删除。 -/
@[inline]
def isLive (liveness : StableIdLiveness) (id : Nat) : Bool :=
  match liveness.states[id]? with
  | some state => state != 1
  | none => true

/-- 当前索引是否包含需要在查询时过滤的 tombstone。 -/
@[inline]
def hasTombstones (liveness : StableIdLiveness) : Bool :=
  liveness.tombstones != 0

/-- 索引 occurrence 的热路径读取；新追加编号可以自然位于当前位图范围之外。 -/
@[inline]
def isLive! (liveness : StableIdLiveness) (id : Nat) : Bool :=
  id >= liveness.states.size || liveness.states.get! id != 1

/-- 标记一个已经进入过索引的稳定编号为 tombstone。 -/
@[inline]
def delete (liveness : StableIdLiveness) (id : Nat) : StableIdLiveness :=
  if liveness.isLive id then
    { states := setByteArrayD liveness.states id 1 0
      tombstones := liveness.tombstones + 1 }
  else
    liveness

/-- 顺序应用一组稳定删除；热位图始终由本地 `mut` 独占持有。 -/
def deleteMany (liveness : StableIdLiveness) (ids : Array Nat) : StableIdLiveness :=
  Id.run do
    let mut liveness := liveness
    for id in ids do
      liveness := liveness.delete id
    return liveness

end StableIdLiveness

end Data
end Automation
end YesMetaZFC
