import YesMetaZFC.Automation.Data.StableIdMap

/-!
# canonical SearchDAG seed 构造工作区

该工作区只保存稳定输入编号到 DAG 节点编号的直接寻址映射和 used 位图。DAG 节点、
字句与 payload 仍由材料化层持有；工作区不复制这些大型对象。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- canonical source/split/component seed 构造的 Data 层状态。 -/
structure CanonicalSeedWorkspace where
  sourceNodes : StableIdMap Nat := {}
  splitNodes : StableIdMap Nat := {}
  componentNodes : StableIdMap Nat := {}
  sourceUsed : ByteArray := ByteArray.empty
  splitUsed : ByteArray := ByteArray.empty
  componentUsed : ByteArray := ByteArray.empty
  deriving Inhabited

namespace CanonicalSeedWorkspace

private def usedAt (used : ByteArray) (id : Nat) : Bool :=
  used[id]? == some 1

private def markUsed (used : ByteArray) (id : Nat) : ByteArray :=
  (ensureByteArraySize used (id + 1) 0).set! id 1

/-- 按预期编号范围创建空工作区。 -/
def emptyWithCapacity (sourceCapacity splitCapacity componentCapacity : Nat := 0) :
    CanonicalSeedWorkspace :=
  {
    sourceNodes := StableIdMap.emptyWithCapacity sourceCapacity
    splitNodes := StableIdMap.emptyWithCapacity splitCapacity
    componentNodes := StableIdMap.emptyWithCapacity componentCapacity
    sourceUsed := ByteArray.emptyWithCapacity sourceCapacity
    splitUsed := ByteArray.emptyWithCapacity splitCapacity
    componentUsed := ByteArray.emptyWithCapacity componentCapacity
  }

@[inline]
def sourceNode? (workspace : CanonicalSeedWorkspace) (sourceIndex : Nat) : Option Nat :=
  workspace.sourceNodes.get? sourceIndex

@[inline]
def splitNode? (workspace : CanonicalSeedWorkspace) (splitIndex : Nat) : Option Nat :=
  workspace.splitNodes.get? splitIndex

@[inline]
def componentNode? (workspace : CanonicalSeedWorkspace) (componentId : Nat) : Option Nat :=
  workspace.componentNodes.get? componentId

@[inline]
def sourceIsUsed (workspace : CanonicalSeedWorkspace) (sourceIndex : Nat) : Bool :=
  usedAt workspace.sourceUsed sourceIndex

@[inline]
def splitIsUsed (workspace : CanonicalSeedWorkspace) (splitIndex : Nat) : Bool :=
  usedAt workspace.splitUsed splitIndex

@[inline]
def componentIsUsed (workspace : CanonicalSeedWorkspace) (componentId : Nat) : Bool :=
  usedAt workspace.componentUsed componentId

/-- 登记一个尚未使用的 source 编号。 -/
def registerSource? (workspace : CanonicalSeedWorkspace) (sourceIndex nodeId : Nat) :
    Option CanonicalSeedWorkspace :=
  if workspace.sourceIsUsed sourceIndex then
    none
  else
    some {
      workspace with
      sourceNodes := workspace.sourceNodes.insert sourceIndex nodeId
      sourceUsed := markUsed workspace.sourceUsed sourceIndex
    }

/-- 登记一个尚未使用的 split 编号。 -/
def registerSplit? (workspace : CanonicalSeedWorkspace) (splitIndex nodeId : Nat) :
    Option CanonicalSeedWorkspace :=
  if workspace.splitIsUsed splitIndex then
    none
  else
    some {
      workspace with
      splitNodes := workspace.splitNodes.insert splitIndex nodeId
      splitUsed := markUsed workspace.splitUsed splitIndex
    }

/-- 登记一个尚未使用的 interned component 编号。 -/
def registerComponent? (workspace : CanonicalSeedWorkspace) (componentId nodeId : Nat) :
    Option CanonicalSeedWorkspace :=
  if workspace.componentIsUsed componentId then
    none
  else
    some {
      workspace with
      componentNodes := workspace.componentNodes.insert componentId nodeId
      componentUsed := markUsed workspace.componentUsed componentId
    }

end CanonicalSeedWorkspace

end Data
end Automation
end YesMetaZFC
