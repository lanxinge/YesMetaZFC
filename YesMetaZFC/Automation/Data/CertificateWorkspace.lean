import YesMetaZFC.Automation.Data.StableIdRegistry

/-!
# 证书材料化工作区

证书冷路径需要同时维护稳定父节点集合、residual-CDCL feature 数组和最终节点构造状态。
这些数组统一放在 Data 层，调用方只负责把具体 payload 类型实例化到通用工作区中。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/-- residual-CDCL feature 构造使用的单次函数式工作区。 -/
structure ResidualCdclWorkspace
    (Atom Parent InitialFeature AvatarFeature LearnedFeature GuardFeature : Type) where
  atoms : Array Atom := #[]
  initialIndex : Nat := 0
  parentRegistry : StableIdRegistry := {}
  parents : Array Parent := #[]
  initialFeatures : Array InitialFeature := #[]
  avatarFeatures : Array AvatarFeature := #[]
  learnedFeatures : Array LearnedFeature := #[]
  guardFeatures : Array GuardFeature := #[]

namespace ResidualCdclWorkspace

variable {Atom Parent Initial Avatar Learned Guard : Type}

/-- 只更新对象原子表；不产生新的 initial feature。 -/
def setAtoms
    (workspace : ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard)
    (atoms : Array Atom) :
    ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard :=
  { workspace with atoms := atoms }

/-- 按稳定父节点编号登记一次父边，保持首次出现顺序。 -/
private def addParent
    (workspace : ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard)
    (parentId : Nat) (parent : Parent) :
    ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard :=
  if workspace.parentRegistry.contains parentId then
    workspace
  else
    {
      workspace with
      parentRegistry := workspace.parentRegistry.insert parentId
      parents := workspace.parents.push parent
    }

/-- 加入普通对象 initial feature。 -/
def pushInitial
    (workspace : ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard)
    (parentId : Nat) (parent : Parent) (atoms : Array Atom) (feature : Initial) :
    ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard :=
  let workspace := workspace.addParent parentId parent
  {
    workspace with
    atoms := atoms
    initialIndex := workspace.initialIndex + 1
    initialFeatures := workspace.initialFeatures.push feature
  }

/-- 加入 AVATAR selector skeleton feature。 -/
def pushAvatar
    (workspace : ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard)
    (parentId : Nat) (parent : Parent) (feature : Avatar) :
    ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard :=
  let workspace := workspace.addParent parentId parent
  {
    workspace with
    initialIndex := workspace.initialIndex + 1
    avatarFeatures := workspace.avatarFeatures.push feature
  }

/-- 加入 theory-conflict learned feature。 -/
def pushLearned
    (workspace : ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard)
    (parentId : Nat) (parent : Parent) (feature : Learned) :
    ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard :=
  let workspace := workspace.addParent parentId parent
  {
    workspace with
    initialIndex := workspace.initialIndex + 1
    learnedFeatures := workspace.learnedFeatures.push feature
  }

/-- 加入 guarded activation feature。 -/
def pushGuard
    (workspace : ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard)
    (parentId : Nat) (parent : Parent) (atoms : Array Atom) (feature : Guard) :
    ResidualCdclWorkspace Atom Parent Initial Avatar Learned Guard :=
  let workspace := workspace.addParent parentId parent
  {
    workspace with
    atoms := atoms
    initialIndex := workspace.initialIndex + 1
    guardFeatures := workspace.guardFeatures.push feature
  }

end ResidualCdclWorkspace

/--
AVATAR certificate 单次材料化工作区。

`Certificate` 与 `Dag` 保持高层类型不透明；Data 层只负责统一持有一次检查结果、proof
切片和节点数组，避免调用层把同一批大数组拆散到多个并存局部结构中。
-/
structure CertificateMaterializationWorkspace
    (Certificate Dag ArenaMap Node : Type) where
  certificate : Certificate
  dag : Dag
  arenaToSearch : ArenaMap
  splitNodes : Array Node
  conflictProofNodes : Array Node
  theoryConflictNodes : Array Node := #[]
  learnedClauseNodes : Array Node := #[]

namespace CertificateMaterializationWorkspace

variable {Certificate Dag ArenaMap Node : Type}

/-- 更新正在构造的 SearchDAG。 -/
def setDag
    (workspace : CertificateMaterializationWorkspace Certificate Dag ArenaMap Node)
    (dag : Dag) :
    CertificateMaterializationWorkspace Certificate Dag ArenaMap Node :=
  { workspace with dag := dag }

/-- 追加一个 theory-conflict 节点。 -/
def pushTheoryConflict
    (workspace : CertificateMaterializationWorkspace Certificate Dag ArenaMap Node)
    (node : Node) :
    CertificateMaterializationWorkspace Certificate Dag ArenaMap Node :=
  { workspace with theoryConflictNodes := workspace.theoryConflictNodes.push node }

/-- 追加一个 propositional learned-clause 节点。 -/
def pushLearnedClause
    (workspace : CertificateMaterializationWorkspace Certificate Dag ArenaMap Node)
    (node : Node) :
    CertificateMaterializationWorkspace Certificate Dag ArenaMap Node :=
  { workspace with learnedClauseNodes := workspace.learnedClauseNodes.push node }

/-- 按 residual CDCL initial 顺序组装 source 节点。 -/
def sources
    (workspace : CertificateMaterializationWorkspace Certificate Dag ArenaMap Node) :
    Array Node :=
  workspace.splitNodes ++ workspace.learnedClauseNodes

end CertificateMaterializationWorkspace

end Data
end Automation
end YesMetaZFC
