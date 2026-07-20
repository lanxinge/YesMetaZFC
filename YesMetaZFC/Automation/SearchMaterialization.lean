import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.CoreNormalForm.CheckedPreprocessing
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.DAGCertificate
import YesMetaZFC.Automation.AvatarRegistrySoundness
import YesMetaZFC.Automation.ResourceTrace
import YesMetaZFC.Automation.Data.StableIdMap
import YesMetaZFC.Automation.Data.CertificateWorkspace

/-!
# 搜索器到新 DAG 的材料化层

本模块定义一个轻量 search-DAG 输入协议，并把它材料化为
`Automation.DAGCertificate` 的 `Type 0` 可计算 DAG。它刻意不 import 旧 LCF replay/MF1
模块；旧搜索器只需要把自己的 `ProverState` 投影到这里的 `SearchDAG` 数据结构即可。

设计边界：

* `SearchDAG` 持有 canonical initial-clause table；source 只能引用其中的唯一索引；
* 材料化前会完整核对 search table 与 `ClauseProblem.initialClauses`，不从 source 切片猜来源；
* AVATAR guard 会材料化进 DAG 节点；全局 selector registry checker 负责闭合其语义；
* residual CDCL 会重建普通对象父字句、AVATAR selector skeleton、theory-conflict learned
  clause 与 guard activation 四类 initial 链接；
* selector skeleton 通过 fixed-bound-stack AVATAR 拓扑定理进入专用 soundness 出口；
* 带 substitution 的一阶规则会材料化成 substituted local evidence；这些 evidence 已经可计算
  检查 result clause，但在 substitution soundness 引理补齐前不进入 soundness-supported 片段；
-/

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization

universe x

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Automation.LogicSoundness

abbrev SearchTerm := CoreSyntax.Search.Term
abbrev SearchLiteral := CoreSyntax.Search.Literal
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev SearchFunc := CoreSyntax.Search.FunctionSymbol
abbrev SearchSort := CoreSyntax.CoreSort
abbrev Substitution := CoreSyntax.Search.Substitution
abbrev NodeId := Nat

/-! ## 轻量 search-DAG 输入协议 -/

/-- 对一个旧搜索节点的稳定引用。`clause?` 可保存自包含父字句快照。 -/
structure ClauseRef where
  id : NodeId
  clause? : Option SearchClause := none
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 单个父字句的 standardize-apart 元数据。 -/
structure StandardizeApartSideMetadata where
  original : SearchClause
  offset : Nat := 0
  renamed : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/--
二元规则的 standardize-apart 元数据。

resolution 中 `left/right` 表示左右父字句；rewrite/superposition 中表示
`equality/target` 父字句。
-/
structure StandardizeApartMetadata where
  left : StandardizeApartSideMetadata
  right : StandardizeApartSideMetadata
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- DAG 中父字句的稳定引用。 -/
structure ProofParent where
  id : NodeId
  clause : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- AVATAR/CDCL 侧的 guard literal。 -/
abbrev GuardLit := PropResolution.Lit

/-- 规范化 guard 集。语义上作为合取使用，表示当前对象字句激活所需的 CDCL 假设。 -/
abbrev GuardSet := PropResolution.Clause

/-- guard 集的规范形式。复用命题字句的稳定排序/去重，作为 conjunction-set 编码。 -/
def canonicalGuards (guards : GuardSet) : GuardSet :=
  PropResolution.canonicalClause guards

/-- 合并两个 guard 集。 -/
def mergeGuards (left right : GuardSet) : GuardSet :=
  canonicalGuards (left ++ right)

/-- guard 集结构相等。 -/
def guardSetEq (left right : GuardSet) : Bool :=
  PropResolution.clauseEq (canonicalGuards left) (canonicalGuards right)

/-- 搜索核内部的 guarded clause。空 guard 退化成普通一阶字句。 -/
structure GuardedClause where
  guards : GuardSet := #[]
  clause : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

namespace GuardedClause

/-- 裸 clause 视为无 guard 的 guarded clause。 -/
def plain (clause : SearchClause) : GuardedClause :=
  { guards := #[], clause := clause }

/-- guard 集是否为空。 -/
def unguarded (gclause : GuardedClause) : Bool :=
  gclause.guards.isEmpty

/-- guarded clause 是否为空对象字句且没有 guard，可作为全局 refutation root。 -/
def globallyEmpty (gclause : GuardedClause) : Bool :=
  gclause.unguarded && gclause.clause.isEmpty

/-- guarded clause 是否是 AVATAR theory conflict：在某组 guard 下推出对象空字句。 -/
def theoryConflict (gclause : GuardedClause) : Bool :=
  !gclause.unguarded && gclause.clause.isEmpty

/-- guarded clause 的结构比较。 -/
def eq (left right : GuardedClause) : Bool :=
  guardSetEq left.guards right.guards &&
    CoreSyntax.Search.clauseEq left.clause right.clause

end GuardedClause

/-- source 节点显式引用原生初始字句。 -/
structure SourcePayload where
  initialIndex : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- AVATAR source split descriptor；完整 partition 与 selector 表只保存一次。 -/
structure AvatarSplitPayload where
  source : ProofParent
  partitions : Array (Array Nat)
  selectors : PropResolution.Clause
  note : String := ""
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- AVATAR component 只引用 split descriptor 与局部 component 索引。 -/
structure AvatarComponentPayload where
  split : ProofParent
  componentIndex : Nat
  note : String := ""
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 一元规则族。 -/
inductive UnaryKind where
  | ordinaryFactoring
  | equalityFactoring
  | equalityResolution
  | booleanExtensionality
  | argumentCongruence
  | functionExtensionality
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 重写/叠加规则族。 -/
inductive RewriteKind where
  | demodulation
  | contextualDemodulation
  | positiveSuperposition
  | negativeSuperposition
  | extensionalParamodulation
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 子项路径。空路径表示整个项。 -/
abbrev TermPath := List Nat

/-- 文字中的左右项位置。 -/
inductive LiteralSide where
  | left
  | right
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 带位置的子项。 -/
structure PositionedTerm where
  side : LiteralSide
  path : TermPath
  term : SearchTerm
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 一元规则的局部 witness。 -/
structure UnaryResource where
  kind : UnaryKind
  parent : ClauseRef
  literalIndex? : Option Nat := none
  otherLiteralIndex? : Option Nat := none
  substitution : Substitution := []
  result : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 二元 resolution 的局部 witness。 -/
structure ResolutionResource where
  left : ClauseRef
  right : ClauseRef
  leftLiteralIndex? : Option Nat := none
  rightLiteralIndex? : Option Nat := none
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : SearchClause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 重写/叠加使用到的等词与目标位置资源。 -/
structure RewriteResource where
  kind : RewriteKind
  equality : ClauseRef
  target : ClauseRef
  equalityLiteral : Nat
  targetLiteral : Nat
  targetPosition : PositionedTerm
  orientedLhs : SearchTerm
  orientedRhs : SearchTerm
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : SearchClause
  contextual : Bool := false
  deriving Repr, BEq, Lean.ToExpr

/-- 一个新增 clause 的局部推导 witness。 -/
inductive LocalStepWitness where
  | unary (resource : UnaryResource)
  | resolution (resource : ResolutionResource)
  | rewrite (resource : RewriteResource)
  deriving Repr, BEq, Lean.ToExpr

namespace LocalStepWitness

/-- witness 记录的父节点引用。 -/
def parents : LocalStepWitness → Array ClauseRef
  | unary resource => #[resource.parent]
  | resolution resource => #[resource.left, resource.right]
  | rewrite resource => #[resource.equality, resource.target]

/-- witness 记录的结果 clause。 -/
def result : LocalStepWitness → SearchClause
  | unary resource => resource.result
  | resolution resource => resource.result
  | rewrite resource => resource.result

/-- witness 结果是否和入库字句一致。 -/
def resultMatches (witness : LocalStepWitness) (clause : SearchClause) : Bool :=
  CoreSyntax.Search.clauseEq witness.result clause

end LocalStepWitness

/-! ### ResourceTrace 原生适配

搜索器内部只记录轻量资源轨迹；进入可信边界前统一转换为本模块的 search-DAG
witness。这里仍然只是纯数据搬运，具体规则合法性由后续 DAG checker 复算。
-/

/-- 资源轨迹中的父引用转换为 search-DAG 父引用。 -/
def clauseRefOfResource (ref : ResourceTrace.ClauseRef) : ClauseRef :=
  { id := ref.id, clause? := ref.clause? }

/-- standardize-apart 单侧元数据转换。 -/
def standardizeApartSideMetadataOfResource
    (metadata : ResourceTrace.StandardizeApartSideMetadata) :
    StandardizeApartSideMetadata := {
  original := metadata.original
  offset := metadata.offset
  renamed := metadata.renamed
}

/-- standardize-apart 二元元数据转换。 -/
def standardizeApartMetadataOfResource
    (metadata : ResourceTrace.StandardizeApartMetadata) :
    StandardizeApartMetadata := {
  left := standardizeApartSideMetadataOfResource metadata.left
  right := standardizeApartSideMetadataOfResource metadata.right
}

/-- 资源轨迹一元规则族转换。 -/
def unaryKindOfResource : ResourceTrace.UnaryKind → UnaryKind
  | .ordinaryFactoring => .ordinaryFactoring
  | .equalityFactoring => .equalityFactoring
  | .equalityResolution => .equalityResolution
  | .booleanExtensionality => .booleanExtensionality
  | .argumentCongruence => .argumentCongruence
  | .functionExtensionality => .functionExtensionality

/-- 资源轨迹重写/叠加规则族转换。 -/
def rewriteKindOfResource : ResourceTrace.RewriteKind → RewriteKind
  | .demodulation => .demodulation
  | .contextualDemodulation => .contextualDemodulation
  | .positiveSuperposition => .positiveSuperposition
  | .negativeSuperposition => .negativeSuperposition
  | .extensionalParamodulation => .extensionalParamodulation

/-- 资源轨迹中的 literal side 转换。 -/
def literalSideOfResource : ResourceTrace.LiteralSide → LiteralSide
  | .left => .left
  | .right => .right

/-- 资源轨迹中的定位子项转换。 -/
def positionedTermOfResource (position : ResourceTrace.PositionedTerm) :
    PositionedTerm := {
  side := literalSideOfResource position.side
  path := position.path
  term := position.term
}

/-- 资源轨迹一元 witness 转换。 -/
def unaryResourceOfTrace (resource : ResourceTrace.UnaryResource) :
    UnaryResource := {
  kind := unaryKindOfResource resource.kind
  parent := clauseRefOfResource resource.parent
  literalIndex? := resource.literalIndex?
  otherLiteralIndex? := resource.otherLiteralIndex?
  substitution := resource.substitution
  result := resource.result
}

/-- 资源轨迹 resolution witness 转换。 -/
def resolutionResourceOfTrace (resource : ResourceTrace.ResolutionResource) :
    ResolutionResource := {
  left := clauseRefOfResource resource.left
  right := clauseRefOfResource resource.right
  leftLiteralIndex? := resource.leftLiteralIndex?
  rightLiteralIndex? := resource.rightLiteralIndex?
  standardizeApart? := resource.standardizeApart?.map standardizeApartMetadataOfResource
  substitution := resource.substitution
  result := resource.result
}

/-- 资源轨迹重写/叠加 witness 转换。 -/
def rewriteResourceOfTrace (resource : ResourceTrace.RewriteResource) :
    RewriteResource := {
  kind := rewriteKindOfResource resource.kind
  equality := clauseRefOfResource resource.equality
  target := clauseRefOfResource resource.target
  equalityLiteral := resource.equalityLiteral
  targetLiteral := resource.targetLiteral
  targetPosition := positionedTermOfResource resource.targetPosition
  orientedLhs := resource.orientedLhs
  orientedRhs := resource.orientedRhs
  standardizeApart? := resource.standardizeApart?.map standardizeApartMetadataOfResource
  substitution := resource.substitution
  result := resource.result
  contextual := resource.contextual
}

/-- 资源轨迹本地 witness 转换为 search-DAG witness。 -/
def localStepWitnessOfResource :
    ResourceTrace.LocalStepWitness → LocalStepWitness
  | .unary resource => .unary (unaryResourceOfTrace resource)
  | .resolution resource => .resolution (resolutionResourceOfTrace resource)
  | .rewrite resource => .rewrite (rewriteResourceOfTrace resource)

/-- residual CDCL 命题化时，一条 initial prop clause 对应的原 DAG clause。 -/
structure CdclInitialFeature where
  initialIndex : Nat
  clauseId : NodeId
  sourceClause : SearchClause
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr

/-- residual CDCL initial prop clause 可以来自 theory-conflict learned clause 节点。 -/
structure CdclLearnedFeature where
  initialIndex : Nat
  learnedNode : NodeId
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr

/-- residual CDCL initial prop clause 可以来自 guarded activation clause。 -/
structure CdclGuardActivationFeature where
  initialIndex : Nat
  clauseId : NodeId
  sourceClause : SearchClause
  guards : GuardSet
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr

/-- residual CDCL initial prop clause 可以来自 AVATAR selector skeleton。 -/
structure CdclAvatarSkeletonFeature where
  initialIndex : Nat
  splitId : NodeId
  skeleton : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr

/-- residual CDCL 依赖到的 initial clause 切片。 -/
structure CdclResourceSummary where
  phase : String := ""
  initialFeatures : Array CdclInitialFeature := #[]
  avatarSkeletonFeatures : Array CdclAvatarSkeletonFeature := #[]
  learnedFeatures : Array CdclLearnedFeature := #[]
  guardActivationFeatures : Array CdclGuardActivationFeature := #[]
  objectAtomCount : Nat := 0
  usedInitialIndices : Array Nat := #[]
  journalSize : Nat := 0
  learnedClauses : Nat := 0
  resolutionSteps : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr

/-- residual CDCL 节点只携带 proof-free 搜索数据；最终 checker 在材料化后统一复算。 -/
structure ResidualCdclPayload where
  initialClauses : Array PropResolution.InitialClause
  proof : PropResolution.CdclProof
  summary : CdclResourceSummary
  deriving Repr, Lean.ToExpr

/-- 显式 theory-conflict 节点，表示父 guarded empty clause 的 `Γ ⟹ ⊥`。 -/
structure TheoryConflictPayload where
  conflict : ProofParent
  note : String := ""
  deriving Repr, Inhabited, Lean.ToExpr

/-- 由 theory-conflict 节点生成的 CDCL learned clause `¬Γ`。 -/
structure PropositionalLearnedClausePayload where
  conflict : NodeId
  learned : PropResolution.Clause
  note : String := ""
  deriving Repr, Inhabited, Lean.ToExpr

/-- 搜索节点 payload。 -/
inductive NodePayload where
  | source (payload : SourcePayload)
  | avatarSplit (payload : AvatarSplitPayload)
  | avatarComponent (payload : AvatarComponentPayload)
  | localStep (witness : LocalStepWitness)
  | theoryConflict (payload : TheoryConflictPayload)
  | propositionalLearnedClause (payload : PropositionalLearnedClausePayload)
  | residualCdcl (payload : ResidualCdclPayload)
  deriving Repr, Lean.ToExpr

namespace NodePayload

/-- payload 是否允许把无 guard 空对象字句登记为全局 refutation root。 -/
def rootClosureEligible : NodePayload → Bool
  | propositionalLearnedClause _ => false
  | _ => true

end NodePayload

/-- search-DAG 中的一条 clause。 -/
structure ClauseInfo where
  id : NodeId
  guards : GuardSet := #[]
  clause : SearchClause
  parents : Array ProofParent := #[]
  payload : NodePayload
  deriving Repr, Lean.ToExpr

namespace ClauseInfo

/-- 当前节点作为 guarded clause 的结论。 -/
def guarded (info : ClauseInfo) : GuardedClause :=
  { guards := info.guards, clause := info.clause }

/-- 转成后继节点使用的父字句快照。guard 由 DAG 中真实父节点读取，不重复放进父边。 -/
def toParent (info : ClauseInfo) : ProofParent :=
  { id := info.id, clause := info.clause }

/-- 当前节点是否是无 guard 的全局空字句。 -/
def globallyEmpty (info : ClauseInfo) : Bool :=
  info.guarded.globallyEmpty

/-- 当前节点是否是带 guard 的 theory conflict。 -/
def theoryConflict (info : ClauseInfo) : Bool :=
  info.guarded.theoryConflict

end ClauseInfo

/-- 搜索器输出的轻量 DAG 状态。 -/
structure SearchDAG where
  initialClauses : Array SearchClause := #[]
  clauses : Array ClauseInfo := #[]
  emptyClause? : Option NodeId := none
  deriving Repr, Lean.ToExpr

namespace SearchDAG

/-- 从固定的原生初始字句表建立空 search-DAG。 -/
def ofInitialClauses (initialClauses : Array SearchClause) : SearchDAG :=
  { initialClauses := initialClauses }

/-- 下一个 dense 节点编号。 -/
def nextId (dag : SearchDAG) : NodeId :=
  dag.clauses.size

/-- 按 id 取出 clause info。 -/
def get? (dag : SearchDAG) (id : NodeId) : Option ClauseInfo :=
  dag.clauses[id]?

/-- 加入一个 guarded clause 节点。 -/
def addClause (dag : SearchDAG) (gclause : GuardedClause)
    (parents : Array ProofParent) (payload : NodePayload) :
    SearchDAG × ClauseInfo :=
  let info : ClauseInfo := {
    id := dag.nextId
    guards := canonicalGuards gclause.guards
    clause := gclause.clause
    parents := parents
    payload := payload
  }
  let emptyClause? :=
    match dag.emptyClause? with
    | some id => some id
    | none =>
        if info.globallyEmpty && payload.rootClosureEligible then
          some info.id
        else
          none
  ({ dag with clauses := dag.clauses.push info, emptyClause? := emptyClause? }, info)

/-- 加入一个无 guard 的普通字句节点。 -/
def addPlainClause (dag : SearchDAG) (clause : SearchClause)
    (parents : Array ProofParent) (payload : NodePayload) :
    SearchDAG × ClauseInfo :=
  dag.addClause (GuardedClause.plain clause) parents payload

/-- 父节点必须存在、早于子节点，并且快照和入库字句一致。 -/
def parentOk (dag : SearchDAG) (childId : NodeId) (parent : ProofParent) : Bool :=
  parent.id < childId &&
    match dag.get? parent.id with
    | some info => CoreSyntax.Search.clauseEq info.clause parent.clause
    | none => false

/-- 取父节点的 guard 集。 -/
def parentGuards? (dag : SearchDAG) (parent : ProofParent) : Option GuardSet := do
  let info ← dag.get? parent.id
  if CoreSyntax.Search.clauseEq info.clause parent.clause then
    some info.guards
  else
    none

/-- 合并父节点 guard 集。 -/
def parentGuardUnion? (dag : SearchDAG) (parents : Array ProofParent) :
    Option GuardSet := do
  let mut guards : GuardSet := #[]
  for parent in parents do
    let parentGuards ← dag.parentGuards? parent
    guards := mergeGuards guards parentGuards
  some guards

/-- 本地叠加/消解规则的 guard 约束：结论 guard 必须正好是父 guard 合并。 -/
def localGuardsOk (dag : SearchDAG) (info : ClauseInfo) : Bool :=
  match dag.parentGuardUnion? info.parents with
  | some guards => guardSetEq info.guards guards
  | none => false

/-- 根据父节点 guard 和 witness 结果构造本地规则结论。 -/
def guardedLocalResult? (dag : SearchDAG) (parents : Array ProofParent)
    (witness : LocalStepWitness) : Option GuardedClause := do
  let guards ← dag.parentGuardUnion? parents
  some { guards := guards, clause := witness.result }

/-- 某个初始字句 slot 是否已经有 source 节点。 -/
def sourceIndexUsed (dag : SearchDAG) (initialIndex : Nat) : Bool :=
  dag.clauses.any fun info =>
    match info.payload with
    | .source payload => payload.initialIndex == initialIndex
    | _ => false

private def addSourceAt? (dag : SearchDAG) (guards : GuardSet) (initialIndex : Nat) :
    Option (SearchDAG × ClauseInfo) := do
  let initial ← dag.initialClauses[initialIndex]?
  some (dag.addClause { guards := guards, clause := initial } #[]
    (.source { initialIndex := initialIndex }))

/--
加入 source 节点。

调用者只提供 guard 与初始字句索引；对象字句必须从 search-DAG 自己持有的固定表读取，
因此无法在构造阶段伪造 source 快照。同一初始字句 slot 最多建立一个 source 节点。
-/
def addSource? (dag : SearchDAG) (guards : GuardSet) (initialIndex : Nat) :
    Option (SearchDAG × ClauseInfo) := do
  if dag.sourceIndexUsed initialIndex then
    none
  else
    dag.addSourceAt? guards initialIndex

/-- 在 Data 层 workspace 已证明 source 编号未使用时加入 source 节点。 -/
def addSourceKnownUnused? (dag : SearchDAG) (guards : GuardSet) (initialIndex : Nat) :
    Option (SearchDAG × ClauseInfo) :=
  dag.addSourceAt? guards initialIndex

/-- 某个 source 节点是否已经登记 split descriptor。 -/
def avatarSplitSourceUsed (dag : SearchDAG) (sourceId : NodeId) : Bool :=
  dag.clauses.any fun info =>
    match info.payload with
    | .avatarSplit payload => payload.source.id == sourceId
    | _ => false

private def addAvatarSplitAt? (dag : SearchDAG) (source : ClauseInfo)
    (partitions : Array (Array Nat)) (selectors : PropResolution.Clause) :
    Option (SearchDAG × ClauseInfo) := do
  match source.payload with
  | .source _ =>
      if !source.guards.isEmpty ||
          !AvatarSplit.indexPartitionOk source.clause.size partitions ||
          !AvatarSplit.selectorsOk partitions selectors then
        none
      else
        let parent := source.toParent
        let payload : AvatarSplitPayload := {
          source := parent
          partitions := partitions
          selectors := selectors
          note := "materialized AVATAR source split"
        }
        some (dag.addPlainClause source.clause #[parent] (.avatarSplit payload))
  | _ => none

/-- 加入一个完整 AVATAR split descriptor。 -/
def addAvatarSplit? (dag : SearchDAG) (source : ClauseInfo)
    (partitions : Array (Array Nat)) (selectors : PropResolution.Clause) :
    Option (SearchDAG × ClauseInfo) :=
  if dag.avatarSplitSourceUsed source.id then
    none
  else
    dag.addAvatarSplitAt? source partitions selectors

/-- 在 Data 层 workspace 已证明 source 尚未登记 split 时加入 split 节点。 -/
def addAvatarSplitKnownUnused? (dag : SearchDAG) (source : ClauseInfo)
    (partitions : Array (Array Nat)) (selectors : PropResolution.Clause) :
    Option (SearchDAG × ClauseInfo) :=
  dag.addAvatarSplitAt? source partitions selectors

/-- 某个 split descriptor 的 component slot 是否已经登记。 -/
def avatarComponentUsed (dag : SearchDAG) (splitId componentIndex : Nat) : Bool :=
  dag.clauses.any fun info =>
    match info.payload with
    | .avatarComponent payload =>
        payload.split.id == splitId && payload.componentIndex == componentIndex
    | _ => false

private def addAvatarComponentAt? (dag : SearchDAG) (split : ClauseInfo)
    (componentIndex : Nat) : Option (SearchDAG × ClauseInfo) := do
  match split.payload with
  | .avatarSplit splitPayload =>
      let indices ← splitPayload.partitions[componentIndex]?
      let selector ← AvatarSplit.selectorAt? splitPayload.selectors componentIndex
      let parent := split.toParent
      let payload : AvatarComponentPayload := {
        split := parent
        componentIndex := componentIndex
        note := "materialized AVATAR component"
      }
      some (dag.addClause {
        guards := #[selector]
        clause := AvatarSplit.clauseAtIndices split.clause indices
      } #[parent] (.avatarComponent payload))
  | _ => none

/-- 从 split descriptor 机械生成一个 singleton-guarded component 节点。 -/
def addAvatarComponent? (dag : SearchDAG) (split : ClauseInfo)
    (componentIndex : Nat) : Option (SearchDAG × ClauseInfo) :=
  if dag.avatarComponentUsed split.id componentIndex then
    none
  else
    dag.addAvatarComponentAt? split componentIndex

/-- 在 Data 层 workspace 已证明 split slot 未登记时加入 component 节点。 -/
def addAvatarComponentKnownUnused? (dag : SearchDAG) (split : ClauseInfo)
    (componentIndex : Nat) : Option (SearchDAG × ClauseInfo) :=
  dag.addAvatarComponentAt? split componentIndex

/-- 加入本地叠加/消解步骤，自动把父节点 guard 合并为结论 guard。 -/
def addLocalStep? (dag : SearchDAG) (parents : Array ProofParent)
    (witness : LocalStepWitness) : Option (SearchDAG × ClauseInfo) := do
  let gclause ← dag.guardedLocalResult? parents witness
  some (dag.addClause gclause parents (.localStep witness))

/-- `ClauseRef.clause?` 若存在，必须与真实父字句一致。 -/
private def clauseRefSnapshotMatches (ref : ClauseRef) (actual : SearchClause) : Bool :=
  match ref.clause? with
  | some snapshot => CoreSyntax.Search.clauseEq snapshot actual
  | none => true

/-- 从 witness 中记录的父引用恢复 search-DAG 父边。 -/
def parentFromClauseRef? (dag : SearchDAG) (ref : ClauseRef) :
    Option ProofParent := do
  let info ← dag.get? ref.id
  if clauseRefSnapshotMatches ref info.clause then
    some info.toParent
  else
    none

/-- 根据 witness 自带父引用加入本地叠加/消解步骤。 -/
def addLocalWitness? (dag : SearchDAG) (witness : LocalStepWitness) :
    Option (SearchDAG × ClauseInfo) := do
  let parents ← witness.parents.mapM dag.parentFromClauseRef?
  dag.addLocalStep? parents witness

/-- 从搜索器资源轨迹加入本地叠加/消解步骤。 -/
def addResourceTraceLocalWitness? (dag : SearchDAG)
    (witness : ResourceTrace.LocalStepWitness) :
    Option (SearchDAG × ClauseInfo) :=
  dag.addLocalWitness? (localStepWitnessOfResource witness)

/-- 将已有 guarded empty clause 显式登记为 theory conflict `Γ ⟹ ⊥`。 -/
def addTheoryConflict? (dag : SearchDAG) (conflict : ClauseInfo) :
    Option (SearchDAG × ClauseInfo) := do
  if !conflict.theoryConflict then
    none
  else
    let parent := conflict.toParent
    let payload : TheoryConflictPayload := {
      conflict := parent
      note := "materialized theory conflict"
    }
    some (dag.addClause conflict.guarded #[parent] (.theoryConflict payload))

/-- 从显式 theory conflict 节点物化 CDCL learned clause `¬Γ`。 -/
def addPropositionalLearnedClause? (dag : SearchDAG) (conflict : ClauseInfo) :
    Option (SearchDAG × ClauseInfo) := do
  match conflict.payload with
  | .theoryConflict _ =>
      let learned := DAGCertificate.learnedClauseOfGuards conflict.guards
      let parent := conflict.toParent
      let payload : PropositionalLearnedClausePayload := {
        conflict := conflict.id
        learned := learned
        note := "learned from theory conflict"
      }
      some (dag.addClause conflict.guarded #[parent] (.propositionalLearnedClause payload))
  | _ => none

/-- 当前 search-DAG 中已经产生的 AVATAR theory conflicts。 -/
def theoryConflicts (dag : SearchDAG) : Array ClauseInfo :=
  dag.clauses.filter ClauseInfo.theoryConflict

/-- CDCL feature 声明的命题字句必须命中 checked certificate 的 initial slot。 -/
def cdclInitialSlotOk (initialClauses : Array PropResolution.InitialClause)
    (index : Nat) (encodedClause : PropResolution.Clause) : Bool :=
  match initialClauses[index]? with
  | some initial => PropResolution.clauseEq initial.clause encodedClause
  | none => false

/-- residual CDCL 普通 parent feature 必须命中真实 search-DAG 节点和 initial slot。 -/
def initialFeatureOk (dag : SearchDAG)
    (initialClauses : Array PropResolution.InitialClause)
    (feature : CdclInitialFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause &&
    match dag.get? feature.clauseId with
    | some info =>
        info.guards.isEmpty &&
          CoreSyntax.Search.clauseEq info.clause feature.sourceClause
    | none => false

/-- residual CDCL summary 中的 learned feature 必须指向已物化 learned 节点。 -/
def learnedFeatureOk (dag : SearchDAG)
    (initialClauses : Array PropResolution.InitialClause)
    (feature : CdclLearnedFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause &&
    match dag.get? feature.learnedNode with
    | some info =>
        match info.payload with
        | .propositionalLearnedClause payload =>
            PropResolution.clauseEq
              (PropResolution.canonicalClause feature.encodedClause) payload.learned
        | _ => false
    | none => false

/-- guarded activation feature 必须命中真实 search-DAG 节点、guard 和 initial slot。 -/
def guardActivationFeatureOk (dag : SearchDAG)
    (initialClauses : Array PropResolution.InitialClause)
    (feature : CdclGuardActivationFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause &&
    match dag.get? feature.clauseId with
    | some info =>
        !info.guards.isEmpty &&
          CoreSyntax.Search.clauseEq info.clause feature.sourceClause &&
            guardSetEq info.guards feature.guards
    | none => false

/-- AVATAR skeleton feature 必须命中真实 split descriptor 和 initial slot。 -/
def avatarSkeletonFeatureOk (dag : SearchDAG)
    (initialClauses : Array PropResolution.InitialClause)
    (feature : CdclAvatarSkeletonFeature) : Bool :=
  cdclInitialSlotOk initialClauses feature.initialIndex feature.skeleton &&
    match dag.get? feature.splitId with
    | some info =>
        info.guards.isEmpty &&
          match info.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq feature.skeleton
                (PropResolution.canonicalClause payload.selectors)
          | _ => false
    | none => false

/-- residual CDCL 四类 initial 来源的数量必须覆盖完整 initial 数组。 -/
def cdclFeatureCount (summary : CdclResourceSummary) : Nat :=
  summary.initialFeatures.size + summary.avatarSkeletonFeatures.size +
    summary.learnedFeatures.size + summary.guardActivationFeatures.size

/-- residual CDCL 四类 initial 来源声明的 slot 集。 -/
def cdclFeatureSlots (summary : CdclResourceSummary) : Array Nat :=
  (summary.initialFeatures.map fun feature => feature.initialIndex) ++
    (summary.avatarSkeletonFeatures.map fun feature => feature.initialIndex) ++
      (summary.learnedFeatures.map fun feature => feature.initialIndex) ++
        (summary.guardActivationFeatures.map fun feature => feature.initialIndex)

private def pushNatUnique (values : Array Nat) (value : Nat) : Array Nat :=
  if values.contains value then values else values.push value

/-- search-DAG 中所有 source 节点引用的初始字句 slot。 -/
def sourceInitialIndices (dag : SearchDAG) : Array Nat :=
  dag.clauses.filterMap fun info =>
    match info.payload with
    | .source payload => some payload.initialIndex
    | _ => none

/-- 每个初始字句 slot 最多只能对应一个 source 节点。 -/
def sourceIndicesUnique (dag : SearchDAG) : Bool := Id.run do
  let mut seen := (List.replicate dag.initialClauses.size false).toArray
  for info in dag.clauses do
    match info.payload with
    | .source payload =>
        if h : payload.initialIndex < seen.size then
          if seen[payload.initialIndex] then
            return false
          else
            seen := seen.set payload.initialIndex true h
        else
          return false
    | _ => pure ()
  return true

/-- 每个 canonical source 最多登记一个 AVATAR split descriptor。 -/
def avatarSplitSourcesUnique (dag : SearchDAG) : Bool := Id.run do
  let mut seen : Array NodeId := #[]
  for info in dag.clauses do
    match info.payload with
    | .avatarSplit payload =>
        if seen.contains payload.source.id then
          return false
        else
          seen := seen.push payload.source.id
    | _ => pure ()
  return true

/-- 每个 split descriptor 的 component slot 最多登记一个节点。 -/
def avatarComponentSlotsUnique (dag : SearchDAG) : Bool := Id.run do
  let mut seen : Array (NodeId × Nat) := #[]
  for info in dag.clauses do
    match info.payload with
    | .avatarComponent payload =>
        let key := (payload.split.id, payload.componentIndex)
        if seen.contains key then
          return false
        else
          seen := seen.push key
    | _ => pure ()
  return true

/-- residual CDCL 四类来源必须一一覆盖 initial 数组的所有 slot。 -/
def cdclFeatureSlotsComplete (summary : CdclResourceSummary)
    (initialClauses : Array PropResolution.InitialClause) : Bool :=
  let slots := cdclFeatureSlots summary
  let unique := slots.foldl pushNatUnique #[]
  cdclFeatureCount summary == initialClauses.size &&
    unique.size == slots.size &&
      unique.size == initialClauses.size

/-- 一个 guard literal 必须落在对象原子 `atomMap` 的索引范围之外。 -/
def guardLiteralOutsideObjectAtoms (objectAtomCount : Nat)
    (literal : PropResolution.Lit) : Bool :=
  decide (objectAtomCount <= literal.var)

/-- guard 集必须整体落在对象原子 `atomMap` 的索引范围之外。 -/
def guardSetOutsideObjectAtoms (objectAtomCount : Nat) (guards : GuardSet) : Bool :=
  guards.all fun literal => guardLiteralOutsideObjectAtoms objectAtomCount literal

/-- theory-conflict learned clause 的全部 guard 文字必须在对象原子范围之外。 -/
def propClauseOutsideObjectAtoms (objectAtomCount : Nat)
    (clause : PropResolution.Clause) : Bool :=
  clause.all fun literal => guardLiteralOutsideObjectAtoms objectAtomCount literal

/-- residual CDCL summary 中 guard/CDCL 变量和对象 atomMap 变量不能碰撞。 -/
def cdclGuardVariablesOk (summary : CdclResourceSummary) : Bool :=
  summary.guardActivationFeatures.all
      (fun feature => guardSetOutsideObjectAtoms summary.objectAtomCount feature.guards) &&
    summary.avatarSkeletonFeatures.all
      (fun feature =>
        propClauseOutsideObjectAtoms summary.objectAtomCount feature.skeleton) &&
      summary.learnedFeatures.all
        (fun feature =>
          propClauseOutsideObjectAtoms summary.objectAtomCount feature.encodedClause)

/-- `ClauseRef.clause?` 若存在，必须与真实父字句一致。 -/
def clauseRefSnapshotOk (ref : ClauseRef) (actual : SearchClause) : Bool :=
  match ref.clause? with
  | some snapshot => CoreSyntax.Search.clauseEq snapshot actual
  | none => true

/-- 单侧 standardize-apart metadata 必须从真实父字句复算出来。 -/
def standardizeApartSideOk (ref : ClauseRef)
    (actual : SearchClause) (side : StandardizeApartSideMetadata) : Bool :=
  clauseRefSnapshotOk ref actual &&
    CoreSyntax.Search.clauseEq side.original actual &&
      CoreSyntax.Search.clauseEq side.renamed
        (CoreSyntax.Search.Clause.renameVars side.offset side.original)

/-- 二元 standardize-apart metadata 必须与两个真实父节点一致。 -/
def standardizeApartMetadataOk (dag : SearchDAG)
    (leftRef rightRef : ClauseRef) (metadata : StandardizeApartMetadata) : Bool :=
  match dag.get? leftRef.id, dag.get? rightRef.id with
  | some leftInfo, some rightInfo =>
      standardizeApartSideOk leftRef leftInfo.clause metadata.left &&
        standardizeApartSideOk rightRef rightInfo.clause metadata.right
  | _, _ => false

/-- 本地 witness 内部携带的 standardize-apart metadata 检查。 -/
def localWitnessStandardizeApartOk (dag : SearchDAG)
    (witness : LocalStepWitness) : Bool :=
  match witness with
  | .unary _ => true
  | .resolution resource =>
      match resource.standardizeApart? with
      | some metadata => dag.standardizeApartMetadataOk resource.left resource.right metadata
      | none => true
  | .rewrite resource =>
      match resource.standardizeApart? with
      | some metadata =>
          dag.standardizeApartMetadataOk resource.equality resource.target metadata
      | none => true

/-- source 必须是无父节点、命中固定 initial slot 且与表中字句完全一致。 -/
def sourceOk (dag : SearchDAG) (info : ClauseInfo) (payload : SourcePayload) : Bool :=
  info.parents.isEmpty &&
    match dag.initialClauses[payload.initialIndex]? with
    | some initial => CoreSyntax.Search.clauseEq info.clause initial
    | none => false

/-- split descriptor 必须精确复述一个无 guard canonical source。 -/
def avatarSplitOk (dag : SearchDAG) (info : ClauseInfo)
    (payload : AvatarSplitPayload) : Bool :=
  info.parents.size == 1 &&
    info.parents.contains payload.source &&
      info.guards.isEmpty &&
        AvatarSplit.indexPartitionOk payload.source.clause.size payload.partitions &&
          AvatarSplit.selectorsOk payload.partitions payload.selectors &&
            match dag.get? payload.source.id with
            | some source =>
                source.guards.isEmpty &&
                  CoreSyntax.Search.clauseEq source.clause payload.source.clause &&
                    CoreSyntax.Search.clauseEq info.clause source.clause &&
                      match source.payload with
                      | .source _ => true
                      | _ => false
            | none => false

/-- component 必须从父 split descriptor 的 partition 与 selector 表机械复算。 -/
def avatarComponentOk (dag : SearchDAG) (info : ClauseInfo)
    (payload : AvatarComponentPayload) : Bool :=
  info.parents.size == 1 &&
    info.parents.contains payload.split &&
      match dag.get? payload.split.id with
      | some split =>
          split.guards.isEmpty &&
            CoreSyntax.Search.clauseEq split.clause payload.split.clause &&
              match split.payload with
              | .avatarSplit splitPayload =>
                  match splitPayload.partitions[payload.componentIndex]?,
                      AvatarSplit.selectorAt? splitPayload.selectors payload.componentIndex with
                  | some indices, some selector =>
                      CoreSyntax.Search.clauseEq info.clause
                          (AvatarSplit.clauseAtIndices split.clause indices) &&
                        guardSetEq info.guards #[selector]
                  | _, _ => false
              | _ => false
      | none => false

/-- payload 层面的整图结构检查。source 可以原生带 guard；本地规则必须合并父 guard。 -/
def payloadGuardsOk (dag : SearchDAG) (info : ClauseInfo) : Bool :=
  match info.payload with
  | .source payload => dag.sourceOk info payload
  | .avatarSplit payload => dag.avatarSplitOk info payload
  | .avatarComponent payload => dag.avatarComponentOk info payload
  | .localStep witness => localGuardsOk dag info && localWitnessStandardizeApartOk dag witness
  | .theoryConflict _ => localGuardsOk dag info
  | .propositionalLearnedClause payload =>
      info.clause.isEmpty &&
        match dag.get? payload.conflict with
        | some conflict =>
          conflict.theoryConflict &&
            guardSetEq info.guards conflict.guards &&
              PropResolution.clauseEq payload.learned
                (DAGCertificate.learnedClauseOfGuards conflict.guards)
        | none => false
  | .residualCdcl payload =>
      cdclFeatureSlotsComplete payload.summary payload.initialClauses &&
        cdclGuardVariablesOk payload.summary &&
        payload.summary.initialFeatures.all
          (fun feature => dag.initialFeatureOk payload.initialClauses feature) &&
          payload.summary.avatarSkeletonFeatures.all
            (fun feature =>
              dag.avatarSkeletonFeatureOk payload.initialClauses feature) &&
            payload.summary.learnedFeatures.all
              (fun feature => dag.learnedFeatureOk payload.initialClauses feature) &&
              payload.summary.guardActivationFeatures.all
                (fun feature =>
                  dag.guardActivationFeatureOk payload.initialClauses feature)

/-- 单个节点的 dense-id 和父边检查。 -/
def infoOk (dag : SearchDAG) (index : Nat) (info : ClauseInfo) : Bool :=
  info.id == index &&
    info.parents.all (fun parent => dag.parentOk info.id parent) &&
      payloadGuardsOk dag info

private def infosOkFrom (dag : SearchDAG) (index : Nat) : List ClauseInfo → Bool
  | [] => true
  | info :: rest => dag.infoOk index info && infosOkFrom dag (index + 1) rest

/-- 轻量 search-DAG 的结构检查。 -/
def check (dag : SearchDAG) : Bool :=
  infosOkFrom dag 0 dag.clauses.toList && dag.sourceIndicesUnique &&
    dag.avatarSplitSourcesUnique && dag.avatarComponentSlotsUnique &&
    match dag.emptyClause? with
    | some id =>
        match dag.get? id with
        | some info => info.globallyEmpty
        | none => false
    | none => true

private partial def collectIdsWith (dag : SearchDAG) :
    Nat → Array Bool → Array NodeId → NodeId → Option (Array Bool × Array NodeId)
  | 0, _, _, _ => none
  | fuel + 1, seen, acc, id => do
      match seen[id]? with
      | none => none
      | some true => some (seen, acc)
      | some false =>
          let info ← dag.get? id
          let mut seen := seen.set! id true
          let mut acc := acc
          for parent in info.parents do
            let result ← collectIdsWith dag fuel seen acc parent.id
            seen := result.1
            acc := result.2
          pure (seen, acc.push id)

/-- 从某个 root 反向收集依赖，返回父节点在前、目标节点在后的拓扑序。 -/
def collectDependencies? (dag : SearchDAG) (id : NodeId) : Option (Array ClauseInfo) := do
  if !dag.check then
    none
  else
    let seen := (List.replicate dag.clauses.size false).toArray
    let (_, ids) ← collectIdsWith dag (dag.clauses.size + 1) seen #[] id
    ids.mapM (fun id => dag.get? id)

/-- 从当前记录的空字句开始反向收集依赖。 -/
def collectEmptyDependencies? (dag : SearchDAG) : Option (Array ClauseInfo) := do
  let id ← dag.emptyClause?
  dag.collectDependencies? id

end SearchDAG

/-! ## 新 DAG 签名与基础翻译 -/

/-- 搜索层中除内建等词外需要进入一阶 DAG 的关系符号。 -/
inductive RelSymbol where
  | member
  | boolHolds
  | definition (id arity : Nat)
  | predicate (symbol : CoreSyntax.PredicateSymbol)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace RelSymbol

/-- 材料化关系符号的稳定审计标签。 -/
def label : RelSymbol → String
  | member => "member"
  | boolHolds => "boolHolds"
  | definition id arity => s!"definition[{id}/{arity}]"
  | predicate symbol => s!"predicate[{symbol.id}/{symbol.arity}]"

end RelSymbol

/-- 旧搜索语法对应的新一阶 DAG 签名。 -/
def SearchSignature : LogicSoundness.SetLevel.Signature where
  SortSymbol := SearchSort
  FuncSymbol := SearchFunc
  RelSymbol := RelSymbol
  funcDomain f :=
    if f.inputSorts.isEmpty then
      List.replicate f.arity CoreSyntax.CoreSort.object
    else
      f.inputSorts
  funcCodomain f := f.outputSort
  relDomain
    | .member => [CoreSyntax.CoreSort.object, CoreSyntax.CoreSort.object]
    | .boolHolds => [CoreSyntax.CoreSort.bool]
    | .definition .. => [CoreSyntax.CoreSort.object]
    | .predicate symbol =>
        if symbol.inputSorts.isEmpty then
          List.replicate symbol.arity CoreSyntax.CoreSort.object
        else
          symbol.inputSorts

abbrev Term := DAGCertificate.Term SearchSignature
abbrev Formula := DAGCertificate.Formula SearchSignature
abbrev Literal := DAGCertificate.Literal SearchSignature
abbrev Clause := DAGCertificate.Clause SearchSignature
abbrev ParentClause := DAGCertificate.ParentClause SearchSignature
abbrev Node := DAGCertificate.Node SearchSignature
abbrev Payload := DAGCertificate.Payload SearchSignature
abbrev DeepProblem := DAGCertificate.DeepProblem SearchSignature
abbrev ClauseProblem := DAGCertificate.ClauseProblem SearchSignature
abbrev DAG := DAGCertificate.DAG SearchSignature

instance instSearchSignatureSortDecidableEq :
    DecidableEq SearchSignature.SortSymbol := by
  change DecidableEq SearchSort
  infer_instance

instance instSearchSignatureFuncDecidableEq :
    DecidableEq SearchSignature.FuncSymbol := by
  change DecidableEq SearchFunc
  infer_instance

instance instSearchSignatureRelDecidableEq :
    DecidableEq SearchSignature.RelSymbol := by
  change DecidableEq RelSymbol
  infer_instance

abbrev CheckedDAG := DAGCertificate.CheckedDAG (σ := SearchSignature)

abbrev Result (α : Type) := Except Certificate.Diagnostic α

/-- 构造材料化阶段的结构化诊断。 -/
def diagnostic (phase : Certificate.Phase) (message : String) :
    Certificate.Diagnostic :=
  Certificate.Diagnostic.ofMessage .dagReflection phase message

/-- 把 `Option` 提升成材料化诊断。 -/
def requireSome {α : Type} (phase : Certificate.Phase) (message : String) :
    Option α → Result α
  | some value => pure value
  | none => throw (diagnostic phase message)

/-- 当前材料化只把非箭头 sort 当作一阶 sort 使用。 -/
def firstOrderSortOk : SearchSort → Bool
  | .arrow .. => false
  | _ => true

/-- 检查函数符号不会把高阶箭头 sort 带入一阶材料化签名。 -/
def functionSymbolFirstOrderOk (symbol : SearchFunc) : Bool :=
  firstOrderSortOk symbol.outputSort &&
    symbol.inputSorts.all firstOrderSortOk

/-- 翻译搜索层函数应用参数前的 arity/sort 边界检查。 -/
def checkFunctionSymbol (symbol : SearchFunc) (actualArity : Nat) : Result Unit := do
  if !functionSymbolFirstOrderOk symbol then
    throw (diagnostic .sourceMaterialization
      (s!"function symbol {reprStr symbol} uses arrow sort; " ++
        "first-order DAG materialization rejected it"))
  if actualArity != symbol.arity then
    throw (diagnostic .sourceMaterialization
      s!"function symbol arity mismatch: symbol={reprStr symbol}, actual={actualArity}")
  if !(symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity) then
    throw (diagnostic .sourceMaterialization
      s!"function symbol input sort arity mismatch: {reprStr symbol}")

/-- 搜索项到新一阶 DAG 项的翻译。 -/
partial def term (input : SearchTerm) : Result Term := do
  match input with
  | .var id =>
      pure (.var (.fvar CoreSyntax.CoreSort.object id))
  | .bvar sort index =>
      if firstOrderSortOk sort then
        pure (.var (.bvar sort index))
      else
        throw (diagnostic .sourceMaterialization
          s!"bound variable uses arrow sort: {reprStr sort}")
  | .fvar sort id =>
      if firstOrderSortOk sort then
        pure (.var (.fvar sort id))
      else
        throw (diagnostic .sourceMaterialization
          s!"free variable uses arrow sort: {reprStr sort}")
  | .app symbol args =>
      checkFunctionSymbol symbol args.length
      pure (.app symbol (← args.mapM term))
  | .apply .. =>
      throw (diagnostic .sourceMaterialization
        "higher-order application is not representable in the current first-order DAG")
  | .lam .. =>
      throw (diagnostic .sourceMaterialization
        "lambda term is not representable in the current first-order DAG")

/-- 翻译无极性的搜索原子。 -/
def projectedPredicateArguments (predicate : CoreSyntax.PredicateSymbol)
    (input : SearchTerm) : Result (List SearchTerm) := do
  match input with
  | .app tuple arguments =>
      let expected : SearchFunc := {
        id := predicate.id
        arity := arguments.length
        kind := CoreSyntax.Search.SymbolKind.tuple
        inputSorts := predicate.inputSorts
      }
      if tuple != expected then
        throw (diagnostic .sourceMaterialization
          s!"predicate tuple marker mismatch: predicate={reprStr predicate}, tuple={reprStr tuple}")
      if arguments.length != predicate.arity then
        throw (diagnostic .sourceMaterialization
          (s!"predicate tuple arity mismatch: predicate={reprStr predicate}, " ++
            s!"actual={arguments.length}"))
      pure arguments
  | _ =>
      throw (diagnostic .sourceMaterialization
        s!"predicate arguments are not carried by a checked tuple: {reprStr input}")

/-- 翻译无极性的搜索原子。 -/
def atom (predicate : CoreSyntax.Search.PredicateKind)
    (left right : SearchTerm) : Result Formula := do
  match predicate with
  | .equal =>
      pure (.equal (← term left) (← term right))
  | .member =>
      pure (.rel .member [← term left, ← term right])
  | .boolHolds =>
      pure (.rel .boolHolds [← term left])
  | .definition id arity =>
      -- 旧搜索层 `Literal.toCoreAtom` 对 definition predicate 只消费 `left`；
      -- 这里保持同一对象形状，`arity` 仅作为关系符号的审计元数据。
      pure (.rel (.definition id arity) [← term left])
  | .predicate symbol =>
      let arguments ← projectedPredicateArguments symbol left
      pure (.rel (.predicate symbol) (← arguments.mapM term))

/-- 搜索 literal 到新 DAG literal 的翻译。 -/
def literal (input : SearchLiteral) : Result Literal := do
  pure { polarity := input.positive, atom := (← atom input.predicate input.left input.right) }

/-- 搜索 clause 到新 DAG clause 的翻译。 -/
def clause (input : SearchClause) : Result Clause := do
  pure { literals := (← input.mapM literal) }

/-- projectable core 项到一阶 DAG 项的 canonical 直接翻译。 -/
def coreTerm : CoreSyntax.Term → Term
  | .fvar sort id => .var (.fvar sort id)
  | .app symbol arguments =>
      .app (CoreSyntax.NormalForm.FirstOrderProjection.functionSymbol symbol)
        (arguments.map coreTerm)
  | .bvar _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .apply _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .bool _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .notE _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .andE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .orE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .impE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .iffE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .quote _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .lam _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
  | .ite _ _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)

/-- projectable core 原子到一阶 DAG 公式的 canonical 直接翻译。 -/
def coreAtom : CoreSyntax.NormalForm.Atom → Formula
  | .predicate symbol arguments =>
      .rel (.predicate symbol) (arguments.map coreTerm)
  | .equal _ left right =>
      .equal (coreTerm left) (coreTerm right)
  | .boolTerm term =>
      .rel .boolHolds [coreTerm term]

/-- projectable core 文字到一阶 DAG 文字的 canonical 直接翻译。 -/
def coreLiteral (input : CoreSyntax.NormalForm.Literal) : Literal :=
  { polarity := input.positive, atom := coreAtom input.atom }

/-- projectable core 字句到一阶 DAG 字句的 canonical 直接翻译。 -/
def coreClause (input : CoreSyntax.NormalForm.Clause) : Clause :=
  { literals := input.map coreLiteral }

/-- projectable core 字句集到一阶 DAG 初始字句表的 canonical 直接翻译。 -/
def coreClauseSet (input : CoreSyntax.NormalForm.ClauseSet) : Array Clause :=
  input.map coreClause

/-
Kernel replay 使用显式结构递归引用 canonical core projection。

搜索与语义层继续保留上面的 Array/List map 接口；这里只提供 definitionally
transparent 的同值视图，避免 concrete DAG checker 展开容器实现。
-/
namespace ReplayCoreProjection

mutual
  /-- 可归约的 core 项投影。 -/
  def term : CoreSyntax.Term → Term
    | .bvar _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .fvar sort id => .var (.fvar sort id)
    | .app symbol arguments =>
        .app (CoreSyntax.NormalForm.FirstOrderProjection.functionSymbol symbol)
          (termList arguments)
    | .apply _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .bool _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .notE _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .andE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .orE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .impE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .iffE _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .quote _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .lam _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)
    | .ite _ _ _ _ => .var (.fvar CoreSyntax.CoreSort.object 0)

  /-- 可归约的 core 项列表投影。 -/
  def termList : List CoreSyntax.Term → List Term
    | [] => []
    | head :: tail => term head :: termList tail
end

mutual
  /-- 显式项投影与 canonical 投影一致。 -/
  theorem term_eq_coreTerm :
      ∀ input : CoreSyntax.Term, term input = coreTerm input
    | .bvar sort index => by
        rw [term.eq_1, coreTerm.eq_3]
    | .fvar sort id => by
        rw [term.eq_2, coreTerm.eq_1]
    | .app symbol arguments => by
        rw [term.eq_3, coreTerm.eq_2]
        exact congrArg
          (fun translated =>
            (.app
              (CoreSyntax.NormalForm.FirstOrderProjection.functionSymbol symbol)
              translated : Term))
          (termList_eq_map arguments)
    | .apply function argument => by
        rw [term.eq_4, coreTerm.eq_4]
    | .bool value => by
        rw [term.eq_5, coreTerm.eq_5]
    | .notE body => by
        rw [term.eq_6, coreTerm.eq_6]
    | .andE left right => by
        rw [term.eq_7, coreTerm.eq_7]
    | .orE left right => by
        rw [term.eq_8, coreTerm.eq_8]
    | .impE left right => by
        rw [term.eq_9, coreTerm.eq_9]
    | .iffE left right => by
        rw [term.eq_10, coreTerm.eq_10]
    | .quote formula => by
        rw [term.eq_11, coreTerm.eq_11]
    | .lam domain codomain body => by
        rw [term.eq_12, coreTerm.eq_12]
    | .ite sort condition thenTerm elseTerm => by
        rw [term.eq_13, coreTerm.eq_13]

  /-- 显式项列表投影与 canonical map 投影一致。 -/
  theorem termList_eq_map :
      ∀ terms : List CoreSyntax.Term, termList terms = terms.map coreTerm
    | [] => rfl
    | head :: tail => by
        rw [termList, List.map, term_eq_coreTerm, termList_eq_map]
end

/-- 可归约的 core 原子投影。 -/
def atom : CoreSyntax.NormalForm.Atom → Formula
  | .predicate symbol arguments =>
      .rel (.predicate symbol) (termList arguments)
  | .equal _ left right =>
      .equal (term left) (term right)
  | .boolTerm input =>
      .rel .boolHolds [term input]

/-- 显式原子投影与 canonical 投影一致。 -/
theorem atom_eq_coreAtom :
    ∀ input : CoreSyntax.NormalForm.Atom, atom input = coreAtom input
  | .predicate symbol arguments =>
      congrArg
        (fun translated =>
          (.rel (RelSymbol.predicate symbol) translated : Formula))
        (termList_eq_map arguments)
  | .equal sort left right => by
      rw [atom, coreAtom, term_eq_coreTerm, term_eq_coreTerm]
  | .boolTerm input => by
      rw [atom, coreAtom, term_eq_coreTerm]

/-- 可归约的 core 文字投影。 -/
def literal (input : CoreSyntax.NormalForm.Literal) : Literal :=
  { polarity := input.positive, atom := atom input.atom }

/-- 显式文字投影与 canonical 投影一致。 -/
theorem literal_eq_coreLiteral
    (input : CoreSyntax.NormalForm.Literal) :
    literal input = coreLiteral input := by
  exact congrArg
    (fun translated =>
      ({ polarity := input.positive, atom := translated } : Literal))
    (atom_eq_coreAtom input.atom)

/-- 可归约的 core 文字列表投影。 -/
def literalList : List CoreSyntax.NormalForm.Literal → List Literal
  | [] => []
  | head :: tail => literal head :: literalList tail

/-- 显式文字列表投影与 canonical map 投影一致。 -/
theorem literalList_eq_map :
    ∀ literals : List CoreSyntax.NormalForm.Literal,
      literalList literals = literals.map coreLiteral
  | [] => rfl
  | head :: tail => by
      rw [literalList, List.map, literal_eq_coreLiteral, literalList_eq_map]

/-- 可归约的 core 字句投影。 -/
def clause (input : CoreSyntax.NormalForm.Clause) : Clause :=
  { literals := (literalList input.toList).toArray }

/-- 显式字句投影与 canonical Array map 投影一致。 -/
theorem clause_eq_coreClause (input : CoreSyntax.NormalForm.Clause) :
    clause input = coreClause input := by
  apply congrArg (fun literals => ({ literals := literals } : Clause))
  apply Array.toList_inj.mp
  simp [literalList_eq_map]

/-- 可归约的 core 字句列表投影。 -/
def clauseList : List CoreSyntax.NormalForm.Clause → List Clause
  | [] => []
  | head :: tail => clause head :: clauseList tail

/-- 显式字句列表投影与 canonical map 投影一致。 -/
theorem clauseList_eq_map :
    ∀ clauses : List CoreSyntax.NormalForm.Clause,
      clauseList clauses = clauses.map coreClause
  | [] => rfl
  | head :: tail => by
      rw [clauseList, List.map, clause_eq_coreClause, clauseList_eq_map]

/-- 可归约的 core 字句集投影。 -/
def clauseSet (input : CoreSyntax.NormalForm.ClauseSet) : Array Clause :=
  (clauseList input.toList).toArray

/-- Replay 投影与现有 canonical core 字句投影一致。 -/
theorem clauseSet_eq_coreClauseSet
    (input : CoreSyntax.NormalForm.ClauseSet) :
    clauseSet input = coreClauseSet input := by
  apply Array.toList_inj.mp
  simp [clauseSet, coreClauseSet, clauseList_eq_map]

end ReplayCoreProjection

/-- 新 DAG 字句数组的顺序敏感结构比较。 -/
private def clauseListEq : List Clause → List Clause → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.eq right && clauseListEq leftRest rightRest
  | _, _ => false

/-- 新 DAG 字句数组的顺序敏感结构比较。 -/
def clauseArrayEq (left right : Array Clause) : Bool :=
  clauseListEq left.toList right.toList

private theorem clauseListEq_sound :
    ∀ {left right : List Clause}, clauseListEq left right = true → left = right
  | [], [], _ => rfl
  | left :: leftRest, right :: rightRest, h => by
      simp only [clauseListEq, Bool.and_eq_true_iff] at h
      have hHead := DAGCertificate.Clause.eq_sound left right h.1
      have hRest := clauseListEq_sound h.2
      cases hHead
      cases hRest
      rfl
  | [], _ :: _, h => by
      simp [clauseListEq] at h
  | _ :: _, [], h => by
      simp [clauseListEq] at h

/-- 字句数组结构比较通过时，两侧数组实际相等。 -/
theorem clauseArrayEq_sound {left right : Array Clause}
    (h : clauseArrayEq left right = true) : left = right := by
  apply Array.toList_inj.mp
  exact clauseListEq_sound h

namespace SearchDAG

/-- 把 search-DAG 自己持有的 canonical initial table 翻译成新 DAG 字句。 -/
def materializedInitialClauses (dag : SearchDAG) : Result (Array Clause) :=
  dag.initialClauses.mapM clause

/--
确认 search-DAG initial table 与调用者要求的原生字句问题完全一致。

材料化只接受完整表的一一对应，不允许依赖当前 root 切片猜测 source 来自哪个问题。
-/
def ensureInitialClausesMatchProblem (dag : SearchDAG)
    (problem : ClauseProblem) : Result Unit := do
  let initialClauses ← dag.materializedInitialClauses
  if clauseArrayEq initialClauses problem.initialClauses then
    pure ()
  else
    throw (diagnostic .sourceMaterialization
      "search DAG canonical initial-clause table does not match the requested clause problem")

end SearchDAG

/-- 搜索层 substitution 到新 DAG substitution 的翻译。 -/
def termSubstitution (input : Substitution) :
    Result (DAGCertificate.TermSubstitution SearchSignature) := do
  input.mapM fun binding => do
    if !firstOrderSortOk binding.key.sort then
      throw (diagnostic .sourceMaterialization
        s!"first-order substitution key uses arrow sort: {reprStr binding.key}")
    if binding.replacement.inferSort? != some binding.key.sort then
      throw (diagnostic .sourceMaterialization
        s!"substitution replacement sort does not match key: {reprStr binding}")
    pure (binding.key.sort, binding.key.id, ← term binding.replacement)

/-- residual 命题化时忽略 literal 极性的搜索原子。 -/
structure PropAtom where
  predicate : CoreSyntax.Search.PredicateKind
  left : SearchTerm
  right : SearchTerm
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace PropAtom

/-- 从搜索 literal 抽出无极性的命题原子。 -/
def ofLiteral (literal : SearchLiteral) : PropAtom where
  predicate := literal.predicate
  left := literal.left
  right := literal.right

/-- 转回新 DAG 原子公式。 -/
def toFormula (input : PropAtom) : Result Formula :=
  atom input.predicate input.left input.right

end PropAtom

/-- 查找已登记的命题原子。 -/
def findPropAtom? (atoms : Array PropAtom) (atom : PropAtom) : Option Nat := Id.run do
  for h : index in [:atoms.size] do
    if atoms[index] == atom then
      return some index
  return none

/-- 登记命题原子并返回变量编号。 -/
def internPropAtom (atoms : Array PropAtom) (atom : PropAtom) :
    Nat × Array PropAtom :=
  match findPropAtom? atoms atom with
  | some index => (index, atoms)
  | none => (atoms.size, atoms.push atom)

/-- 命题化一个搜索 literal，使用 residual CDCL 的全局 atom 顺序。 -/
def encodeLiteral (atoms : Array PropAtom) (literal : SearchLiteral) :
    PropResolution.Lit × Array PropAtom :=
  let (var, atoms) := internPropAtom atoms (PropAtom.ofLiteral literal)
  ({ var := var, positive := literal.positive }, atoms)

/-- 命题化一个搜索 clause，并延续 residual CDCL 的全局 atom 顺序。 -/
def encodePropClause (atoms : Array PropAtom) (input : SearchClause) :
    PropResolution.Clause × Array PropAtom := Id.run do
  let mut atoms := atoms
  let mut encoded : PropResolution.Clause := #[]
  for literal in input do
    let (propLiteral, atoms') := encodeLiteral atoms literal
    atoms := atoms'
    encoded := encoded.push propLiteral
  return (encoded, atoms)

/-- guarded activation initial 的命题字句：`¬Γ ∨ prop(C)`。 -/
def guardActivationEncodedClause (guards : GuardSet)
    (encodedObject : PropResolution.Clause) : PropResolution.Clause :=
  PropResolution.canonicalClause (guards.map PropResolution.Lit.neg ++ encodedObject)

/-- `[0, size)` 的 compact slot 列表，用作 CDCL summary 的默认 used set。 -/
def allInitialIndices (size : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for _h : index in [:size] do
    out := out.push index
  return out

/-! ## residual CDCL 搜索层自动材料化 -/

namespace SearchDAG

private abbrev CdclFeatureWorkspace :=
  Data.ResidualCdclWorkspace
    PropAtom ProofParent CdclInitialFeature CdclAvatarSkeletonFeature
      CdclLearnedFeature CdclGuardActivationFeature

/-- 自动构造 residual CDCL features 时维护的中间状态。 -/
private structure CdclFeatureBuildState where
  dag : SearchDAG
  workspace : CdclFeatureWorkspace := {}

private def requireCurrentInfo (dag : SearchDAG) (info : ClauseInfo) :
    Result ClauseInfo := do
  let current ← requireSome .residualSplit
    s!"residual CDCL source node {info.id} is not present in search DAG" <|
      dag.get? info.id
  if GuardedClause.eq current.guarded info.guarded then
    pure current
  else
    throw (diagnostic .residualSplit
      s!"residual CDCL source node {info.id} does not match current search DAG clause")

private def requireInitialSlot (initialClauses : Array PropResolution.InitialClause)
    (index : Nat) (encoded : PropResolution.Clause) (label : String) : Result Unit := do
  if cdclInitialSlotOk initialClauses index encoded then
    pure ()
  else
    throw (diagnostic .residualSplit
      s!"residual CDCL {label} feature does not match initial slot {index}")

private def addParentFeature (initialClauses : Array PropResolution.InitialClause)
    (state : CdclFeatureBuildState) (info : ClauseInfo) :
    Result CdclFeatureBuildState := do
  let (encodedRaw, atoms) := encodePropClause state.workspace.atoms info.clause
  match PropResolution.canonicalClause? encodedRaw with
  | none =>
      pure { state with workspace := state.workspace.setAtoms atoms }
  | some encoded =>
      requireInitialSlot initialClauses state.workspace.initialIndex encoded "parent"
      let feature : CdclInitialFeature := {
        initialIndex := state.workspace.initialIndex
        clauseId := info.id
        sourceClause := info.clause
        encodedClause := encoded
        originLabel? := some "parent"
      }
      pure {
        state with
        workspace :=
          state.workspace.pushInitial info.id info.toParent atoms feature
      }

private def addGuardActivationFeature
    (initialClauses : Array PropResolution.InitialClause)
    (state : CdclFeatureBuildState) (info : ClauseInfo) :
    Result CdclFeatureBuildState := do
  let (encodedObject, atoms) :=
    encodePropClause state.workspace.atoms info.clause
  let encoded := guardActivationEncodedClause info.guards encodedObject
  match PropResolution.canonicalClause? encoded with
  | none =>
      pure { state with workspace := state.workspace.setAtoms atoms }
  | some encoded =>
      requireInitialSlot initialClauses state.workspace.initialIndex
        encoded "guard activation"
      let feature : CdclGuardActivationFeature := {
        initialIndex := state.workspace.initialIndex
        clauseId := info.id
        sourceClause := info.clause
        guards := canonicalGuards info.guards
        encodedClause := encoded
        originLabel? := some "guard activation"
      }
      pure {
        state with
        workspace :=
          state.workspace.pushGuard info.id info.toParent atoms feature
      }

private def addAvatarSkeletonFeature
    (initialClauses : Array PropResolution.InitialClause)
    (state : CdclFeatureBuildState) (info : ClauseInfo)
    (payload : AvatarSplitPayload) :
    Result CdclFeatureBuildState := do
  let skeleton := PropResolution.canonicalClause payload.selectors
  requireInitialSlot initialClauses state.workspace.initialIndex
    skeleton "AVATAR skeleton"
  let feature : CdclAvatarSkeletonFeature := {
    initialIndex := state.workspace.initialIndex
    splitId := info.id
    skeleton := skeleton
    originLabel? := some "AVATAR selector skeleton"
  }
  pure {
    state with
    workspace := state.workspace.pushAvatar info.id info.toParent feature
  }

private def ensureTheoryConflictAndLearned
    (state : CdclFeatureBuildState) (info : ClauseInfo) :
    Result (CdclFeatureBuildState × ClauseInfo) := do
  let (dag, conflict) ←
    match info.payload with
    | .theoryConflict _ =>
        pure (state.dag, info)
    | _ =>
        requireSome .residualSplit
          s!"residual CDCL source node {info.id} is not a theory conflict" <|
            state.dag.addTheoryConflict? info
  let (dag, learned) ← requireSome .residualSplit
    s!"residual CDCL could not materialize learned clause for conflict {conflict.id}" <|
      dag.addPropositionalLearnedClause? conflict
  pure ({ state with dag := dag }, learned)

private def addLearnedFeature (initialClauses : Array PropResolution.InitialClause)
    (state : CdclFeatureBuildState) (learned : ClauseInfo)
    (encoded : PropResolution.Clause) :
    Result CdclFeatureBuildState := do
  match PropResolution.canonicalClause? encoded with
  | none =>
      pure state
  | some encoded =>
      requireInitialSlot initialClauses state.workspace.initialIndex encoded "learned"
      let feature : CdclLearnedFeature := {
        initialIndex := state.workspace.initialIndex
        learnedNode := learned.id
        encodedClause := encoded
        originLabel? := some "theory conflict learned"
      }
      pure {
        state with
        workspace :=
          state.workspace.pushLearned learned.id learned.toParent feature
      }

private def addSourceInitialFeature
    (initialClauses : Array PropResolution.InitialClause)
    (state : CdclFeatureBuildState) (source : ClauseInfo) :
    Result CdclFeatureBuildState := do
  let info ← requireCurrentInfo state.dag source
  match info.payload with
  | .avatarSplit payload =>
      addAvatarSkeletonFeature initialClauses state info payload
  | .propositionalLearnedClause payload =>
      addLearnedFeature initialClauses state info payload.learned
  | _ =>
      if info.guards.isEmpty then
        addParentFeature initialClauses state info
      else if info.clause.isEmpty then
        let (state, learned) ← ensureTheoryConflictAndLearned state info
        addLearnedFeature initialClauses state learned
          (DAGCertificate.learnedClauseOfGuards info.guards)
      else
        addGuardActivationFeature initialClauses state info

private def finishCdclSummary
    (initialClauses : Array PropResolution.InitialClause)
    (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String) (state : CdclFeatureBuildState) :
    Result CdclResourceSummary := do
  let workspace := state.workspace
  if workspace.initialIndex != initialClauses.size then
    throw (diagnostic .residualSplit
      (s!"residual CDCL feature slots ended at {workspace.initialIndex}, " ++
        s!"expected {initialClauses.size}"))
  let summary : CdclResourceSummary := {
    phase := phase
    initialFeatures := workspace.initialFeatures
    avatarSkeletonFeatures := workspace.avatarFeatures
    learnedFeatures := workspace.learnedFeatures
    guardActivationFeatures := workspace.guardFeatures
    objectAtomCount := workspace.atoms.size
    usedInitialIndices := allInitialIndices initialClauses.size
    journalSize := certificate.proof.journal.learns.size
    learnedClauses := certificate.proof.journal.learns.size
    resolutionSteps := certificate.proof.journal.steps.size
  }
  if cdclFeatureSlotsComplete summary initialClauses &&
      cdclGuardVariablesOk summary then
    pure summary
  else
    throw (diagnostic .residualSplit
      "residual CDCL generated features failed slot or guard-variable checks")

/--
从一组按 CDCL initial 顺序排列的 search-DAG 字句自动生成 residual CDCL 根节点。

AVATAR split descriptor 生成 selector skeleton initial；普通无 guard 字句生成 parent
initial；guarded 非空字句生成 activation initial；guarded empty 字句会先物化
theory-conflict 与 propositional learned clause，再生成 learned initial。返回的新根已经
通过 SearchDAG 结构 checker。
-/
def addResidualCdclFromSources (dag : SearchDAG)
    (sources : Array ClauseInfo)
    (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String := "search residual CDCL") :
    Result (SearchDAG × ClauseInfo) := do
  let initialClauses := certificate.initialClauses
  let mut state : CdclFeatureBuildState := { dag := dag }
  for source in sources do
    state ← addSourceInitialFeature initialClauses state source
  let summary ← finishCdclSummary initialClauses certificate phase state
  if state.workspace.parents.isEmpty then
    throw (diagnostic .residualSplit
      "residual CDCL root has no materialized parent initial sources")
  let payload : ResidualCdclPayload := {
    initialClauses := certificate.initialClauses
    proof := certificate.proof
    summary := summary
  }
  let (dag, info) :=
    state.dag.addPlainClause #[] state.workspace.parents (.residualCdcl payload)
  if dag.check then
    pure (dag, info)
  else
    throw (diagnostic .dagCheck
      s!"search DAG failed checker after residual CDCL materialization at node {info.id}")

end SearchDAG

/-! ## 材料化状态与父快照 -/

/-- 一个旧稳定编号对应的材料化节点信息。 -/
structure MaterializedEntry where
  newId : DAGCertificate.NodeId
  clause : Clause

/-- 已材料化节点表中的旧 id 映射。 -/
structure MaterializationState where
  entries : Data.StableIdMap MaterializedEntry := {}
  nodes : Array Node := #[]

namespace MaterializationState

/-- 创建材料化状态，并按依赖切片规模预留直接寻址表与节点数组。 -/
def emptyWithCapacity (capacity : Nat) : MaterializationState :=
  {
    entries := Data.StableIdMap.emptyWithCapacity capacity
    nodes := Array.emptyWithCapacity capacity
  }

/-- 查找旧 id 对应的新 dense id。 -/
def newId? (state : MaterializationState) (oldId : NodeId) :
    Option DAGCertificate.NodeId :=
  (state.entries.get? oldId).map (·.newId)

/-- 查找已经材料化的旧 id 字句快照。 -/
def clause? (state : MaterializationState) (oldId : NodeId) :
    Option Clause :=
  (state.entries.get? oldId).map (·.clause)

/-- 登记一个新节点。 -/
def push (state : MaterializationState) (oldId : NodeId)
    (node : Node) : MaterializationState :=
  { entries := state.entries.insert oldId { newId := node.id, clause := node.conclusion }
    nodes := state.nodes.push node }

end MaterializationState

/-- 根据旧父引用构造新 DAG 父字句快照。 -/
def parentFromProofParent (state : MaterializationState)
    (parent : ProofParent) : Result ParentClause := do
  let id ← requireSome .sourceMaterialization
    s!"parent id {parent.id} has not been materialized before child" <|
      state.newId? parent.id
  let stored ← requireSome .sourceMaterialization
    s!"parent id {parent.id} has no materialized clause snapshot" <|
      state.clause? parent.id
  let recorded ← clause parent.clause
  if stored.eq recorded then
    pure { id := id, clause := stored }
  else
    throw (diagnostic .sourceMaterialization
      s!"parent snapshot mismatch for old id {parent.id}")

/-- 根据资源层 `ClauseRef` 构造新 DAG 父字句快照。 -/
def parentFromRef (state : MaterializationState)
    (ref : ClauseRef) : Result ParentClause := do
  let id ← requireSome .sourceMaterialization
    s!"resource parent id {ref.id} has not been materialized before child" <|
      state.newId? ref.id
  let stored ← requireSome .sourceMaterialization
    s!"resource parent id {ref.id} has no materialized clause snapshot" <|
      state.clause? ref.id
  match ref.clause? with
  | none =>
      pure { id := id, clause := stored }
  | some raw =>
      let recorded ← clause raw
      if stored.eq recorded then
        pure { id := id, clause := stored }
      else
        throw (diagnostic .sourceMaterialization
          s!"resource parent snapshot mismatch for old id {ref.id}")

/-- 翻译并检查单侧 standardize-apart metadata。 -/
def standardizeApartSideEvidence (state : MaterializationState)
    (ref : ClauseRef) (side : StandardizeApartSideMetadata) :
    Result (DAGCertificate.StandardizeApartSideEvidence SearchSignature) := do
  let parent ← parentFromRef state ref
  let original ← clause side.original
  if !parent.clause.eq original then
    throw (diagnostic .sourceMaterialization
      s!"standardize-apart original snapshot mismatch for old id {ref.id}")
  let renamed ← clause side.renamed
  let evidence : DAGCertificate.StandardizeApartSideEvidence SearchSignature := {
    parent := parent
    offset := side.offset
    renamed := renamed
  }
  if evidence.check then
    pure evidence
  else
    throw (diagnostic .sourceMaterialization
      s!"standardize-apart renamed snapshot does not replay for old id {ref.id}")

/-- 翻译并检查二元 standardize-apart metadata。 -/
def standardizeApartEvidence (state : MaterializationState)
    (leftRef rightRef : ClauseRef) (metadata : StandardizeApartMetadata) :
    Result (DAGCertificate.StandardizeApartEvidence SearchSignature) := do
  pure {
    left := (← standardizeApartSideEvidence state leftRef metadata.left)
    right := (← standardizeApartSideEvidence state rightRef metadata.right)
  }

/-- 查找数组中的第 `index` 个 literal，并给出材料化诊断。 -/
def getSearchLiteral (parentLabel : String) (clause : SearchClause)
    (index : Nat) : Result SearchLiteral :=
  requireSome .sourceMaterialization
    s!"literal index {index} out of bounds in {parentLabel}" clause[index]?

/-- 本地规则 witness 必须显式记录关键 literal 索引。 -/
def requireLiteralIndex (label : String) (index? : Option Nat) : Result Nat :=
  requireSome .sourceMaterialization
    s!"{label} literal index is missing from local rule witness" index?

/-- 查找新 DAG 字句中的第 `index` 个 literal。 -/
def getDagLiteral (parentLabel : String) (clause : Clause)
    (index : Nat) : Result Literal :=
  requireSome .sourceMaterialization
    s!"literal index {index} out of bounds in {parentLabel}" clause.literals[index]?

/-- 从新 DAG literal 中取出等词原子。 -/
def equalityAtom? (lit : Literal) : Option (Term × Term) :=
  match lit.atom with
  | .equal left right => some (left, right)
  | _ => none

/-- 在材料化阶段立即用新 DAG 的本地 checker 复核证据与 result。 -/
def ensureLocalEvidenceChecks (label : String) (parentIds : Array NodeId)
    (result : SearchClause)
    (evidence : DAGCertificate.LocalRuleEvidence SearchSignature) : Result Unit := do
  let conclusion ← clause result
  if DAGCertificate.LocalRuleEvidence.check parentIds conclusion evidence then
    pure ()
  else
    throw (diagnostic .sourceMaterialization
      s!"{label} local rule witness does not replay to its recorded result")

/-! ## 本地规则材料化 -/

/-- resolution evidence 的 pivot 选择。 -/
def resolutionEvidence (state : MaterializationState)
    (resource : ResolutionResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let left ← parentFromRef state resource.left
  let right ← parentFromRef state resource.right
  let standardizeApart? ←
    match resource.standardizeApart? with
    | some metadata => do
        pure (some (← standardizeApartEvidence state resource.left resource.right metadata))
    | none => pure none
  let leftBaseClause :=
    match standardizeApart? with
    | some evidence => evidence.left.renamed
    | none => left.clause
  let rightBaseClause :=
    match standardizeApart? with
    | some evidence => evidence.right.renamed
    | none => right.clause
  let leftClause := DAGCertificate.Clause.applySubstitution subst leftBaseClause
  let rightClause := DAGCertificate.Clause.applySubstitution subst rightBaseClause
  let leftIndex ← requireLiteralIndex "resolution left pivot" resource.leftLiteralIndex?
  let rightIndex ← requireLiteralIndex "resolution right pivot" resource.rightLiteralIndex?
  let leftLit ← getDagLiteral "resolution left parent after substitution" leftClause leftIndex
  let rightLit ← getDagLiteral "resolution right parent after substitution" rightClause rightIndex
  let pivot := leftLit.atom
  if rightLit.matchesAtom (!leftLit.polarity) pivot then
    let evidence : DAGCertificate.LocalRuleEvidence SearchSignature :=
      match standardizeApart? with
      | some standardizeApart =>
          .standardizedSubstitutedResolution {
            standardizeApart := standardizeApart
            substitution := subst
            pivot := pivot
            leftPolarity := leftLit.polarity
          }
      | none =>
          if subst.isEmpty then
            .resolution {
              left := left
              right := right
              pivot := pivot
              leftPolarity := leftLit.polarity
            }
          else
            .substitutedResolution {
              left := left
              right := right
              substitution := subst
              pivot := pivot
              leftPolarity := leftLit.polarity
            }
    ensureLocalEvidenceChecks "resolution" #[left.id, right.id] resource.result evidence
    pure evidence
  else
    throw (diagnostic .sourceMaterialization
      "resolution indexed pivots are not complementary after first-order materialization")

/-- factoring evidence。 -/
def factoringEvidence (state : MaterializationState)
    (resource : UnaryResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let parent ← parentFromRef state resource.parent
  let firstIndex ← requireLiteralIndex "factoring first literal" resource.literalIndex?
  let secondIndex ← requireLiteralIndex "factoring second literal" resource.otherLiteralIndex?
  if firstIndex == secondIndex then
    throw (diagnostic .sourceMaterialization
      "factoring witness points both occurrences at the same literal index")
  let parentClause := DAGCertificate.Clause.applySubstitution subst parent.clause
  let _ ← getDagLiteral "factoring parent after substitution" parentClause firstIndex
  let _ ← getDagLiteral "factoring parent after substitution" parentClause secondIndex
  let evidence : DAGCertificate.LocalRuleEvidence SearchSignature :=
    if subst.isEmpty then
      .factoring { parent := parent }
    else
      .substitutedFactoring { parent := parent, substitution := subst }
  ensureLocalEvidenceChecks "factoring" #[parent.id] resource.result evidence
  pure evidence

/-- equality-resolution evidence。 -/
def equalityResolutionEvidence (state : MaterializationState)
    (resource : UnaryResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let parent ← parentFromRef state resource.parent
  let literalIndex ←
    requireLiteralIndex "equality-resolution reflexive equality" resource.literalIndex?
  let parentClause := DAGCertificate.Clause.applySubstitution subst parent.clause
  let lit ← getDagLiteral "equality-resolution parent after substitution"
    parentClause literalIndex
  match equalityAtom? lit with
  | some (left, right) =>
      if !lit.polarity && DAGCertificate.StructuralEq.term left right then
        let evidence : DAGCertificate.LocalRuleEvidence SearchSignature :=
          if subst.isEmpty then
            .equalityResolution { parent := parent, left := left, right := right }
          else
            .substitutedEqualityResolution {
              parent := parent
              substitution := subst
              left := left
              right := right
            }
        ensureLocalEvidenceChecks "equality-resolution" #[parent.id] resource.result evidence
        pure evidence
      else
        throw (diagnostic .sourceMaterialization
          "selected equality-resolution literal is not a negative reflexive equality")
  | none =>
      throw (diagnostic .sourceMaterialization
        "selected equality-resolution literal is not an equality atom")

/-- 安全拆分列表，返回前缀、目标元素和后缀。 -/
def splitAt? {α : Type} : List α → Nat → Option (List α × α × List α)
  | [], _ => none
  | head :: rest, 0 => some ([], head, rest)
  | head :: rest, index + 1 => do
      let (before, value, suffix) ← splitAt? rest index
      some (head :: before, value, suffix)

/-- 从旧项和路径构造新 DAG 项上下文及洞中旧项。 -/
partial def termContextAt? (input : SearchTerm) (path : TermPath) :
    Result (DAGCertificate.TermContext SearchSignature × SearchTerm) := do
  match path with
  | [] =>
      pure (.hole, input)
  | index :: rest =>
      match input with
      | .app symbol args =>
          checkFunctionSymbol symbol args.length
          let (before, selected, suffix) ← requireSome .sourceMaterialization
            s!"term path index {index} out of bounds in application {reprStr symbol}" <|
              splitAt? args index
          let (ctx, hole) ← termContextAt? selected rest
          let before' ← before.mapM term
          let suffix' ← suffix.mapM term
          pure (.app symbol before' ctx suffix', hole)
      | .apply .. =>
          throw (diagnostic .sourceMaterialization
            "rewrite position enters higher-order application; first-order DAG rejected it")
      | .lam .. =>
          throw (diagnostic .sourceMaterialization
            "rewrite position enters lambda body; first-order DAG rejected it")
      | _ =>
          throw (diagnostic .sourceMaterialization
            s!"nonempty rewrite path enters non-application term: {reprStr input}")

/-- 从目标 literal 与位置构造原子上下文。 -/
def atomContextAt? (targetLiteral : SearchLiteral)
    (position : PositionedTerm) :
    Result (DAGCertificate.AtomContext SearchSignature × Term × Bool) := do
  match targetLiteral.predicate with
  | .equal =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.equalLeft ctx (← term targetLiteral.right), (← term hole), targetLiteral.positive)
      | .right =>
          let (ctx, hole) ← termContextAt? targetLiteral.right position.path
          pure (.equalRight (← term targetLiteral.left) ctx, (← term hole), targetLiteral.positive)
  | .member =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.rel .member [] ctx [← term targetLiteral.right], (← term hole),
            targetLiteral.positive)
      | .right =>
          let (ctx, hole) ← termContextAt? targetLiteral.right position.path
          pure (.rel .member [← term targetLiteral.left] ctx [], (← term hole),
            targetLiteral.positive)
  | .boolHolds =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.rel .boolHolds [] ctx [], (← term hole), targetLiteral.positive)
      | .right =>
          throw (diagnostic .sourceMaterialization
            "boolHolds right side is metadata in the binary search surface and cannot be rewritten")
  | .definition id arity =>
      match position.side with
      | .left =>
          let (ctx, hole) ← termContextAt? targetLiteral.left position.path
          pure (.rel (.definition id arity) [] ctx [], (← term hole), targetLiteral.positive)
      | .right =>
          throw (diagnostic .sourceMaterialization
            ("definition predicate right side is metadata in the old search literal " ++
              "and cannot be rewritten"))
  | .predicate symbol =>
      match position.side, position.path with
      | .left, index :: rest =>
          let arguments ← projectedPredicateArguments symbol targetLiteral.left
          let (before, selected, suffix) ← requireSome .sourceMaterialization
            s!"predicate argument index {index} out of bounds for {reprStr symbol}" <|
              splitAt? arguments index
          let (ctx, hole) ← termContextAt? selected rest
          pure (.rel (.predicate symbol) (← before.mapM term) ctx
            (← suffix.mapM term), (← term hole), targetLiteral.positive)
      | .left, [] =>
          throw (diagnostic .sourceMaterialization
            ("the predicate tuple wrapper is search metadata and cannot be rewritten " ++
              "as an object term"))
      | .right, _ =>
          throw (diagnostic .sourceMaterialization
            "predicate right side is metadata in the binary search surface and cannot be rewritten")

/-- 重写/叠加 evidence。 -/
def rewriteEvidence (state : MaterializationState)
    (resource : RewriteResource) :
    Result (DAGCertificate.LocalRuleEvidence SearchSignature) := do
  let subst ← termSubstitution resource.substitution
  let equality ← parentFromRef state resource.equality
  let target ← parentFromRef state resource.target
  let standardizeApart? ←
    match resource.standardizeApart? with
    | some metadata => do
        pure (some (← standardizeApartEvidence state resource.equality resource.target metadata))
    | none => pure none
  let rawTargetBase ←
    match resource.standardizeApart? with
    | some metadata => pure metadata.right.renamed
    | none =>
        match resource.target.clause? with
        | some raw => pure raw
        | none =>
            throw (diagnostic .sourceMaterialization
              "rewrite resource does not carry target clause snapshot; cannot rebuild atom context")
  let rawTarget := CoreSyntax.Search.Substitution.applyClause resource.substitution rawTargetBase
  let targetLiteral ← getSearchLiteral "rewrite target parent" rawTarget resource.targetLiteral
  let (context, hole, polarity) ← atomContextAt? targetLiteral resource.targetPosition
  let expectedHole ←
    term (CoreSyntax.Search.Substitution.applyTerm resource.substitution
      resource.targetPosition.term)
  if !(DAGCertificate.StructuralEq.term expectedHole hole) then
    throw (diagnostic .sourceMaterialization
      "rewrite target position snapshot does not match the selected target literal")
  let lhsRaw := CoreSyntax.Search.Substitution.applyTerm resource.substitution resource.orientedLhs
  let rhsRaw := CoreSyntax.Search.Substitution.applyTerm resource.substitution resource.orientedRhs
  let lhs ← term lhsRaw
  let rhs ← term rhsRaw
  if !(DAGCertificate.StructuralEq.term hole lhs) then
    throw (diagnostic .sourceMaterialization
      "rewrite target position is not the substituted oriented lhs")
  let equalityBaseClause :=
    match standardizeApart? with
    | some evidence => evidence.left.renamed
    | none => equality.clause
  let equalityClause := DAGCertificate.Clause.applySubstitution subst equalityBaseClause
  let equalityLiteral ←
    getDagLiteral "rewrite equality parent after substitution"
      equalityClause resource.equalityLiteral
  let equalityReversed ←
    if equalityLiteral.matchesAtom true (.equal lhs rhs) then
      pure false
    else if equalityLiteral.matchesAtom true (.equal rhs lhs) then
      pure true
    else
      throw (diagnostic .sourceMaterialization
        "rewrite equality literal index does not point at either orientation of the equality")
  let evidence : DAGCertificate.RewriteEvidence SearchSignature := {
    equality := equality
    target := target
    context := context
    lhs := lhs
    rhs := rhs
    equalityReversed := equalityReversed
    targetPolarity := polarity
  }
  let substitutedEvidence : DAGCertificate.SubstitutedRewriteEvidence SearchSignature := {
    equality := equality
    target := target
    substitution := subst
    context := context
    lhs := lhs
    rhs := rhs
    equalityReversed := equalityReversed
    targetPolarity := polarity
  }
  let standardizedEvidence? :
      Option (DAGCertificate.StandardizedSubstitutedRewriteEvidence SearchSignature) :=
    standardizeApart?.map fun standardizeApart => {
      standardizeApart := standardizeApart
      substitution := subst
      context := context
      lhs := lhs
      rhs := rhs
      equalityReversed := equalityReversed
      targetPolarity := polarity
    }
  let localEvidence ←
    match resource.kind with
  | .demodulation =>
      if resource.contextual then
        throw (diagnostic .sourceMaterialization
          "contextual demodulation needs a non-unit equality rule in the new DAG evidence")
      else
        match standardizedEvidence? with
        | some standardizedEvidence =>
            pure (.standardizedSubstitutedDemodulation standardizedEvidence)
        | none =>
            if subst.isEmpty then
              pure (.demodulation evidence)
            else
              pure (.substitutedDemodulation substitutedEvidence)
  | .positiveSuperposition =>
      match standardizedEvidence? with
      | some standardizedEvidence =>
          pure (.standardizedSubstitutedPositiveSuperposition standardizedEvidence)
      | none =>
          if subst.isEmpty then
            pure (.positiveSuperposition evidence)
          else
            pure (.substitutedPositiveSuperposition substitutedEvidence)
  | .negativeSuperposition =>
      match standardizedEvidence? with
      | some standardizedEvidence =>
          pure (.standardizedSubstitutedNegativeSuperposition standardizedEvidence)
      | none =>
          if subst.isEmpty then
            pure (.negativeSuperposition evidence)
          else
            pure (.substitutedNegativeSuperposition substitutedEvidence)
  | .contextualDemodulation =>
      throw (diagnostic .sourceMaterialization
        "contextual demodulation is not representable by the current unit demodulation evidence")
  | .extensionalParamodulation =>
      throw (diagnostic .sourceMaterialization
        "extensional paramodulation needs function-theory evidence in the new DAG")
  ensureLocalEvidenceChecks "rewrite/superposition" #[equality.id, target.id]
    resource.result localEvidence
  pure localEvidence

/-- 本地 step witness 到新 DAG 本地规则 payload。 -/
def localRulePayload (state : MaterializationState)
    (witness : LocalStepWitness) :
    Result (DAGCertificate.LocalRulePayload SearchSignature) := do
  let evidence ←
    match witness with
    | .resolution resource =>
        resolutionEvidence state resource
    | .unary resource =>
        match resource.kind with
        | .ordinaryFactoring | .equalityFactoring =>
            factoringEvidence state resource
        | .equalityResolution =>
            equalityResolutionEvidence state resource
        | .booleanExtensionality =>
            throw (diagnostic .sourceMaterialization
              "boolean extensionality needs FOOL-specific DAG evidence")
        | .argumentCongruence =>
            throw (diagnostic .sourceMaterialization
              "argument congruence needs function-theory DAG evidence")
        | .functionExtensionality =>
            throw (diagnostic .sourceMaterialization
              "function extensionality needs function-theory DAG evidence")
    | .rewrite resource =>
        rewriteEvidence state resource
  pure {
    family := evidence.family
    evidence := evidence
    note := "materialized from search local witness"
  }

/-! ## residual CDCL 材料化 -/

/-- 旧 residual CDCL features 重建出的命题链接材料。 -/
structure CdclMaterial where
  atomMap : Array Formula
  justifications : Array (DAGCertificate.PropInitialJustification SearchSignature)

/-- 按 residual feature 重建全局 atom map 与 initial-clause justifications。 -/
def cdclMaterial (state : MaterializationState)
    (summary : CdclResourceSummary) (initialClauses : Array PropResolution.InitialClause) :
    Result CdclMaterial := do
  let mut atoms : Array PropAtom := #[]
  let mut justifications :
    Array (Option (DAGCertificate.PropInitialJustification SearchSignature)) :=
      (List.replicate initialClauses.size none).toArray
  for feature in summary.initialFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL parent feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause then
      throw (diagnostic .residualSplit
        s!"residual CDCL parent feature does not match initial slot {feature.initialIndex}")
    let parentId ← requireSome .residualSplit
      s!"residual CDCL parent id {feature.clauseId} has not been materialized" <|
        state.newId? feature.clauseId
    let parentClause ← requireSome .residualSplit
      s!"residual CDCL parent clause {feature.clauseId} has not been materialized" <|
        state.clause? feature.clauseId
    let translatedSource ← clause feature.sourceClause
    if !parentClause.eq translatedSource then
      throw (diagnostic .residualSplit
        s!"residual CDCL source clause mismatch for parent {feature.clauseId}")
    let mut links : Array (DAGCertificate.PropLiteralLink SearchSignature) := #[]
    for lit in feature.sourceClause do
      let (propLit, atoms') := encodeLiteral atoms lit
      atoms := atoms'
      links := links.push {
        prop := propLit
        object := (← literal lit)
      }
    let link : DAGCertificate.PropParentClauseLink SearchSignature := {
      parent := { id := parentId, clause := parentClause }
      literalLinks := links
    }
    justifications :=
      justifications.set! feature.initialIndex (some (.parentClause link))
  for feature in summary.avatarSkeletonFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL AVATAR skeleton feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk
        initialClauses feature.initialIndex feature.skeleton then
      throw (diagnostic .residualSplit
        s!"residual CDCL AVATAR skeleton does not match initial slot {feature.initialIndex}")
    let splitId ← requireSome .residualSplit
      s!"residual CDCL AVATAR split node {feature.splitId} has not been materialized" <|
        state.newId? feature.splitId
    justifications :=
      justifications.set! feature.initialIndex
        (some (.avatarSkeleton {
          parent := splitId
          skeleton := feature.skeleton
        }))
  for feature in summary.guardActivationFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL guard activation feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause then
      throw (diagnostic .residualSplit
        (s!"residual CDCL guard activation feature does not match initial slot " ++
          s!"{feature.initialIndex}"))
    let parentId ← requireSome .residualSplit
      s!"residual CDCL guard activation parent id {feature.clauseId} has not been materialized" <|
        state.newId? feature.clauseId
    let parentClause ← requireSome .residualSplit
      (s!"residual CDCL guard activation parent clause {feature.clauseId} " ++
        "has not been materialized") <|
        state.clause? feature.clauseId
    let translatedSource ← clause feature.sourceClause
    if !parentClause.eq translatedSource then
      throw (diagnostic .residualSplit
        s!"residual CDCL guard activation source clause mismatch for parent {feature.clauseId}")
    let mut links : Array (DAGCertificate.PropLiteralLink SearchSignature) := #[]
    for lit in feature.sourceClause do
      let (propLit, atoms') := encodeLiteral atoms lit
      atoms := atoms'
      links := links.push {
        prop := propLit
        object := (← literal lit)
      }
    let link : DAGCertificate.PropGuardActivationLink SearchSignature := {
      parent := { id := parentId, clause := parentClause }
      guards := DAGCertificate.canonicalGuards feature.guards
      literalLinks := links
    }
    justifications :=
      justifications.set! feature.initialIndex (some (.guardActivationClause link))
  for feature in summary.learnedFeatures do
    if _hIndex : feature.initialIndex < initialClauses.size then
      if justifications[feature.initialIndex]!.isSome then
        throw (diagnostic .residualSplit
          s!"duplicate residual CDCL initial justification at slot {feature.initialIndex}")
    else
      throw (diagnostic .residualSplit
        s!"residual CDCL learned feature index out of range: {feature.initialIndex}")
    if !SearchDAG.cdclInitialSlotOk initialClauses feature.initialIndex feature.encodedClause then
      throw (diagnostic .residualSplit
        s!"residual CDCL learned feature does not match initial slot {feature.initialIndex}")
    let learnedId ← requireSome .residualSplit
      s!"residual CDCL learned node {feature.learnedNode} has not been materialized" <|
        state.newId? feature.learnedNode
    justifications :=
      justifications.set! feature.initialIndex
        (some (.propLearnedClause {
          parent := learnedId
          clause := PropResolution.canonicalClause feature.encodedClause
        }))
  let mut packed :
      Array (DAGCertificate.PropInitialJustification SearchSignature) := #[]
  for h : index in [:justifications.size] do
    match justifications[index] with
    | some justification =>
        packed := packed.push justification
    | none =>
        throw (diagnostic .residualSplit
          s!"missing residual CDCL initial justification at slot {index}")
  let atomMap ← atoms.mapM PropAtom.toFormula
  pure { atomMap := atomMap, justifications := packed }

/-- residual CDCL payload 材料化。 -/
def residualPayload (state : MaterializationState)
    (payload : ResidualCdclPayload) :
    Result (DAGCertificate.PropositionalClosurePayload SearchSignature) := do
  let material ← cdclMaterial state payload.summary payload.initialClauses
  if payload.initialClauses.size != material.justifications.size then
    throw (diagnostic .residualSplit
      "residual CDCL initial clauses and materialized justifications have different sizes")
  pure <|
    DAGCertificate.PropositionalClosurePayload.ofRaw payload.initialClauses payload.proof
      material.atomMap material.justifications payload.summary.resolutionSteps
      "materialized from residual CDCL"

/-- AVATAR split descriptor 材料化。 -/
def avatarSplitPayload (state : MaterializationState)
    (payload : AvatarSplitPayload) :
    Result (DAGCertificate.AvatarSplitPayload SearchSignature) := do
  pure {
    source := (← parentFromProofParent state payload.source)
    partitions := payload.partitions
    selectors := payload.selectors
    note := payload.note
  }

/-- AVATAR component 引用材料化。 -/
def avatarComponentPayload (state : MaterializationState)
    (payload : AvatarComponentPayload) :
    Result (DAGCertificate.AvatarComponentPayload SearchSignature) := do
  pure {
    split := (← parentFromProofParent state payload.split)
    componentIndex := payload.componentIndex
    note := payload.note
  }

/-- theory-conflict payload 材料化。 -/
def theoryConflictPayload (state : MaterializationState)
    (payload : TheoryConflictPayload) :
    Result (DAGCertificate.TheoryConflictPayload SearchSignature) := do
  pure {
    conflict := (← parentFromProofParent state payload.conflict)
    note := payload.note
  }

/-- propositional learned clause payload 材料化。 -/
def propositionalLearnedClausePayload (state : MaterializationState)
    (payload : PropositionalLearnedClausePayload) :
    Result DAGCertificate.PropositionalLearnedClausePayload := do
  let conflict ← requireSome .residualSplit
    s!"learned-clause conflict node {payload.conflict} has not been materialized" <|
      state.newId? payload.conflict
  pure {
    conflict := conflict
    learned := PropResolution.canonicalClause payload.learned
    note := payload.note
  }

/-! ## 整图材料化入口 -/

/-- 输入 payload 到新 payload。 -/
def payload (problem : ClauseProblem) (state : MaterializationState)
    (info : ClauseInfo) (conclusion : Clause) :
    Result Payload := do
  match info.payload with
  | .source source =>
      if !info.parents.isEmpty then
        throw (diagnostic .sourceMaterialization
          s!"source node {info.id} has nonempty parents")
      let initial ← requireSome .sourceMaterialization
        s!"source node {info.id} references missing initial clause {source.initialIndex}" <|
          problem.initialClauses[source.initialIndex]?
      if conclusion.eq initial then
        pure (.source source.initialIndex)
      else
        throw (diagnostic .sourceMaterialization
          s!"source node {info.id} does not match initial clause {source.initialIndex}")
  | .avatarSplit payload =>
      pure (.avatarSplit (← avatarSplitPayload state payload))
  | .avatarComponent payload =>
      pure (.avatarComponent (← avatarComponentPayload state payload))
  | .localStep witness =>
      if !LocalStepWitness.resultMatches witness info.clause then
        throw (diagnostic .sourceMaterialization
          s!"local witness result does not match clause info at node {info.id}")
      pure (.localRule (← localRulePayload state witness))
  | .theoryConflict payload =>
      pure (.theoryConflict (← theoryConflictPayload state payload))
  | .propositionalLearnedClause payload =>
      pure (.propositionalLearnedClause (← propositionalLearnedClausePayload state payload))
  | .residualCdcl payload =>
      pure (.residualCdcl (← residualPayload state payload))

/-- 单个输入 `ClauseInfo` 材料化为新 DAG node。 -/
def node (problem : ClauseProblem) (state : MaterializationState)
    (info : ClauseInfo) : Result Node := do
  let conclusion ← clause info.clause
  let parents ← info.parents.mapM (fun parent => parentFromProofParent state parent)
  let parentIds := parents.map (fun parent => parent.id)
  let id := state.nodes.size
  let payload ← payload problem state info conclusion
  pure {
    id := id
    parents := parentIds
    ruleTags := payload.ruleTags
    guards := canonicalGuards info.guards
    conclusion := conclusion
    payload := payload
  }

/-- 把拓扑依赖数组材料化成 dense-id 新 DAG。 -/
private def dependencies (problem : ClauseProblem) (root : NodeId)
    (infos : Array ClauseInfo) : Result DAG := do
  let mut state := MaterializationState.emptyWithCapacity infos.size
  for info in infos do
    let node ← node problem state info
    state := state.push info.id node
  let rootId ← requireSome .dagCheck
    s!"root id {root} is not present in the materialized dependency slice" <|
      state.newId? root
  pure {
    problem := problem
    root := rootId
    nodes := state.nodes
  }

/-- 材料化后保留“DAG problem 正是输入 problem”的证据。 -/
structure DAGWithProblem (problem : ClauseProblem) where
  dag : DAG
  problem_eq : dag.problem = problem

/-- 带 problem 等同性的拓扑依赖材料化。 -/
private def dependenciesWithProblem (problem : ClauseProblem) (root : NodeId)
    (infos : Array ClauseInfo) : Result (DAGWithProblem problem) := do
  let mut state := MaterializationState.emptyWithCapacity infos.size
  for info in infos do
    let node ← node problem state info
    state := state.push info.id node
  let rootId ← requireSome .dagCheck
    s!"root id {root} is not present in the materialized dependency slice" <|
      state.newId? root
  pure {
    dag := {
      problem := problem
      root := rootId
      nodes := state.nodes
    }
    problem_eq := rfl
  }

/--
取得可进入材料化的可信 root 切片。

这里统一执行 canonical initial table 对齐与 SearchDAG 全图检查，避免不同材料化出口
分别维护 source 纪律。
-/
private def checkedDependencySlice? (problem : ClauseProblem) (dag : SearchDAG)
    (root : NodeId) : Result (Array ClauseInfo) := do
  dag.ensureInitialClausesMatchProblem problem
  requireSome .dagCheck
    s!"failed to collect checked dependency slice for root {root}" <|
      dag.collectDependencies? root

/-- 从轻量 search-DAG 的指定 root 反向收集依赖并材料化新 DAG。 -/
def materializeRoot? (problem : ClauseProblem) (dag : SearchDAG)
    (root : NodeId) : Result DAG := do
  let infos ← checkedDependencySlice? problem dag root
  dependencies problem root infos

/-- 从轻量 search-DAG 的指定 root 反向收集依赖，并保留 problem 等同性。 -/
def materializeRootWithProblem? (problem : ClauseProblem) (dag : SearchDAG)
    (root : NodeId) : Result (DAGWithProblem problem) := do
  let infos ← checkedDependencySlice? problem dag root
  dependenciesWithProblem problem root infos

/-- 从轻量 search-DAG 当前记录的空字句 root 材料化新 DAG。 -/
def materializeEmpty? (problem : ClauseProblem) (dag : SearchDAG) :
    Result DAG := do
  let root ← requireSome .dagCheck
    "search DAG does not contain an empty-clause root" dag.emptyClause?
  materializeRoot? problem dag root

/-- 从轻量 search-DAG 当前记录的空字句 root 材料化新 DAG，并保留 problem 等同性。 -/
def materializeEmptyWithProblem? (problem : ClauseProblem) (dag : SearchDAG) :
    Result (DAGWithProblem problem) := do
  let root ← requireSome .dagCheck
    "search DAG does not contain an empty-clause root" dag.emptyClause?
  materializeRootWithProblem? problem dag root

/-- 已 checked 且 problem 字段等于调用者输入 problem 的 DAG 证书。 -/
structure CheckedArtifact (problem : ClauseProblem) where
  checked : CheckedDAG
  problem_eq : checked.dag.problem = problem

namespace CheckedArtifact

/-- 已检查 DAG 的审计摘要。 -/
def summary {problem : ClauseProblem}
    (artifact : CheckedArtifact problem) : String :=
  artifact.checked.dag.summary

/-- 当前 guarded soundness artifact 降为任意模型 universe 的后端成功对象。 -/
def guardedBackendSuccessAtForDeepProblem?
    {problem : ClauseProblem}
    (artifact : CheckedArtifact problem) (deepProblem : DeepProblem)
    (hProblem : problem = DAGCertificate.ClauseProblem.ofDeepProblem deepProblem) :
    Result (LogicSoundness.SetLevel.BackendSuccessAt.{x} deepProblem) := do
  if hSupported : artifact.checked.dag.guardedSoundnessSupported = true then
    if hClosed : deepProblem.freeClosed = true then
      pure <| DAGCertificate.CheckedDAG.backendSuccessAt_of_guardedSoundnessSupported
        artifact.checked deepProblem (artifact.problem_eq.trans hProblem)
        (DAGCertificate.DeepProblem.freeClosed_sound hClosed) hSupported
    else
      throw (diagnostic .dagCheck
        "formula problem is not free-closed; direct clause replay is not admissible")
  else
    throw (diagnostic .dagCheck
      ("materialized DAG passed structural checker but contains payloads outside " ++
        "the proved guarded soundness fragment"))

/-- 当前 guarded soundness artifact 降为零 universe 主线后端成功对象。 -/
def guardedBackendSuccessForDeepProblem?
    {problem : ClauseProblem}
    (artifact : CheckedArtifact problem) (deepProblem : DeepProblem)
    (hProblem : problem = DAGCertificate.ClauseProblem.ofDeepProblem deepProblem) :
    Result (LogicSoundness.SetLevel.BackendSuccess deepProblem) :=
  artifact.guardedBackendSuccessAtForDeepProblem? deepProblem hProblem

end CheckedArtifact

/-- 从带 problem 等同性的未检查 DAG 构造 checked artifact。 -/
def checkedArtifact? {problem : ClauseProblem}
    (materialized : DAGWithProblem problem) : Result (CheckedArtifact problem) := do
  if h : materialized.dag.check = true then
    pure {
      checked := { dag := materialized.dag, checked := h }
      problem_eq := materialized.problem_eq
    }
  else
    throw (diagnostic .dagCheck
      s!"materialized DAG failed checker: {materialized.dag.summary}")

/-- 材料化并运行新 DAG checker。 -/
def checkedRoot? (problem : ClauseProblem) (dag : SearchDAG)
    (root : NodeId) : Result CheckedDAG := do
  let dag ← materializeRoot? problem dag root
  match DAGCertificate.CheckedDAG.mk? dag with
  | some checked => pure checked
  | none =>
      throw (diagnostic .dagCheck
        s!"materialized DAG failed checker: {dag.summary}")

/-- 材料化并运行新 DAG checker，同时保留 problem 等同性。 -/
def checkedRootArtifact? (problem : ClauseProblem) (dag : SearchDAG)
    (root : NodeId) : Result (CheckedArtifact problem) := do
  checkedArtifact? (← materializeRootWithProblem? problem dag root)

/-- 从旧空字句 root 材料化并运行新 DAG checker。 -/
def checkedEmpty? (problem : ClauseProblem) (dag : SearchDAG) :
    Result CheckedDAG := do
  let dag ← materializeEmpty? problem dag
  match DAGCertificate.CheckedDAG.mk? dag with
  | some checked => pure checked
  | none =>
      throw (diagnostic .dagCheck
        s!"materialized empty-root DAG failed checker: {dag.summary}")

/-- 从旧空字句 root 材料化并运行新 DAG checker，同时保留 problem 等同性。 -/
def checkedEmptyArtifact? (problem : ClauseProblem) (dag : SearchDAG) :
    Result (CheckedArtifact problem) := do
  checkedArtifact? (← materializeEmptyWithProblem? problem dag)

/-- 材料化、运行 checker，并确认全图落在已证明 guarded soundness 的 payload 片段中。 -/
def checkedSupportedRoot? (problem : ClauseProblem) (dag : SearchDAG)
    (root : NodeId) : Result CheckedDAG := do
  let checked ← checkedRoot? problem dag root
  if checked.dag.guardedSoundnessSupported then
    pure checked
  else
    throw (diagnostic .dagCheck
      ("materialized DAG passed structural checker but contains payloads outside " ++
        "the proved guarded soundness fragment"))

/-- 材料化、运行 checker，并返回可主线消费的 guarded soundness-supported artifact。 -/
def checkedSupportedRootArtifact? (problem : ClauseProblem)
    (dag : SearchDAG)
    (root : NodeId) : Result (CheckedArtifact problem) := do
  let artifact ← checkedRootArtifact? problem dag root
  if artifact.checked.dag.guardedSoundnessSupported then
    pure artifact
  else
    throw (diagnostic .dagCheck
      ("materialized DAG passed structural checker but contains payloads outside " ++
        "the proved guarded soundness fragment"))

/-- 空字句 root 版本的 guarded soundness-supported 检查入口。 -/
def checkedSupportedEmpty? (problem : ClauseProblem) (dag : SearchDAG) :
    Result CheckedDAG := do
  let checked ← checkedEmpty? problem dag
  if checked.dag.guardedSoundnessSupported then
    pure checked
  else
    throw (diagnostic .dagCheck
      ("materialized empty-root DAG passed structural checker but contains payloads outside " ++
        "the proved guarded soundness fragment"))

/-- 空字句 root 版本的 guarded soundness-supported artifact 检查入口。 -/
def checkedSupportedEmptyArtifact? (problem : ClauseProblem)
    (dag : SearchDAG) :
    Result (CheckedArtifact problem) := do
  let artifact ← checkedEmptyArtifact? problem dag
  if artifact.checked.dag.guardedSoundnessSupported then
    pure artifact
  else
    throw (diagnostic .dagCheck
      ("materialized empty-root DAG passed structural checker but contains payloads outside " ++
        "the proved guarded soundness fragment"))

/--
搜索层 residual CDCL 的双层检查入口。

先用 `SearchDAG.addResidualCdclFromSources` 自动生成四类 initial feature 并检查轻量
SearchDAG，再材料化到 `DAGCertificate.CheckedDAG`。通用入口仍只返回普通 guarded
支持片段；完整 AVATAR 证书由 provider 的全局 registry 路线消费。
-/
def checkedResidualCdclFromSources? (problem : ClauseProblem)
    (dag : SearchDAG)
    (sources : Array ClauseInfo)
    (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String := "search residual CDCL") : Result CheckedDAG := do
  let (dag, root) ← dag.addResidualCdclFromSources sources certificate phase
  checkedSupportedRoot? problem dag root.id

/-- residual CDCL 双层检查入口，并保留 problem 等同性供主线 provider 使用。 -/
def checkedResidualCdclFromSourcesArtifact?
    (problem : ClauseProblem) (dag : SearchDAG)
    (sources : Array ClauseInfo)
    (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String := "search residual CDCL") :
    Result (CheckedArtifact problem) := do
  let (dag, root) ← dag.addResidualCdclFromSources sources certificate phase
  checkedSupportedRootArtifact? problem dag root.id

/-! ## 主线 SearchCertificateProvider -/

namespace SearchCertificateProvider

/-- 主线 provider 消费的一次 search-DAG 输入。`root? = none` 表示使用空字句 root。 -/
structure Input where
  dag : SearchDAG
  root? : Option NodeId := none
  label : String := "search-DAG"
  deriving Repr, Lean.ToExpr

/-- 公式问题反模型到 canonical 初始字句有效性的显式 universe-polymorphic 语义桥。 -/
structure RefutationBridgeAt (problem : DeepProblem)
    (clauseProblem : ClauseProblem) : Prop where
  validOfCountermodel :
    ∀ {M : LogicSoundness.SetLevel.StructureAt.{x} SearchSignature}
      (env : LogicSoundness.SetLevel.EnvAt.{x} M),
      Logic.FirstOrder.Theory.Models problem.theory env →
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
          ∃ (target : LogicSoundness.SetLevel.StructureAt.{x} SearchSignature),
            ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
              clauseProblem.Valid targetEnv

/-- 现有 provider 使用的零 universe 反模型 bridge。 -/
abbrev RefutationBridge (problem : DeepProblem)
    (clauseProblem : ClauseProblem) :=
  RefutationBridgeAt.{0} problem clauseProblem

/-- 公式列表的顺序敏感结构比较。 -/
private def formulaListEq : List Formula → List Formula → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      DAGCertificate.StructuralEq.formula left right &&
        formulaListEq leftRest rightRest
  | _, _ => false

private theorem formulaListEq_sound :
    ∀ {left right : List Formula}, formulaListEq left right = true → left = right
  | [], [], _ => rfl
  | left :: leftRest, right :: rightRest, h => by
      simp only [formulaListEq, Bool.and_eq_true_iff] at h
      have hHead :=
        DAGCertificate.StructuralEq.formula_sound left right h.1
      have hRest := formulaListEq_sound h.2
      cases hHead
      cases hRest
      rfl
  | [], _ :: _, h => by
      simp [formulaListEq] at h
  | _ :: _, [], h => by
      simp [formulaListEq] at h

/-- deep problem 的顺序敏感结构比较。 -/
def deepProblemEq (left right : DeepProblem) : Bool :=
  formulaListEq left.premises right.premises &&
    DAGCertificate.StructuralEq.formula left.target right.target

/-- deep problem 结构比较通过时，两侧问题实际相等。 -/
theorem deepProblemEq_sound {left right : DeepProblem}
    (h : deepProblemEq left right = true) : left = right := by
  rcases Bool.and_eq_true_iff.mp h with ⟨hPremises, hTarget⟩
  have hPremisesEq := formulaListEq_sound hPremises
  have hTargetEq :=
    DAGCertificate.StructuralEq.formula_sound left.target right.target hTarget
  cases left
  cases right
  simp only at hPremisesEq hTargetEq
  cases hPremisesEq
  cases hTargetEq
  rfl

/--
checked replay 使用的纯搜索输入。

它只携带 deep problem、canonical clause problem 与搜索 DAG，不包含 preprocessing
证明或语义 bridge。
-/
structure ReplaySearchInput where
  problem : DeepProblem
  clauseProblem : ClauseProblem
  search? : Option Input := none
  label : String := "replayed search-DAG"

namespace ReplaySearchInput

/-- replay 没有提供搜索 DAG 时的明确诊断。 -/
def unsupportedDiagnostic (input : ReplaySearchInput) : Certificate.Diagnostic :=
  diagnostic .clausification
    s!"checked replay for {input.label} did not supply a search DAG/refutation root"

/-- 只执行 search-DAG 材料化，不构造后端 soundness 函数。 -/
def materializeSearch? (input : ReplaySearchInput)
    (unsupported : Certificate.Diagnostic := input.unsupportedDiagnostic) :
    Result (DAGWithProblem input.clauseProblem) :=
  match input.search? with
  | some search =>
      match search.root? with
      | some root =>
          materializeRootWithProblem? input.clauseProblem search.dag root
      | none =>
          materializeEmptyWithProblem? input.clauseProblem search.dag
  | none =>
      throw unsupported

end ReplaySearchInput

/--
预处理后的纯计算输入。

这里故意不携带反模型 bridge，使搜索、材料化和 checker 的成功状态可以独立执行。
-/
structure PreprocessedSearchInput where
  problem : DeepProblem
  clauseProblem : ClauseProblem
  preprocessing : CoreSyntax.NormalForm.CheckedPreprocessing.Checked
  search? : Option Input := none
  label : String := "preprocessed search-DAG"

namespace PreprocessedSearchInput

/-- checked preprocessing 暴露给 provider 的结构 soundness 骨架。 -/
def structuralSound (input : PreprocessedSearchInput) :
    CoreSyntax.NormalForm.CheckedPreprocessing.Sound input.preprocessing.payload :=
  CoreSyntax.NormalForm.CheckedPreprocessing.sound input.preprocessing

/-- 预处理输入降为不含证明字段的 replay search 输入。 -/
def toReplaySearchInput (input : PreprocessedSearchInput) : ReplaySearchInput := {
  problem := input.problem
  clauseProblem := input.clauseProblem
  search? := input.search?
  label := input.label
}

/-- 当前缺少 preprocessing-to-DAG 语义桥时的明确诊断。 -/
def unsupportedDiagnostic (input : PreprocessedSearchInput) : Certificate.Diagnostic :=
  let stats := input.preprocessing.payload.stats
  diagnostic .clausification
    (s!"checked preprocessing accepted for {input.label} " ++
      s!"(clauses={stats.clauses}, literals={stats.literals}, steps={stats.steps}), " ++
      "but no search DAG/refutation root was supplied; structural preprocessing soundness " ++
      "alone is not a semantic backend success")

end PreprocessedSearchInput

/-- replay terminal 已通过的 proof-carrying 数据分类，不包含语义后端函数。 -/
inductive PreparedReplaySearchData (input : ReplaySearchInput) where
  | avatar
      (artifact : CheckedArtifact input.clauseProblem)
      (avatarSupported : artifact.checked.dag.avatarSoundnessSupported = true)
      (registryChecked : artifact.checked.dag.avatarRegistryCheck = true)
  | guarded
      (artifact : CheckedArtifact input.clauseProblem)
      (guardedSupported : artifact.checked.dag.guardedSoundnessSupported = true)

/-- 统一执行 DAG checker 与 capability gate，但尚不构造 soundness consumer。 -/
def prepareReplaySearchData (input : ReplaySearchInput)
    (unsupported : Certificate.Diagnostic := input.unsupportedDiagnostic) :
    Result (PreparedReplaySearchData input) := do
  let materialized ← input.materializeSearch? unsupported
  if hChecked : materialized.dag.check = true then
    let artifact : CheckedArtifact input.clauseProblem := {
      checked := { dag := materialized.dag, checked := hChecked }
      problem_eq := materialized.problem_eq
    }
    if hAvatarSupported :
        artifact.checked.dag.avatarSoundnessSupported = true then
      if hRegistry :
          artifact.checked.dag.avatarRegistryCheck = true then
        pure <| .avatar artifact hAvatarSupported hRegistry
      else
        throw (diagnostic .dagCheck
          ("materialized AVATAR DAG passed the common structural checker " ++
            "but failed the global selector registry checker"))
    else if hGuardedSupported :
        artifact.checked.dag.guardedSoundnessSupported = true then
      pure <| .guarded artifact hGuardedSupported
    else
      throw (diagnostic .dagCheck
        ("materialized preprocessed DAG passed structural checker but contains " ++
          "payloads outside both the proved AVATAR and guarded soundness fragments"))
  else
    throw (diagnostic .dagCheck
      s!"materialized DAG failed checker: {materialized.dag.summary}")

/-- 现有 preprocessing 输入复用同一 replay terminal checker。 -/
abbrev PreparedPreprocessedData (input : PreprocessedSearchInput) :=
  PreparedReplaySearchData input.toReplaySearchInput

/-- preprocessing 包装保留原有缺失搜索时的统计诊断。 -/
def preparePreprocessedData (input : PreprocessedSearchInput) :
    Result (PreparedPreprocessedData input) :=
  prepareReplaySearchData input.toReplaySearchInput input.unsupportedDiagnostic

/--
预处理后的 universe-polymorphic proof-carrying provider 输入。

纯搜索数据与反模型 bridge 分开存放，避免局部证明参数进入计算状态。
-/
structure PreprocessedInputAt where
  search : PreprocessedSearchInput
  bridge : RefutationBridgeAt.{x} search.problem search.clauseProblem

/-- 现有 provider 使用的零 universe 预处理输入。 -/
abbrev PreprocessedInput :=
  PreprocessedInputAt.{0}

/-- 把材料化阶段的 `Except` 结果降为 universe-polymorphic provider 尝试结果。 -/
def attemptOfResultAt {problem : DeepProblem}
    (result : Result (LogicSoundness.SetLevel.BackendSuccessAt.{x} problem)) :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match result with
  | Except.ok success => .success success
  | Except.error diagnostic => .failure diagnostic

/-- 把零 universe 材料化结果降为现有 provider 尝试结果。 -/
def attemptOfResult {problem : DeepProblem}
    (result : Result (LogicSoundness.SetLevel.BackendSuccess problem)) :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  attemptOfResultAt result

/-- 指定 root 的 universe-polymorphic search-DAG provider 尝试。 -/
def runRootAt (problem : DeepProblem) (dag : SearchDAG) (root : NodeId) :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  attemptOfResultAt <| do
    let clauseProblem := DAGCertificate.ClauseProblem.ofDeepProblem problem
    let artifact ← checkedSupportedRootArtifact? clauseProblem dag root
    artifact.guardedBackendSuccessAtForDeepProblem? problem rfl

/-- 指定 root 的零 universe search-DAG provider 尝试。 -/
def runRoot (problem : DeepProblem) (dag : SearchDAG) (root : NodeId) :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runRootAt problem dag root

/-- 空字句 root 的 universe-polymorphic search-DAG provider 尝试。 -/
def runEmptyAt (problem : DeepProblem) (dag : SearchDAG) :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  attemptOfResultAt <| do
    let clauseProblem := DAGCertificate.ClauseProblem.ofDeepProblem problem
    let artifact ← checkedSupportedEmptyArtifact? clauseProblem dag
    artifact.guardedBackendSuccessAtForDeepProblem? problem rfl

/-- 空字句 root 的零 universe search-DAG provider 尝试。 -/
def runEmpty (problem : DeepProblem) (dag : SearchDAG) :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runEmptyAt problem dag

/-- 按输入中的 root 策略运行 universe-polymorphic provider。 -/
def runAt (input : Input) (problem : DeepProblem) :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match input.root? with
  | some root => runRootAt problem input.dag root
  | none => runEmptyAt problem input.dag

/-- 按输入中的 root 策略运行零 universe provider。 -/
def run (input : Input) (problem : DeepProblem) :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runAt input problem

/-- 纯材料化阶段成功后，等待同 universe 反模型 bridge 构造语义后端结果。 -/
structure PreparedPreprocessedAt (input : PreprocessedSearchInput) where
  success :
    RefutationBridgeAt.{x} input.problem input.clauseProblem →
      LogicSoundness.SetLevel.BackendSuccessAt.{x} input.problem

/-- 现有 provider 使用的零 universe 已准备预处理结果。 -/
abbrev PreparedPreprocessed (input : PreprocessedSearchInput) :=
  PreparedPreprocessedAt.{0} input

private theorem artifactValidOfBridgeAt (input : ReplaySearchInput)
    (artifact : CheckedArtifact input.clauseProblem)
    (bridge : RefutationBridgeAt.{x} input.problem input.clauseProblem) :
    ∀ {M : LogicSoundness.SetLevel.StructureAt.{x} SearchSignature}
      (env : LogicSoundness.SetLevel.EnvAt.{x} M),
      Logic.FirstOrder.Theory.Models input.problem.theory env →
        ¬ Logic.FirstOrder.Formula.satisfies env input.problem.target →
          ∃ (target : LogicSoundness.SetLevel.StructureAt.{x} SearchSignature),
            ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
              artifact.checked.dag.problem.Valid targetEnv := by
  intro M env hModels hTarget
  rcases bridge.validOfCountermodel env hModels hTarget with
    ⟨target, targetEnv, hClauseValid⟩
  refine ⟨target, targetEnv, ?_⟩
  rw [artifact.problem_eq]
  exact hClauseValid

/-- 已检查 replay search 数据消费同 universe 反模型 bridge。 -/
def PreparedReplaySearchData.backendSuccessAt
    {input : ReplaySearchInput} (data : PreparedReplaySearchData input)
    (bridge : RefutationBridgeAt.{x} input.problem input.clauseProblem) :
    LogicSoundness.SetLevel.BackendSuccessAt.{x} input.problem :=
  match data with
  | .avatar artifact hAvatarSupported hRegistry =>
      let avatarCert : DAGCertificate.CheckedAvatarDAG := {
        checked := artifact.checked
        registryChecked := hRegistry
      }
      DAGCertificate.CheckedAvatarDAG.backendSuccess_of_avatarSoundnessSupported_of_valid
        avatarCert input.problem hAvatarSupported
        (artifactValidOfBridgeAt input artifact bridge)
  | .guarded artifact hGuardedSupported =>
      artifact.checked.backendSuccessAt_of_guardedSoundnessSupported_of_valid
        input.problem hGuardedSupported
        (artifactValidOfBridgeAt input artifact bridge)

/-- 运行与 soundness bridge 无关的 universe-polymorphic preprocessing/DAG 阶段。 -/
def preparePreprocessedAt (input : PreprocessedSearchInput) :
    Result (PreparedPreprocessedAt.{x} input) :=
  let _structuralSound := input.structuralSound
  match preparePreprocessedData input with
  | Except.error error =>
      .error error
  | Except.ok data =>
      pure {
        success := fun bridge =>
          data.backendSuccessAt bridge
      }

/-- 运行现有零 universe preprocessing/DAG 阶段。 -/
def preparePreprocessed (input : PreprocessedSearchInput) :
    Result (PreparedPreprocessed input) :=
  preparePreprocessedAt input

/-- 纯 replay search 数据与同 universe bridge 组合成 checked provider。 -/
def runReplayMatchedAt (input : ReplaySearchInput)
    (bridge : RefutationBridgeAt.{x} input.problem input.clauseProblem) :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} input.problem :=
  match prepareReplaySearchData input with
  | Except.ok data => .success (data.backendSuccessAt bridge)
  | Except.error error => .failure error

/-- 纯 replay search terminal 是否通过全部 checker。 -/
def runReplayClosed (input : ReplaySearchInput) : Bool :=
  match prepareReplaySearchData input with
  | Except.ok _ => true
  | Except.error _ => false

/-- 纯 replay search provider 的结构化摘要。 -/
def runReplaySummary (input : ReplaySearchInput) : String :=
  match prepareReplaySearchData input with
  | Except.ok _ => "DAG reflection/DAG check: closed"
  | Except.error error => error.label

/-- proof-carrying replay search provider 与纯 closed 标记一致。 -/
theorem runReplayMatchedAt_closed (input : ReplaySearchInput)
    (bridge : RefutationBridgeAt.{x} input.problem input.clauseProblem) :
    LogicSoundness.SetLevel.BackendAttemptAt.closed
        (runReplayMatchedAt input bridge) =
      runReplayClosed input := by
  unfold runReplayMatchedAt runReplayClosed
    LogicSoundness.SetLevel.BackendAttemptAt.closed
  cases prepareReplaySearchData input <;> rfl

/-- 任意模型 universe 下，纯计算 preprocessing/DAG 阶段是否成功。 -/
def runPreprocessedClosedAt (input : PreprocessedSearchInput) : Bool :=
  match preparePreprocessedData input with
  | Except.ok _ => true
  | Except.error _ => false

/-- 零模型 universe 下，纯计算 preprocessing/DAG 阶段是否成功。 -/
def runPreprocessedClosed (input : PreprocessedSearchInput) : Bool :=
  runPreprocessedClosedAt input

/-- 纯计算 preprocessing/DAG 阶段的结构化摘要。 -/
def runPreprocessedSummary (input : PreprocessedSearchInput) : String :=
  match preparePreprocessed input with
  | Except.ok _ => "DAG reflection/DAG check: closed"
  | Except.error error => error.label

/-- 对固定问题运行 capability-closed universe-polymorphic 预处理 DAG provider。 -/
def runPreprocessedMatchedAt (input : PreprocessedInputAt.{x}) :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} input.search.problem :=
  match preparePreprocessedAt input.search with
  | Except.ok prepared => .success (prepared.success input.bridge)
  | Except.error error => .failure error

/-- 对固定问题运行现有零 universe 预处理 DAG provider。 -/
def runPreprocessedMatched (input : PreprocessedInput) :
    LogicSoundness.SetLevel.BackendAttempt input.search.problem :=
  runPreprocessedMatchedAt input

/-- universe-polymorphic proof-carrying provider 的闭合状态等于纯材料化结果。 -/
theorem runPreprocessedMatchedAt_closed (input : PreprocessedInputAt.{x}) :
    LogicSoundness.SetLevel.BackendAttemptAt.closed
        (runPreprocessedMatchedAt input) =
      runPreprocessedClosedAt input.search := by
  unfold runPreprocessedMatchedAt runPreprocessedClosedAt preparePreprocessedAt
    LogicSoundness.SetLevel.BackendAttemptAt.closed
  cases preparePreprocessedData input.search with
  | error error =>
      rfl
  | ok data =>
      rfl

/-- 零 universe proof-carrying provider 的闭合状态等于纯材料化结果。 -/
theorem runPreprocessedMatched_closed (input : PreprocessedInput) :
    LogicSoundness.SetLevel.BackendAttempt.closed (runPreprocessedMatched input) =
      runPreprocessedClosed input.search :=
  runPreprocessedMatchedAt_closed input

/-- universe-polymorphic 运行时问题必须与预处理输入记录的问题完全一致。 -/
def runPreprocessedAt (input : PreprocessedInputAt.{x}) (problem : DeepProblem) :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  if hProblem : deepProblemEq problem input.search.problem = true then
    have hEq : problem = input.search.problem := deepProblemEq_sound hProblem
    hEq.symm ▸ runPreprocessedMatchedAt input
  else
    .failure <| diagnostic .clausification
      "preprocessed source problem does not match the provider deep problem"

/-- 零 universe 运行时问题必须与预处理输入记录的问题完全一致。 -/
def runPreprocessed (input : PreprocessedInput) (problem : DeepProblem) :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runPreprocessedAt input problem

/-- 可放入 `ProviderAt.runAll` 的 universe-polymorphic search-DAG provider。 -/
def providerAt (input : Input) :
    LogicSoundness.SetLevel.ProviderAt.{x} SearchSignature where
  name := input.label
  backend := .dagReflection
  run := fun problem => runAt input problem

/-- 可放入现有 `Provider.runAll` 的零 universe search-DAG provider。 -/
def provider (input : Input) :
    LogicSoundness.SetLevel.Provider SearchSignature :=
  providerAt input

/-- 可放入 `ProviderAt.runAll` 的 universe-polymorphic checked-preprocessing provider。 -/
def preprocessedProviderAt (input : PreprocessedInputAt.{x}) :
    LogicSoundness.SetLevel.ProviderAt.{x} SearchSignature where
  name := input.search.label
  backend := .dagReflection
  run := fun problem => runPreprocessedAt input problem

/-- 可放入现有 `Provider.runAll` 的零 universe checked-preprocessing provider。 -/
def preprocessedProvider (input : PreprocessedInput) :
    LogicSoundness.SetLevel.Provider SearchSignature :=
  preprocessedProviderAt input

/-- 直接运行 universe-polymorphic search-DAG provider 并尝试取出成功对象。 -/
def solveAt? (input : Input) (problem : DeepProblem) :
    Option (LogicSoundness.SetLevel.BackendSuccessAt.{x} problem) :=
  LogicSoundness.SetLevel.BackendAttemptAt.success? (runAt input problem)

/-- 直接运行零 universe search-DAG provider 并尝试取出成功对象。 -/
def solve? (input : Input) (problem : DeepProblem) :
    Option (LogicSoundness.SetLevel.BackendSuccess problem) :=
  solveAt? input problem

/-- 直接运行 universe-polymorphic checked-preprocessing provider。 -/
def solvePreprocessedAt? (input : PreprocessedInputAt.{x}) (problem : DeepProblem) :
    Option (LogicSoundness.SetLevel.BackendSuccessAt.{x} problem) :=
  LogicSoundness.SetLevel.BackendAttemptAt.success? (runPreprocessedAt input problem)

/-- 直接运行零 universe checked-preprocessing provider。 -/
def solvePreprocessed? (input : PreprocessedInput) (problem : DeepProblem) :
    Option (LogicSoundness.SetLevel.BackendSuccess problem) :=
  solvePreprocessedAt? input problem

/--
residual CDCL 直连接口：搜索层给出 source 切片和 checked UNSAT payload，
provider 自动生成四类 CDCL initial 节点。该直接接口保持普通 guarded 语义；
AVATAR skeleton 由预处理 provider 的全局 registry 路线消费。
-/
def runResidualCdclFromSourcesAt (problem : DeepProblem) (dag : SearchDAG)
    (sources : Array ClauseInfo)
    (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String := "search residual CDCL") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  attemptOfResultAt <| do
    let clauseProblem := DAGCertificate.ClauseProblem.ofDeepProblem problem
    let artifact ←
      checkedResidualCdclFromSourcesArtifact?
        clauseProblem dag sources certificate phase
    artifact.guardedBackendSuccessAtForDeepProblem? problem rfl

/-- residual CDCL 的零 universe 直连接口。 -/
def runResidualCdclFromSources (problem : DeepProblem) (dag : SearchDAG)
    (sources : Array ClauseInfo)
    (certificate : PropResolution.CheckedUnsatCertificate)
    (phase : String := "search residual CDCL") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runResidualCdclFromSourcesAt problem dag sources certificate phase

end SearchCertificateProvider

end SearchMaterialization
end Automation
end YesMetaZFC
