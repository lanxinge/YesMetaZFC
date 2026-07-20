import YesMetaZFC.Automation.PropCdcl
import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Automation.Superposition
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.Data.CanonicalSeedWorkspace
import YesMetaZFC.Automation.LazyDefinitionRegistry
import YesMetaZFC.Automation.Data.CertificateWorkspace

/-!
# AVATAR 一阶饱和 / CDCL 双核协调器

本模块实现搜索期的正统 AVATAR 数据流：

1. 每个输入字句按变量连通性拆成 components；
2. 跨 source 复用结构相同的 component selector；
3. SAT 层持有 source 的 component 析取 skeleton；
4. 一阶层只在当前 assignment 激活的 support 上运行 given-clause；
5. guarded empty `Γ ⟹ ⊥` 立即学习为命题字句 `¬Γ`；
6. 同一个 CDCL machine 与同一个一阶 clause/proof arena 跨轮保留。

component splitting 已通过独立 split descriptor/component payload 接入 SearchDAG 与
最终 DAG checker；它绝不把 component 伪装成 canonical source。对象模型诱导 selector
valuation 的整图 soundness 仍由后续专用 AVATAR 归纳负责。
-/

namespace YesMetaZFC
namespace Automation
namespace Avatar

abbrev Clause := CoreSyntax.Search.Clause
abbrev GuardSet := Superposition.GuardSet
abbrev ComponentId := Nat

/-- 一个输入字句中的 component 来源。 -/
structure ComponentOrigin where
  sourceIndex : Nat
  literalIndices : Array Nat
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 跨 source intern 后的稳定 AVATAR component。 -/
structure Component where
  id : ComponentId
  guard : PropResolution.Lit
  clause : Clause
  origins : Array ComponentOrigin := #[]
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 一个 source 字句的 component 分解。 -/
structure SourceSplit where
  sourceIndex : Nat
  original : Clause
  partitions : Array (Array Nat)
  components : Array ComponentId
  selectors : PropResolution.Clause
  skeleton : PropResolution.Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 一个保留 canonical source 编号、初始关闭的 lazy definition split。 -/
structure LazySource where
  sourceIndex : Nat
  clause : Clause
  components : Array ComponentId
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- AVATAR 前端固定下来的 component table 与命题 skeleton。 -/
structure Problem where
  initialClauses : Array Clause
  objectAtomCount : Nat
  components : Array Component
  sourceSplits : Array SourceSplit
  lazySources : Array LazySource := #[]
  sourceArenaSlots : Array (Array Superposition.ClauseId) := #[]
  seedSlots : Array Nat := #[]
  lazyDefinitions? : Option LazyDefinitionRegistry.Payload := none
  propClauses : Array PropResolution.Clause
  numVars : Nat
  deriving Repr, Inhabited, Lean.ToExpr

private def pushNatUnique (values : Array Nat) (value : Nat) : Array Nat :=
  if values.contains value then values else values.push value

/-- 一个搜索项中的 typed 自由变量。 -/
abbrev termVars := AvatarSplit.termVars

/-- 一个 literal 中的 typed 自由变量。 -/
abbrev literalVars := AvatarSplit.literalVars

/-- 两个变量集合是否相交。 -/
abbrev varsOverlap := AvatarSplit.varsOverlap

/-- 按索引抽取一个 component clause。 -/
abbrev clauseAtIndices := AvatarSplit.clauseAtIndices

/-- 按变量连通性拆分字句。 -/
abbrev splitClause := AvatarSplit.splitClause

/-- 统计所有 source clauses 中实际出现的对象命题原子。 -/
def objectAtomCount (clauses : Array Clause) : Nat :=
  Id.run do
    let mut atoms : Array SearchMaterialization.PropAtom := #[]
    for clause in clauses do
      let (_, next) := SearchMaterialization.encodePropClause atoms clause
      atoms := next
    return atoms.size

private def findComponent? (components : Array Component) (clause : Clause) :
    Option ComponentId := Id.run do
  for h : index in [:components.size] do
    if CoreSyntax.Search.clauseEq components[index].clause clause then
      return some index
  return none

private def addOrigin (component : Component) (origin : ComponentOrigin) : Component :=
  if component.origins.contains origin then
    component
  else
    { component with origins := component.origins.push origin }

/-- intern 一个 component，并追加其 source origin。 -/
def internComponent (guardBase : Nat) (components : Array Component)
    (clause : Clause) (origin : ComponentOrigin) :
    Array Component × ComponentId :=
  match findComponent? components clause with
  | some id =>
      let component := components[id]!
      (components.set! id (addOrigin component origin), id)
  | none =>
      let id := components.size
      let component : Component := {
        id := id
        guard := { var := guardBase + id, positive := true }
        clause := clause
        origins := #[origin]
      }
      (components.push component, id)

private def Problem.buildWithSlots (initialClauses : Array Clause)
    (seedSlots : Array Nat)
    (lazyDefinitions? : Option LazyDefinitionRegistry.Payload) : Problem :=
  Id.run do
    let initialClauses := initialClauses.map Redundancy.normalizeClause
    let guardBase := Avatar.objectAtomCount initialClauses
    let mut components : Array Component := #[]
    let mut sourceSplits : Array SourceSplit := #[]
    let mut propClauses : Array PropResolution.Clause := #[]
    let mut sourceArenaSlots :=
      (List.replicate initialClauses.size #[]).toArray
    for h : sourceIndex in [:initialClauses.size] do
      let original := initialClauses[sourceIndex]
      let mut componentIds := #[]
      let mut partitions := #[]
      for split in splitClause original do
        let origin : ComponentOrigin := {
          sourceIndex := sourceIndex
          literalIndices := split.1
        }
        let (next, id) := internComponent guardBase components split.2 origin
        components := next
        partitions := partitions.push split.1
        componentIds := pushNatUnique componentIds id
      let selectors :=
        componentIds.filterMap fun id =>
          components[id]?.map (fun component => component.guard)
      let skeleton := PropResolution.canonicalClause selectors
      sourceSplits := sourceSplits.push {
        sourceIndex := sourceIndex
        original := original
        partitions := partitions
        components := componentIds
        selectors := selectors
        skeleton := skeleton
      }
      sourceArenaSlots := sourceArenaSlots.set! sourceIndex componentIds
      propClauses := propClauses.push skeleton
    let lazySlots :=
      match lazyDefinitions? with
      | some registry => registry.lazySlots
      | none => #[]
    let mut lazySources : Array LazySource := #[]
    for h : sourceIndex in [:initialClauses.size] do
      if lazySlots.contains sourceIndex then
        lazySources := lazySources.push {
          sourceIndex := sourceIndex
          clause := initialClauses[sourceIndex]
          components := sourceArenaSlots.getD sourceIndex #[]
        }
    return {
      initialClauses := initialClauses
      objectAtomCount := guardBase
      components := components
      sourceSplits := sourceSplits
      lazySources := lazySources
      sourceArenaSlots := sourceArenaSlots
      seedSlots := seedSlots
      lazyDefinitions? := lazyDefinitions?
      propClauses := propClauses
      numVars := guardBase + components.size
    }

/-- 从 canonical input clause table 建立普通 AVATAR component problem。 -/
def Problem.build (initialClauses : Array Clause) : Problem :=
  Problem.buildWithSlots initialClauses
    (List.range initialClauses.size).toArray none

/-- 从 checked registry 建立 seed/lazy 分流后的 AVATAR problem。 -/
def Problem.buildWithLazyDefinitions
    (registry : LazyDefinitionRegistry.Checked) : Problem :=
  Problem.buildWithSlots registry.payload.initialClauses
    registry.payload.seedSlots (some registry.payload)

namespace Problem

/-- 一阶搜索层消费的 dormant guarded component arena。 -/
def guardedComponents (problem : Problem) : Array Superposition.GuardedClause :=
  problem.components.map fun component => {
    guards := #[component.guard]
    clause := component.clause
  }

/-- persistent saturation 的固定输入前缀始终使用 canonical AVATAR components。 -/
def guardedArenaInputs (problem : Problem) : Array Superposition.GuardedClause :=
  problem.guardedComponents

/--
固定输入前缀的初始开放掩码。

只要一个 interned component 至少有一个 seed source origin，它就从第一轮开始开放。
-/
def initialEnabled (problem : Problem) : Array Bool :=
  problem.components.map fun component =>
    component.origins.any fun origin =>
      problem.seedSlots.contains origin.sourceIndex

/-- saturation 固定输入前缀的长度。 -/
def arenaInputSize (problem : Problem) : Nat :=
  problem.components.size

/-- 一个最终 given clause 触发的 lazy source arena ids。 -/
def lazyArenaIdsForClause (problem : Problem) (clause : Clause) :
    Array Superposition.ClauseId :=
  match problem.lazyDefinitions? with
  | none => #[]
  | some registry =>
      clause.foldl
        (fun ids literal =>
          (registry.slotsForLiteral literal).foldl
            (fun ids slot =>
              match problem.sourceArenaSlots[slot]? with
              | some sourceIds => sourceIds.foldl pushNatUnique ids
              | none => ids)
            ids)
        #[]

/-- 在 generation 前按最终 given 文字幂等开放对应的 lazy definition sources。 -/
def enableLazySourcesForGiven (problem : Problem)
    (supportIsActive : GuardSet → Bool) (state : Superposition.State)
    (given : Superposition.PassiveEntry) : Superposition.State :=
  match state.clauses[given.clauseId]? with
  | some clause =>
      state.enableClausesSupported (problem.lazyArenaIdsForClause clause)
        supportIsActive
  | none => state

/-- SAT skeleton 使用的带来源 initial clauses。 -/
def propInitialClauses (problem : Problem) :
    Array PropResolution.InitialClause :=
  problem.sourceSplits.map fun split => {
    clause := split.skeleton
    origin := .residual split.sourceIndex
  }

/-- AVATAR 搜索开始前固定下来的 SearchDAG source/split/component 节点表。 -/
structure SearchSeed where
  dag : SearchMaterialization.SearchDAG
  sourceNodes : Array SearchMaterialization.ClauseInfo
  splitNodes : Array SearchMaterialization.ClauseInfo
  componentNodes : Array SearchMaterialization.ClauseInfo

/--
把 AVATAR problem 的 canonical source table 自动物化为轻量 SearchDAG。

同一个 interned component 只建立一个节点；它可以被多个 source skeleton 复用，但其
split 来源固定为首次出现的 source descriptor。
-/
def searchSeed? (problem : Problem) : Option SearchSeed := do
  let mut dag := SearchMaterialization.SearchDAG.ofInitialClauses problem.initialClauses
  let mut workspace :=
    Data.CanonicalSeedWorkspace.emptyWithCapacity
      problem.sourceSplits.size problem.sourceSplits.size problem.components.size
  for h : splitIndex in [:problem.sourceSplits.size] do
    let split := problem.sourceSplits[splitIndex]
    if workspace.sourceIsUsed split.sourceIndex || workspace.splitIsUsed splitIndex then
      none
    else
      let (nextDag, source) ←
        dag.addSourceKnownUnused? #[] split.sourceIndex
      dag := nextDag
      let nextWorkspace ← workspace.registerSource? split.sourceIndex source.id
      workspace := nextWorkspace
      let (nextDag, splitNode) ←
        dag.addAvatarSplitKnownUnused? source split.partitions split.selectors
      dag := nextDag
      let nextWorkspace ← workspace.registerSplit? splitIndex splitNode.id
      workspace := nextWorkspace
      if split.components.size != split.partitions.size then
        none
      else
        for h : localIndex in [:split.components.size] do
          let componentId := split.components[localIndex]
          match workspace.componentNode? componentId with
          | some _ => pure ()
          | none =>
              let (nextDag, componentNode) ←
                dag.addAvatarComponentKnownUnused? splitNode localIndex
              let component ← problem.components[componentId]?
              if CoreSyntax.Search.clauseEq componentNode.clause component.clause then
                let nextWorkspace ←
                  workspace.registerComponent? componentId componentNode.id
                dag := nextDag
                workspace := nextWorkspace
              else
                none
  let mut sourceNodes : Array SearchMaterialization.ClauseInfo := #[]
  for split in problem.sourceSplits do
    let sourceId ← workspace.sourceNode? split.sourceIndex
    let source ← dag.get? sourceId
    sourceNodes := sourceNodes.push source
  let mut splitNodes : Array SearchMaterialization.ClauseInfo := #[]
  for h : splitIndex in [:problem.sourceSplits.size] do
    let splitId ← workspace.splitNode? splitIndex
    let splitNode ← dag.get? splitId
    splitNodes := splitNodes.push splitNode
  let mut componentNodes : Array SearchMaterialization.ClauseInfo := #[]
  for h : componentId in [:problem.components.size] do
    let componentNodeId ← workspace.componentNode? componentId
    let componentNode ← dag.get? componentNodeId
    componentNodes := componentNodes.push componentNode
  pure {
    dag := dag
    sourceNodes := sourceNodes
    splitNodes := splitNodes
    componentNodes := componentNodes
  }

end Problem

/-- assignment 中一个命题 literal 是否为真。 -/
def literalTrue (assignment : Array (Option Bool)) (literal : PropResolution.Lit) : Bool :=
  match assignment.getD literal.var none with
  | some value => if literal.positive then value else !value
  | none => false

/-- 当前 assignment 是否激活整个 guard support。 -/
def supportActive (assignment : Array (Option Bool)) (guards : GuardSet) : Bool :=
  guards.all (literalTrue assignment)

/-- guarded empty 产生的 theory conflict 证据。 -/
structure TheoryConflict where
  clauseId : Superposition.ClauseId
  guards : GuardSet
  learned : PropResolution.Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 跨 SAT 模型持久保留的一阶搜索状态。 -/
structure TheoryState where
  saturation : Superposition.State
  lastAssignment : Array (Option Bool) := #[]
  deriving Repr, Lean.ToExpr

/-- AVATAR 双核配置。 -/
structure Config where
  saturation : Redundancy.Config := {}
  cdcl : PropCdcl.Incremental.Config := {}
  theoryFuelPerModel : Nat := 256
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- theory state 中当前 assignment 已激活的第一个 empty support。 -/
def firstActiveConflictFrom? (state : Superposition.State)
    (assignment : Array (Option Bool))
    (cursor : Data.ClauseMetadataTable.RetainedEmptyCursor) :
    Data.ClauseMetadataTable.RetainedEmptyCursor × Option TheoryConflict :=
  state.clauseMetadata.foldRetainedEmptyFromUntil cursor none fun _ id =>
    if state.enabledAt id then
      match state.clauses[id]?, state.guardsAt? id with
      | some clause, some guards =>
          if clause.isEmpty && supportActive assignment guards then
            .done <| some {
              clauseId := id
              guards := guards
              learned := PropResolution.canonicalClause (guards.map PropResolution.Lit.neg)
            }
          else
            .next none
      | _, _ => .next none
    else
      .next none

/-- theory state 中当前 assignment 已激活的第一个 empty support。 -/
def firstActiveConflict? (state : Superposition.State)
    (assignment : Array (Option Bool)) : Option TheoryConflict :=
  (firstActiveConflictFrom? state assignment {}).2

/-- theory conflict 是否满足 CDCL callback 的显式协议。 -/
def TheoryConflict.check (state : Superposition.State)
    (assignment : Array (Option Bool)) (conflict : TheoryConflict) : Bool :=
  state.enabledAt conflict.clauseId && state.retained conflict.clauseId &&
    match state.clauses[conflict.clauseId]?, state.guardsAt? conflict.clauseId with
    | some clause, some guards =>
        clause.isEmpty &&
          SearchMaterialization.guardSetEq guards conflict.guards &&
            supportActive assignment conflict.guards &&
              PropResolution.clauseEq conflict.learned
                (PropResolution.canonicalClause
                  (conflict.guards.map PropResolution.Lit.neg))
    | _, _ => false

/-- 在一个 SAT 模型下运行增量 given-clause，直到 conflict、饱和或 fuel 耗尽。 -/
def saturateModel (config : Config) (problem : Problem)
    (assignment : Array (Option Bool)) :
    Nat → Redundancy.WorkBudget → Superposition.State →
      Data.ClauseMetadataTable.RetainedEmptyCursor →
      Superposition.State × Data.ClauseMetadataTable.RetainedEmptyCursor ×
        Option TheoryConflict × Bool
  | 0, _, state, cursor =>
      let (cursor, conflict?) := firstActiveConflictFrom? state assignment cursor
      (state, cursor, conflict?, false)
  | fuel + 1, budget, state, cursor =>
      let (cursor, conflict?) := firstActiveConflictFrom? state assignment cursor
      match conflict? with
      | some conflict => (state, cursor, some conflict, true)
      | none =>
          match Superposition.State.selectGiven? config.saturation state with
          | some (given, state) =>
              let step :=
                Superposition.State.processGivenWith config.saturation state given budget
                  (problem.enableLazySourcesForGiven (supportActive assignment))
              if step.complete then
                saturateModel config problem assignment fuel step.budget step.state cursor
              else
                (step.state, cursor, none, false)
          | none => (state, cursor, none, true)

/-- 一个 selector assignment 下的 saturation 轮次结果。 -/
structure TheoryRoundResult where
  state : TheoryState
  conflict? : Option TheoryConflict
  complete : Bool
  deriving Repr, Lean.ToExpr

/-- 在一个 selector assignment 下运行持久 saturation arena。 -/
def runTheoryRound (config : Config) (problem : Problem) (state : TheoryState)
    (assignment : Array (Option Bool)) : TheoryRoundResult :=
  let seeded :=
    state.saturation.reseed assignment (supportActive assignment)
  let (saturation, _, conflict?, complete) :=
    saturateModel config problem assignment config.theoryFuelPerModel
      (Redundancy.WorkBudget.ofConfig config.saturation seeded.lifecycle.work) seeded {}
  {
    state := { saturation := saturation, lastAssignment := assignment }
    conflict? := conflict?
    complete := complete
  }

namespace TheoryRoundResult

/-- 把 saturation 轮次转换成 CDCL 消费的显式 TheoryResponse。 -/
def toTheoryResponse (round : TheoryRoundResult)
    (assignment : Array (Option Bool)) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  match round.conflict? with
  | some conflict =>
      if conflict.check round.state.saturation assignment then
        .conflict round.state conflict.learned conflict
      else
        .unknown round.state
          "AVATAR theory conflict failed the selector/guard protocol checker"
  | none =>
      if round.complete then
        .model round.state
      else
        .unknown round.state "AVATAR theory saturation exhausted its per-model fuel"

end TheoryRoundResult

/-- 一个 SAT 模型上的 AVATAR theory callback。 -/
def theoryStep (config : Config) (problem : Problem) (state : TheoryState)
    (assignment : Array (Option Bool)) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  (runTheoryRound config problem state assignment).toTheoryResponse assignment

/-- 完整 AVATAR 双核搜索结果。 -/
structure RunResult where
  problem : Problem
  search :
    PropCdcl.Incremental.RunResult TheoryState TheoryConflict

/-- AVATAR 双核搜索的结构化性能指标。 -/
structure Metrics where
  sourceClauses : Nat
  components : Nat
  saturationProcessed : Nat
  generatedCandidates : Nat
  checkedCandidates : Nat
  retainedCandidates : Nat
  ruleRejectedCandidates : Nat
  retentionRejectedCandidates : Nat
  indexedBatches : Nat
  indexedBatchHits : Nat
  indexedCandidates : Nat
  workConsumed : Nat
  workExhaustions : Nat
  indexOccurrences : Nat
  indexMaintenanceSteps : Nat
  termPositions : Nat
  inferenceAttempts : Nat
  unificationAttempts : Nat
  localChecks : Nat
  retentionChecks : Nat
  subsumptionNodes : Nat
  backwardDeletionChecks : Nat
  forwardSimplificationSteps : Nat
  activatedClauses : Nat
  deletedClauses : Nat
  arenaInitial : Nat
  arenaFinal : Nat
  arenaGrowth : Nat
  theoryRounds : Nat
  theoryClauses : Nat
  cdclDecisions : Nat
  cdclConflicts : Nat
  cdclPropagations : Nat
  cdclBacktracks : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Metrics

/-- 索引辅助 generator 批次命中率的千分比。 -/
def indexedBatchHitPermille (metrics : Metrics) : Nat :=
  if metrics.indexedBatches == 0 then
    0
  else
    metrics.indexedBatchHits * 1000 / metrics.indexedBatches

end Metrics

/-- 运行一个已经固定 source/component/lazy 布局的常驻 AVATAR/CDCL 双核搜索。 -/
private def runProblem (config : Config) (problem : Problem) : RunResult :=
  let theoryState : TheoryState := {
    saturation :=
      Superposition.State.dormantWithEnabled config.saturation
        problem.guardedArenaInputs problem.initialEnabled
  }
  {
    problem := problem
    search :=
      PropCdcl.Incremental.run config.cdcl problem.numVars problem.propClauses
        theoryState (theoryStep config problem)
  }

/-- 运行普通的常驻 AVATAR/CDCL 双核搜索。 -/
def run (config : Config) (initialClauses : Array Clause) : RunResult :=
  runProblem config (Problem.build initialClauses)

/-- 运行带 checked search-time lazy definition registry 的 AVATAR/CDCL 双核搜索。 -/
def runWithLazyDefinitions (config : Config)
    (registry : LazyDefinitionRegistry.Checked) : RunResult :=
  runProblem config (Problem.buildWithLazyDefinitions registry)

namespace RunResult

/-- 从最终双核状态提取观察指标。 -/
def metrics (result : RunResult) : Metrics :=
  let saturation := result.search.state.saturation
  let lifecycle := saturation.lifecycle
  {
    sourceClauses := result.problem.initialClauses.size
    components := result.problem.components.size
    saturationProcessed := saturation.processed
    generatedCandidates := lifecycle.generatedCandidates
    checkedCandidates := lifecycle.checkedCandidates
    retainedCandidates := lifecycle.retainedCandidates
    ruleRejectedCandidates := lifecycle.ruleRejectedCandidates
    retentionRejectedCandidates := lifecycle.retentionRejectedCandidates
    indexedBatches := lifecycle.indexedBatches
    indexedBatchHits := lifecycle.indexedBatchHits
    indexedCandidates := lifecycle.indexedCandidates
    workConsumed := lifecycle.work.consumed
    workExhaustions := lifecycle.workExhaustions
    indexOccurrences := lifecycle.work.indexOccurrences
    indexMaintenanceSteps := lifecycle.work.indexMaintenanceSteps
    termPositions := lifecycle.work.termPositions
    inferenceAttempts := lifecycle.work.inferenceAttempts
    unificationAttempts := lifecycle.work.unificationAttempts
    localChecks := lifecycle.work.localChecks
    retentionChecks := lifecycle.work.retentionChecks
    subsumptionNodes := lifecycle.work.subsumptionNodes
    backwardDeletionChecks := lifecycle.work.backwardDeletionChecks
    forwardSimplificationSteps := lifecycle.work.forwardSimplificationSteps
    activatedClauses := lifecycle.activatedClauses
    deletedClauses := lifecycle.deletedClauses
    arenaInitial := result.problem.arenaInputSize
    arenaFinal := saturation.clauses.size
    arenaGrowth := saturation.steps.size
    theoryRounds := result.search.theoryRounds
    theoryClauses := result.search.theoryClauses.size
    cdclDecisions := result.search.stats.decisions
    cdclConflicts := result.search.stats.conflicts
    cdclPropagations := result.search.stats.propagations
    cdclBacktracks := result.search.stats.backtracks
  }

/-- 重建与本次搜索 problem 对齐的 canonical SearchDAG source/split/component 前缀。 -/
def searchSeed? (result : RunResult) : Option Problem.SearchSeed :=
  result.problem.searchSeed?

/-- persistent saturation arena 到 SearchDAG 的 proof materialization 结果。 -/
structure ProofMaterialization where
  dag : SearchMaterialization.SearchDAG
  arenaToSearch : Array (Option SearchMaterialization.NodeId)
  splitNodes : Array SearchMaterialization.ClauseInfo
  conflictProofNodes : Array SearchMaterialization.ClauseInfo
  deriving Repr

/-- theory conflict、learned clause 与最终 residual-CDCL root 的完整材料化结果。 -/
structure CertificateMaterialization where
  dag : SearchMaterialization.SearchDAG
  arenaToSearch : Array (Option SearchMaterialization.NodeId)
  splitNodes : Array SearchMaterialization.ClauseInfo
  conflictProofNodes : Array SearchMaterialization.ClauseInfo
  theoryConflictNodes : Array SearchMaterialization.ClauseInfo
  learnedClauseNodes : Array SearchMaterialization.ClauseInfo
  root : SearchMaterialization.ClauseInfo
  deriving Repr

private def arenaShapeAligned (result : RunResult) : Bool := Id.run do
  let state := result.search.state.saturation
  let inputSize := result.problem.arenaInputSize
  if state.clauses.size != inputSize + state.steps.size ||
      state.guards.size != state.clauses.size ||
      state.enabled.size != state.clauses.size ||
      !state.clauseMetadata.alignedWith state.clauses.size then
    return false
  for h : id in [:result.problem.components.size] do
    match result.problem.components[id]?, state.clauses[id]?, state.guardsAt? id with
    | some component, some clause, some guards =>
        if !CoreSyntax.Search.clauseEq component.clause clause ||
            !SearchMaterialization.guardSetEq guards #[component.guard] then
          return false
    | _, _, _ => return false
  for h : index in [:state.steps.size] do
    let id := inputSize + index
    let step := state.steps[index]
    if !state.enabledAt id || !step.rule.parents.all (fun parent => parent < id) then
      return false
    match state.clauses[id]?, state.guardsAt? id, state.ruleGuards? step.rule with
    | some clause, some guards, some expectedGuards =>
        if !CoreSyntax.Search.clauseEq clause step.clause ||
            !SearchMaterialization.guardSetEq guards expectedGuards then
          return false
    | _, _, _ => return false
  return true

private def remapResourceRef?
    (arenaToSearch : Array (Option SearchMaterialization.NodeId))
    (ref : ResourceTrace.ClauseRef) : Option ResourceTrace.ClauseRef := do
  let target? ← arenaToSearch[ref.id]?
  let target ← target?
  pure { ref with id := target }

private def remapLocalWitness?
    (arenaToSearch : Array (Option SearchMaterialization.NodeId)) :
    ResourceTrace.LocalStepWitness → Option ResourceTrace.LocalStepWitness
  | .unary resource => do
      let parent ← remapResourceRef? arenaToSearch resource.parent
      pure (.unary { resource with parent := parent })
  | .resolution resource => do
      let left ← remapResourceRef? arenaToSearch resource.left
      let right ← remapResourceRef? arenaToSearch resource.right
      pure (.resolution { resource with left := left, right := right })
  | .rewrite resource => do
      let equality ← remapResourceRef? arenaToSearch resource.equality
      let target ← remapResourceRef? arenaToSearch resource.target
      pure (.rewrite { resource with equality := equality, target := target })

private def neededProofSteps (inputSize : Nat) (steps : Array Superposition.ProofStep)
    (roots : Array Superposition.ClauseId) : Array Bool :=
  roots.foldl
    (fun needed root =>
      Superposition.markProofAncestor inputSize steps (steps.size + 1) root needed)
    (List.replicate steps.size false).toArray

private def initialArenaMap (arenaSize : Nat)
    (componentNodes : Array SearchMaterialization.ClauseInfo) :
    Array (Option SearchMaterialization.NodeId) := Id.run do
  let mut mapping := (List.replicate arenaSize none).toArray
  for h : id in [:componentNodes.size] do
    mapping := mapping.set! id (some componentNodes[id].id)
  return mapping

private def mappedInfo?
    (dag : SearchMaterialization.SearchDAG)
    (arenaToSearch : Array (Option SearchMaterialization.NodeId))
    (arenaId : Superposition.ClauseId) :
    Option SearchMaterialization.ClauseInfo := do
  let searchId? ← arenaToSearch[arenaId]?
  let searchId ← searchId?
  dag.get? searchId

private def conflictMatches
    (result : RunResult)
    (index : Nat)
    (info : SearchMaterialization.ClauseInfo) : Bool :=
  match result.search.theoryEvidence[index]?, result.search.theoryClauses[index]? with
  | some evidence, some learned =>
      info.clause.isEmpty &&
        SearchMaterialization.guardSetEq info.guards evidence.guards &&
          PropResolution.clauseEq learned evidence.learned &&
            PropResolution.clauseEq evidence.learned
              (DAGCertificate.learnedClauseOfGuards info.guards)
  | _, _ => false

/--
把 persistent saturation arena 中实际参与 theory conflicts 的 proof-step 祖先闭包
自动映射进 canonical SearchDAG。

映射表按原始 arena clause id 索引；未进入冲突祖先闭包的派生槽保持 `none`。输入
component 固定绑定到 split/component 节点，派生槽只能引用已经完成映射的父节点。
-/
def materializeProofSteps? (config : Config) (result : RunResult) :
    SearchMaterialization.Result ProofMaterialization := do
  if result.search.theoryClauses.size != result.search.theoryEvidence.size then
    throw (SearchMaterialization.diagnostic .sourceMaterialization
      "AVATAR theory clauses and theory evidence have different sizes")
  if !result.arenaShapeAligned then
    throw (SearchMaterialization.diagnostic .sourceMaterialization
      "persistent saturation clause/proof arena is not aligned")
  let seed ← SearchMaterialization.requireSome .sourceMaterialization
    "failed to rebuild canonical AVATAR SearchDAG seed" result.searchSeed?
  let state := result.search.state.saturation
  let inputSize := result.problem.arenaInputSize
  if seed.componentNodes.size != result.problem.components.size ||
      seed.splitNodes.size != result.problem.sourceSplits.size then
    throw (SearchMaterialization.diagnostic .sourceMaterialization
      "canonical AVATAR SearchDAG seed does not cover the persistent input arena")
  let roots := result.search.theoryEvidence.map (fun evidence => evidence.clauseId)
  let needed := neededProofSteps inputSize state.steps roots
  let mut dag := seed.dag
  let mut arenaToSearch := initialArenaMap state.clauses.size seed.componentNodes
  for h : index in [:state.steps.size] do
    if needed[index]? == some true then
      let step := state.steps[index]
      let arenaId := inputSize + index
      if !Superposition.validProofStep config.saturation state.clauses step then
        throw (SearchMaterialization.diagnostic .sourceMaterialization
          s!"persistent saturation proof step {arenaId} failed its local checker")
      let resource ← SearchMaterialization.requireSome .sourceMaterialization
        s!"persistent saturation proof step {arenaId} has no resource witness" step.resource?
      let resource ← SearchMaterialization.requireSome .sourceMaterialization
        s!"persistent saturation proof step {arenaId} references an unmapped parent" <|
          remapLocalWitness? arenaToSearch resource
      let (nextDag, info) ← SearchMaterialization.requireSome .sourceMaterialization
        s!"failed to add persistent saturation proof step {arenaId} to SearchDAG" <|
          dag.addResourceTraceLocalWitness? resource
      if !CoreSyntax.Search.clauseEq info.clause step.clause then
        throw (SearchMaterialization.diagnostic .sourceMaterialization
          s!"persistent saturation proof step {arenaId} changed its result clause")
      dag := nextDag
      arenaToSearch := arenaToSearch.set! arenaId (some info.id)
  let conflictNodes ← roots.mapM fun root =>
    SearchMaterialization.requireSome .sourceMaterialization
      s!"persistent saturation conflict root {root} was not materialized" <|
        mappedInfo? dag arenaToSearch root
  for h : index in [:conflictNodes.size] do
    if !result.conflictMatches index conflictNodes[index] then
      throw (SearchMaterialization.diagnostic .sourceMaterialization
        s!"persistent saturation conflict {index} does not match its SearchDAG root")
  if dag.check then
    pure {
      dag := dag
      arenaToSearch := arenaToSearch
      splitNodes := seed.splitNodes
      conflictProofNodes := conflictNodes
    }
  else
    throw (SearchMaterialization.diagnostic .dagCheck
      "SearchDAG checker rejected persistent saturation proof materialization")

/-- 最终命题 certificate 使用的全部 initial clauses。 -/
def finalInitialClauses (result : RunResult) :
    Array PropResolution.InitialClause :=
  result.problem.propInitialClauses ++
    result.search.theoryClauses.mapIdx fun index clause => {
      clause := clause
      origin := .residual (result.problem.sourceSplits.size + index)
    }

/--
若常驻搜索得到 UNSAT，统一重建一次 checked 命题证书。

搜索期保留的 CDCL learned state 只服务性能；可信边界只消费基础 skeleton 与全部显式
theory conflict clauses。
-/
def checkedUnsat? (config : Config) (result : RunResult) :
    Option PropResolution.CheckedUnsatCertificate :=
  match result.search.outcome with
  | .unsat =>
      PropCdcl.checkedUnsat? config.cdcl.cdcl result.problem.numVars
        result.finalInitialClauses
  | _ => none

/--
自动材料化 theory conflicts、对应的 propositional learned clauses，以及最终
residual-CDCL 空 root。

CDCL initial 顺序固定为 source skeleton 前缀加 learned-clause 后缀；root 只引用显式
learned 节点，不再把 guarded-empty 对象推导节点直接当作命题 initial。
-/
def materializeCertificate? (config : Config) (result : RunResult) :
    SearchMaterialization.Result CertificateMaterialization := do
  let certificate ← SearchMaterialization.requireSome .residualSplit
    "persistent AVATAR search did not produce a checked UNSAT certificate" <|
      result.checkedUnsat? config
  let proof ← result.materializeProofSteps? config
  let mut workspace :
      Data.CertificateMaterializationWorkspace
        PropResolution.CheckedUnsatCertificate SearchMaterialization.SearchDAG
          (Array (Option SearchMaterialization.NodeId))
          SearchMaterialization.ClauseInfo := {
    certificate := certificate
    dag := proof.dag
    arenaToSearch := proof.arenaToSearch
    splitNodes := proof.splitNodes
    conflictProofNodes := proof.conflictProofNodes
  }
  for conflictProof in workspace.conflictProofNodes do
    let (nextDag, theoryConflict) ← SearchMaterialization.requireSome .residualSplit
      s!"failed to materialize theory conflict from proof node {conflictProof.id}" <|
        workspace.dag.addTheoryConflict? conflictProof
    workspace := workspace.setDag nextDag |>.pushTheoryConflict theoryConflict
    let (nextDag, learned) ← SearchMaterialization.requireSome .residualSplit
      s!"failed to materialize learned clause from theory conflict {theoryConflict.id}" <|
        workspace.dag.addPropositionalLearnedClause? theoryConflict
    workspace := workspace.setDag nextDag |>.pushLearnedClause learned
  let sources := workspace.sources
  let (finalDag, root) ←
    workspace.dag.addResidualCdclFromSources sources workspace.certificate
    "persistent AVATAR saturation/CDCL"
  if workspace.theoryConflictNodes.size != result.search.theoryEvidence.size ||
      workspace.learnedClauseNodes.size != result.search.theoryClauses.size ||
      !root.globallyEmpty then
    throw (SearchMaterialization.diagnostic .dagCheck
      "persistent AVATAR certificate artifacts are not aligned")
  pure {
    dag := finalDag
    arenaToSearch := workspace.arenaToSearch
    splitNodes := workspace.splitNodes
    conflictProofNodes := workspace.conflictProofNodes
    theoryConflictNodes := workspace.theoryConflictNodes
    learnedClauseNodes := workspace.learnedClauseNodes
    root := root
  }

/-- AVATAR UNSAT 搜索出口自动生成带 residual-CDCL root 的完整 SearchDAG。 -/
def searchDAG? (config : Config) (result : RunResult) :
    SearchMaterialization.Result
      (SearchMaterialization.SearchDAG × SearchMaterialization.ClauseInfo) := do
  let materialized ← result.materializeCertificate? config
  pure (materialized.dag, materialized.root)

/-- AVATAR 搜索出口继续材料化并运行最终 DAG checker。 -/
def checkedDAG? (config : Config) (result : RunResult)
    (problem : SearchMaterialization.ClauseProblem) :
    SearchMaterialization.Result SearchMaterialization.CheckedDAG := do
  let (dag, root) ← result.searchDAG? config
  SearchMaterialization.checkedRoot? problem dag root.id

/--
AVATAR 搜索出口继续运行全局 selector registry checker。

成功结果已经自动携带 fixed-bound-stack soundness 所需的 valuation 与 selector 语义合同。
-/
def checkedAvatarDAG? (config : Config) (result : RunResult)
    (problem : SearchMaterialization.ClauseProblem) :
    SearchMaterialization.Result
      (DAGCertificate.CheckedAvatarDAG
        (σ := SearchMaterialization.SearchSignature)) := do
  let checked ← result.checkedDAG? config problem
  match DAGCertificate.CheckedAvatarDAG.mk? checked with
  | some avatarChecked => pure avatarChecked
  | none =>
      throw (SearchMaterialization.diagnostic .dagCheck
        "materialized AVATAR DAG failed the global selector registry checker")

end RunResult

end Avatar
end Automation
end YesMetaZFC
