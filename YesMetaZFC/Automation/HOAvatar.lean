import YesMetaZFC.Automation.HOSearch
import YesMetaZFC.Automation.PropCdcl
import YesMetaZFC.Automation.Superposition

/-!
# 原生高阶 saturation / CDCL 双核协调器

本模块直接以 HO-AVATAR split/component DAG 为搜索种子。saturation clause id 与
HO-DAG node id 通过显式表对齐；每轮 given-clause 新增的 proof step 会立即写回同一个
persistent DAG arena。CDCL UNSAT 后再自动追加 theory conflict、learned clause 与
residual root。
-/

namespace YesMetaZFC
namespace Automation
namespace HOAvatar

open HOSearchMaterialization

abbrev SearchClause := CoreSyntax.Search.Clause
abbrev DAG := HOSearchMaterialization.DAG
abbrev Node := HOSearchMaterialization.Node
abbrev CheckedAvatarDAG :=
  HODAGCertificate.CheckedAvatarDAG
    (σ := HOSearchMaterialization.SearchSignature)
abbrev Diagnostic := Certificate.Diagnostic

/-- HO-AVATAR runner 的结构化诊断。 -/
def diagnostic (phase : Certificate.Phase) (message : String) : Diagnostic :=
  Certificate.Diagnostic.ofMessage .superposition phase message

/-- 双核 runner 配置。所有上界都只影响搜索，不进入可信证书。 -/
structure Config where
  higherOrder : HOSearch.Config := {}
  saturation : Redundancy.Config := {}
  cdcl : PropCdcl.Incremental.Config := {}
  theoryFuelPerModel : Nat := 256
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 只有 component 与普通 HO 推理资源进入 saturation arena。 -/
def saturationEligible : HODAGCertificate.Payload
    HOSearchMaterialization.SearchSignature → Bool
  | .avatarComponent _ => true
  | .beta _ => true
  | .eta _ => true
  | .substitution _ => true
  | .standardizeApart _ => true
  | .resolution _ => true
  | .factoring _ => true
  | .equalityResolution _ => true
  | .booleanExtensionality _ => true
  | .demodulation _ => true
  | .positiveSuperposition _ => true
  | .negativeSuperposition _ => true
  | .extensionalParamodulation _ => true
  | .argumentCongruence _ => true
  | .functionExtensionality _ => true
  | .source _ => false
  | .avatarSplit _ => false
  | .theoryConflict _ => false
  | .propositionalLearnedClause _ => false
  | .residualCdcl _ => false

/-- 一个外延一元 seed 节点的直接父节点必须满足 AVATAR 来源纪律。 -/
private def extensionalSeedParentOk (dag : DAG) (parentId : Nat) : Bool :=
  match dag.node? parentId with
  | some parent => HOSearch.avatarExtensionalParentEligible parent
  | none => false

/--
HO-AVATAR saturation seed 的来源纪律。

component 必须携带 selector guard；β/η 是唯一允许无 guard 进入 arena 的全局公理；
其余普通推理节点必须继承非空 component guard。外延一元节点还要追溯直接父来源。
-/
def saturationSeedNodeOk (dag : DAG) (node : Node) : Bool :=
  node.check dag.problem &&
    dag.localNodeGuardsOk node &&
      match node.payload with
      | .avatarComponent _ => !node.unguarded
      | .beta _ => node.unguarded
      | .eta _ => node.unguarded
      | .substitution _ => !node.unguarded
      | .standardizeApart _ => !node.unguarded
      | .resolution _ => !node.unguarded
      | .factoring _ => !node.unguarded
      | .equalityResolution _ => !node.unguarded
      | .booleanExtensionality evidence =>
          !node.unguarded && extensionalSeedParentOk dag evidence.parent.id
      | .demodulation _ => !node.unguarded
      | .positiveSuperposition _ => !node.unguarded
      | .negativeSuperposition _ => !node.unguarded
      | .extensionalParamodulation _ => !node.unguarded
      | .argumentCongruence evidence =>
          !node.unguarded && extensionalSeedParentOk dag evidence.parent.id
      | .functionExtensionality evidence =>
          !node.unguarded && extensionalSeedParentOk dag evidence.parent.id
      | _ => false

/--
HO-AVATAR DAG 到双核搜索的稳定 seed。

`guardedClauses`、`dagNodeIds` 同槽；`splitNodeIds`、`propInitialClauses` 同槽。
-/
structure ArenaSeed where
  dag : DAG
  guardedClauses : Array Superposition.GuardedClause
  dagNodeIds : Array Nat
  splitNodeIds : Array Nat
  propInitialClauses : Array PropResolution.InitialClause

namespace ArenaSeed

/-- 一个 saturation seed 槽必须精确对应合法 DAG 节点、guard 与结论。 -/
private def guardedSlotOk (seed : ArenaSeed) (slot : Nat)
    (guarded : Superposition.GuardedClause) : Bool :=
  match seed.dagNodeIds[slot]? with
  | none => false
  | some nodeId =>
      match seed.dag.node? nodeId with
      | none => false
      | some node =>
          saturationSeedNodeOk seed.dag node &&
            HODAGCertificate.guardSetEq node.guards guarded.guards &&
              match node.conclusion? seed.dag.problem with
              | none => false
              | some conclusion =>
                  match HOSearch.searchClause? conclusion with
                  | none => false
                  | some projected =>
                      CoreSyntax.Search.clauseEq projected guarded.clause

/-- 一个 CDCL skeleton 槽必须精确对应 split descriptor 与 residual origin。 -/
private def splitSlotOk (seed : ArenaSeed) (slot : Nat)
    (initial : PropResolution.InitialClause) : Bool :=
  match seed.splitNodeIds[slot]? with
  | none => false
  | some nodeId =>
      match seed.dag.node? nodeId with
      | none => false
      | some node =>
          match node.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq initial.clause
                  (PropResolution.canonicalClause payload.selectors) &&
                match initial.origin with
                | .residual index => index == node.id
                | _ => false
          | _ => false

/-- seed 的稳定映射、来源、guard 与字句投影必须全部逐槽对齐。 -/
def check (seed : ArenaSeed) : Bool :=
  seed.guardedClauses.size == seed.dagNodeIds.size &&
    seed.splitNodeIds.size == seed.propInitialClauses.size &&
      (seed.guardedClauses.mapIdx seed.guardedSlotOk).all id &&
        (seed.propInitialClauses.mapIdx seed.splitSlotOk).all id

/-- 从 HOSearch 已认证 DAG 提取 saturation 与 CDCL 的共同 seed。 -/
def ofSearch? (search : HOSearch.Result) : Option ArenaSeed := do
  let mut guardedClauses : Array Superposition.GuardedClause := #[]
  let mut dagNodeIds : Array Nat := #[]
  let mut splitNodeIds : Array Nat := #[]
  let mut propInitialClauses : Array PropResolution.InitialClause := #[]
  for node in search.dag.nodes do
    match node.payload with
    | .avatarSplit payload =>
        splitNodeIds := splitNodeIds.push node.id
        propInitialClauses := propInitialClauses.push {
          clause := PropResolution.canonicalClause payload.selectors
          origin := .residual node.id
        }
    | _ =>
        pure ()
    if saturationEligible node.payload then
      let conclusion ← node.conclusion? search.dag.problem
      let clause ← HOSearch.searchClause? conclusion
      guardedClauses := guardedClauses.push {
        guards := node.guards
        clause := clause
      }
      dagNodeIds := dagNodeIds.push node.id
  let seed : ArenaSeed := {
    dag := search.dag
    guardedClauses := guardedClauses
    dagNodeIds := dagNodeIds
    splitNodeIds := splitNodeIds
    propInitialClauses := propInitialClauses
  }
  if seed.check && !seed.splitNodeIds.isEmpty then some seed else none

end ArenaSeed

/--
常驻 saturation arena 与同一 HO-DAG 的稳定映射。

`clauseNodeIds[id]` 是 saturation clause `id` 当前对应的最终规则 DAG 节点。
-/
structure PersistentArena where
  saturation : Superposition.State
  dag : DAG
  clauseNodeIds : Array Nat
  seedSize : Nat

namespace PersistentArena

/-- 按 saturation clause id 读取真实 HO-DAG node id。 -/
def dagNodeId? (arena : PersistentArena) (clauseId : Nat) : Option Nat :=
  arena.clauseNodeIds[clauseId]?

/-- proof journal 的第 `stepIndex` 步对应的真实 HO-DAG node id。 -/
def proofStepNodeId? (arena : PersistentArena) (stepIndex : Nat) :
    Option Nat :=
  arena.dagNodeId? (arena.seedSize + stepIndex)

/-- 单个 saturation proof step 立即写回同一 HO-DAG arena。 -/
private def syncStep (arena : PersistentArena)
    (saturation : Superposition.State) (stepIndex : Nat) :
    Except String PersistentArena := do
  let step ←
    match saturation.steps[stepIndex]? with
    | some step => pure step
    | none => throw s!"missing saturation proof step {stepIndex}"
  let arenaId := arena.seedSize + stepIndex
  let arenaClause ←
    match saturation.clauses[arenaId]? with
    | some clause => pure clause
    | none => throw s!"missing saturation clause {arenaId}"
  let guards ←
    match saturation.guardsAt? arenaId with
    | some guards => pure guards
    | none => throw s!"missing saturation guards {arenaId}"
  if !CoreSyntax.Search.clauseEq arenaClause step.clause then
    throw s!"saturation step {stepIndex} changed its retained clause"
  let resource ←
    match step.resource? with
    | some resource => pure resource
    | none => throw s!"saturation step {stepIndex} has no local proof witness"
  let resource ←
    match resource.remapParentsWith? arena.dagNodeId? with
    | some resource => pure resource
    | none => throw s!"saturation step {stepIndex} has an unmapped parent"
  let next ←
    match pushHigherOrderResource? arena.dag (.local resource) with
    | some next => pure next
    | none => throw s!"saturation step {stepIndex} failed HO-DAG materialization"
  if next.nodes.size ≤ arena.dag.nodes.size then
    throw s!"saturation step {stepIndex} did not append a conclusion node"
  let finalId := next.nodes.size - 1
  let finalNode ←
    match next.node? finalId with
    | some node => pure node
    | none => throw s!"saturation step {stepIndex} lost its final DAG node"
  let conclusion ←
    match finalNode.conclusion? next.problem with
    | some clause => pure clause
    | none => throw s!"saturation step {stepIndex} has no final conclusion"
  let projected ←
    match HOSearch.searchClause? conclusion with
    | some clause => pure clause
    | none => throw s!"saturation step {stepIndex} is not search-projectable"
  if !CoreSyntax.Search.clauseEq projected arenaClause ||
      !HODAGCertificate.guardSetEq finalNode.guards guards then
    throw s!"saturation step {stepIndex} changed its clause or guard support"
  pure {
    arena with
    saturation := saturation
    dag := next
    clauseNodeIds := arena.clauseNodeIds.push finalId
  }

/-- 将 saturation 新增的全部 proof steps 同步进 persistent HO-DAG。 -/
def syncProofSteps (arena : PersistentArena)
    (saturation : Superposition.State) : Except String PersistentArena := do
  if saturation.clauses.size != arena.seedSize + saturation.steps.size ||
      saturation.guards.size != saturation.clauses.size ||
      saturation.enabled.size != saturation.clauses.size then
    throw "persistent HO saturation clause/proof arena is not aligned"
  if arena.clauseNodeIds.size < arena.seedSize then
    throw "persistent HO DAG mapping is shorter than its seed"
  let synced := arena.clauseNodeIds.size - arena.seedSize
  if synced > saturation.steps.size then
    throw "persistent HO DAG mapping is ahead of the saturation journal"
  let mut current := { arena with saturation := saturation }
  for _h : stepIndex in [:saturation.steps.size] do
    if synced ≤ stepIndex then
      current ← current.syncStep saturation stepIndex
  pure current

end PersistentArena

/-- guarded empty HO 子句产生的显式 theory conflict。 -/
structure TheoryConflict where
  clauseId : Superposition.ClauseId
  guards : Superposition.GuardSet
  learned : PropResolution.Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 跨 CDCL 模型持久保留的 HO 双核状态。 -/
structure TheoryState where
  arena : PersistentArena
  lastAssignment : Array (Option Bool) := #[]

/-- assignment 中一个命题 literal 是否为真。 -/
def literalTrue (assignment : Array (Option Bool))
    (literal : PropResolution.Lit) : Bool :=
  match assignment.getD literal.var none with
  | some value => if literal.positive then value else !value
  | none => false

/-- 当前 assignment 是否激活整个 guard support。 -/
def supportActive (assignment : Array (Option Bool))
    (guards : Superposition.GuardSet) : Bool :=
  guards.all (literalTrue assignment)

/-- 当前 assignment 下第一个 retained guarded empty。 -/
def firstActiveConflict? (state : Superposition.State)
    (assignment : Array (Option Bool)) : Option TheoryConflict := Id.run do
  for id in state.retainedIds do
    match state.clauses[id]?, state.guardsAt? id with
    | some clause, some guards =>
        if clause.isEmpty && supportActive assignment guards then
          return some {
            clauseId := id
            guards := guards
            learned :=
              PropResolution.canonicalClause
                (guards.map PropResolution.Lit.neg)
          }
    | _, _ =>
        pure ()
  return none

/-- theory conflict 是否满足 assignment、guard 与 learned-clause 协议。 -/
def TheoryConflict.check (state : Superposition.State)
    (assignment : Array (Option Bool)) (conflict : TheoryConflict) : Bool :=
  state.enabledAt conflict.clauseId && state.retained conflict.clauseId &&
    match state.clauses[conflict.clauseId]?,
        state.guardsAt? conflict.clauseId with
    | some clause, some guards =>
        clause.isEmpty &&
          HODAGCertificate.guardSetEq guards conflict.guards &&
            supportActive assignment conflict.guards &&
              PropResolution.clauseEq conflict.learned
                (PropResolution.canonicalClause
                  (conflict.guards.map PropResolution.Lit.neg))
    | _, _ => false

/--
在一个 selector assignment 下运行 given-clause，并逐步同步 persistent HO-DAG。
-/
def saturateModel (config : Config) (assignment : Array (Option Bool)) :
    Nat → Redundancy.WorkBudget → PersistentArena →
      Except String (PersistentArena × Option TheoryConflict × Bool)
  | 0, _, arena =>
      pure (arena, firstActiveConflict? arena.saturation assignment, false)
  | fuel + 1, budget, arena =>
      match firstActiveConflict? arena.saturation assignment with
      | some conflict =>
          pure (arena, some conflict, true)
      | none =>
          match
              Superposition.State.selectGiven?
                config.saturation arena.saturation with
          | some (given, saturation) => do
              let step :=
                Superposition.State.processGiven
                  config.saturation saturation given budget
              let arena ← arena.syncProofSteps step.state
              if step.complete then
                saturateModel config assignment fuel step.budget arena
              else
                pure (arena, none, false)
          | none =>
              pure (arena, none, true)

/-- 一个 CDCL 模型下的 HO theory 轮次。 -/
structure TheoryRoundResult where
  state : TheoryState
  conflict? : Option TheoryConflict
  complete : Bool
  error? : Option String := none

/-- 在一个 selector assignment 下运行持久 HO saturation arena。 -/
def runTheoryRound (config : Config) (state : TheoryState)
    (assignment : Array (Option Bool)) : TheoryRoundResult :=
  let saturation :=
    state.arena.saturation.reseed assignment (supportActive assignment)
  let arena := { state.arena with saturation := saturation }
  match saturateModel config assignment config.theoryFuelPerModel
      (Redundancy.WorkBudget.ofConfig config.saturation saturation.lifecycle.work) arena with
  | .ok (arena, conflict?, complete) =>
      {
        state := { arena := arena, lastAssignment := assignment }
        conflict? := conflict?
        complete := complete
      }
  | .error message =>
      {
        state := { arena := arena, lastAssignment := assignment }
        conflict? := none
        complete := false
        error? := some message
      }

namespace TheoryRoundResult

/-- 把 HO saturation 轮次转换成 CDCL 消费的显式 TheoryResponse。 -/
def toTheoryResponse (round : TheoryRoundResult)
    (assignment : Array (Option Bool)) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  match round.error? with
  | some message =>
      .unknown round.state message
  | none =>
      match round.conflict? with
      | some conflict =>
          if conflict.check round.state.arena.saturation assignment then
            .conflict round.state conflict.learned conflict
          else
            .unknown round.state
              "HO-AVATAR theory conflict failed its guard protocol checker"
      | none =>
          if round.complete then
            .model round.state
          else
            .unknown round.state
              "HO-AVATAR theory saturation exhausted its per-model fuel"

end TheoryRoundResult

/-- 一个 SAT 模型上的 HO-AVATAR theory callback。 -/
def theoryStep (config : Config) (state : TheoryState)
    (assignment : Array (Option Bool)) :
    PropCdcl.Incremental.TheoryResponse TheoryState TheoryConflict :=
  (runTheoryRound config state assignment).toTheoryResponse assignment

/-- 完整 HO-AVATAR 双核搜索结果。 -/
structure RunResult where
  initialClauses : Array SearchClause
  higherOrderSearch : HOSearch.Result
  seed : ArenaSeed
  search :
    PropCdcl.Incremental.RunResult TheoryState TheoryConflict

/-- 运行常驻 HO saturation / CDCL 双核。 -/
def run (config : Config) (initialClauses : Array SearchClause) :
    Except Diagnostic RunResult := do
  let sourceDag ←
    match avatarSourceDAG? initialClauses with
    | some dag => pure dag
    | none =>
        throw (diagnostic .sourceMaterialization
          "native HO clauses failed HO-AVATAR split/component materialization")
  let higherOrderSearch := HOSearch.runAvatar sourceDag config.higherOrder
  let seed ←
    match ArenaSeed.ofSearch? higherOrderSearch with
    | some seed => pure seed
    | none =>
        throw (diagnostic .sourceMaterialization
          "HO-AVATAR DAG failed persistent saturation/CDCL seed extraction")
  let arena : PersistentArena := {
    saturation :=
      Superposition.State.dormant
        config.saturation seed.guardedClauses
    dag := seed.dag
    clauseNodeIds := seed.dagNodeIds
    seedSize := seed.guardedClauses.size
  }
  let initialState : TheoryState := { arena := arena }
  let search :=
    PropCdcl.Incremental.run config.cdcl 0
      (seed.propInitialClauses.map (fun initial => initial.clause))
      initialState (theoryStep config)
  pure {
    initialClauses := initialClauses
    higherOrderSearch := higherOrderSearch
    seed := seed
    search := search
  }

namespace RunResult

/-- 最终命题证书使用 split skeleton 前缀与显式 theory learned 后缀。 -/
def finalInitialClauses (result : RunResult) :
    Array PropResolution.InitialClause :=
  result.seed.propInitialClauses ++
    result.search.theoryClauses.mapIdx fun index clause => {
      clause := clause
      origin := .residual (result.seed.splitNodeIds.size + index)
    }

/-- 双核 UNSAT 后统一重建 checked 命题证书。 -/
def checkedUnsat? (config : Config) (result : RunResult) :
    Option PropResolution.CheckedUnsatCertificate :=
  match result.search.outcome with
  | .unsat =>
      PropCdcl.checkedUnsat? config.cdcl.cdcl 0 result.finalInitialClauses
  | _ =>
      none

/-- 双核运行的公共统计摘要。 -/
def stats (result : RunResult) : Certificate.Stats :=
  let saturation := result.search.state.arena.saturation
  {
    steps := saturation.steps.size
    clauses := saturation.clauses.size
    generated := saturation.lifecycle.generatedCandidates
    retained := saturation.lifecycle.retainedCandidates
    verified := saturation.lifecycle.checkedCandidates
    residuals := result.search.theoryClauses.size
    fuel := saturation.processed
  }

/-- final theory evidence 是否仍精确指向 persistent HO-DAG guarded empty。 -/
private def conflictNode? (result : RunResult) (index : Nat) :
    Option Nat := do
  let evidence ← result.search.theoryEvidence[index]?
  let learned ← result.search.theoryClauses[index]?
  if !PropResolution.clauseEq learned evidence.learned then
    none
  let nodeId ←
    result.search.state.arena.dagNodeId? evidence.clauseId
  let node ← result.search.state.arena.dag.node? nodeId
  let conclusion ← node.conclusion? result.search.state.arena.dag.problem
  if conclusion.isEmpty &&
      HODAGCertificate.guardSetEq node.guards evidence.guards &&
        PropResolution.clauseEq learned
          (HODAGCertificate.learnedClauseOfGuards node.guards) then
    some nodeId
  else
    none

/-- residual root 材料化后的完整 HO-AVATAR certificate。 -/
structure CertificateMaterialization where
  checked : CheckedAvatarDAG
  theoryConflictNodeIds : Array Nat
  learnedClauseNodeIds : Array Nat
  root : Nat

/--
自动把 theory conflict、propositional learned clause 与最终 CDCL root 写入同一
persistent HO-DAG arena，并运行 DAG/selector-registry 双 checker。
-/
def materializeCertificate? (config : Config) (result : RunResult) :
    Except Diagnostic CertificateMaterialization := do
  let certificate ←
    match result.checkedUnsat? config with
    | some certificate => pure certificate
    | none =>
        throw (diagnostic .residualSplit
          "HO-AVATAR dual-core search did not produce checked CDCL UNSAT")
  if result.search.theoryClauses.size !=
      result.search.theoryEvidence.size then
    throw (diagnostic .sourceMaterialization
      "HO-AVATAR theory clauses and evidence are not slot-aligned")
  let mut dag := result.search.state.arena.dag
  let mut theoryConflictNodeIds : Array Nat := #[]
  let mut learnedClauseNodeIds : Array Nat := #[]
  for _h : index in [:result.search.theoryEvidence.size] do
    let proofNodeId ←
      match result.conflictNode? index with
      | some id => pure id
      | none =>
          throw (diagnostic .sourceMaterialization
            s!"HO-AVATAR theory conflict {index} lost its persistent DAG origin")
    let (nextDag, conflictId) ←
      match pushTheoryConflict? dag proofNodeId with
      | some result => pure result
      | none =>
          throw (diagnostic .residualSplit
            s!"failed to materialize HO theory conflict {index}")
    dag := nextDag
    let (nextDag, learnedId) ←
      match pushPropositionalLearnedClause? dag conflictId with
      | some result => pure result
      | none =>
          throw (diagnostic .residualSplit
            s!"failed to materialize HO learned clause {index}")
    dag := nextDag
    theoryConflictNodeIds := theoryConflictNodeIds.push conflictId
    learnedClauseNodeIds := learnedClauseNodeIds.push learnedId
  let sourceIds := result.seed.splitNodeIds ++ learnedClauseNodeIds
  let checked ←
    match checkedResidualCdclFromSources? dag sourceIds certificate with
    | some checked => pure checked
    | none =>
        throw (diagnostic .dagCheck
          "HO-AVATAR residual root failed the complete HO-DAG checker")
  let avatarChecked ←
    match HODAGCertificate.CheckedAvatarDAG.mk? checked with
    | some checked => pure checked
    | none =>
        throw (diagnostic .dagCheck
          "HO-AVATAR residual graph failed the selector registry checker")
  pure {
    checked := avatarChecked
    theoryConflictNodeIds := theoryConflictNodeIds
    learnedClauseNodeIds := learnedClauseNodeIds
    root := avatarChecked.checked.dag.root
  }

end RunResult

end HOAvatar
end Automation
end YesMetaZFC
