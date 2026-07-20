import Lean
import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.HostNormalization
import YesMetaZFC.Automation.HostNormalization.RestrictedSuperposition

/-!
# 宿主规则驱动的证明产生式等式闭包

本模块把宿主正规化组织成四阶段、显式规则驱动的 proof-producing 固定点：

* `Prepared` 一次性保存稳定规则、受限叠加索引和逐规则 `SimpTheorems`；
* 每个阶段先由受限索引选择候选，再只用这些候选运行 congruence-aware `simp`；
* β/ι/ζ/投影由独立的 `ConservativeReduction` 小核产生普通 `Eq` 证明；
* 搜索、候选和排序仍是不可信可调层，结果由图验证和 checked replay 重新检查。

这里不接入裸 `prove_auto`，也不改写局部假设；本轮只建立可由聚焦相继式复用的
target-normalization 边界。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization
namespace EqualityClosure

open Lean Meta

abbrev NodeId := Nat

/-- 等式闭包搜索护栏；这些限制只约束不可信搜索，不改变证明含义。 -/
structure Config where
  maxNodes : Nat := 128
  maxAttempts : Nat := 4096
  maxDepth : Nat := 32
  maxCycles : Nat := 4
  maxSteps : Nat := 512
deriving Repr, Inhabited

/-- 一次闭包搜索的可观测计数。`attempts` 只统计实际运行的 simp。 -/
structure Stats where
  closureElapsedNs : Nat := 0
  resultValidationNs : Nat := 0
  nodes : Nat := 0
  attempts : Nat := 0
  conservativeAttempts : Nat := 0
  conservativeEdges : Nat := 0
  phaseQueries : Nat := 0
  emptyPhasePrunes : Nat := 0
  successfulEdges : Nat := 0
  duplicateEdges : Nat := 0
  failedEdges : Nat := 0
  unresolvedEdges : Nat := 0
  rootPruned : Nat := 0
  indexQueries : Nat := 0
  indexedCandidates : Nat := 0
  rootCandidates : Nat := 0
  fallbackCandidates : Nat := 0
  indexFailures : Nat := 0
  indexedRules : Nat := 0
  fallbackRules : Nat := 0
  candidateRules : Nat := 0
  rulesConsidered : Nat := 0
  rewrites : Nat := 0
  definitionEdges : Nat := 0
  indexEdges : Nat := 0
  semanticEdges : Nat := 0
  logicalEdges : Nat := 0
  terminalNodes : Nat := 0
  backtracks : Nat := 0
  maxDepthReached : Nat := 0
  cycles : Nat := 0
  totalReduction : Nat := 0
  fixedPoint : Bool := false
  terminatedAtTrue : Bool := false
  exhausted : Bool := false
deriving Repr, Inhabited

/-- 正规化边的来源；保守总重化不借用任何注册规则。 -/
inductive StepKind where
  | conservativeReduction
  | phase (phase : Phase)
deriving BEq, Repr, Inhabited

def StepKind.label : StepKind → String
  | .conservativeReduction => "conservative"
  | .phase normalizationPhase => normalizationPhase.label

/-- 一条 proof-producing simp 边；声明数组记录 simplifier 实际使用的全局来源。 -/
structure Step where
  kind : StepKind
  candidateRules : Array Name := #[]
  usedRules : Array Name := #[]
  usedDeclarations : Array Name := #[]
  source : Expr
  target : Expr
  proof : Expr
  ruleAttempts : Nat := 0
  rewrites : Nat := 0
deriving Inhabited

/-- 闭包图中的一个状态；证明项只挂在入边上，避免复制完整证明链。 -/
structure Node where
  id : NodeId
  expression : Expr
  parent? : Option NodeId := none
  incoming? : Option Step := none
  depth : Nat := 0
deriving Inhabited

/-- 规则闭包的 proof-producing 结果。 -/
structure Result where
  source : Expr
  normal : Expr
  proof : Expr
  path : Array Step := #[]
  nodes : Array Node := #[]
  stats : Stats := {}
deriving Inhabited

/--
可在一次聚焦相继式运行中复用的规则准备结果。

`simpTheorems[ruleId]` 只含对应规则；查询后通过 `SimpTheoremsArray` 选择候选，
不合并回全局默认 simp 集。私有构造器保证只有 `prepare` 能产生完成包、索引和
逐规则 simp 对齐检查的值，后续 closure 不再重复验证这一不可变准备面。
-/
structure Prepared where
  private mk ::
  package : RuleCompiler.Package
  rules : Array RuleCompiler.Rule := #[]
  index : RestrictedSuperposition.Index := {}
  simpTheorems : Array SimpTheorems := #[]
  validationElapsedNs : Nat := 0

private inductive Attempt where
  | failed (ruleAttempts : Nat)
  | unresolved (ruleAttempts : Nat)
  | success (step : Step)

private def phaseRank : Phase → Nat
  | .definitionExposure => 0
  | .indexAlgebra => 1
  | .semanticAlignment => 2
  | .logicalCleanup => 3

private def orderedRules (rules : Array RuleCompiler.Rule) :
    Array RuleCompiler.Rule :=
  rules.qsort fun left right =>
    let leftPhase := phaseRank left.phase
    let rightPhase := phaseRank right.phase
    if leftPhase != rightPhase then
      leftPhase < rightPhase
    else
      Name.quickLt left.declaration right.declaration

private partial def expressionSize (expression : Expr) : Nat :=
  let expression := expression.consumeMData
  1 +
    match expression with
    | .app function argument =>
        expressionSize function + expressionSize argument
    | .lam _ domain body _ =>
        expressionSize domain + expressionSize body
    | .forallE _ domain body _ =>
        expressionSize domain + expressionSize body
    | .letE _ type value body _ =>
        expressionSize type + expressionSize value + expressionSize body
    | .mdata _ body =>
        expressionSize body
    | .proj _ _ structureExpr =>
        expressionSize structureExpr
    | _ => 0

private def counterTotal (counter : PHashMap Origin Nat) : Nat :=
  counter.toArray.foldl (fun total entry => total + entry.2) 0

private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private def usedDeclarations (stats : Simp.Stats) : Array Name :=
  stats.usedTheorems.toArray.foldl
    (fun declarations origin =>
      pushNameUnique declarations origin.key) #[]

private def ruleCoversDeclaration
    (rule : RuleCompiler.Rule) (declaration : Name) : Bool :=
  rule.simpDeclarations.contains declaration

private def usedRuleNames
    (rules : Array RuleCompiler.Rule)
    (candidateIds : Array RestrictedSuperposition.RuleId)
    (declarations : Array Name) : Array Name := Id.run do
  let mut result := #[]
  for ruleId in candidateIds do
    let some rule := rules[ruleId]?
      | continue
    if declarations.any (ruleCoversDeclaration rule) then
      result := pushNameUnique result rule.declaration
  return result

private def candidateRuleNames
    (rules : Array RuleCompiler.Rule)
    (candidateIds : Array RestrictedSuperposition.RuleId) : Array Name := Id.run do
  let mut result := #[]
  for ruleId in candidateIds do
    if let some rule := rules[ruleId]? then
      result := pushNameUnique result rule.declaration
  return result

private def candidateSimpTheorems
    (prepared : Prepared)
    (candidateIds : Array RestrictedSuperposition.RuleId) :
    SimpTheoremsArray := Id.run do
  let mut result : SimpTheoremsArray := #[{}]
  for ruleId in candidateIds do
    if let some theorems := prepared.simpTheorems[ruleId]? then
      result := result.push theorems
  return result

private def prepareRule
    (rule : RuleCompiler.Rule) : MetaM SimpTheorems := do
  match rule.kind with
  | .theorem _ =>
      ({} : SimpTheorems).addConst
        rule.declaration true false 1000
  | .definition =>
      ({} : SimpTheorems).addDeclToUnfold rule.declaration
  | .unsupported =>
      pure {}

private def Prepared.validateAlignment (prepared : Prepared) : MetaM Unit := do
  unless prepared.rules.size == prepared.simpTheorems.size do
    throwError "equality closure prepared simp array is not aligned with its rules"
  unless prepared.index.rules.size == prepared.rules.size do
    throwError "equality closure prepared index is not aligned with its rules"
  for index in [0 : prepared.rules.size] do
    let some rule := prepared.rules[index]?
      | throwError "equality closure prepared rule array is sparse"
    let some indexed := prepared.index.rules[index]?
      | throwError "equality closure prepared index rule array is sparse"
    unless rule.declaration == indexed.declaration &&
        rule.phase == indexed.phase do
      throwError "equality closure prepared index rule order is unstable"

/-- 从 proof-free 规则包一次性准备稳定规则、受限索引和逐规则 simp 集。 -/
def prepare (package : RuleCompiler.Package) : MetaM Prepared := do
  unless package.check do
    throwError "equality closure received an invalid proof-free rule package"
  let rules := orderedRules package.rules
  let index ← RestrictedSuperposition.Index.build rules
  let simpTheorems ← rules.mapM prepareRule
  let prepared : Prepared := {
    package
    rules
    index
    simpTheorems
  }
  let validationStarted ← IO.monoNanosNow
  prepared.validateAlignment
  let validationElapsed := (← IO.monoNanosNow) - validationStarted
  return { prepared with validationElapsedNs := validationElapsed }

private def simpContext
    (theorems : SimpTheoremsArray) (maxSteps : Nat) : MetaM Simp.Context := do
  Simp.mkContext
    (config := {
      maxSteps
      maxDischargeDepth := 0
      contextual := false
      memoize := true
      failIfUnchanged := false
      autoUnfold := false
      beta := true
      iota := true
      zeta := true
      zetaDelta := false
      proj := true
      index := true
    })
    (simpTheorems := theorems)
    (congrTheorems := ← getSimpCongrTheorems)

private def attemptPhase
    (prepared : Prepared) (phase : Phase)
    (candidateIds : Array RestrictedSuperposition.RuleId)
    (source : Expr) (maxSteps : Nat) : MetaM Attempt := do
  let saved ← saveState
  try
    let context ← simpContext
      (candidateSimpTheorems prepared candidateIds) maxSteps
    let (result, simpStats) ←
      withOptions (diagnostics.set · true) <|
        simp source context
    let target ← instantiateMVars result.expr
    let proof ←
      match result.proof? with
      | some proof => instantiateMVars proof
      | none => mkEqRefl source
    let ruleAttempts := counterTotal simpStats.diag.triedThmCounter
    if target.hasMVar || proof.hasMVar then
      saved.restore
      return .unresolved ruleAttempts
    if target == source then
      saved.restore
      return .failed ruleAttempts
    let expected ← mkEq source target
    let proofType ← inferType proof
    unless ← isDefEq proofType expected do
      saved.restore
      return .unresolved ruleAttempts
    let actualDeclarations := usedDeclarations simpStats
    let usedRules := usedRuleNames prepared.rules candidateIds actualDeclarations
    let allCovered := actualDeclarations.all fun declaration =>
      candidateIds.any fun ruleId =>
        prepared.rules[ruleId]?.any fun rule =>
          ruleCoversDeclaration rule declaration
    unless allCovered do
      saved.restore
      return .unresolved ruleAttempts
    let step : Step := {
      kind := .phase phase
      candidateRules := candidateRuleNames prepared.rules candidateIds
      usedRules
      usedDeclarations := actualDeclarations
      source
      target
      proof
      ruleAttempts
      rewrites := counterTotal simpStats.diag.usedThmCounter
    }
    saved.restore
    return .success step
  catch _ =>
    saved.restore
    return .unresolved 0

private def attemptConservative
    (source : Expr) (maxSteps : Nat) : MetaM Attempt := do
  try
    let result ←
      ConservativeReduction.reduce source { maxSteps }
    if !result.changed then
      return .failed 0
    let step : Step := {
      kind := .conservativeReduction
      source := result.source
      target := result.normal
      proof := result.proof
    }
    return .success step
  catch _ =>
    return .unresolved 0

private def pathToNode
    (nodes : Array Node) (target : NodeId) : Array Step := Id.run do
  let mut current := target
  let mut reversePath := #[]
  while current != 0 do
    let incoming := nodes[current]!.incoming?.get!
    reversePath := reversePath.push incoming
    current := nodes[current]!.parent?.getD 0
  return reversePath.reverse

private def composePath
    (source : Expr) (path : Array Step) : MetaM Expr := do
  let mut proof ← mkEqRefl source
  for step in path do
    proof ← mkEqTrans proof step.proof
  return proof

private def sameStep (left right : Step) : Bool :=
  left.kind == right.kind &&
    left.candidateRules == right.candidateRules &&
      left.usedRules == right.usedRules &&
        left.usedDeclarations == right.usedDeclarations &&
          left.source == right.source &&
            left.target == right.target &&
              left.proof == right.proof &&
                left.ruleAttempts == right.ruleAttempts &&
                  left.rewrites == right.rewrites

private def stepEdgeStats (stats : Stats) (kind : StepKind) : Stats :=
  match kind with
  | .conservativeReduction =>
      { stats with conservativeEdges := stats.conservativeEdges + 1 }
  | .phase normalizationPhase =>
      match normalizationPhase with
      | .definitionExposure =>
          { stats with definitionEdges := stats.definitionEdges + 1 }
      | .indexAlgebra =>
          { stats with indexEdges := stats.indexEdges + 1 }
      | .semanticAlignment =>
          { stats with semanticEdges := stats.semanticEdges + 1 }
      | .logicalCleanup =>
          { stats with logicalEdges := stats.logicalEdges + 1 }

private def stepKindShape (step : Step) : Bool :=
  match step.kind with
  | .conservativeReduction =>
      step.candidateRules.isEmpty &&
        step.usedRules.isEmpty &&
          step.usedDeclarations.isEmpty &&
            step.ruleAttempts == 0 &&
              step.rewrites == 0
  | .phase _normalizationPhase =>
      !step.candidateRules.isEmpty

private def stepReduction (step : Step) : Nat :=
  expressionSize step.source - expressionSize step.target

/-- 验证闭包图、固定点统计与每条边携带的 Lean 等式证明。 -/
def Result.validate (result : Result) : MetaM Unit := do
  unless !result.nodes.isEmpty do
    throwError "equality closure graph is empty"
  let rootSource := (result.nodes[0]?.map Node.expression).getD result.source
  unless result.source == rootSource do
    throwError "equality closure source is not the graph root"
  let root := result.nodes[0]!
  unless root.id == 0 && root.parent?.isNone && root.incoming?.isNone &&
      root.depth == 0 do
    throwError "equality closure root node is malformed"
  unless result.stats.nodes == result.nodes.size do
    throwError "equality closure node statistics disagree with the graph"
  unless result.stats.attempts ==
      result.stats.successfulEdges +
        result.stats.failedEdges +
          result.stats.unresolvedEdges do
    throwError "equality closure attempt statistics are inconsistent"
  unless result.stats.conservativeAttempts <= result.stats.attempts &&
      result.stats.conservativeAttempts == result.stats.cycles do
    throwError "equality closure conservative attempt statistics are inconsistent"
  unless result.stats.phaseQueries ==
      result.stats.attempts - result.stats.conservativeAttempts +
        result.stats.emptyPhasePrunes do
    throwError "equality closure phase query statistics are inconsistent"
  unless result.stats.backtracks ==
      result.stats.failedEdges +
        result.stats.unresolvedEdges +
          result.stats.duplicateEdges do
    throwError "equality closure backtrack statistics are inconsistent"
  unless result.stats.conservativeEdges +
      result.stats.definitionEdges +
        result.stats.indexEdges +
          result.stats.semanticEdges +
            result.stats.logicalEdges == result.stats.successfulEdges do
    throwError "equality closure step edge statistics are inconsistent"
  unless result.stats.fixedPoint || result.stats.exhausted do
    throwError "equality closure result is neither fixed nor exhausted"
  unless !(result.stats.fixedPoint && result.stats.exhausted) do
    throwError "equality closure result cannot be fixed and exhausted"
  unless !result.stats.terminatedAtTrue ||
      (result.stats.fixedPoint && result.normal.isTrue) do
    throwError "equality closure True termination statistics are inconsistent"
  let finalType ← inferType result.proof
  let finalExpected ← mkEq result.source result.normal
  unless ← isDefEq finalType finalExpected do
    throwError "equality closure final proof has the wrong type"
  let mut expressions : ExprMap Unit := {}
  for index in [0 : result.nodes.size] do
    let node := result.nodes[index]!
    unless node.id == index do
      throwError "equality closure node ids are not dense"
    if expressions.contains node.expression then
      throwError "equality closure contains duplicate expression nodes"
    expressions := expressions.insert node.expression ()
    match node.parent?, node.incoming? with
    | none, none =>
        unless index == 0 do
          throwError "equality closure has a non-root node without an incoming edge"
    | some parent, some incoming =>
        unless parent < index do
          throwError "equality closure parent edge is not topological"
        unless incoming.source == result.nodes[parent]!.expression &&
            incoming.target == node.expression do
          throwError "equality closure edge does not match its parent and child"
        unless node.depth == result.nodes[parent]!.depth + 1 do
          throwError "equality closure node depth does not match its parent"
        unless stepKindShape incoming do
          throwError "equality closure edge kind does not match its rule payload"
        let edgeType ← inferType incoming.proof
        let edgeExpected ← mkEq incoming.source incoming.target
        unless ← isDefEq edgeType edgeExpected do
          throwError "equality closure edge has the wrong proof type"
    | _, _ =>
        throwError "equality closure node has an incomplete parent edge"
  let some normalNode := result.nodes.find? fun node =>
      node.expression == result.normal
    | throwError "equality closure normal form is absent from the graph"
  let expectedPath := pathToNode result.nodes normalNode.id
  unless expectedPath.size == result.path.size do
    throwError "equality closure path length disagrees with the selected graph node"
  for index in [0 : result.path.size] do
    let step := result.path[index]!
    let expected := expectedPath[index]!
    unless sameStep step expected do
      throwError "equality closure path is not the selected graph parent path"
  let mut current := result.source
  let mut reduction := 0
  for step in result.path do
    unless step.source == current do
      throwError "equality closure path contains a discontinuous edge"
    let edgeType ← inferType step.proof
    let edgeExpected ← mkEq step.source step.target
    unless ← isDefEq edgeType edgeExpected do
      throwError "equality closure path edge has the wrong proof type"
    unless stepKindShape step do
      throwError "equality closure path contains a malformed step kind"
    reduction := reduction + stepReduction step
    current := step.target
  unless current == result.normal do
    throwError "equality closure path does not end at the reported normal form"
  unless reduction == result.stats.totalReduction do
    throwError "equality closure total reduction statistics disagree with its path"
  unless result.path.size + result.stats.duplicateEdges ==
      result.stats.successfulEdges do
    throwError "equality closure successful edge statistics disagree with its path"

/-- 将闭包摘要映射到公共证书节点；这里不宣称后端 checker 已完成。 -/
def Result.toCertificateNode
    (result : Result) : Certificate.Node :=
  {
    id := 0
    backend := .equalityKernel
    phase := .equalityReplay
    label := "proof-producing host equality closure"
    ruleTags := #[
      .equalityNormalization,
      .equalityEdge,
      .equalityPath,
      .congruenceClosure
    ]
    stats := {
      steps := result.path.size
      generated := result.stats.nodes
      retained := result.stats.nodes
      verified := result.stats.successfulEdges
      fuel := result.stats.attempts
    }
    dependencies := #[]
  }

private def updateQueryStats
    (stats : Stats) (query : RestrictedSuperposition.QueryResult) : Stats :=
  {
    stats with
    indexQueries := stats.indexQueries + query.stats.treeQueries
    indexedCandidates :=
      stats.indexedCandidates + query.stats.indexedCandidates
    rootCandidates := stats.rootCandidates + query.stats.rootCandidates
    fallbackCandidates :=
      stats.fallbackCandidates + query.stats.fallbackCandidates
    indexFailures := stats.indexFailures + query.stats.queryFailures
    rootPruned := stats.rootPruned + query.stats.prunedRules
    candidateRules := stats.candidateRules + query.ruleIds.size
  }

/--
复用已准备的规则面运行有界 proof-producing 固定点。

所有循环共享 `seen`、节点、深度和尝试预算；到达 `True` 时立即收口。
-/
def closeWithPrepared
    (source : Expr) (prepared : Prepared)
    (config : Config := {}) : MetaM Result := do
  let profile ←
    Lean.isTracingEnabledFor `YesMetaZFC.proveAuto.normalization
  let closureStarted ←
    if profile then IO.monoNanosNow else pure 0
  let source ← instantiateMVars source
  if source.hasMVar then
    throwError "equality closure refused a source with unresolved metavariables"
  let root : Node := { id := 0, expression := source }
  let mut nodes := #[root]
  let mut seen : ExprMap NodeId := {}
  seen := seen.insert source 0
  let mut stats : Stats := {
    nodes := 1
    indexedRules :=
      prepared.index.stats.indexedTheorems +
        prepared.index.stats.rootedDefinitions
    fallbackRules := prepared.index.stats.fallbackRules
  }
  let phases : Array Phase := #[
    .definitionExposure,
    .indexAlgebra,
    .semanticAlignment,
    .logicalCleanup
  ]
  let maxNodes := Nat.max 1 config.maxNodes
  let maxCycles := Nat.max 1 config.maxCycles
  let mut currentId := 0
  let mut stop := false
  let mut exhausted := false
  for _cycle in [0 : maxCycles] do
    if stop then
      break
    let current := nodes[currentId]!
    if nodes.size >= maxNodes ||
        stats.attempts >= config.maxAttempts ||
        current.depth >= config.maxDepth then
      exhausted := true
      stop := true
      break
    stats := {
      stats with
      cycles := stats.cycles + 1
      attempts := stats.attempts + 1
      conservativeAttempts := stats.conservativeAttempts + 1
    }
    let mut cycleChanged := false
    match ← attemptConservative current.expression config.maxSteps with
    | .failed ruleAttempts =>
        stats := {
          stats with
          failedEdges := stats.failedEdges + 1
          backtracks := stats.backtracks + 1
          rulesConsidered := stats.rulesConsidered + ruleAttempts
        }
    | .unresolved ruleAttempts =>
        stats := {
          stats with
          unresolvedEdges := stats.unresolvedEdges + 1
          backtracks := stats.backtracks + 1
          rulesConsidered := stats.rulesConsidered + ruleAttempts
        }
    | .success step =>
        stats := {
          stats with
          successfulEdges := stats.successfulEdges + 1
          rulesConsidered := stats.rulesConsidered + step.ruleAttempts
          rewrites := stats.rewrites + step.rewrites
        }
        stats := stepEdgeStats stats step.kind
        match seen[step.target]? with
        | some _ =>
            stats := {
              stats with
              duplicateEdges := stats.duplicateEdges + 1
              backtracks := stats.backtracks + 1
            }
            exhausted := true
            stop := true
        | none =>
            let id := nodes.size
            let depth := current.depth + 1
            nodes := nodes.push {
              id
              expression := step.target
              parent? := some current.id
              incoming? := some step
              depth
            }
            seen := seen.insert step.target id
            currentId := id
            cycleChanged := true
            stats := {
              stats with
              nodes := nodes.size
              maxDepthReached := Nat.max stats.maxDepthReached depth
              totalReduction := stats.totalReduction + stepReduction step
            }
            if step.target.isTrue then
              stats := {
                stats with
                fixedPoint := true
                terminatedAtTrue := true
                terminalNodes := 1
              }
              stop := true
    for phase in phases do
      if stop then
        break
      let current := nodes[currentId]!
      if nodes.size >= maxNodes ||
          stats.attempts >= config.maxAttempts ||
          current.depth >= config.maxDepth then
        exhausted := true
        stop := true
        break
      let query ← prepared.index.query phase current.expression
      stats := updateQueryStats stats query
      stats := { stats with phaseQueries := stats.phaseQueries + 1 }
      if query.ruleIds.isEmpty then
        stats := {
          stats with emptyPhasePrunes := stats.emptyPhasePrunes + 1
        }
        continue
      stats := { stats with attempts := stats.attempts + 1 }
      match ← attemptPhase prepared phase query.ruleIds current.expression config.maxSteps with
      | .failed ruleAttempts =>
          stats := {
            stats with
            failedEdges := stats.failedEdges + 1
            backtracks := stats.backtracks + 1
            rulesConsidered := stats.rulesConsidered + ruleAttempts
          }
      | .unresolved ruleAttempts =>
          stats := {
            stats with
            unresolvedEdges := stats.unresolvedEdges + 1
            backtracks := stats.backtracks + 1
            rulesConsidered := stats.rulesConsidered + ruleAttempts
          }
      | .success step =>
          stats := {
            stats with
            successfulEdges := stats.successfulEdges + 1
            rulesConsidered := stats.rulesConsidered + step.ruleAttempts
            rewrites := stats.rewrites + step.rewrites
          }
          stats := stepEdgeStats stats step.kind
          match seen[step.target]? with
          | some _ =>
              stats := {
                stats with
                duplicateEdges := stats.duplicateEdges + 1
                backtracks := stats.backtracks + 1
              }
              exhausted := true
              stop := true
          | none =>
              let id := nodes.size
              let depth := current.depth + 1
              nodes := nodes.push {
                id
                expression := step.target
                parent? := some current.id
                incoming? := some step
                depth
              }
              seen := seen.insert step.target id
              currentId := id
              cycleChanged := true
              stats := {
                stats with
                nodes := nodes.size
                maxDepthReached := Nat.max stats.maxDepthReached depth
                totalReduction := stats.totalReduction + stepReduction step
              }
              if step.target.isTrue then
                stats := {
                  stats with
                  fixedPoint := true
                  terminatedAtTrue := true
                  terminalNodes := 1
                }
                stop := true
    if !stop && !cycleChanged then
      stats := {
        stats with
        fixedPoint := true
        terminalNodes := 1
      }
      stop := true
  if !stop then
    exhausted := true
  stats := {
    stats with
    exhausted := exhausted && !stats.fixedPoint
  }
  let path := pathToNode nodes currentId
  let proof ← composePath source path
  let closureElapsed ←
    if profile then
      pure ((← IO.monoNanosNow) - closureStarted)
    else
      pure 0
  let result : Result := {
    source
    normal := nodes[currentId]!.expression
    proof
    path
    nodes
    stats := { stats with closureElapsedNs := closureElapsed }
  }
  let resultValidationStarted ←
    if profile then IO.monoNanosNow else pure 0
  result.validate
  let resultValidationElapsed ←
    if profile then
      pure ((← IO.monoNanosNow) - resultValidationStarted)
    else
      pure 0
  return {
    result with
    stats := {
      result.stats with resultValidationNs := resultValidationElapsed
    }
  }

/-- 准备给定规则包并运行宿主等式闭包。 -/
def closeWithPackage
    (source : Expr) (package : RuleCompiler.Package)
    (config : Config := {}) : MetaM Result := do
  closeWithPrepared source (← prepare package) config

/-- 编译当前环境规则并运行宿主等式闭包。 -/
def close (source : Expr) (config : Config := {}) : MetaM Result := do
  closeWithPackage source (← RuleCompiler.compile) config

end EqualityClosure
end HostNormalization
end Automation
end YesMetaZFC
