import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.HostReification
import YesMetaZFC.Automation.HostNormalization.EqualityClosure

/-!
# 宿主正规化的 checked 证书回放

搜索器、索引和闭包图都属于不可信的可调层。本模块只把它们投影成 proof-free
回放 payload，再由纯 checker 检查规则覆盖、路径拓扑和固定点统计，最后由 Lean
Meta 逐边检查真实等式证明。公共 `Certificate.Node` 只有在这些边界全部通过后产生。

这里不把宿主 `Expr` 强行转换成 `CoreSyntax.NormalForm.Formula`：宿主快照的结构检查、
上下文闭包和 round-trip 是本层的边界；Core normal form 的语义定理仍由它自己的
checked payload 消费。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization
namespace CheckedReplay

open Lean Meta

/-- proof-free payload 中的正规化边来源。 -/
inductive StepKind where
  | conservativeReduction
  | phase (phase : Phase)
deriving BEq, Repr, Inhabited

def StepKind.label : StepKind → String
  | .conservativeReduction => "conservative"
  | .phase normalizationPhase => normalizationPhase.label

private def StepKind.ofClosure :
    EqualityClosure.StepKind → StepKind
  | .conservativeReduction => .conservativeReduction
  | .phase normalizationPhase => .phase normalizationPhase

/-- 证书 payload 中的一条 proof-free simp 回放边。 -/
structure Step where
  kind : StepKind
  candidateRules : Array Name := #[]
  usedRules : Array Name := #[]
  usedDeclarations : Array Name := #[]
  source : Expr
  target : Expr
  ruleAttempts : Nat := 0
  rewrites : Nat := 0
deriving Repr, Inhabited

namespace Step

private def findRule?
    (package : RuleCompiler.Package) (phase : Phase) (declaration : Name) :
    Option RuleCompiler.Rule :=
  package.rules.find? fun rule =>
    rule.declaration == declaration &&
      rule.phase == phase

private def candidateRuleCheck
    (package : RuleCompiler.Package) (step : Step) : Bool :=
  match step.kind with
  | .conservativeReduction =>
      step.candidateRules.isEmpty
  | .phase normalizationPhase =>
      !step.candidateRules.isEmpty &&
        step.candidateRules.all fun declaration =>
          (findRule? package normalizationPhase declaration).isSome

private def usedRuleCheck
    (package : RuleCompiler.Package) (step : Step) : Bool :=
  match step.kind with
  | .conservativeReduction =>
      step.usedRules.isEmpty
  | .phase normalizationPhase =>
      step.usedRules.all fun declaration =>
        step.candidateRules.contains declaration &&
          (findRule? package normalizationPhase declaration).isSome

private def usedDeclarationCheck
    (package : RuleCompiler.Package) (step : Step) : Bool :=
  match step.kind with
  | .conservativeReduction =>
      step.usedDeclarations.isEmpty
  | .phase normalizationPhase =>
      step.usedDeclarations.all fun declaration =>
        step.usedRules.any fun ruleName =>
          (findRule? package normalizationPhase ruleName).any fun rule =>
            rule.simpDeclarations.contains declaration

def ofClosure
    (_package : RuleCompiler.Package)
    (step : EqualityClosure.Step) : Except String Step :=
  .ok {
    kind := StepKind.ofClosure step.kind
    candidateRules := step.candidateRules
    usedRules := step.usedRules
    usedDeclarations := step.usedDeclarations
    source := step.source
    target := step.target
    ruleAttempts := step.ruleAttempts
    rewrites := step.rewrites
  }

def checkRule (package : RuleCompiler.Package) (step : Step) : Bool :=
  candidateRuleCheck package step &&
    usedRuleCheck package step &&
      usedDeclarationCheck package step &&
        (match step.kind with
        | .conservativeReduction =>
            step.ruleAttempts == 0 && step.rewrites == 0
        | .phase _normalizationPhase => true) &&
        step.usedDeclarations.all fun declaration =>
          declaration != .anonymous

end Step

/-- 只保存搜索结果的 proof-free 证书 payload。 -/
structure Payload where
  source : Expr
  normal : Expr
  steps : Array Step := #[]
  nodes : Nat := 0
  attempts : Nat := 0
  conservativeAttempts : Nat := 0
  conservativeEdges : Nat := 0
  phaseQueries : Nat := 0
  emptyPhasePrunes : Nat := 0
  backtracks : Nat := 0
  successfulEdges : Nat := 0
  duplicateEdges : Nat := 0
  failedEdges : Nat := 0
  unresolvedEdges : Nat := 0
  candidateRules : Nat := 0
  rulesConsidered : Nat := 0
  rewrites : Nat := 0
  definitionEdges : Nat := 0
  indexEdges : Nat := 0
  semanticEdges : Nat := 0
  logicalEdges : Nat := 0
  cycles : Nat := 0
  fixedPoint : Bool := false
  terminatedAtTrue : Bool := false
  exhausted : Bool := false
  totalReduction : Nat := 0
  rules : Nat := 0
  indexedRules : Nat := 0
  fallbackRules : Nat := 0
deriving Repr, Inhabited

namespace Payload

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

private def pathCheck (payload : Payload) : Bool := Id.run do
  let mut current := payload.source
  for step in payload.steps do
    if step.source != current then
      return false
    current := step.target
  return current == payload.normal

private def reductionCheck (payload : Payload) : Bool :=
  payload.steps.foldl
    (fun total step =>
      total + (expressionSize step.source - expressionSize step.target)) 0 ==
    payload.totalReduction

private def noMetavariables (payload : Payload) : Bool :=
  !payload.source.hasMVar &&
    !payload.normal.hasMVar &&
      payload.steps.all fun step =>
        !step.source.hasMVar && !step.target.hasMVar

private def coverageCheck
    (package : RuleCompiler.Package) (payload : Payload) : Bool :=
  payload.steps.all (Step.checkRule package)

/-- proof-free payload 的纯结构 checker；不检查宿主表达式的语义等价。 -/
def check (package : RuleCompiler.Package) (payload : Payload) : Bool :=
  package.check &&
    noMetavariables payload &&
      pathCheck payload &&
        reductionCheck payload &&
          coverageCheck package payload &&
            payload.nodes > 0 &&
              (payload.cycles > 0 ||
                (payload.cycles == 0 &&
                  payload.exhausted &&
                    payload.attempts == 0)) &&
                payload.rules == package.rules.size &&
                  payload.indexedRules + payload.fallbackRules <= payload.rules &&
                    payload.attempts ==
                      payload.successfulEdges +
                        payload.failedEdges +
                          payload.unresolvedEdges &&
                    payload.conservativeAttempts <= payload.attempts &&
                      payload.conservativeAttempts == payload.cycles &&
                        payload.phaseQueries ==
                          payload.attempts - payload.conservativeAttempts +
                            payload.emptyPhasePrunes &&
                    payload.backtracks ==
                      payload.failedEdges +
                        payload.unresolvedEdges +
                          payload.duplicateEdges &&
                    payload.successfulEdges ==
                      payload.steps.size + payload.duplicateEdges &&
                    payload.conservativeEdges +
                        payload.definitionEdges +
                          payload.indexEdges +
                            payload.semanticEdges +
                              payload.logicalEdges == payload.successfulEdges &&
                    payload.successfulEdges <= payload.attempts &&
                      payload.backtracks <= payload.attempts &&
                        payload.candidateRules >=
                          payload.steps.foldl
                            (fun total step => total + step.candidateRules.size) 0 &&
                        payload.rewrites >=
                          payload.steps.foldl
                            (fun total step => total + step.rewrites) 0 &&
                        (payload.fixedPoint || payload.exhausted) &&
                          !(payload.fixedPoint && payload.exhausted) &&
                            (!payload.terminatedAtTrue ||
                              (payload.fixedPoint && payload.normal.isTrue))

/-- 把闭包图压缩成不携带证明项的回放 payload。 -/
def ofResult
    (package : RuleCompiler.Package)
    (result : EqualityClosure.Result) : Except String Payload := do
  let steps ← result.path.mapM (Step.ofClosure package)
  return {
    source := result.source
    normal := result.normal
    steps
    nodes := result.stats.nodes
    attempts := result.stats.attempts
    conservativeAttempts := result.stats.conservativeAttempts
    conservativeEdges := result.stats.conservativeEdges
    phaseQueries := result.stats.phaseQueries
    emptyPhasePrunes := result.stats.emptyPhasePrunes
    backtracks := result.stats.backtracks
    successfulEdges := result.stats.successfulEdges
    duplicateEdges := result.stats.duplicateEdges
    failedEdges := result.stats.failedEdges
    unresolvedEdges := result.stats.unresolvedEdges
    candidateRules := result.stats.candidateRules
    rulesConsidered := result.stats.rulesConsidered
    rewrites := result.stats.rewrites
    definitionEdges := result.stats.definitionEdges
    indexEdges := result.stats.indexEdges
    semanticEdges := result.stats.semanticEdges
    logicalEdges := result.stats.logicalEdges
    cycles := result.stats.cycles
    fixedPoint := result.stats.fixedPoint
    terminatedAtTrue := result.stats.terminatedAtTrue
    exhausted := result.stats.exhausted
    totalReduction := result.stats.totalReduction
    rules := package.rules.size
    indexedRules := result.stats.indexedRules
    fallbackRules := result.stats.fallbackRules
  }

end Payload

/-- checked replay 各可信阶段的观测墙钟。 -/
structure ReplayStats where
  payloadElapsedNs : Nat := 0
  checkerElapsedNs : Nat := 0
  snapshotElapsedNs : Nat := 0
  proofReplayElapsedNs : Nat := 0
  artifactValidationNs : Nat := 0
deriving Repr, Inhabited

/-- 通过纯 payload checker 的宿主回放对象。 -/
structure Artifact (package : RuleCompiler.Package) where
  private mk ::
  checked : Certificate.Checked Payload (Payload.check package)
  sourceSnapshot : HostReification.Snapshot
  normalSnapshot : HostReification.Snapshot
  proof : Expr
  replayedSteps : Nat
  stats : ReplayStats := {}

namespace Artifact

/-- 回放对象转公共证书节点；调用方无法绕过 checked replay 获得该摘要。 -/
def toCertificateNode
    {package : RuleCompiler.Package}
    (artifact : Artifact package)
    (id : Certificate.NodeId := 0)
    (dependencies : Array Certificate.NodeId := #[]) :
    Certificate.Node :=
  let payload := artifact.checked.payload
  {
    id
    backend := .equalityKernel
    phase := .equalityReplay
    label := "checked host normalization replay"
    ruleTags := #[
      .equalityNormalization,
      .equalityEdge,
      .equalityPath,
      .congruenceClosure,
      .replayChecker
    ]
    closureKind? := some .frontendNormalization
    stats := {
      steps := artifact.replayedSteps
      generated := payload.nodes
      retained := payload.steps.size + 1
      verified := artifact.replayedSteps + 2
      residuals := payload.backtracks
      fuel := payload.attempts
    }
    dependencies
  }

end Artifact

/--
闭包的 checked 消费结果。

固定点 no-op 已由 `EqualityClosure.closeWithPrepared` 完整执行 `Result.validate`，但不
产生没有推理内容的 payload、快照和 replay artifact；真正改变表达式的闭包仍保留
完整 artifact。私有构造器防止调用方伪造这一分流。
-/
structure CloseResult (package : RuleCompiler.Package) where
  private mk ::
  result : EqualityClosure.Result
  artifact? : Option (Artifact package)

namespace CloseResult

/-- 是否剪掉了固定点 no-op 的重复 replay。 -/
def replayPruned {package : RuleCompiler.Package}
    (result : CloseResult package) : Bool :=
  result.artifact?.isNone

end CloseResult

private def replayEdge
    (step : EqualityClosure.Step) : MetaM Expr := do
  let proof := step.proof
  let proofType ← inferType proof
  let expected ← mkEq step.source step.target
  unless ← isDefEq proofType expected do
    throwError
      "checked host replay rejected `{step.kind.label}` edge: proof type mismatch"
  return proof

private def composeReplay
    (source : Expr) (steps : Array EqualityClosure.Step) : MetaM Expr := do
  let mut proof ← mkEqRefl source
  for step in steps do
    proof ← mkEqTrans proof (← replayEdge step)
  return proof

/-- 在公共节点产生前检查回放对象的 Meta 层不变量。 -/
def validate
    {package : RuleCompiler.Package}
    (artifact : Artifact package) : MetaM Unit := do
  let payload := artifact.checked.payload
  artifact.sourceSnapshot.validate
  artifact.normalSnapshot.validate
  unless artifact.sourceSnapshot.source == payload.source &&
      artifact.normalSnapshot.source == payload.normal do
    throwError "checked host replay snapshots are not aligned with the payload"
  unless artifact.replayedSteps == payload.steps.size do
    throwError "checked host replay step count is not aligned with the payload"
  let proofType ← inferType artifact.proof
  let expected ← mkEq payload.source payload.normal
  unless ← isDefEq proofType expected do
    throwError "checked host replay final proof has the wrong type"

private def replayValidatedWithPackage
    (package : RuleCompiler.Package)
    (result : EqualityClosure.Result) :
    MetaM (Artifact package) := do
  let profile ←
    Lean.isTracingEnabledFor `YesMetaZFC.proveAuto.normalization
  let payloadStarted ←
    if profile then IO.monoNanosNow else pure 0
  let payload ←
    match Payload.ofResult package result with
    | .ok payload => pure payload
    | .error message => throwError message
  let payloadElapsed ←
    if profile then
      pure ((← IO.monoNanosNow) - payloadStarted)
    else
      pure 0
  let checkerStarted ←
    if profile then IO.monoNanosNow else pure 0
  let checked? :
      Option (Certificate.Checked Payload (Payload.check package)) :=
    Certificate.Checked.mk? payload
  let some checked := checked?
    | throwError "checked host replay proof-free payload failed its checker"
  let checkerElapsed ←
    if profile then
      pure ((← IO.monoNanosNow) - checkerStarted)
    else
      pure 0
  let snapshotStarted ←
    if profile then IO.monoNanosNow else pure 0
  let sourceSnapshot ← HostReification.snapshot result.source
  let normalSnapshot ← HostReification.snapshot result.normal
  let snapshotElapsed ←
    if profile then
      pure ((← IO.monoNanosNow) - snapshotStarted)
    else
      pure 0
  let proofReplayStarted ←
    if profile then IO.monoNanosNow else pure 0
  let proof ← composeReplay result.source result.path
  let proofReplayElapsed ←
    if profile then
      pure ((← IO.monoNanosNow) - proofReplayStarted)
    else
      pure 0
  let artifact : Artifact package := {
    checked
    sourceSnapshot
    normalSnapshot
    proof
    replayedSteps := result.path.size
    stats := {
      payloadElapsedNs := payloadElapsed
      checkerElapsedNs := checkerElapsed
      snapshotElapsedNs := snapshotElapsed
      proofReplayElapsedNs := proofReplayElapsed
    }
  }
  let artifactValidationStarted ←
    if profile then IO.monoNanosNow else pure 0
  validate artifact
  let artifactValidationElapsed ←
    if profile then
      pure ((← IO.monoNanosNow) - artifactValidationStarted)
    else
      pure 0
  return {
    artifact with
    stats := {
      artifact.stats with
      artifactValidationNs := artifactValidationElapsed
    }
  }

/-- 对任意不可信闭包结果执行完整 checked replay。 -/
def replayWithPackage
    (source : Expr)
    (package : RuleCompiler.Package)
    (result : EqualityClosure.Result) :
    MetaM (Artifact package) := do
  unless package.check do
    throwError "checked host replay received an invalid rule package"
  unless source == result.source do
    throwError "checked host replay source disagrees with the closure result"
  result.validate
  replayValidatedWithPackage package result

/-- 复用同一规则包运行受限候选、phase-simp 闭包和 checked replay。 -/
def closeWithPackage
    (source : Expr)
    (package : RuleCompiler.Package)
    (config : EqualityClosure.Config := {}) :
    MetaM (CloseResult package) := do
  let result ← EqualityClosure.closeWithPackage source package config
  if result.normal == result.source && result.path.isEmpty then
    return { result, artifact? := none }
  let artifact ← replayValidatedWithPackage package result
  return { result, artifact? := some artifact }

/-- 复用已经准备好的规则面运行闭包与 checked replay。 -/
def closeWithPrepared
    (source : Expr)
    (prepared : EqualityClosure.Prepared)
    (config : EqualityClosure.Config := {}) :
    MetaM (CloseResult prepared.package) := do
  let result ← EqualityClosure.closeWithPrepared source prepared config
  if result.normal == result.source && result.path.isEmpty then
    return { result, artifact? := none }
  let artifact ← replayValidatedWithPackage prepared.package result
  return { result, artifact? := some artifact }

/-- 用当前规则编译结果执行一次完整 checked replay。 -/
def replay (source : Expr) (result : EqualityClosure.Result) :
    MetaM (Sigma fun package : RuleCompiler.Package => Artifact package) := do
  let package ← RuleCompiler.compile
  let artifact ← replayWithPackage source package result
  return ⟨package, artifact⟩

/-- 编译当前规则面并执行闭包与 checked replay 的统一入口。 -/
def close
    (source : Expr) (config : EqualityClosure.Config := {}) :
    MetaM
      (Sigma fun package : RuleCompiler.Package =>
        CloseResult package) := do
  let package ← RuleCompiler.compile
  let result ← closeWithPackage source package config
  return ⟨package, result⟩

end CheckedReplay
end HostNormalization
end Automation
end YesMetaZFC
