import Lean.Meta.Tactic.Replace
import YesMetaZFC.Automation.HostNormalization.CheckedReplay

/-!
# 宿主正规化的 checked 事务边界

本模块把已经回放检查的宿主等式闭包应用到一个真实 Lean 目标：

* 规则包、受限索引和逐规则 `SimpTheorems` 只准备一次；
* 安全普通 `Prop` 假设按局部上下文逆序正规化，并用 `replaceLocalDecl` 的
  `Eq.mp` 传输和 `FVarSubst` 精确迁移资源；
* 目标只消费 checked replay 产生的等式证明，再由 `replaceTargetEq` 的 `Eq.mpr`
  改写；正规形为 `True` 时直接用 `True.intro` 闭合；
* 任一闭包未到固定点、证明或 FVar 不变量失效时，整笔 Meta 状态回滚。

这里不调用旧 `HostNormalization.normalize`，也不接入裸 `prove_auto`。调用方只能看到
提交后的目标/资源，或带完整日志的回滚结果，不存在静默 fallback。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization
namespace CheckedTransaction

open Lean Elab Tactic Meta

initialize registerTraceClass `YesMetaZFC.proveAuto.normalization

register_option prove_auto.normalizer.maxNodes : Nat := {
  defValue := 128
  descr := "maximum expression nodes retained by one checked host-normalization closure"
}

register_option prove_auto.normalizer.maxAttempts : Nat := {
  defValue := 4096
  descr := "maximum phase-simp attempts in one checked host-normalization closure"
}

register_option prove_auto.normalizer.maxDepth : Nat := {
  defValue := 32
  descr := "maximum proof-producing equality path depth in host normalization"
}

register_option prove_auto.normalizer.maxCycles : Nat := {
  defValue := 4
  descr := "maximum fixed-point cycles in one checked host-normalization closure"
}

register_option prove_auto.normalizer.maxSteps : Nat := {
  defValue := 512
  descr := "maximum simplifier steps in one candidate-restricted normalization phase"
}

/-- 一次规则编译与受限索引准备的观测数据。 -/
structure PrepareStats where
  compileElapsedNs : Nat := 0
  prepareElapsedNs : Nat := 0
  validationElapsedNs : Nat := 0
  rules : Nat := 0
  indexedRules : Nat := 0
  fallbackRules : Nat := 0
deriving Repr, Inhabited

/-- 可由多个目标和假设闭包复用的 checked 事务准备结果。 -/
structure Prepared where
  closure : EqualityClosure.Prepared
  stats : PrepareStats := {}

/-- 事务内部每次闭包与回放的完整观测摘要。 -/
structure ClosureJournal where
  closureElapsedNs : Nat := 0
  resultValidationNs : Nat := 0
  payloadElapsedNs : Nat := 0
  checkerElapsedNs : Nat := 0
  snapshotElapsedNs : Nat := 0
  proofReplayElapsedNs : Nat := 0
  artifactValidationNs : Nat := 0
  applicationElapsedNs : Nat := 0
  nodes : Nat := 0
  attempts : Nat := 0
  conservativeAttempts : Nat := 0
  conservativeEdges : Nat := 0
  phaseQueries : Nat := 0
  emptyPhasePrunes : Nat := 0
  backtracks : Nat := 0
  cycles : Nat := 0
  path : Nat := 0
  indexQueries : Nat := 0
  indexedCandidates : Nat := 0
  rootCandidates : Nat := 0
  fallbackCandidates : Nat := 0
  candidateRules : Nat := 0
  rulesConsidered : Nat := 0
  rewrites : Nat := 0
  totalReduction : Nat := 0
  fixedPoint : Bool := false
  terminatedAtTrue : Bool := false
  exhausted : Bool := false
  usedDeclarations : Array Name := #[]
  resultValidated : Bool := false
  fixedNoOp : Bool := false
  replayProduced : Bool := false
  checkerPassed : Bool := false
  replayedSteps : Nat := 0
  providerCalls : Nat := 0
  elapsedNs : Nat := 0
deriving Repr, Inhabited

/-- 一条安全假设迁移的审计记录。 -/
structure HypothesisJournal where
  declaration : Name
  changed : Bool := false
  cleared : Bool := false
  remappedResources : Nat := 0
  closure : ClosureJournal := {}
deriving Repr, Inhabited

/-- 一次目标与假设统一事务的审计日志。 -/
structure Journal where
  prepare : PrepareStats := {}
  hypotheses : Array HypothesisJournal := #[]
  target? : Option ClosureJournal := none
  hypothesisCandidates : Nat := 0
  hypothesesSkipped : Nat := 0
  hypothesesChanged : Nat := 0
  hypothesesCleared : Nat := 0
  resourcesRemapped : Nat := 0
  checkedClosures : Nat := 0
  resultValidatedClosures : Nat := 0
  noOpClosures : Nat := 0
  noOpReplayPrunes : Nat := 0
  replayedClosures : Nat := 0
  nodes : Nat := 0
  attempts : Nat := 0
  conservativeAttempts : Nat := 0
  conservativeEdges : Nat := 0
  phaseQueries : Nat := 0
  emptyPhasePrunes : Nat := 0
  backtracks : Nat := 0
  cycles : Nat := 0
  candidateRules : Nat := 0
  indexQueries : Nat := 0
  indexedCandidates : Nat := 0
  rewrites : Nat := 0
  providerCalls : Nat := 0
  closureElapsedNs : Nat := 0
  resultValidationNs : Nat := 0
  payloadElapsedNs : Nat := 0
  checkerElapsedNs : Nat := 0
  snapshotElapsedNs : Nat := 0
  proofReplayElapsedNs : Nat := 0
  artifactValidationNs : Nat := 0
  applicationElapsedNs : Nat := 0
  hypothesisElapsedNs : Nat := 0
  targetElapsedNs : Nat := 0
  elapsedNs : Nat := 0
  rollbacks : Nat := 0
  rollbackReason? : Option String := none
deriving Repr, Inhabited

/-- 成功提交后的目标和显式 proof 资源；闭合时 `goal? = none`。 -/
structure Result where
  goal? : Option MVarId
  resources : Array FVarId
  changed : Bool := false
  journal : Journal := {}
deriving Repr

/-- checked 事务不会把失败伪装成未变化的成功结果。 -/
inductive Outcome where
  | committed (result : Result)
  | rolledBack (journal : Journal)
deriving Repr

/-- 闭包搜索预算；固定点要求不是可关闭的策略选项。 -/
structure Config where
  closure : EqualityClosure.Config := {}
deriving Repr, Inhabited

/-- 从 tactic options 构造 checked 事务的统一搜索预算。 -/
def configFromOptions (options : Options) : Config :=
  {
    closure := {
      maxNodes :=
        Nat.max 1 <| options.get `prove_auto.normalizer.maxNodes 128
      maxAttempts :=
        Nat.max 1 <| options.get `prove_auto.normalizer.maxAttempts 4096
      maxDepth :=
        Nat.max 1 <| options.get `prove_auto.normalizer.maxDepth 32
      maxCycles :=
        Nat.max 1 <| options.get `prove_auto.normalizer.maxCycles 4
      maxSteps :=
        Nat.max 1 <| options.get `prove_auto.normalizer.maxSteps 512
    }
  }

private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private def pushFVarUnique
    (resources : Array FVarId) (resource : FVarId) : Array FVarId :=
  if resources.contains resource then resources else resources.push resource

private def closureUsedDeclarations
    (result : EqualityClosure.Result) : Array Name :=
  result.path.foldl
    (fun declarations step =>
      step.usedDeclarations.foldl pushNameUnique declarations) #[]

private def ClosureJournal.ofCloseResult
    {package : RuleCompiler.Package}
    (closeResult : CheckedReplay.CloseResult package)
    (elapsedNs : Nat) : ClosureJournal :=
  let result := closeResult.result
  let common : ClosureJournal := {
    closureElapsedNs := result.stats.closureElapsedNs
    resultValidationNs := result.stats.resultValidationNs
    nodes := result.stats.nodes
    attempts := result.stats.attempts
    conservativeAttempts := result.stats.conservativeAttempts
    conservativeEdges := result.stats.conservativeEdges
    phaseQueries := result.stats.phaseQueries
    emptyPhasePrunes := result.stats.emptyPhasePrunes
    backtracks := result.stats.backtracks
    cycles := result.stats.cycles
    path := result.path.size
    indexQueries := result.stats.indexQueries
    indexedCandidates := result.stats.indexedCandidates
    rootCandidates := result.stats.rootCandidates
    fallbackCandidates := result.stats.fallbackCandidates
    candidateRules := result.stats.candidateRules
    rulesConsidered := result.stats.rulesConsidered
    rewrites := result.stats.rewrites
    totalReduction := result.stats.totalReduction
    fixedPoint := result.stats.fixedPoint
    terminatedAtTrue := result.stats.terminatedAtTrue
    exhausted := result.stats.exhausted
    usedDeclarations := closureUsedDeclarations result
    resultValidated := true
    providerCalls := 0
    elapsedNs
  }
  match closeResult.artifact? with
  | none =>
      {
        common with
        fixedNoOp :=
          closeResult.replayPruned &&
            result.stats.fixedPoint &&
            result.normal == result.source &&
              result.path.isEmpty
      }
  | some artifact =>
      {
        common with
        payloadElapsedNs := artifact.stats.payloadElapsedNs
        checkerElapsedNs := artifact.stats.checkerElapsedNs
        snapshotElapsedNs := artifact.stats.snapshotElapsedNs
        proofReplayElapsedNs := artifact.stats.proofReplayElapsedNs
        artifactValidationNs := artifact.stats.artifactValidationNs
        replayProduced := true
        checkerPassed := true
        replayedSteps := artifact.replayedSteps
      }

private def Journal.recordClosure
    (journal : Journal) (closure : ClosureJournal) : Journal :=
  {
    journal with
    checkedClosures := journal.checkedClosures + 1
    resultValidatedClosures :=
      journal.resultValidatedClosures +
        if closure.resultValidated then 1 else 0
    noOpClosures :=
      journal.noOpClosures + if closure.fixedNoOp then 1 else 0
    noOpReplayPrunes :=
      journal.noOpReplayPrunes +
        if closure.fixedNoOp && !closure.replayProduced then 1 else 0
    replayedClosures :=
      journal.replayedClosures +
        if closure.replayProduced then 1 else 0
    nodes := journal.nodes + closure.nodes
    attempts := journal.attempts + closure.attempts
    conservativeAttempts :=
      journal.conservativeAttempts + closure.conservativeAttempts
    conservativeEdges := journal.conservativeEdges + closure.conservativeEdges
    phaseQueries := journal.phaseQueries + closure.phaseQueries
    emptyPhasePrunes :=
      journal.emptyPhasePrunes + closure.emptyPhasePrunes
    backtracks := journal.backtracks + closure.backtracks
    cycles := journal.cycles + closure.cycles
    candidateRules := journal.candidateRules + closure.candidateRules
    indexQueries := journal.indexQueries + closure.indexQueries
    indexedCandidates :=
      journal.indexedCandidates + closure.indexedCandidates
    rewrites := journal.rewrites + closure.rewrites
    providerCalls := journal.providerCalls + closure.providerCalls
    closureElapsedNs := journal.closureElapsedNs + closure.closureElapsedNs
    resultValidationNs :=
      journal.resultValidationNs + closure.resultValidationNs
    payloadElapsedNs := journal.payloadElapsedNs + closure.payloadElapsedNs
    checkerElapsedNs := journal.checkerElapsedNs + closure.checkerElapsedNs
    snapshotElapsedNs :=
      journal.snapshotElapsedNs + closure.snapshotElapsedNs
    proofReplayElapsedNs :=
      journal.proofReplayElapsedNs + closure.proofReplayElapsedNs
    artifactValidationNs :=
      journal.artifactValidationNs + closure.artifactValidationNs
    applicationElapsedNs :=
      journal.applicationElapsedNs + closure.applicationElapsedNs
  }

/-- 编译当前规则包，并一次性准备稳定规则、受限索引和逐规则 simp 集。 -/
def prepare : MetaM Prepared := do
  let compileStarted ← IO.monoNanosNow
  let package ← RuleCompiler.compile
  let compileElapsed := (← IO.monoNanosNow) - compileStarted
  let prepareStarted ← IO.monoNanosNow
  let closure ← EqualityClosure.prepare package
  let prepareElapsed := (← IO.monoNanosNow) - prepareStarted
  return {
    closure
    stats := {
      compileElapsedNs := compileElapsed
      prepareElapsedNs := prepareElapsed - closure.validationElapsedNs
      validationElapsedNs := closure.validationElapsedNs
      rules := closure.rules.size
      indexedRules :=
        closure.index.stats.indexedTheorems +
          closure.index.stats.rootedDefinitions
      fallbackRules := closure.index.stats.fallbackRules
    }
  }

private def localDeclarations (goal : MVarId) :
    MetaM (Array LocalDecl) := goal.withContext do
  let mut declarations := #[]
  for declaration in (← getLCtx) do
    declarations := declarations.push declaration
  return declarations

private def declarationDependsOn
    (declaration : LocalDecl) (fvarId : FVarId) : Bool :=
  declaration.type.containsFVar fvarId ||
    declaration.value?.any (·.containsFVar fvarId)

/--
只选择不出现在目标和后续局部声明中的普通 `Prop` 假设。

逆序处理这些槽位后，`replaceLocalDecl` 可以清除旧 FVar；依赖型上下文继续交给后续
显式相继式规则，不在本事务中猜测迁移。
-/
private def safePropositionHypotheses
    (goal : MVarId) (target : Expr) :
    MetaM (Array FVarId × Nat) := goal.withContext do
  let declarations ← localDeclarations goal
  let mut selected := #[]
  let mut skipped := 0
  for index in [0 : declarations.size] do
    let declaration := declarations[index]!
    let proposition ← instantiateMVars declaration.type
    if declaration.isLet || declaration.isImplementationDetail ||
        declaration.isAuxDecl || declaration.binderInfo.isInstImplicit ||
        !(← isProp proposition) then
      continue
    if proposition.hasMVar then
      skipped := skipped + 1
      continue
    let mut dependent := target.containsFVar declaration.fvarId
    if !dependent then
      for laterIndex in [index + 1 : declarations.size] do
        if declarationDependsOn declarations[laterIndex]! declaration.fvarId then
          dependent := true
          break
    if dependent then
      skipped := skipped + 1
    else
      selected := selected.push declaration.fvarId
  return (selected, skipped)

private def mappedFVar?
    (substitution : FVarSubst) (resource : FVarId) :
    Except String FVarId :=
  match substitution.find? resource with
  | none =>
      .ok resource
  | some expression =>
      match expression.fvarId? with
      | some mapped =>
          .ok mapped
      | none =>
          .error
            s!"checked host transaction mapped proof resource \
            `{resource.name}` to a non-FVar expression"

private def remapResources
    (resources : Array FVarId)
    (source : FVarId) (replacement? : Option FVarId)
    (substitution : FVarSubst) :
    Except String (Array FVarId × Nat) := do
  let mut result := #[]
  let mut remapped := 0
  for resource in resources do
    if resource == source then
      match replacement? with
      | none =>
          remapped := remapped + 1
      | some replacement =>
          result := pushFVarUnique result replacement
          if replacement != resource then
            remapped := remapped + 1
    else
      let mapped ← mappedFVar? substitution resource
      result := pushFVarUnique result mapped
      if mapped != resource then
        remapped := remapped + 1
  if let some replacement := replacement? then
    result := pushFVarUnique result replacement
  return (result, remapped)

private def validateGoalResources
    (goal : MVarId) (resources : Array FVarId) : MetaM Unit :=
  goal.withContext do
    let declaration ← goal.getDecl
    let target ← instantiateMVars declaration.type
    if target.hasMVar then
      throwError
        "checked host transaction left an unresolved metavariable in the target"
    for resource in resources do
      unless declaration.lctx.contains resource do
        throwError
          "checked host transaction leaked stale proof resource `{resource.name}`"
      let proposition ← instantiateMVars (← resource.getType)
      if proposition.hasMVar || !(← isProp proposition) then
        throwError
          "checked host transaction retained an unstable proof resource \
          `{resource.name}`"

private def ensureStableClosure
    (result : EqualityClosure.Result) : MetaM Unit := do
  unless result.stats.fixedPoint && !result.stats.exhausted do
    throwError
      "checked host transaction refused a non-fixed closure; \
      cycles={result.stats.cycles}; nodes={result.stats.nodes}; \
      attempts={result.stats.attempts}; exhausted={result.stats.exhausted}"

private def normalizeHypothesis
    (prepared : Prepared) (config : Config)
    (goal : MVarId) (resources : Array FVarId)
    (source : FVarId) :
    TacticM
      (MVarId × Array FVarId × HypothesisJournal) :=
  goal.withContext do
    let declaration ← source.getDecl
    let proposition ← instantiateMVars declaration.type
    let started ← IO.monoNanosNow
    let closeResult ←
      CheckedReplay.closeWithPrepared
        proposition prepared.closure config.closure
    let closureResult := closeResult.result
    ensureStableClosure closureResult
    let elapsed := (← IO.monoNanosNow) - started
    let closureJournal :=
      ClosureJournal.ofCloseResult closeResult elapsed
    let some artifact := closeResult.artifact?
      | unless closureResult.normal == proposition &&
          closureResult.path.isEmpty do
          throwError
            "checked host transaction received a malformed no-op closure"
        return (goal, resources, {
          declaration := declaration.userName
          closure := closureJournal
        })
    if closureResult.normal == proposition then
      throwError
        "checked host transaction replayed a closure that did not change its source"
    let profile ←
      Lean.isTracingEnabledFor `YesMetaZFC.proveAuto.normalization
    let applicationStarted ←
      if profile then IO.monoNanosNow else pure 0
    let replacement ←
      goal.replaceLocalDecl source closureResult.normal artifact.proof
    let replacementGoal := replacement.mvarId
    let replacementContext := (← replacementGoal.getDecl).lctx
    if replacementContext.contains source then
      throwError
        "checked host transaction could not clear migrated hypothesis \
        `{declaration.userName}`"
    let clearReplacement := closureResult.normal.isTrue
    let replacement? :=
      if clearReplacement then none else some replacement.fvarId
    let (resources, remapped) ←
      match remapResources
          resources source replacement? replacement.subst with
      | .ok result => pure result
      | .error message => throwError message
    let replacementGoal ←
      if clearReplacement then
        replacementGoal.clear replacement.fvarId
      else
        pure replacementGoal
    validateGoalResources replacementGoal resources
    unless clearReplacement do
      let replacementType ←
        replacementGoal.withContext do
          instantiateMVars (← replacement.fvarId.getType)
      unless replacementType == closureResult.normal do
        throwError
          "checked host transaction hypothesis replacement changed its normal form"
    let applicationElapsed ←
      if profile then
        pure ((← IO.monoNanosNow) - applicationStarted)
      else
        pure 0
    return (replacementGoal, resources, {
      declaration := declaration.userName
      changed := true
      cleared := clearReplacement
      remappedResources := remapped
      closure := {
        closureJournal with applicationElapsedNs := applicationElapsed
      }
    })

private def normalizeTarget
    (prepared : Prepared) (config : Config)
    (goal : MVarId) (resources : Array FVarId) :
    TacticM
      (Option MVarId × Bool × ClosureJournal) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let started ← IO.monoNanosNow
    let closeResult ←
      CheckedReplay.closeWithPrepared
        target prepared.closure config.closure
    let closureResult := closeResult.result
    ensureStableClosure closureResult
    let elapsed := (← IO.monoNanosNow) - started
    let closureJournal :=
      ClosureJournal.ofCloseResult closeResult elapsed
    let some artifact := closeResult.artifact?
      | unless closureResult.normal == target &&
          closureResult.path.isEmpty do
          throwError
            "checked host transaction received a malformed no-op target closure"
        validateGoalResources goal resources
        return (some goal, false, closureJournal)
    if closureResult.normal == target then
      throwError
        "checked host transaction replayed a target closure that did not change"
    let profile ←
      Lean.isTracingEnabledFor `YesMetaZFC.proveAuto.normalization
    let applicationStarted ←
      if profile then IO.monoNanosNow else pure 0
    let changed := closureResult.normal != target
    let goal ←
      if changed then
        goal.replaceTargetEq closureResult.normal artifact.proof
      else
        pure goal
    if closureResult.normal.isTrue then
      goal.assign (mkConst ``True.intro)
      let applicationElapsed ←
        if profile then
          pure ((← IO.monoNanosNow) - applicationStarted)
        else
          pure 0
      return (none, true, {
        closureJournal with applicationElapsedNs := applicationElapsed
      })
    validateGoalResources goal resources
    let applicationElapsed ←
      if profile then
        pure ((← IO.monoNanosNow) - applicationStarted)
      else
        pure 0
    return (some goal, changed, {
      closureJournal with applicationElapsedNs := applicationElapsed
    })

/--
在一个事务中正规化安全假设和目标。

成功时所有上下文替换已经由 Lean Meta 构造并由内核待检；失败时恢复调用前的完整
Meta 状态，并把失败原因保存在 `.rolledBack` 日志中。
-/
def run
    (goal : MVarId) (resources : Array FVarId)
    (prepared : Prepared) (config : Config := {}) :
    TacticM Outcome := do
  let savedState ← saveState
  let started ← IO.monoNanosNow
  let mut journal : Journal := { prepare := prepared.stats }
  try
    let target ← goal.withContext do
      instantiateMVars (← goal.getType)
    if target.hasMVar then
      throwError
        "checked host transaction refused a target with unresolved metavariables"
    let (hypotheses, skipped) ←
      safePropositionHypotheses goal target
    journal := {
      journal with
      hypothesisCandidates := hypotheses.size
      hypothesesSkipped := skipped
    }
    let hypothesisStarted ← IO.monoNanosNow
    let mut currentGoal := goal
    let mut currentResources := resources
    let mut changed := false
    for source in hypotheses.reverse do
      let (nextGoal, nextResources, hypothesisJournal) ←
        normalizeHypothesis
          prepared config currentGoal currentResources source
      currentGoal := nextGoal
      currentResources := nextResources
      changed := changed || hypothesisJournal.changed
      journal := journal.recordClosure hypothesisJournal.closure
      journal := {
        journal with
        hypotheses := journal.hypotheses.push hypothesisJournal
        hypothesesChanged :=
          journal.hypothesesChanged +
            if hypothesisJournal.changed then 1 else 0
        hypothesesCleared :=
          journal.hypothesesCleared +
            if hypothesisJournal.cleared then 1 else 0
        resourcesRemapped :=
          journal.resourcesRemapped +
            hypothesisJournal.remappedResources
      }
    journal := {
      journal with
      hypothesisElapsedNs :=
        (← IO.monoNanosNow) - hypothesisStarted
    }
    let targetStarted ← IO.monoNanosNow
    let (goal?, targetChanged, targetJournal) ←
      normalizeTarget
        prepared config currentGoal currentResources
    journal := journal.recordClosure targetJournal
    journal := {
      journal with
      target? := some targetJournal
      targetElapsedNs := (← IO.monoNanosNow) - targetStarted
      elapsedNs := (← IO.monoNanosNow) - started
    }
    return .committed {
      goal?
      resources := if goal?.isNone then #[] else currentResources
      changed := changed || targetChanged
      journal
    }
  catch error =>
    let reason ← error.toMessageData.toString
    savedState.restore
    return .rolledBack {
      journal with
      elapsedNs := (← IO.monoNanosNow) - started
      rollbacks := 1
      rollbackReason? := some reason
    }

end CheckedTransaction
end HostNormalization
end Automation
end YesMetaZFC
