import YesMetaZFC.Automation.Data.BranchHeap
import YesMetaZFC.Automation.Data.ConflictWorkspace
import YesMetaZFC.Automation.Data.Watch
import YesMetaZFC.Automation.Resolution

/-!
# 公共命题 CDCL 搜索核

本模块只处理 `PropResolution` 的命题子句数据，不依赖 `Expr`、Tseitin reify、
MF1 初始字句 soundness 或 LCF replay。逻辑边界仍接受结构化 `Clause`，进入搜索器后
立即打包进连续 `ClauseArena`；传播、冲突分析与 learned journal 不再保存结构化字句。
-/

namespace YesMetaZFC
namespace Automation
namespace PropCdcl

open PropResolution

/-- CDCL 主循环配置。`maxSteps` 是 propagate 后的一次 decide/learn/backjump 宏步上限。 -/
structure Config where
  maxSteps : Nat := 16384
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 搜索失败或耗尽时保留的轻量状态摘要。 -/
structure Snapshot where
  level : Nat
  clauses : Nat
  learned : Nat
  trail : Nat
  assigned : Nat
  vars : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- CDCL 搜索阶段统计；这些观察量不进入可信证书。 -/
structure SearchStats where
  decisions : Nat := 0
  redecisions : Nat := 0
  conflicts : Nat := 0
  propagations : Nat := 0
  backtracks : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq

/-- 搜索结果分类；证明和观察统计统一保存在外层 `Result`。 -/
inductive Outcome where
  | unsat
  | sat (assignment : Array (Option Bool))
  | limitExhausted (snapshot : Snapshot)
  | invariantViolation (message : String) (snapshot : Snapshot)
  deriving Inhabited

/-- 公共 CDCL 搜索结果。 -/
structure Result where
  outcome : Outcome
  proof : CdclProof
  stats : SearchStats
  deriving Inhabited

namespace Result

/-- 搜索器是否报告 UNSAT。 -/
def refuted (result : Result) : Bool :=
  match result.outcome with
  | .unsat => true
  | _ => false

end Result

private abbrev PackedClause := Array Data.PackedLit

private inductive ClauseStatus where
  | satisfied
  | conflict
  | unit (lit : Data.PackedLit)
  | unresolved
  deriving Inhabited

private def describePackedLit (lit : Data.PackedLit) : String :=
  let decoded := Lit.ofPacked lit
  if decoded.positive then s!"v{decoded.var}" else s!"¬v{decoded.var}"

private def describePackedClause (clause : PackedClause) : String :=
  "[" ++ String.intercalate ", " (clause.toList.map describePackedLit) ++ "]"

private def ClauseStatus.describe : ClauseStatus → String
  | .satisfied => "satisfied"
  | .conflict => "conflict"
  | .unit lit => s!"unit {describePackedLit lit}"
  | .unresolved => "unresolved"

/-- 赋值表三态编码：`0 = 未赋值`、`1 = false`、`2 = true`。 -/
private def assignmentUnassigned : UInt8 := 0

private def assignmentFalse : UInt8 := 1

private def assignmentTrue : UInt8 := 2

@[inline]
private def encodeAssignment (value : Bool) : UInt8 :=
  if value then assignmentTrue else assignmentFalse

/-- 从紧凑三态编码恢复逻辑赋值。未知编码按未赋值处理。 -/
private def decodeAssignment (value : UInt8) : Option Bool :=
  if value == assignmentFalse then
    some false
  else if value == assignmentTrue then
    some true
  else
    none

/--
一次 `solve` 生命周期内持续存活的可变 CDCL 状态。

字句正文只存在于连续 arena；watch 桶、reason 和 journal 只保存 1-based ClauseId raw。
`trail` 同时承担传播队列，`qhead` 指向下一条尚未传播的赋值。
-/
private structure CdclMachine (σ : Type) where
  arena : Data.ClauseArena.Builder σ
  assignment : Data.MutByteArray σ
  levels : Data.MutArray σ Nat
  /-- `0` 表示没有 reason，其余值是 `ClauseId.raw`。 -/
  reasons : Data.MutArray σ Nat
  trail : Data.MutArray σ Data.PackedLit
  /-- `trailPos[var] = index + 1`；`0` 表示变量当前不在 trail 中。 -/
  trailPos : Data.MutArray σ Nat
  trailLimits : Data.MutArray σ Nat
  journalSteps : Data.MutArray σ CompactResolutionStep
  journalLearns : Data.MutArray σ LearnRecord
  conflictSteps : Data.MutArray σ CompactResolutionStep
  branch : Data.BranchHeap σ
  branchProfiled : ST.Ref σ Bool
  level : ST.Ref σ Nat
  qhead : ST.Ref σ Nat
  assigned : ST.Ref σ Nat
  propagations : ST.Ref σ Nat
  backtracks : ST.Ref σ Nat
  numVars : Nat
  watchTable : Data.WatchTable.Builder σ

@[inline]
private def CdclMachine.assignmentCodeAt {σ} (machine : CdclMachine σ) (var : Nat) :
    ST σ UInt8 :=
  machine.assignment.get! var

@[inline]
private def CdclMachine.setAssignment {σ} (machine : CdclMachine σ) (var : Nat)
    (value : Bool) : ST σ Unit :=
  machine.assignment.set! var (encodeAssignment value)

@[inline]
private def CdclMachine.clearAssignment {σ} (machine : CdclMachine σ) (var : Nat) :
    ST σ Unit :=
  machine.assignment.set! var assignmentUnassigned

private def CdclMachine.freezeAssignment {σ} (machine : CdclMachine σ) :
    ST σ (Array (Option Bool)) := do
  let assignment ← machine.assignment.freeze
  return Id.run do
    let mut out := Array.emptyWithCapacity assignment.size
    for index in [:assignment.size] do
      out := out.push (decodeAssignment (assignment.get! index))
    return out

private def CdclMachine.freezeProof {σ} (machine : CdclMachine σ) : ST σ CdclProof := do
  return {
    arena := ← machine.arena.freeze
    journal := {
      steps := ← machine.journalSteps.freeze
      learns := ← machine.journalLearns.freeze
    }
  }

/-- 短字句获得更高初始分支权重。 -/
private def branchClauseWeight (length : Nat) : Nat :=
  Nat.max 1 (256 >>> Nat.min length 8)

/-- 安装一个字句的两个 watch；单元字句只登记一次。 -/
private def CdclMachine.installWatches {σ} (machine : CdclMachine σ)
    (id : Data.ClauseId) (clause : PackedClause) (first second : Nat) : ST σ Unit := do
  machine.arena.setWatches id first second
  if first < clause.size then
    let slot := clause[first]!
    if slot < 2 * machine.numVars then
      machine.watchTable.pushBucket slot id.raw
  if second != first && second < clause.size then
    let slot := clause[second]!
    if slot < 2 * machine.numVars then
      machine.watchTable.pushBucket slot id.raw

/-- 初始与外部字句的默认 watch 布局。 -/
private def CdclMachine.installDefaultWatches {σ} (machine : CdclMachine σ)
    (id : Data.ClauseId) (clause : PackedClause) : ST σ Unit :=
  machine.installWatches id clause 0 (if clause.size > 1 then 1 else 0)

/-- 按当前赋值优先选择两个非假 literal 作为新字句的 watch。 -/
private def CdclMachine.currentWatchPositions {σ} (machine : CdclMachine σ)
    (clause : PackedClause) : ST σ (Nat × Nat) := do
  let mut first? : Option Nat := none
  let mut second? : Option Nat := none
  for index in [:clause.size] do
    let lit := clause[index]!
    let value ← machine.assignmentCodeAt (Data.PackedLit.var lit)
    if value == assignmentUnassigned ||
        value == encodeAssignment (Data.PackedLit.positive lit) then
      if first?.isNone then
        first? := some index
      else if second?.isNone then
        second? := some index
        break
  match first?, second? with
  | some first, some second =>
      return (first, second)
  | some first, none =>
      let second :=
        if clause.size <= 1 then first
        else if first == 0 then 1
        else 0
      return (first, second)
  | none, _ =>
      return (0, if clause.size > 1 then 1 else 0)

/-- 新注入字句按当前赋值安装 watch。 -/
private def CdclMachine.installCurrentWatches {σ} (machine : CdclMachine σ)
    (id : Data.ClauseId) (clause : PackedClause) : ST σ Unit := do
  let (first, second) ← machine.currentWatchPositions clause
  machine.installWatches id clause first second

private def CdclMachine.init {σ} (numVars : Nat) (clauses : Array Clause) :
    ST σ (CdclMachine σ) := do
  let arena ← Data.ClauseArena.Builder.empty (σ := σ)
  let watchTable ← Data.WatchTable.Builder.empty (σ := σ) (2 * numVars)
  let assignment ← Data.MutByteArray.mk (σ := σ)
    (Data.filledByteArray numVars assignmentUnassigned)
  let levels ← Data.MutArray.mk (σ := σ) (Data.filledArray numVars 0)
  let reasons ← Data.MutArray.mk (σ := σ) (Data.filledArray numVars 0)
  let trail ← Data.MutArray.mk (σ := σ) (#[] : Array Data.PackedLit)
  let trailPos ← Data.MutArray.mk (σ := σ) (Data.filledArray numVars 0)
  let trailLimits ← Data.MutArray.mk (σ := σ) (#[] : Array Nat)
  let journalSteps ← Data.MutArray.mk (σ := σ) (#[] : Array CompactResolutionStep)
  let journalLearns ← Data.MutArray.mk (σ := σ) (#[] : Array LearnRecord)
  let conflictSteps ← Data.MutArray.mk (σ := σ) (#[] : Array CompactResolutionStep)
  let branch ← Data.BranchHeap.create (σ := σ) numVars
  let level ← ST.mkRef (σ := σ) 0
  let qhead ← ST.mkRef (σ := σ) 0
  let assigned ← ST.mkRef (σ := σ) 0
  let propagations ← ST.mkRef (σ := σ) 0
  let backtracks ← ST.mkRef (σ := σ) 0
  let machine : CdclMachine σ := {
    arena := arena
    assignment := assignment
    levels := levels
    reasons := reasons
    trail := trail
    trailPos := trailPos
    trailLimits := trailLimits
    journalSteps := journalSteps
    journalLearns := journalLearns
    conflictSteps := conflictSteps
    branch := branch
    branchProfiled := ← ST.mkRef (σ := σ) false
    level := level
    qhead := qhead
    assigned := assigned
    propagations := propagations
    backtracks := backtracks
    numVars := numVars
    watchTable := watchTable
  }
  for clause in clauses do
    let packed := packClause clause
    let id ← machine.arena.pushClause packed
    machine.installDefaultWatches id packed
  return machine

private def CdclMachine.snapshot {σ} (machine : CdclMachine σ) : ST σ Snapshot := do
  return {
    level := ← machine.level.get
    clauses := ← machine.arena.size
    learned := ← machine.journalLearns.size
    trail := ← machine.trail.size
    assigned := ← machine.assigned.get
    vars := machine.numVars
  }

/-- 冻结搜索观察计数；不进入 `CdclProof`。 -/
private def CdclMachine.searchStats {σ} (machine : CdclMachine σ) : ST σ SearchStats := do
  let branchStats ← machine.branch.stats
  return {
    decisions := branchStats.decisions
    redecisions := branchStats.redecisions
    conflicts := branchStats.conflicts
    propagations := ← machine.propagations.get
    backtracks := ← machine.backtracks.get
  }

private def CdclMachine.assign {σ} (machine : CdclMachine σ) (lit : Data.PackedLit)
    (reason : Data.ClauseId) : ST σ Bool := do
  let var := Data.PackedLit.var lit
  if (← machine.assignmentCodeAt var) != assignmentUnassigned then
    return false
  let level ← machine.level.get
  let trailPos ← machine.trail.size
  let value := Data.PackedLit.positive lit
  machine.setAssignment var value
  machine.levels.setD var level 0
  machine.reasons.setD var reason.raw 0
  machine.trailPos.setD var (trailPos + 1) 0
  machine.trail.push lit
  machine.assigned.modify (fun count => count + 1)
  if reason.isValid then
    machine.propagations.modify (· + 1)
  return true

private def CdclMachine.decide {σ} (machine : CdclMachine σ) (var : Nat)
    (value : Bool) : ST σ Unit := do
  let trailSize ← machine.trail.size
  machine.trailLimits.push trailSize
  machine.level.modify (fun level => level + 1)
  let lit := Data.PackedLit.pack var value
  let _ ← machine.assign lit Data.Id.invalid

/-- 首次真实分支前从 arena 生成静态 activity 与 polarity。 -/
private def CdclMachine.ensureBranchProfile {σ} (machine : CdclMachine σ) : ST σ Unit := do
  if ← machine.branchProfiled.get then
    return
  let arena ← machine.arena.freeze
  let mut positive := Data.filledArray machine.numVars 0
  let mut negative := Data.filledArray machine.numVars 0
  for header in arena.headers do
    let weight := branchClauseWeight header.length
    for position in [:header.length] do
      if let some lit := arena.literals[header.start + position]? then
        let var := Data.PackedLit.var lit
        if var < machine.numVars then
          if Data.PackedLit.positive lit then
            positive := positive.set! var (positive[var]! + weight)
          else
            negative := negative.set! var (negative[var]! + weight)
  let mut activity := Data.filledArray machine.numVars 0
  let mut phase := Data.filledByteArray machine.numVars 0
  for var in [:machine.numVars] do
    activity := activity.set! var (positive[var]! + negative[var]!)
    if negative[var]! < positive[var]! then
      phase := phase.set! var 1
  machine.branch.loadProfile activity phase
  machine.branchProfiled.set true

private partial def chooseBranchFromHeap? {σ} (machine : CdclMachine σ) :
    ST σ (Option (Nat × Bool)) := do
  let some (var, phase) ← machine.branch.pop? | return none
  if (← machine.assignmentCodeAt var) == assignmentUnassigned then
    machine.branch.noteDecision var
    return some (var, phase)
  chooseBranchFromHeap? machine

/-- 从 activity heap 惰性跳过已赋值项，取得真实分支候选。 -/
private def chooseBranch? {σ} (machine : CdclMachine σ) :
    ST σ (Option (Nat × Bool)) := do
  machine.ensureBranchProfile
  chooseBranchFromHeap? machine

private partial def findNewWatcher {σ} (machine : CdclMachine σ)
    (header : Data.ClauseHeader) (skipPos index : Nat) : ST σ (Option Nat) := do
  if index >= header.length then
    return none
  if index == skipPos then
    return ← findNewWatcher machine header skipPos (index + 1)
  let lit ← machine.arena.litAt! header index
  let value ← machine.assignmentCodeAt (Data.PackedLit.var lit)
  if value == assignmentUnassigned ||
      value == encodeAssignment (Data.PackedLit.positive lit) then
    return some index
  return ← findNewWatcher machine header skipPos (index + 1)

private inductive WatchAction where
  | keepWatch
  | moveWatch (newLitSlot first second : Nat)
  | unitProp (unitLit : Data.PackedLit) (reason : Data.ClauseId)
  | conflict (clause : Data.ClauseId)

private def watchActionForClause {σ} (machine : CdclMachine σ) (id : Data.ClauseId)
    (header : Data.ClauseHeader) (assignedLit : Data.PackedLit) :
    ST σ WatchAction := do
  if header.watch0 >= header.length || header.watch1 >= header.length then
    return .keepWatch
  let firstLit ← machine.arena.litAt! header header.watch0
  let secondLit ← machine.arena.litAt! header header.watch1
  let falseLit := Data.PackedLit.neg assignedLit
  let falsePos? :=
    if firstLit == falseLit then
      some header.watch0
    else if secondLit == falseLit then
      some header.watch1
    else
      none
  let some falsePos := falsePos? | return .keepWatch
  let otherPos := if falsePos == header.watch0 then header.watch1 else header.watch0
  let otherLit ← machine.arena.litAt! header otherPos
  let otherValue ← machine.assignmentCodeAt (Data.PackedLit.var otherLit)
  if otherValue == encodeAssignment (Data.PackedLit.positive otherLit) then
    return .keepWatch
  match ← findNewWatcher machine header otherPos 0 with
  | some newPos =>
      let newLit ← machine.arena.litAt! header newPos
      return .moveWatch newLit newPos otherPos
  | none =>
      if otherValue == assignmentUnassigned then
        return .unitProp otherLit id
      return .conflict id

private partial def inspectClauseAux {σ} (machine : CdclMachine σ)
    (clause : PackedClause) (index unassigned : Nat) (unitLit : Data.PackedLit) :
    ST σ ClauseStatus := do
  if index < clause.size then
    let lit := clause[index]!
    let value ← machine.assignmentCodeAt (Data.PackedLit.var lit)
    if value == encodeAssignment (Data.PackedLit.positive lit) then
      return .satisfied
    if value == assignmentUnassigned then
      return ← inspectClauseAux machine clause (index + 1) (unassigned + 1) lit
    return ← inspectClauseAux machine clause (index + 1) unassigned unitLit
  if unassigned == 0 then
    return .conflict
  if unassigned == 1 then
    return .unit unitLit
  return .unresolved

private def inspectClause {σ} (machine : CdclMachine σ) (clause : PackedClause) :
    ST σ ClauseStatus :=
  inspectClauseAux machine clause 0 0 0

/--
处理一个刚变真的 literal 对应的反向监视桶。

原桶先整体取出，读游标向前扫描，写游标把保留项覆盖回同一块存储；移动到其他槽位的
ClauseId 直接追加到目标桶，watch 位置则原地写回 arena header。
-/
private def processWatchedLit {σ} (machine : CdclMachine σ)
    (assignedLit : Data.PackedLit) : ST σ (Option Data.ClauseId) := do
  let negSlot := Data.PackedLit.neg assignedLit
  if negSlot >= 2 * machine.numVars then
    return none
  let bucket ← Data.MutArray.mk (σ := σ) (← machine.watchTable.drainBucket negSlot)
  let bucketSize ← bucket.size
  let mut keptCount := 0
  let mut conflict? : Option Data.ClauseId := none
  for readIndex in [:bucketSize] do
    let rawId ← bucket.get! readIndex
    let id : Data.ClauseId := Data.Id.ofNat rawId
    let mut keepCurrent := false
    if conflict?.isSome then
      keepCurrent := true
    else
      match ← machine.arena.header? id with
      | none => pure ()
      | some header =>
          if header.length == 0 then
            keepCurrent := true
            conflict? := some id
          else
            match ← watchActionForClause machine id header assignedLit with
            | .keepWatch =>
                keepCurrent := true
            | .moveWatch newLitSlot first second =>
                machine.arena.setWatches id first second
                if newLitSlot < 2 * machine.numVars then
                  machine.watchTable.pushBucket newLitSlot rawId
            | .conflict conflictId =>
                keepCurrent := true
                conflict? := some conflictId
            | .unitProp unitLit reason =>
                let _ ← machine.assign unitLit reason
                keepCurrent := true
    if keepCurrent then
      if keptCount != readIndex then
        bucket.set! keptCount rawId
      keptCount := keptCount + 1
  bucket.truncate keptCount
  machine.watchTable.setBucket negSlot (← bucket.freeze)
  return conflict?

/-- 沿 trail 做增量传播。 -/
private partial def propagateWatched {σ} (machine : CdclMachine σ) :
    ST σ (Option Data.ClauseId) := do
  let head ← machine.qhead.get
  let trailSize ← machine.trail.size
  if head >= trailSize then
    return none
  let lit ← machine.trail.getD head 0
  machine.qhead.set (head + 1)
  match ← processWatchedLit machine lit with
  | some conflictId => return some conflictId
  | none => propagateWatched machine

/-- 当前字句在指定层上的 literal 数。 -/
private def clauseLevelCount {σ} (machine : CdclMachine σ) (clause : PackedClause)
    (level : Nat) : ST σ Nat := do
  let mut count := 0
  for lit in clause do
    if (← machine.levels.getD (Data.PackedLit.var lit) 0) == level then
      count := count + 1
  return count

/-- 一个 arena 字句当前实际涉及的最高决策层。 -/
private def CdclMachine.clauseMaxLevel {σ} (machine : CdclMachine σ)
    (id : Data.ClauseId) : ST σ Nat := do
  let some header ← machine.arena.header? id | return 0
  let mut level := 0
  for position in [:header.length] do
    let lit ← machine.arena.litAt! header position
    level := Nat.max level (← machine.levels.getD (Data.PackedLit.var lit) 0)
  return level

/-- 通过 trail position 在字句中寻找指定层最后赋值的 literal。 -/
private def latestClauseLitAtLevel? {σ} (machine : CdclMachine σ)
    (clause : PackedClause) (level : Nat) : ST σ (Option Data.PackedLit) := do
  let mut latest? : Option Data.PackedLit := none
  let mut latestPos := 0
  for lit in clause do
    let var := Data.PackedLit.var lit
    if (← machine.levels.getD var 0) == level then
      let position ← machine.trailPos.getD var 0
      if latestPos < position then
        latest? := some lit
        latestPos := position
  return latest?

/-- 普通 1-UIP 冲突分析；reason 直接从冻结 arena slab 读取。 -/
private partial def analyzeConflictLoop {σ} (machine : CdclMachine σ)
    (arena : Data.ClauseArena) (analysisLevel : Nat)
    (learned : PackedClause) : ST σ PackedClause := do
  if (← clauseLevelCount machine learned analysisLevel) <= 1 then
    return learned
  let some lit ← latestClauseLitAtLevel? machine learned analysisLevel | return learned
  let var := Data.PackedLit.var lit
  let reasonRaw ← machine.reasons.getD var 0
  if reasonRaw == 0 then
    return learned
  let result := Data.resolvePackedWithArena learned arena (Data.Id.ofNat reasonRaw) var
  machine.conflictSteps.push {
    pivot := var
    reason := reasonRaw
  }
  analyzeConflictLoop machine arena analysisLevel result

/-- level-0 最终冲突分析。 -/
private partial def analyzeFinalConflictLoop {σ} (machine : CdclMachine σ)
    (arena : Data.ClauseArena) (learned : PackedClause) : ST σ PackedClause := do
  let some lit ← latestClauseLitAtLevel? machine learned 0 | return learned
  let var := Data.PackedLit.var lit
  let reasonRaw ← machine.reasons.getD var 0
  if reasonRaw == 0 then
    return learned
  let result := Data.resolvePackedWithArena learned arena (Data.Id.ofNat reasonRaw) var
  machine.conflictSteps.push {
    pivot := var
    reason := reasonRaw
  }
  analyzeFinalConflictLoop machine arena result

private def backjumpLevel {σ} (machine : CdclMachine σ) (analysisLevel : Nat)
    (learned : PackedClause) : ST σ Nat := do
  let mut level := 0
  for lit in learned do
    let litLevel ← machine.levels.getD (Data.PackedLit.var lit) 0
    if litLevel != analysisLevel && level < litLevel then
      level := litLevel
  return level

/-- 回跳到目标决策层，只弹出真正被撤销的 trail 后缀。 -/
private def CdclMachine.backtrack {σ} (machine : CdclMachine σ)
    (targetLevel : Nat) : ST σ Unit := do
  let currentLevel ← machine.level.get
  if targetLevel < currentLevel then
    machine.backtracks.modify (· + 1)
    machine.branch.beginReleaseBatch
    let trailSize ← machine.trail.size
    let targetSize ← machine.trailLimits.getD targetLevel trailSize
    let rec popTrail : Nat → ST σ Unit
      | 0 => pure ()
      | count + 1 => do
        match ← machine.trail.pop? with
        | none => return
        | some lit =>
            let var := Data.PackedLit.var lit
            machine.branch.savePhase var (Data.PackedLit.positive lit)
            machine.clearAssignment var
            machine.levels.setD var 0 0
            machine.reasons.setD var 0 0
            machine.trailPos.setD var 0 0
            machine.branch.queueRelease var
            machine.assigned.modify (fun count => count - 1)
            popTrail count
    popTrail (trailSize - targetSize)
    machine.branch.releaseMany
    let limitCount ← machine.trailLimits.size
    let rec trimLimits : Nat → ST σ Unit
      | 0 => pure ()
      | count + 1 => do
          let _ ← machine.trailLimits.pop?
          trimLimits count
    trimLimits (limitCount - targetLevel)
    let qhead ← machine.qhead.get
    if targetSize < qhead then
      machine.qhead.set targetSize
    machine.level.set targetLevel

private structure ConflictAnalysis where
  learned : PackedClause
  jumpLevel : Nat
  start : Nat
  steps : Array CompactResolutionStep
  tautological : Bool

private def analyzeConflictAtLevel {σ} (machine : CdclMachine σ)
    (conflictId : Data.ClauseId) (analysisLevel : Nat) :
    ST σ ConflictAnalysis := do
  machine.conflictSteps.truncate 0
  let arena ← machine.arena.freeze
  let learned ←
    analyzeConflictLoop machine arena analysisLevel (arena.packedClause conflictId)
  return {
    learned := learned
    jumpLevel := ← backjumpLevel machine analysisLevel learned
    start := conflictId.raw
    steps := ← machine.conflictSteps.freeze
    tautological := Data.packedClauseTautological learned
  }

private def analyzeFinalConflict {σ} (machine : CdclMachine σ)
    (conflictId : Data.ClauseId) : ST σ ConflictAnalysis := do
  machine.conflictSteps.truncate 0
  let arena ← machine.arena.freeze
  let learned ← analyzeFinalConflictLoop machine arena (arena.packedClause conflictId)
  return {
    learned := learned
    jumpLevel := 0
    start := conflictId.raw
    steps := ← machine.conflictSteps.freeze
    tautological := Data.packedClauseTautological learned
  }

private def invariantViolation {σ} (machine : CdclMachine σ) (message : String) :
    ST σ Result := do
  return {
    outcome := .invariantViolation message (← machine.snapshot)
    proof := ← machine.freezeProof
    stats := ← machine.searchStats
  }

private def learnedInvariantError {σ} (machine : CdclMachine σ) (message : String)
    (analysis : ConflictAnalysis) (learned : PackedClause) : ST σ Result := do
  invariantViolation machine
    s!"{message}; learned={describePackedClause learned}, jumpLevel={analysis.jumpLevel}, \
    currentLevel={← machine.level.get}, clauses={← machine.arena.size}, \
    journal={← machine.journalLearns.size}"

private def assertingLiteralAfterBackjump? {σ} (machine : CdclMachine σ)
    (analysis : ConflictAnalysis) : ST σ (Except String (Option Data.PackedLit)) := do
  if analysis.tautological then
    return .error
      s!"learned clause became tautological during conflict analysis: \
      {describePackedClause analysis.learned}"
  let learned := analysis.learned
  machine.backtrack analysis.jumpLevel
  if learned.isEmpty then
    return .ok none
  match ← inspectClause machine learned with
  | .unit lit => return .ok (some lit)
  | status =>
      return .error
        s!"learned clause is not asserting after backjump: status={status.describe}, \
        clause={describePackedClause learned}"

private def addLearnedClause {σ} (machine : CdclMachine σ) (learned : PackedClause)
    (assertLit? : Option Data.PackedLit) :
    ST σ Data.ClauseArena.Builder.InternResult := do
  let mut assertPos? : Option Nat := none
  for i in [:learned.size] do
    if assertLit? == some learned[i]! then
      assertPos? := some i
      break
  let mut secondPos? : Option Nat := none
  let mut bestLevel := 0
  if let some assertPos := assertPos? then
    for i in [:learned.size] do
      if i != assertPos then
        let level ← machine.levels.getD (Data.PackedLit.var learned[i]!) 0
        if secondPos?.isNone || bestLevel < level then
          secondPos? := some i
          bestLevel := level
  let (first, second) :=
    match assertPos?, secondPos? with
    | some assertPos, some secondPos => (assertPos, secondPos)
    | some assertPos, none => (assertPos, assertPos)
    | none, _ => (0, 0)
  let interned ← machine.arena.internClause learned Data.learnedClauseFlag
  if interned.isNew then
    machine.installWatches interned.id learned first second
  return interned

private inductive ExternalClauseAdd where
  | accepted (interned : Data.ClauseArena.Builder.InternResult)
  | conflict (interned : Data.ClauseArena.Builder.InternResult)

/--
向常驻 CDCL 状态加入一个 theory solver 给出的永久字句。

外部字句先按当前 assignment 安装 watch；若它正好构成冲突，调用方会把该节点直接交给
当前层 1-UIP 分析，而不是预先丢弃整条 trail。该字句不写入命题 resolution journal，
最终可信证书仍由调用者把全部外部字句列为有 theory justification 的 initial clauses
后统一重建。
-/
private def CdclMachine.addExternalClause {σ} (machine : CdclMachine σ)
    (clause : Clause) : ST σ ExternalClauseAdd := do
  let packed := packClause clause
  let status ← inspectClause machine packed
  let interned ← machine.arena.internClause packed
  if interned.isNew then
    machine.installCurrentWatches interned.id packed
    for lit in packed do
      let var := Data.PackedLit.var lit
      machine.branch.bump var
      if (← machine.assignmentCodeAt var) == assignmentUnassigned then
        machine.branch.release var
  match status with
  | .conflict => return .conflict interned
  | .unit lit =>
      let _ ← machine.assign lit interned.id
      return .accepted interned
  | .satisfied | .unresolved => return .accepted interned

/-- learned clause 中的变量获得 activity；重复变量已由规范字句消除。 -/
private def bumpLearnedActivity {σ} (machine : CdclMachine σ)
    (learned : PackedClause) : ST σ Unit := do
  for lit in learned do
    machine.branch.bump (Data.PackedLit.var lit)

private def commitLearned {σ} (machine : CdclMachine σ) (analysis : ConflictAnalysis)
    (learned : PackedClause) (assertLit? : Option Data.PackedLit) : ST σ Data.ClauseId := do
  let interned ← addLearnedClause machine learned assertLit?
  match interned with
  | .inserted id =>
      let stepsStart ← machine.journalSteps.size
      machine.journalSteps.appendArray analysis.steps
      machine.journalLearns.push {
        clause := id.raw
        start := analysis.start
        stepsStart := stepsStart
        stepsLength := analysis.steps.size
      }
  | .existing _ =>
      pure ()
  return interned.id

private def finishUnsat {σ} (machine : CdclMachine σ) (analysis : ConflictAnalysis)
    (learned : PackedClause) : ST σ Result := do
  let _ ← commitLearned machine analysis learned none
  return {
    outcome := .unsat
    proof := ← machine.freezeProof
    stats := ← machine.searchStats
  }

private inductive ConflictSource where
  | propagated
  | external

/--
处理一个已经登记进 arena 的冲突字句。

返回 `none` 表示已经完成回跳、学习与 asserting literal 赋值，可以继续搜索；返回结果
表示 UNSAT 或内部不变量错误已经终止当前 CDCL 生命周期。外部字句可能完全不含机器
最高决策层的文字，因此直接以该字句实际涉及的最高层执行分析，再一次性回跳；它不计入
命题核自身的 conflict 统计，但随后使用完全相同的学习与 asserting literal 规则。
-/
private def resolveConflict? {σ} (machine : CdclMachine σ)
    (conflictId : Data.ClauseId) (source : ConflictSource) : ST σ (Option Result) := do
  let analysisLevel ←
    match source with
    | .propagated =>
        machine.branch.finishConflict
        machine.level.get
    | .external => machine.clauseMaxLevel conflictId
  if analysisLevel == 0 then
    let analysis ← analyzeFinalConflict machine conflictId
    if analysis.tautological then
      return some (← learnedInvariantError machine
        "level-0 learned clause is tautological" analysis analysis.learned)
    else if analysis.learned.isEmpty then
      return some (← finishUnsat machine analysis analysis.learned)
    else
      return some (← learnedInvariantError machine
        "level-0 conflict did not derive the empty clause" analysis analysis.learned)
  let analysis ← analyzeConflictAtLevel machine conflictId analysisLevel
  match ← assertingLiteralAfterBackjump? machine analysis with
  | .error message =>
      return some (← invariantViolation machine
        s!"{message}; currentLevel={← machine.level.get}, \
        clauses={← machine.arena.size}, journal={← machine.journalLearns.size}")
  | .ok assertLit? =>
      let learned := analysis.learned
      if learned.isEmpty then
        return some (← finishUnsat machine analysis learned)
      bumpLearnedActivity machine learned
      let learnedId ← commitLearned machine analysis learned assertLit?
      if let some assertLit := assertLit? then
        let _ ← machine.assign assertLit learnedId
      return none

private partial def cdclLoop {σ} (machine : CdclMachine σ) (fuel : Nat) : ST σ Result := do
  match fuel with
  | 0 =>
      return {
        outcome := .limitExhausted (← machine.snapshot)
        proof := ← machine.freezeProof
        stats := ← machine.searchStats
      }
  | fuel + 1 =>
      match ← propagateWatched machine with
      | some conflictId =>
          match ← resolveConflict? machine conflictId .propagated with
          | some result => return result
          | none => cdclLoop machine fuel
      | none =>
          match ← chooseBranch? machine with
          | none =>
              return {
                outcome := .sat (← machine.freezeAssignment)
                proof := ← machine.freezeProof
                stats := ← machine.searchStats
              }
          | some (var, value) =>
              machine.decide var value
              cdclLoop machine fuel

private def processInitialUnits {σ} (machine : CdclMachine σ) : ST σ Unit := do
  let clauseCount ← machine.arena.size
  for index in [:clauseCount] do
    let id : Data.ClauseId := Data.Id.ofIndex index
    if let some header ← machine.arena.header? id then
      if header.length == 1 then
        let lit ← machine.arena.litAt! header 0
        let _ ← machine.assign lit id

private def firstEmptyClauseIndex? (clauses : Array Clause) : Option Nat := Id.run do
  for h : index in [:clauses.size] do
    if clauses[index].isEmpty then
      return some index
  return none

private def emptyInitialProof (clauses : Array Clause) (index : Nat) : CdclProof :=
  runST fun σ => do
    let arena ← Data.ClauseArena.Builder.empty (σ := σ)
    for clause in clauses do
      let _ ← arena.pushClause (packClause clause)
    let startId : Data.ClauseId := Data.Id.ofIndex index
    let learnedId ← arena.pushClause #[] Data.learnedClauseFlag
    return {
      arena := ← arena.freeze
      journal := {
        steps := #[]
        learns := #[{
          clause := learnedId.raw
          start := startId.raw
          stepsStart := 0
          stepsLength := 0
        }]
      }
    }

private def litMaxVarSucc (lit : Lit) : Nat :=
  lit.var + 1

private def clauseMaxVarSucc (clause : Clause) : Nat := Id.run do
  let mut out := 0
  for lit in clause do
    out := Nat.max out (litMaxVarSucc lit)
  return out

/-- 命题子句集里实际出现的最大变量编号加一。 -/
def maxVarSucc (clauses : Array Clause) : Nat := Id.run do
  let mut out := 0
  for clause in clauses do
    out := Nat.max out (clauseMaxVarSucc clause)
  return out

/-- 运行公共 CDCL 搜索核。输入字句会按实际最大变量数扩展 assignment 宽度。 -/
def solve (config : Config) (numVars : Nat) (clauses : Array Clause) : Result :=
  let numVars := Nat.max numVars (maxVarSucc clauses)
  match firstEmptyClauseIndex? clauses with
  | some index =>
      {
        outcome := .unsat
        proof := emptyInitialProof clauses index
        stats := {}
      }
  | none =>
      runST fun σ => do
        let machine ← CdclMachine.init (σ := σ) numVars clauses
        processInitialUnits machine
        cdclLoop machine config.maxSteps

/-- 从带来源的初始字句运行公共 CDCL 搜索核。 -/
def solveInitial (config : Config) (numVars : Nat)
    (initialClauses : Array InitialClause) : Result :=
  solve config numVars (initialClauseDatabase initialClauses)

/-- 若搜索给出可检查 UNSAT，则返回 checked certificate。 -/
def checkedUnsat? (config : Config) (numVars : Nat)
    (initialClauses : Array InitialClause) : Option CheckedUnsatCertificate :=
  let result := solveInitial config numVars initialClauses
  match result.outcome with
  | .unsat => CheckedUnsatCertificate.mk? initialClauses result.proof
  | _ => none

/-! ## 常驻增量 CDCL / theory solver 协调接口 -/

namespace Incremental

/-- 常驻 CDCL 与 theory solver 的联合运行边界。 -/
structure Config where
  cdcl : PropCdcl.Config := {}
  maxTheoryRounds : Nat := 256
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/--
theory solver 对一个完整命题模型的回应。

`conflict` 必须给出当前 assignment 下为假的永久命题字句。证据只由外层保存，最终
材料化为 theory-conflict / propositional-learned-clause DAG 节点。
-/
inductive TheoryResponse (τ ε : Type) where
  | model (state : τ)
  | conflict (state : τ) (clause : Clause) (evidence : ε)
  | unknown (state : τ) (message : String)

/-- 常驻双核协调循环的停止原因。 -/
inductive Outcome where
  | unsat
  | model (assignment : Array (Option Bool))
  | limitExhausted (snapshot : Snapshot)
  | invariantViolation (message : String) (snapshot : Snapshot)
  | theoryUnknown (message : String)

/--
常驻双核协调结果。

`theoryClauses` 与 `theoryEvidence` 一一对应。这里保存的是搜索产物，不是最终 checked
certificate；UNSAT 后调用者应把这些字句作为有 theory justification 的 initial clauses
重新运行 `checkedUnsat?`。
-/
structure RunResult (τ ε : Type) where
  outcome : Outcome
  state : τ
  theoryClauses : Array Clause
  theoryEvidence : Array ε
  stats : SearchStats
  theoryRounds : Nat

private def outcomeOfCdcl : PropCdcl.Outcome → Outcome
  | .unsat => .unsat
  | .sat assignment => .model assignment
  | .limitExhausted snapshot => .limitExhausted snapshot
  | .invariantViolation message snapshot => .invariantViolation message snapshot

private def finish {τ ε : Type} (result : PropCdcl.Result) (state : τ)
    (theoryClauses : Array Clause) (theoryEvidence : Array ε)
    (theoryRounds : Nat) : RunResult τ ε :=
  {
    outcome := outcomeOfCdcl result.outcome
    state := state
    theoryClauses := theoryClauses
    theoryEvidence := theoryEvidence
    stats := result.stats
    theoryRounds := theoryRounds
  }

private def finishTheoryUnknown {τ ε : Type} (machine : CdclMachine σ)
    (state : τ) (theoryClauses : Array Clause) (theoryEvidence : Array ε)
    (theoryRounds : Nat) (message : String) : ST σ (RunResult τ ε) := do
  return {
    outcome := .theoryUnknown message
    state := state
    theoryClauses := theoryClauses
    theoryEvidence := theoryEvidence
    stats := ← machine.searchStats
    theoryRounds := theoryRounds
  }

private def loop {τ ε : Type} (config : Config)
    (machine : CdclMachine σ) (remainingRounds : Nat) (theoryRounds : Nat)
    (state : τ) (theoryClauses : Array Clause) (theoryEvidence : Array ε)
    (theory : τ → Array (Option Bool) → TheoryResponse τ ε) :
    ST σ (RunResult τ ε) := do
  match remainingRounds with
  | 0 =>
      return {
        outcome := .theoryUnknown
          "incremental CDCL/theory coordination exhausted its round limit"
        state := state
        theoryClauses := theoryClauses
        theoryEvidence := theoryEvidence
        stats := ← machine.searchStats
        theoryRounds := theoryRounds
      }
  | remainingRounds + 1 =>
      let result ← cdclLoop machine config.cdcl.maxSteps
      match result.outcome with
      | .sat assignment =>
          match theory state assignment with
          | .model state =>
              return finish result state theoryClauses theoryEvidence theoryRounds
          | .unknown state message =>
              finishTheoryUnknown machine state theoryClauses theoryEvidence theoryRounds message
          | .conflict state rawClause evidence =>
              match canonicalClause? rawClause with
              | none =>
                  finishTheoryUnknown machine state theoryClauses theoryEvidence theoryRounds
                    "theory solver returned a tautological conflict clause"
              | some clause =>
                  match ← machine.addExternalClause clause with
                  | .accepted interned =>
                      let nextClauses :=
                        if interned.isNew then theoryClauses.push clause else theoryClauses
                      let nextEvidence :=
                        if interned.isNew then theoryEvidence.push evidence else theoryEvidence
                      loop config machine remainingRounds (theoryRounds + 1) state
                        nextClauses nextEvidence theory
                  | .conflict interned =>
                      let nextClauses :=
                        if interned.isNew then theoryClauses.push clause else theoryClauses
                      let nextEvidence :=
                        if interned.isNew then theoryEvidence.push evidence else theoryEvidence
                      match ← resolveConflict? machine interned.id .external with
                      | some result =>
                          return finish result state nextClauses nextEvidence
                            (theoryRounds + 1)
                      | none =>
                          loop config machine remainingRounds (theoryRounds + 1) state
                            nextClauses nextEvidence theory
      | .unsat | .limitExhausted _ | .invariantViolation .. =>
          return finish result state theoryClauses theoryEvidence theoryRounds

/--
运行常驻增量 CDCL / theory solver 协调循环。

基础命题字句只装载一次；每个 theory conflict 永久加入同一个 machine，保留 learned
clauses、watch、phase 与 activity。该接口只负责搜索，最终证书仍由外层统一重建。
-/
def run {τ ε : Type} (config : Config) (numVars : Nat)
    (initialClauses : Array Clause) (initialState : τ)
    (theory : τ → Array (Option Bool) → TheoryResponse τ ε) :
    RunResult τ ε :=
  let numVars := Nat.max numVars (maxVarSucc initialClauses)
  match firstEmptyClauseIndex? initialClauses with
  | some _ =>
      {
        outcome := .unsat
        state := initialState
        theoryClauses := #[]
        theoryEvidence := #[]
        stats := {}
        theoryRounds := 0
      }
  | none =>
      runST fun σ => do
        let machine ← CdclMachine.init (σ := σ) numVars initialClauses
        processInitialUnits machine
        loop config machine config.maxTheoryRounds 0 initialState #[] #[] theory

end Incremental

end PropCdcl
end Automation
end YesMetaZFC
