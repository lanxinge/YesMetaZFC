import Lean.Meta.Native
import YesMetaZFC.Automation.Request.GoalAttempt
import YesMetaZFC.Automation.ReplayQuotation
import YesMetaZFC.Automation.CheckerSeal
import YesMetaZFC.Automation.SearchReplayMaterial
import YesMetaZFC.Automation.HODAGCertificate.LinearReplay
import YesMetaZFC.Automation.HOReplayQuotation
/-!
# Checked provider 的内核证明项重放
元层只负责把已物化的纯数据 checker 拆成小的布尔等式，并为每一段建立普通
Lean 证明项。这里不运行搜索，也不生成对象语义证明；Arena 默认票据使用 Lean
官方 native reflection，`prove_auto AUDIT` 则完整重建纯 Lean 完备性证明。
-/
namespace YesMetaZFC
namespace Automation
namespace KernelReplay
open Lean Meta
initialize registerTraceClass `YesMetaZFC.proveAuto.kernelReplay
register_option prove_auto.replay.strictAudit : Bool := {
  defValue := false
  descr := "rebuild replay completeness with pure Lean proofs instead of erasable native tickets"
}
private def traceRemainingHeartbeats (label : String) : MetaM Unit := do
  let remaining ← getRemainingHeartbeats
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "{label}; remainingHb={remaining / 1000}"
def failureAttemptExpr (goal : Expr) (summary : String) : Expr :=
  mkApp2 (mkConst ``ProveAutoRequest.GoalAttempt.failure) goal (toExpr summary)
structure PreprocessingPayloadExprs where
  payload : Expr
  definitionalCnf : Expr
/--
按 checked preprocessing 的确定性阶段构造语义 payload。
这里只引用 concrete trace 与初始 NNF，后续阶段统一由内核中的纯构造器重建，避免
直接报价搜索端完整 payload 后要求内核归约大型递归数据。
-/
def preprocessingPayloadExprs (sourceExpr normalizedExpr settingsExpr : Expr) (normalizationTrace : CoreSyntax.NormalForm.Trace)
    (initialNnf : CoreSyntax.NormalForm.Nnf) : MetaM PreprocessingPayloadExprs := do
  let normalizationTraceExpr := toExpr normalizationTrace
  let initialNnfExpr := toExpr initialNnf
  let antiPrenexConfig ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Settings.antiPrenex
      #[settingsExpr]
  let antiPrenexExpr ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.build
      #[antiPrenexConfig, initialNnfExpr]
  let localSkolemConfig ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Settings.localSkolem
      #[settingsExpr]
  let antiPrenexResult ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.result #[antiPrenexExpr]
  let localSkolemExpr ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.build
      #[localSkolemConfig, antiPrenexResult]
  let definitionalCnfConfig ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Settings.definitionalCnf
      #[settingsExpr]
  let localSkolemResult ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.result #[localSkolemExpr]
  let definitionalCnfExpr ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.build
      #[definitionalCnfConfig, toExpr ([] : List CoreSyntax.CoreSort),
        localSkolemResult]
  let clausesExpr ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.clauses
      #[definitionalCnfExpr]
  let statsExpr ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.statsOf
      #[settingsExpr, sourceExpr, normalizationTraceExpr,
        antiPrenexExpr, localSkolemExpr, definitionalCnfExpr]
  let payloadExpr ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.mk
      #[settingsExpr, sourceExpr, normalizedExpr,
        normalizationTraceExpr, initialNnfExpr, antiPrenexExpr,
        localSkolemExpr, definitionalCnfExpr, clausesExpr, statsExpr]
  return {
    payload := payloadExpr
    definitionalCnf := definitionalCnfExpr
  }
def preprocessingPayloadExpr (sourceExpr normalizedExpr settingsExpr : Expr) (normalizationTrace : CoreSyntax.NormalForm.Trace)
    (initialNnf : CoreSyntax.NormalForm.Nnf) : MetaM Expr := do
  return (← preprocessingPayloadExprs sourceExpr normalizedExpr settingsExpr
    normalizationTrace initialNnf).payload
private def cacheProof (proofType proof : Expr) : MetaM Expr := do
  let proof := mkExpectedPropHint proof proofType
  let lemmaName ← withOptions (fun options =>
        maxRecDepth.set (Elab.async.set options false) 100000) do
    mkAuxLemma [] proofType proof
  return mkConst lemmaName
/--
把大型纯数据 quotation 固化为共享辅助定义。
定义体仍由内核检查；`compile := false` 只表示这些证明期数据不生成可执行代码。
后续 checker 与等式证明引用同一常量，避免在每个 proof type 中重复携带完整数据树。
-/
def cacheReplayData (kind : Name) (expression : Expr) : MetaM Expr := do
  let expressionType ← inferType expression
  let definitionName ← mkAuxDeclName (kind := kind)
  withOptions (fun options =>
        maxRecDepth.set (Elab.async.set options false) 100000) do
    mkAuxDefinition definitionName expressionType expression (compile := false)
private def cacheBoolTrueProof (expression proof : Expr) : MetaM Expr := do
  let proofType ← mkEq expression (mkConst ``Bool.true)
  cacheProof proofType proof
/--
把 concrete checker 的真值立即封装成证明无关的签名。
大型计算只在 seal 边界核对一次，后续契约构造不再携带原始证明树。
-/
def sealedBoolTrueProof (expression proof : Expr) : MetaM Expr := do
  let proofType ← mkEq expression (mkConst ``Bool.true)
  let checked := mkExpectedPropHint proof proofType
  let rawSeal ← mkAppM ``CheckerSeal.ofTrue #[checked]
  let sealType ← inferType rawSeal
  let cachedSeal ← cacheProof sealType rawSeal
  mkAppM ``CheckerSeal.checked #[cachedSeal]
private def boolAndArguments? (expression : Expr) : Option (Expr × Expr) :=
  if expression.isAppOfArity ``Bool.and 2 then
    let arguments := expression.getAppArgs
    some (arguments[0]!, arguments[1]!)
  else
    none
private def boolRecAndArguments? (expression : Expr) : Option (Expr × Expr) :=
  if expression.isAppOfArity ``Bool.rec 4 then
    let arguments := expression.getAppArgs
    if arguments[1]!.isConstOf ``Bool.false then
      some (arguments[3]!, arguments[2]!)
    else
      none
  else
    none
private def beqArguments? (expression : Expr) :
    Option (Expr × Expr × Expr × Expr) :=
  if expression.isAppOfArity ``BEq.beq 4 then
    let arguments := expression.getAppArgs
    some (arguments[0]!, arguments[1]!, arguments[2]!, arguments[3]!)
  else
    none
private def isReplayAtomicBool (expression : Expr) : Bool :=
  expression.isAppOfArity ``DAGCertificate.StructuralEq.formula 6 ||
    expression.isAppOfArity ``DAGCertificate.StructuralEq.term 5 ||
      expression.isAppOfArity ``DAGCertificate.StructuralEq.termList 5
private def isExposedBool (expression : Expr) : Bool := (boolAndArguments? expression).isSome || (boolRecAndArguments? expression).isSome ||
    (beqArguments? expression).isSome ||
      isReplayAtomicBool expression ||
      expression.isConstOf ``Bool.true
private def deltaHead? (expression : Expr) : MetaM (Option Expr) := do
  match expression.getAppFn with
  | .const declaration levels =>
      let info ← getConstInfo declaration
      let some value := info.value?
        | return none
      let value := value.instantiateLevelParams info.levelParams levels
      return some (value.beta expression.getAppArgs)
  | _ =>
      return none
private partial def exposeBoolHead (expression : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let expression ← zetaReduce expression
  if isExposedBool expression || fuel == 0 then
    return expression
  let unfolded? ← deltaHead? expression
  if let some unfolded := unfolded? then
    let unfolded ← zetaReduce unfolded
    if isExposedBool unfolded then
      return unfolded
  let function := expression.getAppFn
  let arguments := expression.getAppArgs
  let mut reducedArguments := Array.mkEmpty arguments.size
  for argument in arguments do
    let reducedArgument ←
      if isReplayAtomicBool argument then
        pure argument
      else
        withTransparency .all <| whnf argument
    reducedArguments := reducedArguments.push reducedArgument
  let reducedApplication := mkAppN function reducedArguments
  let reduced ← withTransparency .all <| whnf reducedApplication
  if reduced == expression then
    match unfolded? with
    | some unfolded => exposeBoolHead unfolded (fuel - 1)
    | none => pure expression
  else
    exposeBoolHead reduced (fuel - 1)
def equalityProof (label : String) (left right : Expr) : MetaM Expr := do
  let proofType ← mkEq left right
  let proof := mkExpectedPropHint (← mkEqRefl left) proofType
  try
    cacheProof proofType proof
  catch error =>
    throwError
      "kernel equality replay failed for {label}; left={indentExpr left}\n\
      right={indentExpr right}\nerror:{indentD error.toMessageData}"
def reflectedEqualityBoolProof (label : String) (reflectionTheorem : Name) (left right : Expr) : MetaM Expr := do
  let hEquality ← equalityProof label left right
  let reflected := mkApp2 (mkConst reflectionTheorem) left right
  mkAppM ``Iff.mpr #[reflected, hEquality]
private def termEqualityProof (label : String) (left right : Expr) : MetaM Expr := do
  try
    equalityProof label left right
  catch directError =>
    unless right.isAppOfArity ``DAGCertificate.Term.renameFreeVars 3 do
      throw directError
    let arguments := right.getAppArgs
    let source := arguments[2]!
    let hSource ← equalityProof (label ++ ".source") left source
    let hOffset ←
      equalityProof (label ++ ".offset") arguments[1]! (toExpr 0)
    let hRename ←
      mkAppM ``DAGCertificate.Term.eq_renameFreeVars_of_offset_eq_zero
        #[source, arguments[1]!, hOffset]
    let proof ← mkAppM ``Eq.trans #[hSource, hRename]
    let proofType ← mkEq left right
    cacheProof proofType proof

private def dependencyBoolProof? (expression : Expr) : MetaM (Option Expr) := do
  if expression.isAppOfArity ``DAGCertificate.StructuralEq.formula 6 then
    let arguments := expression.getAppArgs
    let equality ← equalityProof "DAG formula structural equality"
      arguments[4]! arguments[5]!
    let proof ←
      mkAppM ``DAGCertificate.StructuralEq.formula_eq_true_of_eq #[equality]
    try
      return some (← cacheBoolTrueProof expression proof)
    catch _ =>
      return none
  if expression.isAppOfArity ``DAGCertificate.StructuralEq.term 5 then
    let arguments := expression.getAppArgs
    let equality ← termEqualityProof "DAG term structural equality"
      arguments[3]! arguments[4]!
    let proof ←
      mkAppM ``DAGCertificate.StructuralEq.term_eq_true_of_eq #[equality]
    try
      return some (← cacheBoolTrueProof expression proof)
    catch _ =>
      return none
  if expression.isAppOfArity ``DAGCertificate.StructuralEq.termList 5 then
    let arguments := expression.getAppArgs
    let equality ← equalityProof "DAG term-list structural equality"
      arguments[3]! arguments[4]!
    let proof ←
      mkAppM ``DAGCertificate.StructuralEq.termList_eq_true_of_eq #[equality]
    try
      return some (← cacheBoolTrueProof expression proof)
    catch _ =>
      return none
  if expression.isAppOfArity
      ``CoreSyntax.NormalForm.AntiPrenex.Dependency.checkFor 2 then
    let arguments := expression.getAppArgs
    let proof ←
      mkAppM ``CoreSyntax.NormalForm.AntiPrenex.Dependency.checkFor_ofNnf
        #[arguments[1]!]
    try
      return some (← cacheBoolTrueProof expression proof)
    catch _ =>
      return none
  if expression.isAppOfArity
      ``CoreSyntax.NormalForm.AntiPrenex.Dependency.eq 2 then
    let arguments := expression.getAppArgs
    let proof ←
      mkAppM ``CoreSyntax.NormalForm.AntiPrenex.Dependency.eq_self
        #[arguments[0]!]
    try
      return some (← cacheBoolTrueProof expression proof)
    catch _ =>
      return none
  if expression.isAppOfArity
      ``CoreSyntax.NormalForm.AntiPrenexPayload.check 1 then
    let payload := expression.getAppArgs[0]!
    let config ←
      mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.config #[payload]
    let source ←
      mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.source #[payload]
    let proof ←
      mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.check_build
        #[config, source]
    try
      return some (← cacheBoolTrueProof expression proof)
    catch _ =>
      return none
  return none

/--
把一个具体纯数据 checker 的 `= true` 拆成普通内核证明项。
`fuel` 只限制 proof-term 构造时的布尔表达式拆分，不改变任何搜索资源阈值。
-/
partial def boolTrueProof (label : String) (expression : Expr) (fuel : Nat := 64) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if let some proof ← dependencyBoolProof? expression then
    return proof
  let directProof ← mkEqRefl (mkConst ``Bool.true)
  try
    cacheBoolTrueProof expression directProof
  catch directError =>
    if fuel == 0 then
      throwError
        "kernel replay decomposition exhausted for {label}:{indentD directError.toMessageData}"
    let exposed ← exposeBoolHead expression
    if let some proof ← dependencyBoolProof? exposed then
      return proof
    if exposed.isConstOf ``Bool.true then
      return ← cacheBoolTrueProof expression (← mkEqRefl exposed)
    let split? :=
      boolAndArguments? exposed |>.orElse fun _ =>
        boolRecAndArguments? exposed
    let some (left, right) := split?
      | match beqArguments? exposed with
        | some (alpha, beqInstance, left, right) => do
            let equality ← equalityProof (label ++ ".beq") left right
            let equivalence ←
              mkAppOptM ``beq_iff_eq
                #[some alpha, some beqInstance, none, some left, some right]
            let combined ← mkAppM ``Iff.mpr #[equivalence, equality]
            return ← cacheBoolTrueProof expression combined
        | none =>
            throwError
              "kernel replay failed for {label}; head={repr exposed.getAppFn}; \
              args={exposed.getAppNumArgs} on{indentExpr exposed}\n\
              error:{indentD directError.toMessageData}"
    let boolType := mkConst ``Bool
    let leftType ← inferType left
    let rightType ← inferType right
    unless ← isDefEq leftType boolType do
      throwError
        "kernel replay produced a non-Bool left branch for {label}:\
        {indentExpr left}\ntype:{indentExpr leftType}"
    unless ← isDefEq rightType boolType do
      throwError
        "kernel replay produced a non-Bool right branch for {label}:\
        {indentExpr right}\ntype:{indentExpr rightType}"
    let leftProof ← boolTrueProof (label ++ ".left") left (fuel - 1)
    let rightProof ← boolTrueProof (label ++ ".right") right (fuel - 1)
    let conjunction ← mkAppM ``And.intro #[leftProof, rightProof]
    let equivalence ←
      mkAppOptM ``Bool.and_eq_true_iff #[some left, some right]
    let combined ← mkAppM ``Iff.mpr #[equivalence, conjunction]
    try
      return ← cacheBoolTrueProof expression combined
    catch error =>
      throwError
        "kernel replay composition failed for {label}:{indentD error.toMessageData}"

/-- 用 Lean 官方 native reflection 为一个闭合 Bool 建立局部真值 ticket。 -/
private def nativeBoolTrueProof
    (label : Name) (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then
    throwError
      "native replay retained metavariables{indentExpr expression}"
  if expression.hasFVar then
    throwError
      "native replay retained free variables{indentExpr expression}"
  let heartbeatStart ← getRemainingHeartbeats
  let timeStart ← IO.monoNanosNow
  match ← nativeEqTrue label expression with
  | .notTrue =>
      throwError
        "native replay checker rejected the materialized certificate"
  | .success proof =>
      let timeStop ← IO.monoNanosNow
      let heartbeatStop ← getRemainingHeartbeats
      trace[YesMetaZFC.proveAuto.kernelReplay]
        "native replay ticket established; elapsedNs={timeStop - timeStart}; \
          usedHb={(heartbeatStart - heartbeatStop) / 1000}"
      pure proof

/-- 把已有 Bool 真值证明定向到定义等价的目标 checker。 -/
def retargetBoolTrueProof
    (description : String) (targetExpression proof : Expr) : MetaM Expr := do
  let expectedType ← mkEq targetExpression (mkConst ``Bool.true)
  let nativeType ← inferType proof
  unless ← withTransparency .all <| isDefEq nativeType expectedType do
    throwError
      "replay ticket does not align with {description}"
  let typeEquality ← mkEq nativeType expectedType
  let typeEqualityProof :=
    mkExpectedPropHint (← mkEqRefl nativeType) typeEquality
  mkAppM ``Eq.mp #[typeEqualityProof, proof]

def nativeBoolTrueProofFor
    (nativeLabel : Name) (description : String)
    (nativeExpression targetExpression : Expr) : MetaM Expr := do
  let proof ← nativeBoolTrueProof nativeLabel nativeExpression
  retargetBoolTrueProof description targetExpression proof

/--
默认使用可擦除 native ticket；`prove_auto AUDIT` 对同一目标重建纯 Lean 证明。
-/
def erasableBoolTrueProof
    (nativeLabel : Name) (description : String)
    (nativeExpression targetExpression : Expr) : MetaM Expr := do
  if (← getOptions).getBool `prove_auto.replay.strictAudit false then
    boolTrueProof description targetExpression
  else
    nativeBoolTrueProofFor nativeLabel description
      nativeExpression targetExpression

def boolAndChain (expressions : Array Expr) : MetaM Expr := do
  if expressions.isEmpty then
    return mkConst ``Bool.true
  let mut index := expressions.size - 1
  let mut result := expressions[index]!
  while index > 0 do
    index := index - 1
    result ← mkAppM ``Bool.and #[expressions[index]!, result]
  pure result

partial def splitBoolAndTrueProofs
    (expressions : Array Expr) (proof : Expr) : MetaM (Array Expr) := do
  if expressions.isEmpty then
    return #[]
  if expressions.size == 1 then
    return #[proof]
  let tail := expressions.extract 1 expressions.size
  let tailExpression ← boolAndChain tail
  let equivalence ←
    mkAppOptM ``Bool.and_eq_true_iff
      #[some expressions[0]!, some tailExpression]
  let fields ← mkAppM ``Iff.mp #[equivalence, proof]
  let headProof ← mkAppM ``And.left #[fields]
  let tailProof ← mkAppM ``And.right #[fields]
  return #[headProof] ++ (← splitBoolAndTrueProofs tail tailProof)

/--
把同一阶段的多个 Bool 检查合并成一张 native ticket，降低临时编译固定成本。
严格审计时逐项调用纯 Lean producer，返回顺序与输入完全一致。
-/
def erasableBoolTrueProofs
    (nativeLabel : Name) (descriptions : Array String)
    (nativeExpressions targetExpressions : Array Expr) :
    MetaM (Array Expr) := do
  unless descriptions.size == targetExpressions.size &&
      nativeExpressions.size == targetExpressions.size do
    throwError "erasable replay proof bundle has inconsistent field counts"
  if targetExpressions.isEmpty then
    return #[]
  if (← getOptions).getBool `prove_auto.replay.strictAudit false then
    let mut proofs := #[]
    for index in [0 : targetExpressions.size] do
      proofs := proofs.push
        (← boolTrueProof descriptions[index]! targetExpressions[index]!)
    return proofs
  let nativeExpression ← boolAndChain nativeExpressions
  let targetExpression ← boolAndChain targetExpressions
  let proof ←
    nativeBoolTrueProofFor nativeLabel "bundled proof-only replay quotation"
      nativeExpression targetExpression
  splitBoolAndTrueProofs targetExpressions proof

private def arrayGetElem? (array index : Expr) : MetaM Expr :=
  mkAppM ``getElem? #[array, index]

private def clauseIdExpr (raw : Nat) : MetaM Expr :=
  mkAppOptM ``Data.Id.ofNat
    #[some (mkConst ``Data.ClauseTag), some (toExpr raw)]

private partial def reasonTableRange?
    (database : Array PropResolution.Clause)
    (start length : Nat) : Option PropResolution.ReasonTable := do
  if length == 0 then
    return .empty
  if length == 1 then
    return .leaf (← database[start]?)
  let leftLength := length / 2
  let rightLength := length - leftLength
  let left ← reasonTableRange? database start leftLength
  let right ←
    reasonTableRange? database (start + leftLength) rightLength
  return .branch leftLength left right

private def reasonTable?
    (database : Array PropResolution.Clause) :
    Option PropResolution.ReasonTable :=
  reasonTableRange? database 0 database.size

private def compactResolutionCursorProof
    (database : Array PropResolution.Clause)
    (proof : PropResolution.CdclProof)
    (record : PropResolution.LearnRecord)
    (databaseExpr journalExpr startExpr targetExpr : Expr) :
    MetaM Expr := do
  let some table := reasonTable? database
    | throwError "residual CDCL reason table construction failed"
  let tableExpr ←
    cacheReplayData `_replayResidualReasonTable (toExpr table)
  let databaseListExpr ← mkAppM ``Array.toList #[databaseExpr]
  let tableCheck ←
    mkAppM ``PropResolution.ReasonTable.checkAgainst
      #[databaseListExpr, tableExpr]
  let tableHeartbeatStart ← getRemainingHeartbeats
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "start residual reason table seal: leaves={database.size}"
  let hTable ←
    sealedBoolTrueProof tableCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let tableHeartbeatStop ← getRemainingHeartbeats
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "sealed residual reason table; usedHb={(tableHeartbeatStart - tableHeartbeatStop) / 1000}; \
      remainingHb={tableHeartbeatStop / 1000}"
  let steps := proof.journal.steps.toList.drop record.stepsStart
  let chunkSize : Nat := 8
  let current0 ←
    match (Data.Id.ofNat record.start : Data.ClauseId).index? with
    | some index =>
        match database[index]? with
        | some clause => pure clause
        | none =>
            throwError
              "residual CDCL cursor starts outside the current database"
    | none =>
        throwError "residual CDCL cursor has an invalid start clause id"
  let mut chunks :
      Array (Array PropResolution.CompactResolutionStep ×
        PropResolution.Clause × PropResolution.Clause) := #[]
  let mut offset := 0
  let mut current := current0
  let mut currentWork := 0
  let mut reasonWork := 0
  let mut resultWork := 0
  let mut maxCurrent := current0.size
  let mut maxReason := 0
  let mut maxResult := current0.size
  while offset < record.stepsLength do
    let length := min chunkSize (record.stepsLength - offset)
    let chunk := (steps.drop offset |>.take length).toArray
    let mut next := current
    for step in chunk do
      let some reasonIndex :=
          (Data.Id.ofNat step.reason : Data.ClauseId).index?
        | throwError "residual CDCL cursor found an invalid reason id"
      let some reason := database[reasonIndex]?
        | throwError "residual CDCL cursor found an invalid reason index"
      currentWork := currentWork + next.size
      reasonWork := reasonWork + reason.size
      maxCurrent := max maxCurrent next.size
      maxReason := max maxReason reason.size
      let some plan :=
          PropResolution.resolutionPlan? next reason step.pivot
        | throwError "residual CDCL cursor found an invalid resolution plan"
      next := plan.result
      resultWork := resultWork + next.size
      maxResult := max maxResult next.size
    chunks := chunks.push (chunk, current, next)
    current := next
    offset := offset + length
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "residual cursor width profile: steps={record.stepsLength}; \
      start={current0.size}; final={current.size}; \
      currentWork={currentWork}; reasonWork={reasonWork}; \
      resultWork={resultWork}; maxCurrent={maxCurrent}; \
      maxReason={maxReason}; maxResult={maxResult}"
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  let arenaTarget := PropResolution.arenaClause proof.arena learnedId
  unless current = arenaTarget do
    throwError
      "residual CDCL cursor result differs from arena target; \
        computedSize={current.size}; arenaSize={arenaTarget.size}"
  let emptyStepsExpr :=
    toExpr ([] : List PropResolution.CompactResolutionStep)
  let mut tailExpr := emptyStepsExpr
  let mut checked? : Option Expr := none
  for (chunk, chunkStart, chunkStop) in chunks.reverse do
    let chunkHeartbeatStart ← getRemainingHeartbeats
    unless
        PropResolution.compactResolutionCursorValid table chunk.size
          chunk.toList chunkStart chunkStop do
      throwError
        "residual CDCL concrete cursor chunk failed before quotation; \
          steps={chunk.size}; startSize={chunkStart.size}; \
          stopSize={chunkStop.size}"
    let chunkExpr ←
      cacheReplayData `_replayResidualResolutionChunk
        (toExpr chunk.toList)
    let chunkStartExpr ←
      if chunkStart == current0 then
        pure startExpr
      else
        cacheReplayData `_replayResidualResolutionClause
          (toExpr chunkStart)
    let chunkStopExpr ←
      if chunkStop == current then
        pure targetExpr
      else
        cacheReplayData `_replayResidualResolutionClause
          (toExpr chunkStop)
    let chunkCheck ←
      mkAppM ``PropResolution.compactResolutionCursorValid
        #[tableExpr, toExpr chunk.size, chunkExpr,
          chunkStartExpr, chunkStopExpr]
    let hChunk ←
      sealedBoolTrueProof chunkCheck
        (← mkEqRefl (mkConst ``Bool.true))
    let chunkHeartbeatAfterSeal ← getRemainingHeartbeats
    let hLength ←
      equalityProof "residual CDCL cursor chunk length"
        (← mkAppM ``List.length #[chunkExpr]) (toExpr chunk.size)
    let chunkHeartbeatAfterLength ← getRemainingHeartbeats
    checked? ←
      match checked? with
      | none =>
          pure (some hChunk)
      | some checked =>
          some <$> mkAppM
            ``PropResolution.compactResolutionCursorValid_append
            #[hLength, hChunk, checked]
    let chunkHeartbeatAfterAppend ← getRemainingHeartbeats
    tailExpr ← mkAppM ``List.append #[chunkExpr, tailExpr]
    trace[YesMetaZFC.proveAuto.kernelReplay]
      "sealed residual cursor chunk: steps={chunk.size}; \
        sealHb={(chunkHeartbeatStart - chunkHeartbeatAfterSeal) / 1000}; \
        lengthHb={(chunkHeartbeatAfterSeal - chunkHeartbeatAfterLength) / 1000}; \
        appendHb={(chunkHeartbeatAfterLength - chunkHeartbeatAfterAppend) / 1000}; \
        remainingHb={chunkHeartbeatAfterAppend / 1000}"
  let hCursor ←
    match checked? with
    | some checked =>
        pure checked
    | none =>
        let zeroCheck ←
          mkAppM ``PropResolution.compactResolutionCursorValid
            #[tableExpr, toExpr 0, emptyStepsExpr, startExpr, targetExpr]
        sealedBoolTrueProof zeroCheck
          (← mkEqRefl (mkConst ``Bool.true))
  let journalStepsExpr ←
    mkAppM ``PropResolution.LearnJournal.steps #[journalExpr]
  let journalStepsListExpr ←
    mkAppM ``Array.toList #[journalStepsExpr]
  let journalTailExpr ←
    mkAppM ``List.drop
      #[toExpr record.stepsStart, journalStepsListExpr]
  let hSteps ←
    equalityProof "residual CDCL sequential journal"
      journalTailExpr tailExpr
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "sealed residual sequential journal"
  mkAppM
    ``PropResolution.compactResolutionStepsValidAgainst_eq_true_of_cursor
    #[hTable, hSteps, hCursor]

private def residualUnsatProof
    (initialClauses : Array PropResolution.InitialClause)
    (proof : PropResolution.CdclProof)
    (initialClausesExpr proofExpr : Expr) : MetaM Expr := do
  let database := PropResolution.initialClauseDatabase initialClauses
  let databaseExpr ←
    cacheReplayData `_replayResidualInitialDatabase (toExpr database)
  let computedDatabase ←
    mkAppM ``PropResolution.initialClauseDatabase #[initialClausesExpr]
  let databaseHeartbeatStart ← getRemainingHeartbeats
  let hDatabase ←
    equalityProof "residual CDCL initial database"
      computedDatabase databaseExpr
  let databaseHeartbeatStop ← getRemainingHeartbeats
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "sealed residual initial database; \
      usedHb={(databaseHeartbeatStart - databaseHeartbeatStop) / 1000}; \
      remainingHb={databaseHeartbeatStop / 1000}"
  let [record] := proof.journal.learns.toList
    | throwError
        "residual CDCL range replay currently requires one learned record"
  let recordExpr := toExpr record
  let journalExpr ←
    mkAppM ``PropResolution.CdclProof.journal #[proofExpr]
  let learnsExpr ←
    mkAppM ``PropResolution.LearnJournal.learns #[journalExpr]
  let hLearns ←
    equalityProof "residual CDCL learned record"
      learnsExpr (toExpr #[record])
  let recordStart ←
    mkAppM ``PropResolution.LearnRecord.stepsStart #[recordExpr]
  let hStart ←
    equalityProof "residual CDCL learned step start"
      recordStart (toExpr 0)
  let startId : Data.ClauseId := Data.Id.ofNat record.start
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  let some startIndex := startId.index?
    | throwError "residual CDCL record has an invalid start clause id"
  let some learnedIndex := learnedId.index?
    | throwError "residual CDCL record has an invalid learned clause id"
  let some startClause := database[startIndex]?
    | throwError "residual CDCL record starts outside the current database"
  let startIdExpr ← clauseIdExpr record.start
  let learnedIdExpr ← clauseIdExpr record.clause
  let startIndexExpr ←
    mkAppM ``Data.Id.index? #[startIdExpr]
  let learnedIndexExpr ←
    mkAppM ``Data.Id.index? #[learnedIdExpr]
  let hStartId ←
    equalityProof "residual CDCL start id"
      startIndexExpr (toExpr (some startIndex))
  let hLearnedId ←
    equalityProof "residual CDCL learned id"
      learnedIndexExpr (toExpr (some learnedIndex))
  let startClauseExpr ←
    cacheReplayData `_replayResidualStartClause (toExpr startClause)
  let startClauseLookup ←
    arrayGetElem? databaseExpr (toExpr startIndex)
  let expectedStartClause ← mkAppM ``Option.some #[startClauseExpr]
  let hStartClause ←
    equalityProof "residual CDCL start clause"
      startClauseLookup expectedStartClause
  let databaseSize ← mkAppM ``Array.size #[databaseExpr]
  let hLearnedIndex ←
    equalityProof "residual CDCL learned database slot"
      (toExpr learnedIndex) databaseSize
  let sliceCheck ←
    mkAppM ``PropResolution.LearnJournal.stepSliceValid
      #[journalExpr, recordExpr]
  let hSlice ←
    sealedBoolTrueProof sliceCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let arenaExpr ←
    mkAppM ``PropResolution.CdclProof.arena #[proofExpr]
  let targetExpr ←
    mkAppM ``PropResolution.arenaClause #[arenaExpr, learnedIdExpr]
  let hSteps ←
    compactResolutionCursorProof database proof record
      databaseExpr journalExpr startClauseExpr targetExpr
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "composed residual resolution ranges"
  let hRecord ←
    mkAppOptM
      ``PropResolution.compactLearnRecordValidAgainst_eq_true_of_components
      #[some databaseExpr, some proofExpr, some recordExpr,
        some (toExpr startIndex), some (toExpr learnedIndex),
        some startClauseExpr, some hStartId, some hLearnedId,
        some hStartClause, some hLearnedIndex, some hSlice, some hSteps]
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "composed residual learned record"
  let emptyCheck ← mkAppM ``Array.isEmpty #[targetExpr]
  let hEmpty ←
    sealedBoolTrueProof emptyCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let recordLength ←
    mkAppM ``PropResolution.LearnRecord.stepsLength #[recordExpr]
  let stepsExpr ←
    mkAppM ``PropResolution.LearnJournal.steps #[journalExpr]
  let stepsSize ← mkAppM ``Array.size #[stepsExpr]
  let hLength ←
    equalityProof "residual CDCL final step count"
      recordLength stepsSize
  mkAppOptM ``PropResolution.checkedUnsat_eq_true_of_single
    #[some initialClausesExpr, some proofExpr, some databaseExpr,
      some recordExpr, some hDatabase, some hLearns,
      some hStart, some hRecord, some hEmpty, some hLength]

private def residualJustificationsProof
    (parentsExpr payloadExpr : Expr)
    (payload :
      DAGCertificate.PropositionalClosurePayload
        SearchMaterialization.SearchSignature) : MetaM Expr := do
  let some keys :=
      DAGCertificate.PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList
    | throwError
        "residual CDCL replay found a non-propositional justification"
  let keysExpr ←
    cacheReplayData `_replayResidualJustificationKeys (toExpr keys)
  let initialClausesExpr ←
    mkAppM
      ``DAGCertificate.PropositionalClosurePayload.initialClauses
      #[payloadExpr]
  let initialJustificationsExpr ←
    mkAppM
      ``DAGCertificate.PropositionalClosurePayload.initialJustifications
      #[payloadExpr]
  let initialSize ← mkAppM ``Array.size #[initialClausesExpr]
  let justificationSize ←
    mkAppM ``Array.size #[initialJustificationsExpr]
  let sizeCheck ←
    mkAppM ``BEq.beq #[initialSize, justificationSize]
  let hSize ←
    sealedBoolTrueProof sizeCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let initialJustificationsList ←
    mkAppM ``Array.toList #[initialJustificationsExpr]
  let computedKeys ←
    mkAppM
      ``DAGCertificate.PropositionalJustificationKeys.ofJustifications?
      #[initialJustificationsList]
  let expectedKeys ← mkAppM ``Option.some #[keysExpr]
  let hKeys ←
    equalityProof "residual CDCL justification keys"
      computedKeys expectedKeys
  let initialDatabase ←
    mkAppM ``PropResolution.initialClauseDatabase #[initialClausesExpr]
  let initialClauseList ← mkAppM ``Array.toList #[initialDatabase]
  let keyClauses ←
    mkAppM ``DAGCertificate.PropositionalJustificationKeys.clauses
      #[keysExpr]
  let hClauses ←
    equalityProof "residual CDCL justification clauses"
      initialClauseList keyClauses
  let keyParents ←
    mkAppM ``DAGCertificate.PropositionalJustificationKeys.parents
      #[keysExpr]
  let parentList ← mkAppM ``Array.toList #[parentsExpr]
  let hParentList ←
    equalityProof "residual CDCL justification parents"
      keyParents parentList
  let hParents ←
    mkAppM
      ``DAGCertificate.PropositionalJustificationKeys.parentsCheck_eq_true_of_eq
      #[parentsExpr, keysExpr, hParentList]
  let atomMapExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.atomMap
      #[payloadExpr]
  let outsideCheck ←
    mkAppM
      ``DAGCertificate.PropositionalJustificationKeys.outsideAtomMapCheck
      #[atomMapExpr, keysExpr]
  let hOutside ←
    sealedBoolTrueProof outsideCheck
      (← mkEqRefl (mkConst ``Bool.true))
  mkAppM
    ``DAGCertificate.PropositionalClosurePayload.justificationsCheck_eq_true_of_propositionalKeys
    #[parentsExpr, payloadExpr, keysExpr, hSize, hKeys,
      hClauses, hParents, hOutside]

private def residualClosureCheckProof
    (parentsExpr payloadExpr : Expr)
    (payload :
      DAGCertificate.PropositionalClosurePayload
        SearchMaterialization.SearchSignature) : MetaM Expr := do
  let initialClausesExpr ←
    mkAppM
      ``DAGCertificate.PropositionalClosurePayload.initialClauses
      #[payloadExpr]
  let proofExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.proof
      #[payloadExpr]
  let hUnsat ←
    residualUnsatProof payload.initialClauses payload.proof
      initialClausesExpr proofExpr
  let hJustifications ←
    residualJustificationsProof parentsExpr payloadExpr payload
  let statsExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.stats
      #[payloadExpr]
  let computedStatsExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.computedStats
      #[payloadExpr]
  let proveStat (field : Name) : MetaM Expr := do
    let actual ← mkAppM field #[statsExpr]
    let expected ← mkAppM field #[computedStatsExpr]
    let check ← mkAppM ``BEq.beq #[actual, expected]
    sealedBoolTrueProof check (← mkEqRefl (mkConst ``Bool.true))
  let hSteps ←
    proveStat ``Certificate.Stats.steps
  let hClauses ←
    proveStat ``Certificate.Stats.clauses
  let hGenerated ←
    proveStat ``Certificate.Stats.generated
  let hRetained ←
    proveStat ``Certificate.Stats.retained
  let hVerified ←
    proveStat ``Certificate.Stats.verified
  mkAppM
    ``DAGCertificate.PropositionalClosurePayload.check_eq_true_of_components
    #[parentsExpr, payloadExpr, hUnsat, hJustifications,
      hSteps, hClauses, hGenerated, hRetained, hVerified]

private def residualNodeProof
    (dagExpr nodeExpr : Expr) (index : Nat)
    (payload :
      DAGCertificate.PropositionalClosurePayload
        SearchMaterialization.SearchSignature) : MetaM Expr := do
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "start residual node proof #{index}"
  let payloadExpr ←
    cacheReplayData `_replayResidualPayload (toExpr payload)
  let problemExpr ←
    mkAppM ``DAGCertificate.DAG.problem #[dagExpr]
  let ruleTagsCheck ←
    mkAppM ``DAGCertificate.Node.ruleTagsOk #[nodeExpr]
  let hRuleTags ←
    sealedBoolTrueProof ruleTagsCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let parentsExpr ←
    mkAppM ``DAGCertificate.Node.parents #[nodeExpr]
  let parentsEmpty ← mkAppM ``Array.isEmpty #[parentsExpr]
  let parentsNonempty ← mkAppM ``Bool.not #[parentsEmpty]
  let hParentsNonempty ←
    sealedBoolTrueProof parentsNonempty
      (← mkEqRefl (mkConst ``Bool.true))
  let conclusionExpr ←
    mkAppM ``DAGCertificate.Node.conclusion #[nodeExpr]
  let conclusionEmpty ←
    mkAppM ``DAGCertificate.Clause.isEmpty #[conclusionExpr]
  let hConclusion ←
    sealedBoolTrueProof conclusionEmpty
      (← mkEqRefl (mkConst ``Bool.true))
  let hClosure ←
    residualClosureCheckProof parentsExpr payloadExpr payload
  let hPayload ←
    mkAppM
      ``DAGCertificate.Payload.residualCdcl_check_eq_true_of_components
      #[problemExpr, parentsExpr, conclusionExpr, payloadExpr,
        hParentsNonempty, hConclusion, hClosure]
  let hNodePayload ←
    mkAppM ``DAGCertificate.Node.check_eq_true_of_components
      #[problemExpr, nodeExpr, hRuleTags, hPayload]
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "composed residual node payload #{index}"
  let parentSnapshotsCheck ←
    mkAppM ``DAGCertificate.DAG.nodeParentSnapshotsChecked
      #[dagExpr, nodeExpr]
  let hParentSnapshots ←
    sealedBoolTrueProof parentSnapshotsCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let guardsCheck ←
    mkAppM ``DAGCertificate.DAG.nodeGuardsChecked
      #[dagExpr, nodeExpr]
  let hGuards ←
    sealedBoolTrueProof guardsCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let hNode ←
    mkAppM
      ``DAGCertificate.DAG.LinearReplay.nodeCheck_eq_true_of_components
      #[dagExpr, nodeExpr, hNodePayload, hParentSnapshots, hGuards]
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "composed residual linear node #{index}"
  pure hNode

/-- 由固定数量的线性语义 checker 签名构造完整 DAG 契约。 -/
structure DagContractProofs where
  arenaNodes : Expr
  rootExists : Expr
  rootClosed : Expr
  denseIds : Expr
  parentsBefore : Expr

def dagContractProof
    (dagExpr : Expr) (dag : SearchMaterialization.DAG)
    (includeAvatar : Bool) : MetaM DagContractProofs := do
  let dagNodesExpr ← mkAppM ``DAGCertificate.DAG.nodes #[dagExpr]
  let dagNodesListExpr ← mkAppM ``Array.toList #[dagNodesExpr]
  let linearNodesExpr ←
    cacheReplayData `_replayLinearDagNodes (toExpr dag.nodes.toList)
  let hLinearNodes ←
    equalityProof "DAG sequential structural node list"
      dagNodesListExpr linearNodesExpr
  let provePhase (check : Name) (label : String) : MetaM Expr := do
    let expression ← mkAppM check #[dagExpr]
    let heartbeatStart ← getRemainingHeartbeats
    let checked ←
      sealedBoolTrueProof expression (← mkEqRefl (mkConst ``Bool.true))
    let heartbeatStop ← getRemainingHeartbeats
    trace[YesMetaZFC.proveAuto.kernelReplay]
      "sealed DAG {label}; usedHb={(heartbeatStart - heartbeatStop) / 1000}; \
        remainingHb={heartbeatStop / 1000}"
    pure checked
  let hRootExists ←
    provePhase ``DAGCertificate.DAG.rootExists "root existence"
  let hRootClosed ←
    provePhase ``DAGCertificate.DAG.rootClosed "root closure"
  let graphViewExpr ←
    mkAppM ``DAGCertificate.DAG.graphView #[dagExpr]
  let denseListCheck ←
    mkAppM ``DenseDAG.View.denseIdsListCheck
      #[graphViewExpr, linearNodesExpr]
  let denseHeartbeatStart ← getRemainingHeartbeats
  let hDenseList ←
    sealedBoolTrueProof denseListCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let denseHeartbeatStop ← getRemainingHeartbeats
  let hDenseIds ←
    mkAppM ``DAGCertificate.DAG.denseIds_eq_true_of_listCheck
      #[hLinearNodes, hDenseList]
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "sealed DAG dense ids sequentially; \
      usedHb={(denseHeartbeatStart - denseHeartbeatStop) / 1000}; \
      remainingHb={denseHeartbeatStop / 1000}"
  let parentsListCheck ←
    mkAppM ``DenseDAG.View.parentsBeforeListCheck
      #[graphViewExpr, linearNodesExpr]
  let parentsHeartbeatStart ← getRemainingHeartbeats
  let hParentsList ←
    sealedBoolTrueProof parentsListCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let parentsHeartbeatStop ← getRemainingHeartbeats
  let hParentsBefore ←
    mkAppM ``DAGCertificate.DAG.parentsBefore_eq_true_of_listCheck
      #[hLinearNodes, hParentsList]
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "sealed DAG parent order sequentially; \
      usedHb={(parentsHeartbeatStart - parentsHeartbeatStop) / 1000}; \
      remainingHb={parentsHeartbeatStop / 1000}"
  let chunkSize : Nat := 32
  let nodeCheckFn ←
    if includeAvatar then
      mkAppM ``DAGCertificate.DAG.LinearReplay.arenaNodeCheckAvatar
        #[dagExpr]
    else
      mkAppM ``DAGCertificate.DAG.LinearReplay.nodeCheck #[dagExpr]
  let mut chunks : Array (Nat × Array SearchMaterialization.Node) := #[]
  let mut start := 0
  while start < dag.nodes.size do
    let some node := dag.nodes[start]?
      | throwError "DAG node range construction exceeded node storage"
    match node.payload with
    | .residualCdcl _ =>
        chunks := chunks.push (start, #[node])
        start := start + 1
    | _ =>
        let limit := min (start + chunkSize) dag.nodes.size
        let mut stop := start
        let mut regular := true
        while stop < limit && regular do
          let some candidate := dag.nodes[stop]?
            | throwError
                "DAG node range construction exceeded node storage"
          match candidate.payload with
          | .residualCdcl _ =>
              regular := false
          | _ =>
              stop := stop + 1
        chunks := chunks.push (start, dag.nodes.extract start stop)
        start := stop
  let emptyNodesExpr :=
    toExpr ([] : List SearchMaterialization.Node)
  let mut tailExpr := emptyNodesExpr
  let mut checkedNodes ←
    mkAppOptM ``DAGCertificate.DAG.CheckedListChunks.nil
      #[none, some nodeCheckFn]
  for (chunkStart, chunk) in chunks.reverse do
    let chunkExpr ←
      cacheReplayData `_replayLinearNodeChunk (toExpr chunk.toList)
    let checkedChunk ←
      if chunk.size == 1 then
        match chunk[0]? with
        | some node =>
            match node.payload with
            | .residualCdcl payload =>
                let nodeExpr ←
                  cacheReplayData `_replayResidualNode (toExpr node)
                let hNode ←
                  residualNodeProof dagExpr nodeExpr chunkStart payload
                let hArenaNode ←
                  if includeAvatar then
                    let avatarCheck ←
                      mkAppM
                        ``DAGCertificate.DAG.LinearReplay.avatarNodeCheck
                        #[nodeExpr]
                    let hAvatar ←
                      boolTrueProof "DAG fused AVATAR residual node" avatarCheck
                    mkAppM
                      ``DAGCertificate.DAG.LinearReplay.arenaNodeCheckAvatar_eq_true_of_components
                      #[dagExpr, nodeExpr, hNode, hAvatar]
                  else
                    pure hNode
                let checkedNil ←
                  mkAppOptM ``DAGCertificate.DAG.CheckedList.nil
                    #[none, some nodeCheckFn]
                let checkedSingleton ←
                  mkAppOptM ``DAGCertificate.DAG.CheckedList.cons
                    #[none, some nodeCheckFn, some nodeExpr,
                      some emptyNodesExpr, some hArenaNode, some checkedNil]
                mkAppOptM ``DAGCertificate.DAG.CheckedListChunks.cons
                  #[none, some nodeCheckFn, some chunkExpr, some tailExpr,
                    some checkedSingleton, some checkedNodes]
            | _ =>
                let chunkCheck ← mkAppM ``List.all #[chunkExpr, nodeCheckFn]
                let hChunk ←
                  boolTrueProof
                    "DAG sequential node singleton chunk" chunkCheck
                mkAppOptM ``DAGCertificate.DAG.CheckedListChunks.block
                  #[none, some nodeCheckFn, some chunkExpr, some tailExpr,
                    some hChunk, some checkedNodes]
        | _ =>
            let chunkCheck ← mkAppM ``List.all #[chunkExpr, nodeCheckFn]
            let hChunk ←
              boolTrueProof
                "DAG sequential node fallback chunk" chunkCheck
            mkAppOptM ``DAGCertificate.DAG.CheckedListChunks.block
              #[none, some nodeCheckFn, some chunkExpr, some tailExpr,
                some hChunk, some checkedNodes]
      else
        let chunkCheck ← mkAppM ``List.all #[chunkExpr, nodeCheckFn]
        let hChunk ←
          boolTrueProof "DAG sequential node chunk" chunkCheck
        mkAppOptM ``DAGCertificate.DAG.CheckedListChunks.block
          #[none, some nodeCheckFn, some chunkExpr, some tailExpr,
            some hChunk, some checkedNodes]
    trace[YesMetaZFC.proveAuto.kernelReplay]
      "sealed DAG sequential node chunk [{chunkStart}, \
        {chunkStart + chunk.size})"
    tailExpr ← mkAppM ``List.append #[chunkExpr, tailExpr]
    checkedNodes := checkedChunk
  let hNodeList ←
    equalityProof "DAG sequential node list" dagNodesListExpr tailExpr
  let hArenaNodes ←
    if includeAvatar then
      mkAppM
        ``DAGCertificate.DAG.LinearReplay.arenaNodesChecked_eq_true_of_avatar_chunks
        #[hNodeList, checkedNodes]
    else
      mkAppM
        ``DAGCertificate.DAG.LinearReplay.arenaNodesChecked_eq_true_of_plain_chunks
        #[hNodeList, checkedNodes]
  trace[YesMetaZFC.proveAuto.kernelReplay]
    "sealed DAG fused arena node semantics: size={dag.nodes.size}; \
      includeAvatar={includeAvatar}"
  return {
    arenaNodes := hArenaNodes
    rootExists := hRootExists
    rootClosed := hRootClosed
    denseIds := hDenseIds
    parentsBefore := hParentsBefore
  }

/--
高阶 DAG 的严格审计路径按固定结构阶段和小块节点扫描构造契约。
默认路径的聚合 native 票据已经携带同一 `coreCheck` 真值，不再保留第二个整图
native checker 入口。
-/
def higherOrderDagContractProof
    (dagExpr : Expr) (dag : HOSearchMaterialization.DAG) : MetaM Expr := do
  let dagNodesExpr ← mkAppM ``HODAGCertificate.DAG.nodes #[dagExpr]
  let dagNodesListExpr ← mkAppM ``Array.toList #[dagNodesExpr]
  let linearNodesExpr ←
    cacheReplayData `_replayLinearHoDagNodes (toExpr dag.nodes.toList)
  let hLinearNodes ←
    equalityProof "higher-order DAG sequential node list"
      dagNodesListExpr linearNodesExpr
  let provePhase (check : Name) (label : String) : MetaM Expr := do
    let expression ← mkAppM check #[dagExpr]
    let checked ←
      sealedBoolTrueProof expression (← mkEqRefl (mkConst ``Bool.true))
    trace[YesMetaZFC.proveAuto.kernelReplay]
      "sealed higher-order DAG {label}"
    pure checked
  let hRootExists ←
    provePhase ``HODAGCertificate.DAG.rootExists "root existence"
  let hRootClosed ←
    provePhase ``HODAGCertificate.DAG.rootClosed "root closure"
  let graphViewExpr ←
    mkAppM ``HODAGCertificate.DAG.graphView #[dagExpr]
  let denseListCheck ←
    mkAppM ``DenseDAG.View.denseIdsListCheck
      #[graphViewExpr, linearNodesExpr]
  let hDenseList ←
    sealedBoolTrueProof denseListCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let hDenseIds ←
    mkAppM
      ``HODAGCertificate.DAG.LinearReplay.denseIds_eq_true_of_listCheck
      #[hLinearNodes, hDenseList]
  let parentsListCheck ←
    mkAppM ``DenseDAG.View.parentsBeforeListCheck
      #[graphViewExpr, linearNodesExpr]
  let hParentsList ←
    sealedBoolTrueProof parentsListCheck
      (← mkEqRefl (mkConst ``Bool.true))
  let hParentsBefore ←
    mkAppM
      ``HODAGCertificate.DAG.LinearReplay.parentsBefore_eq_true_of_listCheck
      #[hLinearNodes, hParentsList]
  let nodeCheckFn ←
    mkAppM ``HODAGCertificate.DAG.LinearReplay.nodeCheck #[dagExpr]
  let emptyNodesExpr := toExpr ([] : List HOSearchMaterialization.Node)
  let mut tailExpr := emptyNodesExpr
  let mut checkedNodes ←
    mkAppOptM ``DAGCertificate.DAG.CheckedListChunks.nil
      #[none, some nodeCheckFn]
  let chunkSize : Nat := 8
  let mut stop := dag.nodes.size
  while stop > 0 do
    let start := stop - min chunkSize stop
    let chunk := dag.nodes.extract start stop
    let chunkExpr ←
      cacheReplayData `_replayLinearHoNodeChunk (toExpr chunk.toList)
    let chunkCheck ← mkAppM ``List.all #[chunkExpr, nodeCheckFn]
    let hChunk ←
      sealedBoolTrueProof chunkCheck
        (← mkEqRefl (mkConst ``Bool.true))
    checkedNodes ←
      mkAppOptM ``DAGCertificate.DAG.CheckedListChunks.block
        #[none, some nodeCheckFn, some chunkExpr, some tailExpr,
          some hChunk, some checkedNodes]
    tailExpr ← mkAppM ``List.append #[chunkExpr, tailExpr]
    trace[YesMetaZFC.proveAuto.kernelReplay]
      "sealed higher-order DAG node chunk [{start}, {stop})"
    stop := start
  let hNodeList ←
    equalityProof "higher-order DAG sequential node chunks"
      dagNodesListExpr tailExpr
  let hNodes ←
    mkAppM
      ``HODAGCertificate.DAG.LinearReplay.nodesChecked_eq_true_of_chunks
      #[hNodeList, checkedNodes]
  let hCore ←
    mkAppM
      ``HODAGCertificate.DAG.LinearReplay.coreCheck_eq_true_of_components
      #[dagExpr, hRootExists, hRootClosed, hDenseIds, hParentsBefore, hNodes]
  mkAppM ``HODAGCertificate.DAG.LinearReplay.contract_of_coreCheck #[hCore]

structure ReplayExprs where
  payload : Expr
  search : Expr
  checked : Expr
  data : Expr

end KernelReplay
end Automation
end YesMetaZFC
