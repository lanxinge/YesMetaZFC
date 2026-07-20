import YesMetaZFC.Automation.Request
import YesMetaZFC.Automation.ReplayQuotation

/-!
# Checked provider 的内核证明项重放

元层只负责把已物化的纯数据 checker 拆成小的布尔等式，并为每一段建立普通
Lean 证明项。这里不运行搜索、不引用 native reflection，也不生成对象语义证明。
-/

namespace YesMetaZFC
namespace Automation
namespace KernelReplay

open Lean Meta

/-- 构造不携带 soundness 负担的 provider 失败结果。 -/
def failureAttemptExpr (goal : Expr) (summary : String) : Expr :=
  mkApp2 (mkConst ``ProveAutoRequest.GoalAttempt.failure) goal (toExpr summary)

/-- 预处理 payload 及其可直接复用的定义性 CNF 子项。 -/
private structure PreprocessingPayloadExprs where
  payload : Expr
  definitionalCnf : Expr

/--
按 checked preprocessing 的确定性阶段构造语义 payload。

这里只引用 concrete trace 与初始 NNF，后续阶段统一由内核中的纯构造器重建，避免
直接报价搜索端完整 payload 后要求内核归约大型递归数据。
-/
private def preprocessingPayloadExprs
    (sourceExpr normalizedExpr settingsExpr : Expr)
    (normalizationTrace : CoreSyntax.NormalForm.Trace)
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

/-- 构造 checked preprocessing 的确定性语义 payload。 -/
def preprocessingPayloadExpr
    (sourceExpr normalizedExpr settingsExpr : Expr)
    (normalizationTrace : CoreSyntax.NormalForm.Trace)
    (initialNnf : CoreSyntax.NormalForm.Nnf) : MetaM Expr := do
  return (← preprocessingPayloadExprs sourceExpr normalizedExpr settingsExpr
    normalizationTrace initialNnf).payload

private def cacheProof (proofType proof : Expr) : MetaM Expr := do
  let proof := mkExpectedPropHint proof proofType
  let lemmaName ← withOptions
      (fun options =>
        maxRecDepth.set (Elab.async.set options false) 100000) do
    mkAuxLemma [] proofType proof
  return mkConst lemmaName

/--
把大型纯数据 quotation 固化为共享辅助定义。

定义体仍由内核检查；`compile := false` 只表示这些证明期数据不生成可执行代码。
后续 checker 与等式证明引用同一常量，避免在每个 proof type 中重复携带完整数据树。
-/
private def cacheReplayData (kind : Name) (expression : Expr) : MetaM Expr := do
  let expressionType ← inferType expression
  let definitionName ← mkAuxDeclName (kind := kind)
  withOptions
      (fun options =>
        maxRecDepth.set (Elab.async.set options false) 100000) do
    mkAuxDefinition definitionName expressionType expression (compile := false)

private def cacheBoolTrueProof (expression proof : Expr) : MetaM Expr := do
  let proofType ← mkEq expression (mkConst ``Bool.true)
  cacheProof proofType proof

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

private def isExposedBool (expression : Expr) : Bool :=
  (boolAndArguments? expression).isSome ||
    (boolRecAndArguments? expression).isSome ||
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

private partial def exposeBoolHead
    (expression : Expr) (fuel : Nat := 16) : MetaM Expr := do
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

/-- 用普通等式证明项确认两个引用表达式在内核中定义相等。 -/
def equalityProof (label : String) (left right : Expr) : MetaM Expr := do
  let proofType ← mkEq left right
  let proof := mkExpectedPropHint (← mkEqRefl left) proofType
  try
    cacheProof proofType proof
  catch error =>
    throwError
      "kernel equality replay failed for {label}; left={indentExpr left}\n\
      right={indentExpr right}\nerror:{indentD error.toMessageData}"

/-- 用结构相等的反射定理把普通 Lean 等式转回布尔 checker。 -/
private def reflectedEqualityBoolProof
    (label : String) (reflectionTheorem : Name)
    (left right : Expr) : MetaM Expr := do
  let hEquality ← equalityProof label left right
  let reflected := mkApp2 (mkConst reflectionTheorem) left right
  mkAppM ``Iff.mpr #[reflected, hEquality]

private def termEqualityProof
    (label : String) (left right : Expr) : MetaM Expr := do
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
partial def boolTrueProof
    (label : String) (expression : Expr) (fuel : Nat := 64) : MetaM Expr := do
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

/--
构造延迟到外层组合 lemma 才检查的原子布尔反身证明。

调用方必须只用于宿主已经枚举出的 concrete checker 叶子；最终 `cacheBoolTrueProof`
仍会让内核逐叶核对定义相等，不绕过任何检查。
-/
private def deferredBoolTrueProof (expression : Expr) : MetaM Expr := do
  let proofType ← mkEq expression (mkConst ``Bool.true)
  return mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.true)) proofType

/-- 延迟到外层组合 lemma 才检查的 concrete 定义等式。 -/
private def deferredEqualityProof (left right : Expr) : MetaM Expr := do
  let proofType ← mkEq left right
  return mkExpectedPropHint (← mkEqRefl left) proofType

/-- 构造以 search-DAG 节点为参数的布尔 checker 函数。 -/
private def nodeCheckPredicate (body : Expr → MetaM Expr) : MetaM Expr := do
  let nodeType :=
    mkApp (mkConst ``DAGCertificate.Node)
      (mkConst ``SearchMaterialization.SearchSignature)
  withLocalDeclD `_node nodeType fun node => do
    mkLambdaFVars #[node] (← body node)

/-- 构造同时接收宿主索引与 search-DAG 节点的布尔 checker 函数。 -/
private def indexedNodeCheckPredicate
    (body : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let nodeType :=
    mkApp (mkConst ``DAGCertificate.Node)
      (mkConst ``SearchMaterialization.SearchSignature)
  withLocalDeclD `_index (mkConst ``Nat) fun index =>
    withLocalDeclD `_node nodeType fun node => do
      mkLambdaFVars #[index, node] (← body index node)

/-- SearchSignature 下的 DAG 节点类型。 -/
private def searchNodeTypeExpr : Expr :=
  mkApp (mkConst ``DAGCertificate.Node)
    (mkConst ``SearchMaterialization.SearchSignature)

/-- 普通逐节点列表证书的精确类型。 -/
private def checkedListType
    (predicate : Expr) (nodes : List SearchMaterialization.Node) : Expr :=
  mkAppN (mkConst ``DAGCertificate.DAG.CheckedList)
    #[searchNodeTypeExpr, predicate, toExpr nodes]

/-- 分块逐节点列表证书的精确类型。 -/
private def checkedListChunksType
    (predicate : Expr) (nodes : List SearchMaterialization.Node) : Expr :=
  mkAppN (mkConst ``DAGCertificate.DAG.CheckedListChunks)
    #[searchNodeTypeExpr, predicate, toExpr nodes]

/-- SearchSignature 下的 selector/component registry 项 quotation。 -/
private def avatarSelectorComponentExpr
    (entry :
      DAGCertificate.AvatarSelectorComponent
        SearchMaterialization.SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.AvatarSelectorComponent.mk)
    #[mkConst ``SearchMaterialization.SearchSignature,
      toExpr entry.selector, toExpr entry.component]

/-- SearchSignature 下的全局 selector/component registry quotation。 -/
private def avatarSelectorRegistryExpr
    (entries :
      List
        (DAGCertificate.AvatarSelectorComponent
          SearchMaterialization.SearchSignature)) : MetaM Expr := do
  let entryType :=
    mkApp (mkConst ``DAGCertificate.AvatarSelectorComponent)
      (mkConst ``SearchMaterialization.SearchSignature)
  mkListLit entryType (entries.map avatarSelectorComponentExpr)

/-- 宿主侧逐节点构造局部 checker 证明，再由 `CheckedList` 线性组合。 -/
private def checkedNodeListProof
    (predicate : Expr) (label : SearchMaterialization.Node → String) :
    List SearchMaterialization.Node → MetaM Expr
  | [] =>
      pure <| mkExpectedPropHint
        (mkAppN (mkConst ``DAGCertificate.DAG.CheckedList.nil)
          #[searchNodeTypeExpr, predicate])
        (checkedListType predicate [])
  | node :: rest => do
      let nodeExpr := toExpr node
      let check := mkApp predicate nodeExpr
      let hCheck ← deferredBoolTrueProof check
      let hRest ← checkedNodeListProof predicate label rest
      let proof :=
        mkAppN (mkConst ``DAGCertificate.DAG.CheckedList.cons)
          #[searchNodeTypeExpr, predicate, nodeExpr, toExpr rest, hCheck, hRest]
      pure <| mkExpectedPropHint proof (checkedListType predicate (node :: rest))

/-- 宿主侧逐节点构造带索引的局部 checker 证明。 -/
private def checkedIndexedNodeListProof
    (predicate : Expr) (label : Nat → SearchMaterialization.Node → String) :
    Nat → List SearchMaterialization.Node → MetaM Expr
  | index, [] =>
      mkAppOptM ``DAGCertificate.DAG.CheckedIndexedList.nil
        #[none, some predicate, some (toExpr index)]
  | index, node :: rest => do
      let check := mkApp2 predicate (toExpr index) (toExpr node)
      let hCheck ← deferredBoolTrueProof check
      let hRest ← checkedIndexedNodeListProof predicate label (index + 1) rest
      mkAppM ``DAGCertificate.DAG.CheckedIndexedList.cons
        #[hCheck, hRest]

/-- DAG 节点局部证明的块大小。 -/
private def checkedNodeChunkSize : Nat := 32

/-- 普通节点块的整体 `all` checker 证明。 -/
private def checkedNodeBlockProof
    (predicate : Expr) (nodes : List SearchMaterialization.Node) : MetaM Expr := do
  let check ← mkAppM ``List.all #[toExpr nodes, predicate]
  cacheBoolTrueProof check (← mkEqRefl (mkConst ``Bool.true))

/-- 缓存具有稳定常量头的 DAG 列表 checker。 -/
private def checkedDagListProof
    (_label : String) (check : Expr) : MetaM Expr := do
  cacheBoolTrueProof check (← mkEqRefl (mkConst ``Bool.true))

/-- 构造数组安全读取表达式。 -/
private def arrayGetElem? (array index : Expr) : MetaM Expr :=
  mkAppM ``getElem? #[array, index]

/-- 构造 ClauseId quotation；`Id` 的 tag 参数不参与运行时数据。 -/
private def clauseIdExpr (raw : Nat) : MetaM Expr :=
  mkAppOptM ``Data.Id.ofNat
    #[some (mkConst ``Data.ClauseTag), some (toExpr raw)]

/-- 对 concrete residual resolution 链逐 step 构造共享状态证明。 -/
private partial def checkedCompactResolutionTraceProof
    (databaseExpr journalExpr targetExpr : Expr)
    (database : Array PropResolution.Clause)
    (journal : PropResolution.LearnJournal)
    (remaining stepIndex : Nat)
    (current : PropResolution.Clause) (currentExpr : Expr) : MetaM Expr := do
  match remaining with
  | 0 =>
      let targetCheck ←
        mkAppM ``PropResolution.clauseEq #[currentExpr, targetExpr]
      let hTarget ←
        deferredBoolTrueProof targetCheck
      mkAppOptM ``PropResolution.CheckedCompactResolutionTrace.done
        #[some databaseExpr, some journalExpr, some targetExpr,
          some (toExpr stepIndex), some currentExpr, some hTarget]
  | remaining + 1 =>
      let some next :=
          PropResolution.compactResolutionStep?
            database journal stepIndex current
        | throwError
            "residual CDCL step #{stepIndex} failed during host trace construction"
      let nextExpr ←
        cacheReplayData `_replayResidualResolutionClause (toExpr next)
      let stepResult ←
        mkAppM ``PropResolution.compactResolutionStep?
          #[databaseExpr, journalExpr, toExpr stepIndex, currentExpr]
      let expectedNext ← mkAppM ``Option.some #[nextExpr]
      let hNext ←
        deferredEqualityProof stepResult expectedNext
      let hTail ←
        checkedCompactResolutionTraceProof
          databaseExpr journalExpr targetExpr database journal
          remaining (stepIndex + 1) next nextExpr
      mkAppOptM ``PropResolution.CheckedCompactResolutionTrace.step
        #[some databaseExpr, some journalExpr, some targetExpr,
          some (toExpr remaining), some (toExpr stepIndex),
          some currentExpr, some nextExpr, some hNext, some hTail]

/-- 宿主侧逐 initial clause 构造 arena 前缀对齐证明。 -/
private def checkedInitialArenaClausesProof
    (proofExpr : Expr) :
    Nat → List PropResolution.InitialClause → MetaM Expr
  | index, [] =>
      mkAppOptM ``PropResolution.CheckedInitialArenaClauses.nil
        #[some proofExpr, some (toExpr index)]
  | index, initial :: rest => do
      let check ←
        mkAppM ``PropResolution.initialArenaClauseChecked
          #[proofExpr, toExpr index, toExpr initial]
      let hCheck ← deferredBoolTrueProof check
      let hRest ←
        checkedInitialArenaClausesProof proofExpr (index + 1) rest
      mkAppM ``PropResolution.CheckedInitialArenaClauses.cons
        #[hCheck, hRest]

/-- 单条 learned record 的头部字段与逐 resolution step trace。 -/
private def compactLearnRecordProof
    (proof : PropResolution.CdclProof) (proofExpr : Expr)
    (state : PropResolution.UnsatCheckState) (stateExpr : Expr)
    (record : PropResolution.LearnRecord) : MetaM Expr := do
  let database := state.database
  let databaseExpr ←
    mkAppM ``PropResolution.UnsatCheckState.database #[stateExpr]
  let journalExpr ←
    mkAppM ``PropResolution.CdclProof.journal #[proofExpr]
  let recordExpr := toExpr record
  let startId : Data.ClauseId := Data.Id.ofNat record.start
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  let some startIndex := startId.index?
    | throwError "residual CDCL record has an invalid start clause id"
  let some learnedIndex := learnedId.index?
    | throwError "residual CDCL record has an invalid learned clause id"
  let some startClause := database[startIndex]?
    | throwError "residual CDCL record starts outside the current database"
  let startIdExpr ← clauseIdExpr record.start
  let startIdIndex ←
    mkAppM ``Data.Id.index? #[startIdExpr]
  let hStartId ←
    equalityProof "residual CDCL start id"
      startIdIndex (toExpr (some startIndex))
  let learnedIdExpr ← clauseIdExpr record.clause
  let learnedIdIndex ←
    mkAppM ``Data.Id.index? #[learnedIdExpr]
  let hLearnedId ←
    equalityProof "residual CDCL learned id"
      learnedIdIndex (toExpr (some learnedIndex))
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
    boolTrueProof "residual CDCL learned step slice" sliceCheck
  let arenaExpr ← mkAppM ``PropResolution.CdclProof.arena #[proofExpr]
  let targetExpr ←
    mkAppM ``PropResolution.arenaClause #[arenaExpr, learnedIdExpr]
  let hTrace ←
    checkedCompactResolutionTraceProof
      databaseExpr journalExpr targetExpr database proof.journal
      record.stepsLength record.stepsStart startClause startClauseExpr
  mkAppOptM ``PropResolution.compactLearnRecordValidAgainst_eq_true_of_trace
    #[some databaseExpr, some proofExpr, some recordExpr,
      some (toExpr startIndex), some (toExpr learnedIndex),
      some startClauseExpr, some hStartId, some hLearnedId,
      some hStartClause, some hLearnedIndex, some hSlice, some hTrace]

/-- 逐 learned record 构造共享 UNSAT 状态 trace，并返回最终状态。 -/
private partial def checkedUnsatTraceProof
    (proof : PropResolution.CdclProof) (proofExpr : Expr) :
    List PropResolution.LearnRecord →
      PropResolution.UnsatCheckState → Expr →
        MetaM (Expr × PropResolution.UnsatCheckState × Expr)
  | [], state, stateExpr => do
      let trace ←
        mkAppOptM ``PropResolution.CheckedUnsatTrace.nil
          #[some proofExpr, some stateExpr]
      return (trace, state, stateExpr)
  | record :: rest, state, stateExpr => do
      let recordExpr := toExpr record
      let hRecord ←
        compactLearnRecordProof proof proofExpr state stateExpr record
      let nextStepExpr ←
        mkAppM ``PropResolution.UnsatCheckState.nextStep #[stateExpr]
      let hStart ←
        equalityProof "residual CDCL learned step start"
          (toExpr record.stepsStart) nextStepExpr
      let hAcceptedStep ←
        mkAppOptM ``PropResolution.UnsatCheckState.step_eq_acceptedStep
          #[some proofExpr, some stateExpr, some recordExpr,
            some hStart, some hRecord]
      let acceptedStepExpr ←
        mkAppM ``PropResolution.UnsatCheckState.acceptedStep
          #[proofExpr, stateExpr, recordExpr]
      let nextStateExpr ←
        cacheReplayData `_replayResidualUnsatState acceptedStepExpr
      let hStateAlias ←
        equalityProof "residual CDCL accepted state"
          acceptedStepExpr nextStateExpr
      let hStep ← mkAppM ``Eq.trans #[hAcceptedStep, hStateAlias]
      let nextState :=
        PropResolution.UnsatCheckState.acceptedStep proof state record
      let (hTail, finalState, finalStateExpr) ←
        checkedUnsatTraceProof proof proofExpr rest nextState nextStateExpr
      let trace ←
        mkAppM ``PropResolution.CheckedUnsatTrace.cons #[hStep, hTail]
      return (trace, finalState, finalStateExpr)

/-- 用逐 step/record 状态证书证明 concrete residual CDCL UNSAT checker。 -/
private def checkedUnsatProof
    (initialClauses : Array PropResolution.InitialClause)
    (proof : PropResolution.CdclProof)
    (initialClausesExpr proofExpr : Expr) : MetaM Expr := do
  let database := PropResolution.initialClauseDatabase initialClauses
  let databaseExpr ←
    cacheReplayData `_replayResidualInitialDatabase (toExpr database)
  let computedDatabase ←
    mkAppM ``PropResolution.initialClauseDatabase #[initialClausesExpr]
  let hDatabase ←
    equalityProof "residual CDCL initial database"
      computedDatabase databaseExpr
  let arenaExpr ← mkAppM ``PropResolution.CdclProof.arena #[proofExpr]
  let arenaSize ← mkAppM ``Data.ClauseArena.size #[arenaExpr]
  let initialSize ← mkAppM ``Array.size #[initialClausesExpr]
  let journalExpr ←
    mkAppM ``PropResolution.CdclProof.journal #[proofExpr]
  let learnsExpr ←
    mkAppM ``PropResolution.LearnJournal.learns #[journalExpr]
  let learnsSize ← mkAppM ``Array.size #[learnsExpr]
  let expectedArenaSize := mkApp2 (mkConst ``Nat.add) initialSize learnsSize
  let arenaSizeCheck ← mkAppM ``BEq.beq #[arenaSize, expectedArenaSize]
  let hArenaSize ←
    boolTrueProof "residual CDCL initial arena size" arenaSizeCheck
  let checkedArenaClauses ←
    withOptions (fun options => maxRecDepth.set options 100000) do
      checkedInitialArenaClausesProof proofExpr 0 initialClauses.toList
  let hArena ←
    withOptions (fun options => maxRecDepth.set options 100000) do
      mkAppM ``PropResolution.initialArenaValid_eq_true_of_clauses
        #[initialClausesExpr, proofExpr, hArenaSize, checkedArenaClauses]
  let acceptedInitialExpr ←
    mkAppM ``PropResolution.UnsatCheckState.acceptedInitial #[databaseExpr]
  let initialStateExpr ←
    cacheReplayData `_replayResidualUnsatState acceptedInitialExpr
  let hAcceptedInitial ←
    mkAppM ``PropResolution.UnsatCheckState.initial_eq_acceptedInitial
      #[hDatabase, hArena]
  let hInitialAlias ←
    equalityProof "residual CDCL accepted initial state"
      acceptedInitialExpr initialStateExpr
  let hInitial ← mkAppM ``Eq.trans #[hAcceptedInitial, hInitialAlias]
  let initialState :=
    PropResolution.UnsatCheckState.acceptedInitial database
  let (hTrace, _finalState, finalStateExpr) ←
    checkedUnsatTraceProof proof proofExpr proof.journal.learns.toList
      initialState initialStateExpr
  let hRun ←
    mkAppM ``PropResolution.runUnsatCheck_eq_of_trace #[hInitial, hTrace]
  let finalOk ←
    mkAppM ``PropResolution.UnsatCheckState.ok #[finalStateExpr]
  let hOk ← boolTrueProof "residual CDCL final ok" finalOk
  let finalFoundEmpty ←
    mkAppM ``PropResolution.UnsatCheckState.foundEmpty #[finalStateExpr]
  let hFoundEmpty ←
    boolTrueProof "residual CDCL final empty clause" finalFoundEmpty
  let finalNextStep ←
    mkAppM ``PropResolution.UnsatCheckState.nextStep #[finalStateExpr]
  let journalExpr ←
    mkAppM ``PropResolution.CdclProof.journal #[proofExpr]
  let journalSteps ←
    mkAppM ``PropResolution.LearnJournal.steps #[journalExpr]
  let journalStepsSize ← mkAppM ``Array.size #[journalSteps]
  let nextStepCheck ←
    mkAppM ``BEq.beq #[finalNextStep, journalStepsSize]
  let hNextStep ←
    boolTrueProof "residual CDCL final step count" nextStepCheck
  let checkedProof ←
    mkAppM ``PropResolution.checkedUnsat_eq_true_of_run
      #[hRun, hOk, hFoundEmpty, hNextStep]
  let checkedUnsat ←
    mkAppM ``PropResolution.checkedUnsat #[initialClausesExpr, proofExpr]
  cacheBoolTrueProof checkedUnsat checkedProof

/-- residual CDCL initial justification 的逐槽位证明。 -/
private def residualJustificationsProof
    (parentsExpr payloadExpr : Expr)
    (payload :
      DAGCertificate.PropositionalClosurePayload
        SearchMaterialization.SearchSignature) : MetaM Expr := do
  let some keys :=
      DAGCertificate.PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList
    | throwError
        "residual CDCL replay key extraction found a non-propositional justification"
  let keysExpr ←
    cacheReplayData `_replayResidualJustificationKeys (toExpr keys)
  let initialClausesExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.initialClauses
      #[payloadExpr]
  let initialJustificationsExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.initialJustifications
      #[payloadExpr]
  let initialSize ← mkAppM ``Array.size #[initialClausesExpr]
  let justificationSize ← mkAppM ``Array.size #[initialJustificationsExpr]
  let sizeCheck ← mkAppM ``BEq.beq #[initialSize, justificationSize]
  let hSize ←
    boolTrueProof "residual CDCL justification count" sizeCheck
  let initialJustificationsList ←
    mkAppM ``Array.toList #[initialJustificationsExpr]
  let computedKeys ←
    mkAppM ``DAGCertificate.PropositionalJustificationKeys.ofJustifications?
      #[initialJustificationsList]
  let expectedKeys ← mkAppM ``Option.some #[keysExpr]
  let hKeys ←
    deferredEqualityProof computedKeys expectedKeys
  let initialDatabase ←
    mkAppM ``PropResolution.initialClauseDatabase #[initialClausesExpr]
  let initialClauseList ← mkAppM ``Array.toList #[initialDatabase]
  let keyClauses ←
    mkAppM ``DAGCertificate.PropositionalJustificationKeys.clauses #[keysExpr]
  let hClauses ←
    deferredEqualityProof initialClauseList keyClauses
  let keyParents ←
    mkAppM ``DAGCertificate.PropositionalJustificationKeys.parents #[keysExpr]
  let parentList ← mkAppM ``Array.toList #[parentsExpr]
  let hParentList ←
    deferredEqualityProof keyParents parentList
  let hParents ←
    mkAppM
      ``DAGCertificate.PropositionalJustificationKeys.parentsCheck_eq_true_of_eq
      #[parentsExpr, keysExpr, hParentList]
  let atomMapExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.atomMap #[payloadExpr]
  let outsideCheck ←
    mkAppM
      ``DAGCertificate.PropositionalJustificationKeys.outsideAtomMapCheck
      #[atomMapExpr, keysExpr]
  let hOutside ←
    boolTrueProof "residual CDCL justification outside atom map" outsideCheck
  mkAppM
    ``DAGCertificate.PropositionalClosurePayload.justificationsCheck_eq_true_of_propositionalKeys
    #[parentsExpr, payloadExpr, keysExpr, hSize, hKeys,
      hClauses, hParents, hOutside]

/-- residual closure payload 的 CDCL、来源与统计字段组合证明。 -/
private def residualClosureCheckProof
    (parentsExpr payloadExpr : Expr)
    (payload :
      DAGCertificate.PropositionalClosurePayload
        SearchMaterialization.SearchSignature) : MetaM Expr := do
  let initialClausesExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.initialClauses
      #[payloadExpr]
  let proofExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.proof #[payloadExpr]
  let hUnsat ←
    checkedUnsatProof payload.initialClauses payload.proof
      initialClausesExpr proofExpr
  let hJustifications ←
    residualJustificationsProof parentsExpr payloadExpr payload
  let statsExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.stats #[payloadExpr]
  let computedStatsExpr ←
    mkAppM ``DAGCertificate.PropositionalClosurePayload.computedStats
      #[payloadExpr]
  let proveStat (field : Name) (label : String) : MetaM Expr := do
    let actual ← mkAppM field #[statsExpr]
    let expected ← mkAppM field #[computedStatsExpr]
    let check ← mkAppM ``BEq.beq #[actual, expected]
    boolTrueProof label check
  let hSteps ←
    proveStat ``Certificate.Stats.steps "residual CDCL stats.steps"
  let hClauses ←
    proveStat ``Certificate.Stats.clauses "residual CDCL stats.clauses"
  let hGenerated ←
    proveStat ``Certificate.Stats.generated "residual CDCL stats.generated"
  let hRetained ←
    proveStat ``Certificate.Stats.retained "residual CDCL stats.retained"
  let hVerified ←
    proveStat ``Certificate.Stats.verified "residual CDCL stats.verified"
  mkAppM
    ``DAGCertificate.PropositionalClosurePayload.check_eq_true_of_components
    #[parentsExpr, payloadExpr, hUnsat, hJustifications,
      hSteps, hClauses, hGenerated, hRetained, hVerified]

/-- residual CDCL 节点绕开整节点归约，按命名组件构造 checker 证明。 -/
private def residualCdclNodeCheckProof
    (problemExpr nodeExpr : Expr)
    (payload :
      DAGCertificate.PropositionalClosurePayload
        SearchMaterialization.SearchSignature) : MetaM Expr := do
  let payloadExpr ←
    cacheReplayData `_replayResidualPayload (toExpr payload)
  let ruleTagsCheck ←
    mkAppM ``DAGCertificate.Node.ruleTagsOk #[nodeExpr]
  let hRuleTags ←
    boolTrueProof "residual CDCL node rule tags" ruleTagsCheck
  let parentsExpr ←
    mkAppM ``DAGCertificate.Node.parents #[nodeExpr]
  let parentsEmpty ← mkAppM ``Array.isEmpty #[parentsExpr]
  let parentsNonempty ← mkAppM ``Bool.not #[parentsEmpty]
  let hParents ←
    boolTrueProof "residual CDCL node nonempty parents" parentsNonempty
  let conclusionExpr ←
    mkAppM ``DAGCertificate.Node.conclusion #[nodeExpr]
  let conclusionEmpty ←
    mkAppM ``DAGCertificate.Clause.isEmpty #[conclusionExpr]
  let hConclusion ←
    boolTrueProof "residual CDCL node empty conclusion" conclusionEmpty
  let hClosure ←
    residualClosureCheckProof parentsExpr payloadExpr payload
  let hPayload ←
    mkAppM ``DAGCertificate.Payload.residualCdcl_check_eq_true_of_components
      #[problemExpr, parentsExpr, conclusionExpr, payloadExpr,
        hParents, hConclusion, hClosure]
  mkAppM ``DAGCertificate.Node.check_eq_true_of_components
    #[problemExpr, nodeExpr, hRuleTags, hPayload]

/-- payload 列表对 residual CDCL 使用专用线性 replay，其余节点沿用通用布尔拆分。 -/
private def checkedPayloadNodeListProof
    (problemExpr predicate : Expr) :
    List SearchMaterialization.Node → MetaM Expr
  | [] =>
      mkAppOptM ``DAGCertificate.DAG.CheckedList.nil
        #[none, some predicate]
  | node :: rest => do
      let nodeExpr := toExpr node
      let check := mkApp predicate nodeExpr
      let hCheck ←
        match node.payload with
        | .residualCdcl payload => do
            residualCdclNodeCheckProof problemExpr nodeExpr payload
        | _ =>
            deferredBoolTrueProof check
      let hRest ← checkedPayloadNodeListProof problemExpr predicate rest
      mkAppM ``DAGCertificate.DAG.CheckedList.cons
        #[hCheck, hRest]

/--
payload 逐节点证明按块缓存。

residual CDCL 节点单独成块，避免其专用证明完成后再回卷整段普通节点。
-/
private partial def checkedPayloadNodeChunksProof
    (problemExpr predicate : Expr) :
    List SearchMaterialization.Node → MetaM Expr
  | [] => do
      pure <| mkExpectedPropHint
        (mkAppN (mkConst ``DAGCertificate.DAG.CheckedListChunks.nil)
          #[searchNodeTypeExpr, predicate])
        (checkedListChunksType predicate [])
  | nodes@(node :: rest) => do
      let (chunk, tail) :=
        match node.payload with
        | .residualCdcl _ =>
            ([node], rest)
        | _ =>
            let chunk :=
              (nodes.take checkedNodeChunkSize).takeWhile
                fun (candidate : SearchMaterialization.Node) =>
                match candidate.payload with
                | .residualCdcl _ => false
                | _ => true
            (chunk, nodes.drop chunk.length)
      let hTail ← checkedPayloadNodeChunksProof problemExpr predicate tail
      let proof ←
        match node.payload with
        | .residualCdcl _ => do
            let hChunk ← checkedPayloadNodeListProof problemExpr predicate chunk
            pure <| mkAppN (mkConst ``DAGCertificate.DAG.CheckedListChunks.cons)
              #[searchNodeTypeExpr, predicate, toExpr chunk, toExpr tail, hChunk, hTail]
        | _ => do
            let hChunk ← checkedNodeBlockProof predicate chunk
            pure <| mkAppN (mkConst ``DAGCertificate.DAG.CheckedListChunks.block)
              #[searchNodeTypeExpr, predicate, toExpr chunk, toExpr tail, hChunk, hTail]
      pure <| mkExpectedPropHint proof (checkedListChunksType predicate nodes)

/-- 分别回放 DAG 的命名结构检查，再合成整图 checker。 -/
private def dagCheckProof
    (dag : SearchMaterialization.DAG) (problemExpr dagExpr : Expr) : MetaM Expr := do
  let rootExists ← mkAppM ``DAGCertificate.DAG.rootExists #[dagExpr]
  let hRootExists ← boolTrueProof "search DAG root existence" rootExists
  let rootClosed ← mkAppM ``DAGCertificate.DAG.rootClosed #[dagExpr]
  let hRootClosed ← boolTrueProof "search DAG root closure" rootClosed
  let denseIds ← mkAppM ``DAGCertificate.DAG.denseIds #[dagExpr]
  let densePredicate ←
    indexedNodeCheckPredicate fun index node =>
      mkAppM ``DAGCertificate.DAG.denseIdChecked #[index, node]
  let checkedDenseNodes ←
    checkedIndexedNodeListProof densePredicate
      (fun index _node => s!"search DAG dense id #{index}") 0 dag.nodes.toList
  let denseIdsProof ←
    mkAppM ``DAGCertificate.DAG.denseIds_eq_true_of_nodes
      #[dagExpr, checkedDenseNodes]
  let hDenseIds ← cacheBoolTrueProof denseIds denseIdsProof
  let parentsBefore ← mkAppM ``DAGCertificate.DAG.parentsBefore #[dagExpr]
  let parentsPredicate ←
    indexedNodeCheckPredicate fun index node =>
      mkAppM ``DAGCertificate.DAG.nodeParentsBefore #[index, node]
  let checkedParentNodes ←
    checkedIndexedNodeListProof parentsPredicate
      (fun index _node => s!"search DAG parent order #{index}")
      0 dag.nodes.toList
  let parentsBeforeProof ←
    mkAppM ``DAGCertificate.DAG.parentsBefore_eq_true_of_nodes
      #[dagExpr, checkedParentNodes]
  let hParentsBefore ←
    cacheBoolTrueProof parentsBefore parentsBeforeProof
  let payloadsChecked ←
    mkAppM ``DAGCertificate.DAG.payloadsChecked #[dagExpr]
  let payloadPredicate ←
    nodeCheckPredicate fun node =>
      mkAppM ``DAGCertificate.Node.check #[problemExpr, node]
  let checkedPayloadNodes ←
    checkedPayloadNodeChunksProof problemExpr payloadPredicate dag.nodes.toList
  let payloadsProof ←
    mkAppM ``DAGCertificate.DAG.payloadsChecked_eq_true_of_chunks
      #[dagExpr, checkedPayloadNodes]
  let hPayloadsChecked ←
    cacheBoolTrueProof payloadsChecked payloadsProof
  let parentSnapshotsChecked :=
    mkApp
      (mkConst ``SourcePreprocessing.FirstOrderReplay.searchParentSnapshotsChecked)
      dagExpr
  let parentSnapshotsListChecked :=
    mkApp
      (mkConst ``SourcePreprocessing.FirstOrderReplay.searchParentSnapshotsListChecked)
      dagExpr
  let checkedParentSnapshotNodes ←
    checkedDagListProof "search DAG parent snapshots" parentSnapshotsListChecked
  let parentSnapshotsProof :=
    mkApp2
      (mkConst
        ``SourcePreprocessing.FirstOrderReplay.searchParentSnapshotsChecked_eq_true_of_listCheck)
      dagExpr checkedParentSnapshotNodes
  let hParentSnapshotsChecked ←
    cacheBoolTrueProof parentSnapshotsChecked parentSnapshotsProof
  let guardsChecked :=
    mkApp (mkConst ``SourcePreprocessing.FirstOrderReplay.searchGuardsChecked)
      dagExpr
  let guardsListChecked :=
    mkApp (mkConst ``SourcePreprocessing.FirstOrderReplay.searchGuardsListChecked)
      dagExpr
  let checkedGuardNodes ←
    checkedDagListProof "search DAG guards" guardsListChecked
  let guardsProof :=
    mkApp2
      (mkConst
        ``SourcePreprocessing.FirstOrderReplay.searchGuardsChecked_eq_true_of_listCheck)
      dagExpr checkedGuardNodes
  let hGuardsChecked ← cacheBoolTrueProof guardsChecked guardsProof
  let sourceIndicesUnique ←
    mkAppM ``DAGCertificate.DAG.sourceIndicesUnique #[dagExpr]
  let sourceKeys :=
    DAGCertificate.DAG.sourceUniquenessKeys dag
  let sourceKeysExpr ←
    cacheReplayData `_replaySourceKeys (toExpr sourceKeys)
  let computedSourceKeys ←
    mkAppM ``DAGCertificate.DAG.sourceUniquenessKeys #[dagExpr]
  let hSourceKeys ←
    equalityProof "search DAG source key extraction"
      computedSourceKeys sourceKeysExpr
  let initialClauses ←
    mkAppM ``DAGCertificate.ClauseProblem.initialClauses #[problemExpr]
  let sourceLimit ← mkAppM ``Array.size #[initialClauses]
  let sourceKeysCheck ←
    mkAppM ``DAGCertificate.DAG.SourceUniquenessKeys.check
      #[sourceKeysExpr, sourceLimit]
  let hSourceKeysCheck ←
    boolTrueProof "search DAG source key uniqueness" sourceKeysCheck
  let sourceIndicesUniqueProof ←
    mkAppM ``DAGCertificate.DAG.sourceIndicesUnique_eq_true_of_keys
      #[dagExpr, sourceKeysExpr, hSourceKeys, hSourceKeysCheck]
  let hSourceIndicesUnique ←
    cacheBoolTrueProof sourceIndicesUnique sourceIndicesUniqueProof
  pure <| mkAppN
    (mkConst ``SourcePreprocessing.FirstOrderReplay.searchDagCheck_eq_true_of_components)
    #[dagExpr, hRootExists, hRootClosed, hDenseIds, hParentsBefore,
      hPayloadsChecked, hParentSnapshotsChecked, hGuardsChecked,
      hSourceIndicesUnique]

/-- 一阶 provider 共享的显式 replay 表达式。 -/
structure FirstOrderReplayExprs where
  payload : Expr
  search : Expr
  checked : Expr
  data : Expr

/-- 按局部条件回放定义性 CNF 构造结果，避免重新归约整份 CNF 的结构自反性。 -/
private def definitionalCnfCheckProof
    (definitionalCnfExpr : Expr) : MetaM Expr := do
  let config ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.config
      #[definitionalCnfExpr]
  let contextSorts ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.contextSorts
      #[definitionalCnfExpr]
  let source ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.source
      #[definitionalCnfExpr]
  let quantifierFree ←
    mkAppM ``CoreSyntax.NormalForm.Nnf.quantifierFree #[source]
  let hQuantifierFree ←
    boolTrueProof "preprocessing definitional CNF quantifier free" quantifierFree
  let sourceFormula ←
    mkAppM ``CoreSyntax.NormalForm.Nnf.toFormula #[source]
  let sourceCheck ←
    mkAppM ``CoreSyntax.Formula.checkWith #[contextSorts, sourceFormula]
  let hSourceCheck ←
    boolTrueProof "preprocessing definitional CNF source syntax" sourceCheck
  let built ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.build
      #[config, contextSorts, source]
  let definitions ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.definitions #[built]
  let definitionsList ← mkAppM ``Array.toList #[definitions]
  let definitionsCheck ←
    mkAppM ``List.all
      #[definitionsList,
        mkConst ``CoreSyntax.NormalForm.DefinitionalCnf.Definition.check]
  let hDefinitionsCheck ←
    boolTrueProof "preprocessing definitional CNF definitions" definitionsCheck
  let hBuilt ←
    mkAppM
      ``CoreSyntax.NormalForm.Semantics.DefinitionalCnfPayload.check_build_eq_true_of_components
      #[config, contextSorts, source, hQuantifierFree, hSourceCheck,
        hDefinitionsCheck]
  let actualCheck ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.check
      #[definitionalCnfExpr]
  let expectedType ← mkEq actualCheck (mkConst ``Bool.true)
  return mkExpectedPropHint hBuilt expectedType

/-- 按七条相邻阶段等式回放 preprocessing link checker。 -/
private def preprocessingLinkCheckProof (payloadExpr : Expr) : MetaM Expr := do
  let source ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.source #[payloadExpr]
  let normalized ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalized #[payloadExpr]
  let normalizationTrace ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalizationTrace
      #[payloadExpr]
  let traceSource ←
    mkAppM ``CoreSyntax.NormalForm.Trace.source #[normalizationTrace]
  let traceTarget ←
    mkAppM ``CoreSyntax.NormalForm.Trace.target #[normalizationTrace]
  let sourceTraceExpr ←
    mkAppM ``CoreSyntax.NormalForm.TraceExpr.formula #[source]
  let normalizedTraceExpr ←
    mkAppM ``CoreSyntax.NormalForm.TraceExpr.formula #[normalized]
  let hTraceSource ←
    reflectedEqualityBoolProof "preprocessing trace source link"
      ``CoreSyntax.NormalForm.Semantics.TraceExpr.eq_eq_true
      traceSource sourceTraceExpr
  let hTraceTarget ←
    reflectedEqualityBoolProof "preprocessing trace target link"
      ``CoreSyntax.NormalForm.Semantics.TraceExpr.eq_eq_true
      traceTarget normalizedTraceExpr
  let initialNnf ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.initialNnf
      #[payloadExpr]
  let positiveNnf ←
    mkAppM ``CoreSyntax.NormalForm.toNnfWith
      #[mkConst ``CoreSyntax.NormalForm.Polarity.positive, normalized]
  let hInitialNnf ←
    reflectedEqualityBoolProof "preprocessing initial NNF link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      initialNnf positiveNnf
  let antiPrenex ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.antiPrenex
      #[payloadExpr]
  let antiPrenexSource ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.source #[antiPrenex]
  let antiPrenexResult ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.result #[antiPrenex]
  let hAntiPrenex ←
    reflectedEqualityBoolProof "preprocessing anti-prenex source link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      antiPrenexSource initialNnf
  let localSkolem ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.localSkolem
      #[payloadExpr]
  let localSkolemSource ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.source #[localSkolem]
  let localSkolemResult ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.result #[localSkolem]
  let hLocalSkolem ←
    reflectedEqualityBoolProof "preprocessing local Skolem source link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      localSkolemSource antiPrenexResult
  let definitionalCnf ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.definitionalCnf
      #[payloadExpr]
  let definitionalCnfSource ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.source #[definitionalCnf]
  let hDefinitionalCnf ←
    reflectedEqualityBoolProof "preprocessing definitional CNF source link"
      ``CoreSyntax.NormalForm.SyntaxEq.nnfEq_eq_true
      definitionalCnfSource localSkolemResult
  let clauses ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.clauses #[payloadExpr]
  let definitionalCnfClauses ←
    mkAppM ``CoreSyntax.NormalForm.DefinitionalCnfPayload.clauses #[definitionalCnf]
  let hClauses ←
    reflectedEqualityBoolProof "preprocessing clause output link"
      ``CoreSyntax.NormalForm.Semantics.ClauseSet.eq_eq_true
      clauses definitionalCnfClauses
  mkAppM
    ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.linkCheck_eq_true_of_components
    #[payloadExpr, hTraceSource, hTraceTarget, hInitialNnf, hAntiPrenex,
      hLocalSkolem, hDefinitionalCnf, hClauses]

/--
把元层的一阶搜索产物拆成 preprocessing 与 DAG 的小型 checked 证明项。

返回值只含纯数据引用及其 checker 证明；具体宿主语义仍由各 provider 自己的
universe-polymorphic bridge 消费。
-/
def firstOrderReplayExprs
    (sourceProblem problem settingsExpr : Expr)
    (payload : SourcePreprocessing.Payload)
    (artifact : SourcePreprocessing.Result.AvatarRunArtifact)
    (label : String) : MetaM FirstOrderReplayExprs := do
  let rawPayloadExprs ←
    preprocessingPayloadExprs (toExpr payload.source) (toExpr payload.normalized)
      settingsExpr
      payload.normalizationTrace payload.initialNnf
  let payloadExpr ← cacheReplayData `_replayPayload rawPayloadExprs.payload
  let search := artifact.toSearchInput label
  let searchExpr ← cacheReplayData `_replaySearch (toExpr search)
  let refutationSource ←
    mkAppM ``SourcePreprocessing.Problem.refutationSource #[sourceProblem]
  let payloadSource ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.source
      #[payloadExpr]
  let normalized ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalized
      #[payloadExpr]
  let sourceSyntaxCheck ←
    mkAppM ``CoreSyntax.Formula.check? #[payloadSource]
  let hSourceSyntax ←
    boolTrueProof "preprocessing source syntax" sourceSyntaxCheck
  let normalizedSyntaxCheck ←
    mkAppM ``CoreSyntax.Formula.check? #[normalized]
  let hNormalizedSyntax ←
    boolTrueProof "preprocessing normalized syntax" normalizedSyntaxCheck
  let settings ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.settings
      #[payloadExpr]
  let normalFormConfig ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Settings.normalForm
      #[settings]
  let normalizationTrace ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.normalizationTrace
      #[payloadExpr]
  let traceCheck ←
    mkAppM ``CoreSyntax.NormalForm.Trace.check
      #[normalFormConfig, normalizationTrace]
  let hTrace ←
    boolTrueProof "preprocessing normalization trace" traceCheck
  let antiPrenex ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.antiPrenex
      #[payloadExpr]
  let antiPrenexResult ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.result #[antiPrenex]
  let antiPrenexCheck ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.check #[antiPrenex]
  let hAntiPrenex ←
    boolTrueProof "preprocessing anti-prenex payload" antiPrenexCheck
  let localSkolem ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.localSkolem
      #[payloadExpr]
  let localSkolemCheck ←
    mkAppM ``CoreSyntax.NormalForm.LocalSkolemPayload.check #[localSkolem]
  let hLocalSkolem ←
    boolTrueProof "preprocessing local Skolem payload" localSkolemCheck
  let hDefinitionalCnf ←
    definitionalCnfCheckProof rawPayloadExprs.definitionalCnf
  let hPhase ←
    mkAppM
      ``SourcePreprocessing.FirstOrderReplay.phaseCheck_eq_true_of_components
      #[payloadExpr, hSourceSyntax, hNormalizedSyntax, hTrace,
        hAntiPrenex, hLocalSkolem, hDefinitionalCnf]
  let hLink ←
    preprocessingLinkCheckProof payloadExpr
  let hSourceEquality ←
    equalityProof "preprocessing source equality"
      payloadSource refutationSource
  let sourceCheckIff :=
    mkApp2
      (mkConst ``CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true)
      payloadSource refutationSource
  let hSourceCheck ←
    mkAppM ``Iff.mpr #[sourceCheckIff, hSourceEquality]
  let freeCheck ←
    mkAppM
      ``CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      #[antiPrenexResult]
  let hFree ←
    boolTrueProof "preprocessing free closure" freeCheck
  let clauses ←
    mkAppM ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.clauses
      #[payloadExpr]
  let projectableCheck ←
    mkAppM
      ``CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
      #[clauses]
  let hProjectable ←
    boolTrueProof "first-order clause projection" projectableCheck
  let normalizationCheck ←
    mkAppM ``CoreSyntax.NormalForm.SyntaxEq.formulaEq
      #[normalized, payloadSource]
  let hNormalization ←
    boolTrueProof "first-order normalization identity" normalizationCheck
  let hReplay ←
    mkAppM ``SourcePreprocessing.FirstOrderReplay.check_eq_true_of_components
      #[sourceProblem, payloadExpr, hPhase, hLink,
        hSourceCheck, hFree, hProjectable, hNormalization]
  let replaySearchInput ←
    mkAppM ``SourcePreprocessing.FirstOrderReplay.searchInput
      #[payloadExpr, problem, searchExpr, toExpr label]
  let clauseProblem :=
    SourcePreprocessing.FirstOrderReplay.clauseProblemOf payload
  let materialized ←
    match
      SearchMaterialization.materializeRootWithProblem?
        clauseProblem search.dag artifact.root.id with
    | Except.ok result =>
        pure result
    | Except.error error =>
        throwError "search DAG materialization failed: {error.label}"
  let clauseProblemExpr ←
    mkAppM ``SourcePreprocessing.FirstOrderReplay.clauseProblemOf
      #[payloadExpr]
  let replayProblemExpr ←
    cacheReplayData `_replayProblem (toExpr clauseProblem)
  let rawDagExpr :=
    SearchMaterialization.ReplayQuotation.dagExprWithProblem
      replayProblemExpr materialized.dag
  let dagExpr ← cacheReplayData `_replayDag rawDagExpr
  let hDagCheck ← dagCheckProof materialized.dag replayProblemExpr dagExpr
  let checkedDag ←
    mkAppM ``DAGCertificate.CheckedDAG.mk #[dagExpr, hDagCheck]
  let dagProblem ←
    mkAppM ``DAGCertificate.CheckedDAG.problem #[checkedDag]
  let hDagProblem ←
    equalityProof "search DAG problem alignment" dagProblem clauseProblemExpr
  let checkedArtifact ←
    mkAppM ``SearchMaterialization.CheckedArtifact.mk
      #[checkedDag, hDagProblem]
  let preparedData ←
    if materialized.dag.avatarSoundnessSupported then
      let avatarCheck ←
        mkAppM ``DAGCertificate.DAG.avatarSoundnessSupported #[dagExpr]
      let avatarPredicate ←
        nodeCheckPredicate fun node =>
          mkAppM ``DAGCertificate.DAG.nodeAvatarSoundnessSupported #[node]
      let checkedAvatarNodes ←
        checkedNodeListProof avatarPredicate
          (fun node => s!"search DAG node AVATAR capability #{node.id}")
          materialized.dag.nodes.toList
      let avatarProof ←
        mkAppM ``DAGCertificate.DAG.avatarSoundnessSupported_eq_true_of_nodes
          #[dagExpr, checkedAvatarNodes]
      let hAvatar ← cacheBoolTrueProof avatarCheck avatarProof
      let registryCheck ←
        mkAppM ``DAGCertificate.DAG.avatarRegistryCheck #[dagExpr]
      let registryPredicate ←
        nodeCheckPredicate fun node =>
          mkAppM ``DAGCertificate.DAG.nodeAvatarRegistryLocalCheck #[node]
      let checkedRegistryNodes ←
        checkedNodeListProof registryPredicate
          (fun node => s!"search DAG node AVATAR registry #{node.id}")
          materialized.dag.nodes.toList
      let registry :=
        DAGCertificate.DAG.avatarSelectorRegistry materialized.dag
      let rawRegistryExpr ← avatarSelectorRegistryExpr registry
      let registryExpr ←
        cacheReplayData `_replayAvatarRegistry rawRegistryExpr
      let computedRegistry ←
        mkAppM ``DAGCertificate.DAG.avatarSelectorRegistry #[dagExpr]
      let hRegistryExtraction ←
        equalityProof "search DAG AVATAR registry extraction"
          computedRegistry registryExpr
      let registryCompatibility ←
        mkAppM ``DAGCertificate.AvatarSelectorComponent.compatibleCheck
          #[registryExpr]
      let hRegistryCompatibility ←
        boolTrueProof "search DAG AVATAR registry compatibility"
          registryCompatibility
      let registryProof ←
        mkAppM
          ``DAGCertificate.DAG.avatarRegistryCheck_eq_true_of_nodes_and_registry
          #[dagExpr, registryExpr, checkedRegistryNodes,
            hRegistryExtraction, hRegistryCompatibility]
      let hRegistry ← cacheBoolTrueProof registryCheck registryProof
      mkAppOptM
        ``SearchMaterialization.SearchCertificateProvider.PreparedReplaySearchData.avatar
        #[some replaySearchInput, some checkedArtifact,
          some hAvatar, some hRegistry]
    else if materialized.dag.guardedSoundnessSupported then
      let guardedCheck ←
        mkAppM ``DAGCertificate.DAG.guardedSoundnessSupported #[dagExpr]
      let hGuarded ←
        boolTrueProof "search DAG guarded capability" guardedCheck
      mkAppOptM
        ``SearchMaterialization.SearchCertificateProvider.PreparedReplaySearchData.guarded
        #[some replaySearchInput, some checkedArtifact, some hGuarded]
    else
      throwError
        "materialized search DAG is outside all proved soundness fragments"
  return {
    payload := payloadExpr
    search := searchExpr
    checked := hReplay
    data := preparedData
  }

end KernelReplay
end Automation
end YesMetaZFC
