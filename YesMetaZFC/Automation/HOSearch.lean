import YesMetaZFC.Automation.HOSearchMaterialization

/-!
# 原生高阶资源搜索

本模块负责从当前 HO-DAG 中枚举可检查的高阶一元资源。搜索器只生成候选；
每个候选在准入前仍由 `HOSearchMaterialization` 复算 evidence 和结果字句。

当前自动生成：

* 闭项 β/η 公理实例；
* Boolean extensionality；
* typed argument congruence；
* 带新鲜 `diff` 符号的 function extensionality。
-/

namespace YesMetaZFC
namespace Automation
namespace HOSearch

open Logic.HigherOrder
open HOSearchMaterialization

abbrev SearchTerm := CoreSyntax.Search.Term
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev Resource := ResourceTrace.HigherOrderResource

/-- 高阶一元资源搜索配置。所有上界都属于搜索策略，不进入可信证书。 -/
structure Config where
  beta : Bool := true
  eta : Bool := true
  booleanExtensionality : Bool := true
  argumentCongruence : Bool := true
  functionExtensionality : Bool := true
  maxRounds : Nat := 3
  maxTermSize : Nat := 64
  maxCollectedTerms : Nat := 128
  maxGenerated : Nat := 256
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 外延一元规则的父节点来源纪律。 -/
inductive ExtensionalParentDiscipline where
  | ordinary
  | avatar
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 高阶资源生成统计。 -/
structure Stats where
  rounds : Nat := 0
  candidates : Nat := 0
  generated : Nat := 0
  deduplicated : Nat := 0
  rejected : Nat := 0
  beta : Nat := 0
  eta : Nat := 0
  booleanExtensionality : Nat := 0
  argumentCongruence : Nat := 0
  functionExtensionality : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Stats

/-- 记录一个成功进入 DAG 的资源。 -/
def recordGenerated (stats : Stats) (resource : Resource) : Stats :=
  match resource with
  | .beta _ =>
      { stats with generated := stats.generated + 1, beta := stats.beta + 1 }
  | .eta _ =>
      { stats with generated := stats.generated + 1, eta := stats.eta + 1 }
  | .local (.unary unary) =>
      match unary.kind with
      | .booleanExtensionality =>
          {
            stats with
            generated := stats.generated + 1
            booleanExtensionality := stats.booleanExtensionality + 1
          }
      | .argumentCongruence =>
          {
            stats with
            generated := stats.generated + 1
            argumentCongruence := stats.argumentCongruence + 1
          }
      | .functionExtensionality =>
          {
            stats with
            generated := stats.generated + 1
            functionExtensionality := stats.functionExtensionality + 1
          }
      | _ =>
          { stats with generated := stats.generated + 1 }
  | .local _ =>
      { stats with generated := stats.generated + 1 }

end Stats

/-- 搜索过程中携带的纯状态。 -/
private structure State where
  dag : DAG
  resources : Array Resource := #[]
  stats : Stats := {}
  nextWitnessId : Nat := 0

/-- 高阶资源搜索结果。 -/
structure Result where
  dag : DAG
  resources : Array Resource
  stats : Stats

/--
HO-DAG 进入 persistent saturation arena 的稳定 seed。

数组下标同时是 saturation clause id 与 proof journal id；`dagNodeIds` 显式记录该槽
已经由哪个真实 DAG 节点认证，派生资源不会伪装成新的 source。
-/
structure ArenaSeed where
  clauses : Array SearchClause
  dagNodeIds : Array Nat
  deriving Repr, BEq, Lean.ToExpr

namespace ArenaSeed

/-- seed 的 clause 槽与 DAG origin 必须逐槽对齐。 -/
def check (seed : ArenaSeed) : Bool :=
  seed.clauses.size == seed.dagNodeIds.size

/-- 按 saturation clause id 读取真实 DAG node id。 -/
def dagNodeId? (seed : ArenaSeed) (clauseId : Nat) : Option Nat :=
  seed.dagNodeIds[clauseId]?

end ArenaSeed

/-! ## HO clause 到搜索 AST 的同构投影 -/

/-- 把原生 HO 原子恢复为搜索层谓词与参数。 -/
private def searchAtom? (atom : Atom) :
    Option (CoreSyntax.Search.PredicateKind × SearchTerm × SearchTerm) := do
  match atom with
  | .equal _ left right =>
      some (.equal, searchTerm left, searchTerm right)
  | .rel .member [left, right] =>
      some (.member, searchTerm left, searchTerm right)
  | .rel .boolHolds [argument] =>
      let term := searchTerm argument
      some (.boolHolds, term, term)
  | .rel (.definition id arity) [argument] =>
      let term := searchTerm argument
      some (.definition id arity, term, term)
  | .rel (.predicate symbol) arguments =>
      let arguments := arguments.map searchTerm
      let tuple : CoreSyntax.Search.FunctionSymbol := {
        id := symbol.id
        arity := arguments.length
        kind := CoreSyntax.Search.SymbolKind.tuple
        inputSorts := symbol.inputSorts
      }
      let packed := CoreSyntax.Search.Term.app tuple arguments
      some (.predicate symbol, packed, packed)
  | .rel _ _ =>
      none

/-- 把原生 HO 文字恢复为搜索层文字。 -/
private def searchLiteral? (literal : Literal) : Option CoreSyntax.Search.Literal := do
  let (predicate, left, right) ← searchAtom? literal.atom
  some {
    positive := literal.polarity
    predicate := predicate
    left := left
    right := right
  }

/-- 把原生 HO 字句恢复为搜索层字句。 -/
def searchClause? (clause : Clause) : Option SearchClause :=
  clause.literals.mapM searchLiteral?

namespace ArenaSeed

/-- 每个 seed 槽必须指向同一结论的真实 HO-DAG 节点。 -/
def checkAgainst (seed : ArenaSeed) (dag : DAG) : Bool :=
  seed.check &&
    (seed.clauses.mapIdx fun clauseId clause =>
      match seed.dagNodeId? clauseId with
      | none => false
      | some nodeId =>
          match dag.node? nodeId with
          | none => false
          | some node =>
              match node.conclusion? dag.problem with
              | none => false
              | some conclusion =>
                  match searchClause? conclusion with
                  | none => false
                  | some projected => CoreSyntax.Search.clauseEq projected clause).all id

end ArenaSeed

/--
把 HOSearch 已认证的全部 clause 节点按 DAG 顺序投影为 saturation seed。

生成顺序保持 `clause id = proof journal id = seed slot`；DAG node id 单独保存在
`dagNodeIds`，后续回放不依赖二者碰巧相等。
-/
def Result.arenaSeed? (result : Result) : Option ArenaSeed := do
  let clauses ← result.dag.nodes.mapM fun node => do
    let clause ← node.conclusion? result.dag.problem
    searchClause? clause
  let seed : ArenaSeed := {
    clauses := clauses
    dagNodeIds := result.dag.nodes.map (fun node => node.id)
  }
  if seed.checkAgainst result.dag then some seed else none

/-! ## typed term pool -/

/-- 搜索项的全部子项，包含根项本身。 -/
private partial def subterms : SearchTerm → List SearchTerm
  | term@(.var _) => [term]
  | term@(.bvar ..) => [term]
  | term@(.fvar ..) => [term]
  | term@(.app _ arguments) =>
      term :: arguments.flatMap subterms
  | term@(.apply function argument) =>
      term :: (subterms function ++ subterms argument)
  | term@(.lam _ _ body) =>
      term :: subterms body

/-- 只保留闭合可推断类型且尺寸受限的唯一搜索项。 -/
private def pushTerm? (config : Config) (terms : Array SearchTerm)
    (term : SearchTerm) : Array SearchTerm :=
  if term.size ≤ config.maxTermSize && term.inferSort?.isSome &&
      !terms.contains term then
    terms.push term
  else
    terms

/-- 从当前 DAG 的一个固定前缀收集 typed term pool。 -/
private def collectTerms (config : Config) (dag : DAG) (limit : Nat) :
    Array SearchTerm := Id.run do
  let mut terms : Array SearchTerm := #[]
  for index in [:Nat.min limit dag.nodes.size] do
    match dag.node? index with
    | none =>
        pure ()
    | some node =>
        match node.conclusion? dag.problem with
        | none =>
            pure ()
        | some clause =>
            match searchClause? clause with
            | none =>
                pure ()
            | some searchClause =>
                for literal in searchClause do
                  for term in subterms literal.left do
                    terms := pushTerm? config terms term
                  for term in subterms literal.right do
                    terms := pushTerm? config terms term
  return terms.extract 0 (Nat.min terms.size config.maxCollectedTerms)

/-! ## 新鲜 extensional witness 分配 -/

/-- 一个搜索项中出现过的最大函数符号编号加一。 -/
private partial def termMaxFunctionIdSucc : SearchTerm → Nat
  | .var _ => 0
  | .bvar .. => 0
  | .fvar .. => 0
  | .app symbol arguments =>
      arguments.foldl
        (fun result argument => Nat.max result (termMaxFunctionIdSucc argument))
        (symbol.id + 1)
  | .apply function argument =>
      Nat.max (termMaxFunctionIdSucc function) (termMaxFunctionIdSucc argument)
  | .lam _ _ body =>
      termMaxFunctionIdSucc body

/-- 一个搜索字句中出现过的最大函数符号编号加一。 -/
private def clauseMaxFunctionIdSucc (clause : SearchClause) : Nat :=
  clause.foldl
    (fun result literal =>
      Nat.max result
        (Nat.max (termMaxFunctionIdSucc literal.left)
          (termMaxFunctionIdSucc literal.right)))
    0

/-- 当前 DAG 已使用函数符号编号的上界。 -/
private def nextFunctionId (dag : DAG) : Nat := Id.run do
  let mut next := 0
  for index in [:dag.nodes.size] do
    match dag.node? index with
    | none =>
        pure ()
    | some node =>
        match node.conclusion? dag.problem with
        | none =>
            pure ()
        | some clause =>
            match searchClause? clause with
            | none =>
                pure ()
            | some searchClause =>
                next := Nat.max next (clauseMaxFunctionIdSucc searchClause)
  return next

/-- 为一条函数负等式构造新鲜且类型精确的 `diff` 符号。 -/
private def witnessSymbol (id : Nat) (domain codomain : CoreSyntax.CoreSort) :
    CoreSyntax.Search.FunctionSymbol := {
  id := id
  arity := 2
  kind := .extensionalWitness
  inputSorts := [.arrow domain codomain, .arrow domain codomain]
  outputSort := domain
}

/-! ## 候选构造 -/

/-- 构造 ResourceTrace 使用的自包含父引用。 -/
private def parentRef? (dag : DAG) (parentId : Nat) :
    Option ResourceTrace.ClauseRef := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  let searchParent ← searchClause? parentClause
  some { id := parentId, clause? := some searchParent }

/-- 自动构造 Boolean Extensionality resource，并用现有恢复器复核。 -/
private def booleanExtensionalityResource? (dag : DAG)
    (parentId literalIndex : Nat) : Option Resource := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  let parentLiteral ← parentClause.literals[literalIndex]?
  let parent ← parentRef? dag parentId
  match parentLiteral.atom with
  | .equal (.base .bool) leftTerm rightTerm =>
      let left ← betaEtaTrace? (searchTerm leftTerm)
      let right ← betaEtaTrace? (searchTerm rightTerm)
      let evidence : BooleanExtensionalityEvidence := {
        parent := { id := parentId, clause := parentClause }
        literalIndex := literalIndex
        sort := .base .bool
        polarity := parentLiteral.polarity
        left := left
        right := right
      }
      if !evidence.check #[parentId] then
        none
      if evidence.conclusion.eq parentClause then
        none
      let result ← searchClause? evidence.conclusion
      let _ ← booleanExtensionalityEvidence? dag parentId literalIndex result
      some (.local (.unary {
        kind := .booleanExtensionality
        parent := parent
        literalIndex? := some literalIndex
        result := result
      }))
  | _ =>
      none

/--
自动构造一参数 Argument Congruence resource，并用现有恢复器复核。

实参使用父字句中未出现的新鲜 typed 自由变量。字句自由变量按全称解释，因此单个
资源已经覆盖任意实参，不需要枚举 term pool。
-/
private def argumentCongruenceResource? (dag : DAG)
    (parentId literalIndex : Nat) : Option Resource := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  let parentLiteral ← parentClause.literals[literalIndex]?
  let parent ← parentRef? dag parentId
  let parentInput ← parent.clause?
  match parentLiteral.polarity, parentLiteral.atom with
  | true, .equal (.arrow domain codomain) left right =>
      let argument : SearchTerm :=
        .fvar (coreSort domain) parentInput.maxVarSucc
      let evidence : ArgumentCongruenceEvidence := {
        parent := { id := parentId, clause := parentClause }
        domain := domain
        codomain := codomain
        left := left
        right := right
        argument := term argument
      }
      if !evidence.check #[parentId] then
        none
      let result ← searchClause? evidence.conclusion
      let _ ←
        argumentCongruenceEvidence? dag parentId literalIndex parent.clause? result
      some (.local (.unary {
        kind := .argumentCongruence
        parent := parent
        literalIndex? := some literalIndex
        result := result
      }))
  | _, _ =>
      none

/-- 当前父负函数等式是否已经生成过 Function Extensionality 节点。 -/
private def hasFunctionExtensionality (dag : DAG) (parentId : Nat)
    (needle : Literal) : Bool :=
  dag.nodes.any fun node =>
    match node.payload with
    | .functionExtensionality evidence =>
        evidence.parent.id == parentId && evidence.needle.eq needle
    | _ =>
        false

/-- 自动构造带新鲜 `diff` 符号的 Function Extensionality resource。 -/
private def functionExtensionalityResource? (dag : DAG)
    (parentId literalIndex witnessId : Nat) : Option Resource := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  let parentLiteral ← parentClause.literals[literalIndex]?
  let parent ← parentRef? dag parentId
  match parentLiteral.polarity, parentLiteral.atom with
  | false, .equal (.arrow domain codomain) left right =>
      if hasFunctionExtensionality dag parentId parentLiteral then
        none
      let symbol := witnessSymbol witnessId (coreSort domain) (coreSort codomain)
      let evidence : FunctionExtensionalityEvidence := {
        parent := { id := parentId, clause := parentClause }
        domain := domain
        codomain := codomain
        left := left
        right := right
        witnessSymbol := symbol
      }
      if !evidence.check #[parentId] then
        none
      let result ← searchClause? evidence.conclusion
      let _ ←
        functionExtensionalityEvidence? dag parentId literalIndex parent.clause? result
      some (.local (.unary {
        kind := .functionExtensionality
        parent := parent
        literalIndex? := some literalIndex
        result := result
      }))
  | _, _ =>
      none

/--
HO-AVATAR 外延链只从 component 或携带 component guard 的普通派生节点继续。

canonical source 与 split descriptor 不能绕过 selector 激活直接生成全局推论。
-/
def avatarExtensionalParentEligible (node : Node) : Bool :=
  !node.unguarded &&
    match node.payload with
    | .avatarComponent _ => true
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
    | _ => false

/--
β/η 公理节点只服务归一化与回放，不重新进入外延一元规则的 active parent 集。

普通模式允许 canonical source；AVATAR 模式额外要求 component 来源与非空 guard。
-/
private def extensionalParentEligible (discipline : ExtensionalParentDiscipline)
    (node : Node) : Bool :=
  match discipline with
  | .ordinary =>
      match node.payload with
      | .beta _ => false
      | .eta _ => false
      | _ => true
  | .avatar =>
      avatarExtensionalParentEligible node

/-- 当前父节点是否已经有自动外延一元子节点。 -/
private def hasExtensionalUnaryChild (dag : DAG) (parentId : Nat) : Bool :=
  dag.nodes.any fun node =>
    match node.payload with
    | .booleanExtensionality evidence => evidence.parent.id == parentId
    | .argumentCongruence evidence => evidence.parent.id == parentId
    | .functionExtensionality evidence => evidence.parent.id == parentId
    | _ => false

/-! ## DAG 准入、去重与有界轮转 -/

/-- 一个资源预期生成的 guarded conclusion。 -/
private def expectedGuardedConclusion? (dag : DAG) (resource : Resource) :
    Option (GuardSet × Clause) := do
  match resource with
  | .beta redex =>
      let checked ← checkedBetaPayload? redex
      some (#[], checked.payload.conclusion)
  | .eta redex =>
      let checked ← checkedEtaPayload? redex
      some (#[], checked.payload.conclusion)
  | .local witness =>
      let parents := witness.parents.map (fun parent => parent.id)
      let guards ← dag.parentGuardUnion? parents
      let result ← clause? witness.result
      some (guards, result)

/-- DAG 中是否已经存在相同 guard 与相同结论的节点。 -/
private def containsGuardedConclusion (dag : DAG) (guards : GuardSet)
    (conclusion : Clause) : Bool :=
  dag.nodes.any fun node =>
    HODAGCertificate.guardSetEq node.guards guards &&
      match node.conclusion? dag.problem with
      | some existing => existing.eq conclusion
      | none => false

/-- 先按 guarded conclusion 去重，再交给现有材料化 checker。 -/
private def pushResource? (dag : DAG) (resource : Resource) :
    Option (DAG × Bool) := do
  let (guards, conclusion) ← expectedGuardedConclusion? dag resource
  if containsGuardedConclusion dag guards conclusion then
    some (dag, false)
  else
    let next ← pushHigherOrderResource? dag resource
    some (next, true)

/-- 尝试准入一个资源并更新审计统计。 -/
private def State.tryResource (config : Config) (state : State)
    (resource : Resource) : State × Bool :=
  if state.stats.generated ≥ config.maxGenerated then
    (state, false)
  else
    let state := {
      state with
      stats := { state.stats with candidates := state.stats.candidates + 1 }
    }
    match pushResource? state.dag resource with
    | some (dag, true) =>
        ({
          state with
          dag := dag
          resources := state.resources.push resource
          stats := state.stats.recordGenerated resource
        }, true)
    | some (_, false) =>
        ({
          state with
          stats := { state.stats with deduplicated := state.stats.deduplicated + 1 }
        }, false)
    | none =>
        ({
          state with
          stats := { state.stats with rejected := state.stats.rejected + 1 }
        }, false)

/-- 执行一轮高阶一元资源生成；本轮只展开进入轮次前已经存在的节点。 -/
private def runRound (discipline : ExtensionalParentDiscipline)
    (config : Config) (input : State) : State × Nat := Id.run do
  let sourceSize := input.dag.nodes.size
  let terms := collectTerms config input.dag sourceSize
  let generatedBefore := input.stats.generated
  let mut state := {
    input with
    stats := { input.stats with rounds := input.stats.rounds + 1 }
  }

  for candidate in terms do
    if config.beta && state.stats.generated < config.maxGenerated &&
        (checkedBetaPayload? candidate).isSome then
      state := (state.tryResource config (.beta candidate)).1
    if config.eta && state.stats.generated < config.maxGenerated &&
        (checkedEtaPayload? candidate).isSome then
      state := (state.tryResource config (.eta candidate)).1

  for parentId in [:sourceSize] do
    match state.dag.node? parentId with
    | none =>
        pure ()
    | some parentNode =>
        match parentNode.conclusion? state.dag.problem with
        | none =>
            pure ()
        | some parentClause =>
            if extensionalParentEligible discipline parentNode &&
                !hasExtensionalUnaryChild state.dag parentId then
              let mut selected := false

              for literalIndex in [:parentClause.literals.size] do
                if !selected && config.booleanExtensionality &&
                    state.stats.generated < config.maxGenerated then
                  match booleanExtensionalityResource? state.dag parentId literalIndex with
                  | some resource =>
                      state := (state.tryResource config resource).1
                      selected := true
                  | none =>
                      pure ()

              for literalIndex in [:parentClause.literals.size] do
                if !selected && config.functionExtensionality &&
                    state.stats.generated < config.maxGenerated then
                  match functionExtensionalityResource? state.dag parentId literalIndex
                      state.nextWitnessId with
                  | some resource =>
                      let attempted := state.tryResource config resource
                      state := { attempted.1 with nextWitnessId := state.nextWitnessId + 1 }
                      selected := true
                  | none =>
                      pure ()

              for literalIndex in [:parentClause.literals.size] do
                if !selected && config.argumentCongruence &&
                    state.stats.generated < config.maxGenerated then
                  match argumentCongruenceResource? state.dag parentId literalIndex with
                  | some resource =>
                      state := (state.tryResource config resource).1
                      selected := true
                  | none =>
                      pure ()

  return (state, state.stats.generated - generatedBefore)

/-- 按轮数执行高阶一元资源饱和；无新增资源时提前停止。 -/
private def runRounds : Nat → ExtensionalParentDiscipline → Config → State → State
  | 0, _discipline, _config, state =>
      state
  | rounds + 1, discipline, config, state =>
      if state.stats.generated ≥ config.maxGenerated then
        state
      else
        let (next, generated) := runRound discipline config state
        if generated = 0 then
          next
        else
          runRounds rounds discipline config next

/--
按指定父节点来源纪律生成并材料化高阶一元资源。

返回的 DAG 仍保留原 root；搜索器后续可以继续追加 resolution、superposition 或
residual CDCL 闭合节点。
-/
private def runWithDiscipline (discipline : ExtensionalParentDiscipline)
    (dag : DAG) (config : Config) : Result :=
  let initial : State := {
    dag := dag
    nextWitnessId := nextFunctionId dag
  }
  let final := runRounds config.maxRounds discipline config initial
  {
    dag := final.dag
    resources := final.resources
    stats := final.stats
  }

/-- 从普通 HO-DAG 自动生成高阶一元资源。 -/
def run (dag : DAG) (config : Config := {}) : Result :=
  runWithDiscipline .ordinary dag config

/-- 从 split/component HO-AVATAR DAG 生成保持 selector guard 的高阶一元资源。 -/
def runAvatar (dag : DAG) (config : Config := {}) : Result :=
  runWithDiscipline .avatar dag config

/-- 从 guarded source 直接构造 HO-DAG 并执行高阶一元资源搜索。 -/
def runGuardedSources? (inputs : Array GuardedSourceInput) (root : Nat := 0)
    (config : Config := {}) : Option Result := do
  if inputs.isEmpty || root ≥ inputs.size then
    none
  else
    let dag ← guardedSourceDAG? inputs root
    some (run dag config)

/-- 从普通 source clause 直接构造无 guard HO-DAG 并执行高阶一元资源搜索。 -/
def runSources? (inputs : Array SearchClause) (root : Nat := 0)
    (config : Config := {}) : Option Result :=
  runGuardedSources?
    (inputs.map fun clause => ({ clause := clause } : GuardedSourceInput))
    root config

end HOSearch
end Automation
end YesMetaZFC
