import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.HODAGCertificate
import YesMetaZFC.Automation.ResourceTrace

/-!
# 搜索项到原生 HO 证书的材料化

这里不执行 lambda lifting。搜索层的 `apply/lam` 被逐构造翻译到
`Logic.HigherOrder.Term`，最终由 HO clause checker 统一复核 scope、arity 与 simple type。
-/

namespace YesMetaZFC
namespace Automation
namespace HOSearchMaterialization

open Logic.HigherOrder

/-- `CoreSort` 中不能继续分解为箭头的基础 sort。 -/
inductive BaseSort where
  | object
  | bool
  | prop
  | named (id : Nat)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 搜索层关系符号。 -/
inductive RelSymbol where
  | member
  | boolHolds
  | definition (id arity : Nat)
  | predicate (symbol : CoreSyntax.PredicateSymbol)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 把搜索层递归箭头 sort 透明映射到 HO simple type。 -/
def simpleType : CoreSyntax.CoreSort → SimpleType BaseSort
  | .object => .base .object
  | .bool => .base .bool
  | .prop => .base .prop
  | .named id => .base (.named id)
  | .arrow domain codomain => .arrow (simpleType domain) (simpleType codomain)

/-- 把材料化签名中的 simple type 透明恢复为搜索层 sort。 -/
def coreSort : SimpleType BaseSort → CoreSyntax.CoreSort
  | .base .object => .object
  | .base .bool => .bool
  | .base .prop => .prop
  | .base (.named id) => .named id
  | .arrow domain codomain => .arrow (coreSort domain) (coreSort codomain)

/-- 原生 HO 材料化使用的签名。 -/
def SearchSignature : Logic.HigherOrder.Signature where
  BaseSort := BaseSort
  FuncSymbol := CoreSyntax.Search.FunctionSymbol
  RelSymbol := RelSymbol
  funcDomain symbol :=
    if symbol.inputSorts.isEmpty then
      List.replicate symbol.arity (.base BaseSort.object)
    else
      symbol.inputSorts.map simpleType
  funcCodomain symbol := simpleType symbol.outputSort
  isFunctionExtensionalityWitness symbol :=
    symbol.kind == CoreSyntax.Search.SymbolKind.extensionalWitness
  relDomain
    | .member => [.base .object, .base .object]
    | .boolHolds => [.base .bool]
    | .definition .. => [.base .object]
    | .predicate symbol =>
        if symbol.inputSorts.isEmpty then
          List.replicate symbol.arity (.base BaseSort.object)
        else
          symbol.inputSorts.map simpleType

instance instSearchSignatureBaseSortDecidableEq :
    DecidableEq SearchSignature.BaseSort := by
  change DecidableEq BaseSort
  infer_instance

instance instSearchSignatureFuncSymbolDecidableEq :
    DecidableEq SearchSignature.FuncSymbol := by
  change DecidableEq CoreSyntax.Search.FunctionSymbol
  infer_instance

instance instSearchSignatureRelSymbolDecidableEq :
    DecidableEq SearchSignature.RelSymbol := by
  change DecidableEq RelSymbol
  infer_instance

abbrev Term := HODAGCertificate.Term SearchSignature
abbrev Atom := HODAGCertificate.Atom SearchSignature
abbrev Literal := HODAGCertificate.Literal SearchSignature
abbrev Clause := HODAGCertificate.Clause SearchSignature
abbrev CheckedClause := HODAGCertificate.CheckedClause SearchSignature
abbrev BetaPayload := HODAGCertificate.Beta.Payload SearchSignature
abbrev CheckedBetaPayload := HODAGCertificate.Beta.CheckedPayload SearchSignature
abbrev EtaPayload := HODAGCertificate.Eta.Payload SearchSignature
abbrev CheckedEtaPayload := HODAGCertificate.Eta.CheckedPayload SearchSignature
abbrev BetaEtaTrace := HODAGCertificate.BetaEta.Trace SearchSignature
abbrev Problem := HODAGCertificate.Problem SearchSignature
abbrev Payload := HODAGCertificate.Payload SearchSignature
abbrev Node := HODAGCertificate.Node SearchSignature
abbrev DAG := HODAGCertificate.DAG SearchSignature
abbrev CheckedDAG := HODAGCertificate.CheckedDAG (σ := SearchSignature)
abbrev ParentClause := HODAGCertificate.ParentClause SearchSignature
abbrev TermSubstitution := Logic.HigherOrder.TermSubstitution SearchSignature
abbrev SubstitutionEvidence := HODAGCertificate.Substitution.Evidence SearchSignature
abbrev StandardizeApartEvidence :=
  HODAGCertificate.StandardizeApart.Evidence SearchSignature
abbrev ResolutionEvidence := HODAGCertificate.Resolution.Evidence SearchSignature
abbrev FactoringEvidence := HODAGCertificate.Factoring.Evidence SearchSignature
abbrev EqualityResolutionEvidence :=
  HODAGCertificate.EqualityResolution.Evidence SearchSignature
abbrev BooleanExtensionalityEvidence :=
  HODAGCertificate.BooleanExtensionality.Evidence SearchSignature
abbrev TermContext := HODAGCertificate.TermContext SearchSignature
abbrev AtomContext := HODAGCertificate.AtomContext SearchSignature
abbrev RewriteEvidence := HODAGCertificate.Rewrite.Evidence SearchSignature
abbrev ArgumentCongruenceEvidence :=
  HODAGCertificate.ArgumentCongruence.Evidence SearchSignature
abbrev FunctionExtensionalityEvidence :=
  HODAGCertificate.FunctionExtensionality.Evidence SearchSignature
abbrev GuardSet := HODAGCertificate.GuardSet
abbrev PropLiteralLink := HODAGCertificate.PropLiteralLink SearchSignature
abbrev PropParentClauseLink :=
  HODAGCertificate.PropParentClauseLink SearchSignature
abbrev PropGuardActivationLink :=
  HODAGCertificate.PropGuardActivationLink SearchSignature
abbrev PropLearnedClauseLink := HODAGCertificate.PropLearnedClauseLink
abbrev PropAvatarSkeletonLink := HODAGCertificate.PropAvatarSkeletonLink
abbrev PropInitialJustification :=
  HODAGCertificate.PropInitialJustification SearchSignature
abbrev PropositionalClosurePayload :=
  HODAGCertificate.PropositionalClosurePayload SearchSignature
abbrev TheoryConflictPayload :=
  HODAGCertificate.TheoryConflictPayload SearchSignature
abbrev PropositionalLearnedClausePayload :=
  HODAGCertificate.PropositionalLearnedClausePayload

/-- 搜索项的结构保持材料化；`apply/lam` 不再进入拒绝分支。 -/
def term : CoreSyntax.Search.Term → Term
  | .var id => .var (.fvar (.base .object) id)
  | .bvar sort index => .var (.bvar (simpleType sort) index)
  | .fvar sort id => .var (.fvar (simpleType sort) id)
  | .app symbol arguments => .app symbol (arguments.map term)
  | .apply function argument => .apply (term function) (term argument)
  | .lam domain codomain body =>
      .lam (simpleType domain) (simpleType codomain) (term body)

/-- 从原生 HO 项恢复同构的搜索项；用于从真实父节点重建局部归一化轨迹。 -/
def searchTerm : Term → CoreSyntax.Search.Term
  | .var (.bvar sort index) => .bvar (coreSort sort) index
  | .var (.fvar sort id) => .fvar (coreSort sort) id
  | .app symbol arguments => .app symbol (arguments.map searchTerm)
  | .apply function argument => .apply (searchTerm function) (searchTerm argument)
  | .lam domain codomain body =>
      .lam (coreSort domain) (coreSort codomain) (searchTerm body)

/-- 验证搜索表面的 tuple marker，并恢复真实谓词参数。 -/
def projectedPredicateArguments? (predicate : CoreSyntax.PredicateSymbol)
    (input : CoreSyntax.Search.Term) : Option (List CoreSyntax.Search.Term) := do
  match input with
  | .app tuple arguments =>
      let expected : CoreSyntax.Search.FunctionSymbol := {
        id := predicate.id
        arity := arguments.length
        kind := CoreSyntax.Search.SymbolKind.tuple
        inputSorts := predicate.inputSorts
      }
      if tuple != expected then
        none
      if arguments.length != predicate.arity then
        none
      some arguments
  | _ =>
      none

/-- 搜索原子材料化。等词必须先能在搜索层推断出相同 simple type。 -/
def atom? (predicate : CoreSyntax.Search.PredicateKind)
    (left right : CoreSyntax.Search.Term) : Option Atom := do
  match predicate with
  | .equal =>
      let leftSort ← left.inferSort?
      let rightSort ← right.inferSort?
      if leftSort = rightSort then
        some (.equal (simpleType leftSort) (term left) (term right))
      else
        none
  | .member =>
      some (.rel .member [term left, term right])
  | .boolHolds =>
      some (.rel .boolHolds [term left])
  | .definition id arity =>
      some (.rel (.definition id arity) [term left])
  | .predicate symbol =>
      let arguments ← projectedPredicateArguments? symbol left
      some (.rel (.predicate symbol) (arguments.map term))

/-- 搜索 literal 材料化。 -/
def literal? (input : CoreSyntax.Search.Literal) : Option Literal := do
  let atom ← atom? input.predicate input.left input.right
  some { polarity := input.positive, atom := atom }

/-- 搜索 clause 材料化。 -/
def clause? (input : CoreSyntax.Search.Clause) : Option Clause := do
  let literals ← input.mapM literal?
  some { literals := literals }

/-- 把 typed 搜索 substitution 透明提升为原生 HO substitution。 -/
def termSubstitution? (input : CoreSyntax.Search.Substitution) : Option TermSubstitution :=
  input.mapM fun binding => do
    let sort := simpleType binding.key.sort
    let replacement := term binding.replacement
    if replacement.inferSort? = some sort then
      some {
        sort := sort
        id := binding.key.id
        replacement := replacement
      }
    else
      none

/-- 材料化并立即通过 HO 闭子句 checker。 -/
def checkedClause? (input : CoreSyntax.Search.Clause) : Option CheckedClause := do
  let clause ← clause? input
  if hCheck : clause.check = true then
    some { clause := clause, checked := hCheck }
  else
    none

/-- 从搜索层根部 β-redex 直接生成 checked HO β payload。 -/
def checkedBetaPayload? (input : CoreSyntax.Search.Term) : Option CheckedBetaPayload := do
  match input with
  | .apply (.lam domain codomain body) argument =>
      let payload : BetaPayload := {
        domain := simpleType domain
        codomain := simpleType codomain
        body := term body
        argument := term argument
      }
      if hCheck : payload.check = true then
        some { payload := payload, checked := hCheck }
      else
        none
  | _ =>
      none

/-- 从搜索层规范 η-redex 生成 checked HO η payload。 -/
def checkedEtaPayload? (input : CoreSyntax.Search.Term) : Option CheckedEtaPayload := do
  match input with
  | .lam domain codomain body =>
      let contracted ← CoreSyntax.Search.BetaEta.etaContract? domain body
      let reconstructed : CoreSyntax.Search.Term :=
        .lam domain codomain
          (.apply (CoreSyntax.Search.Term.shift 1 contracted) (.bvar domain 0))
      if !CoreSyntax.Search.termEq input reconstructed then
        none
      else
        let payload : EtaPayload := {
          domain := simpleType domain
          codomain := simpleType codomain
          function := term contracted
        }
        if hCheck : payload.check = true then
          some { payload := payload, checked := hCheck }
        else
          none
  | _ =>
      none

/-- 把一组参数轨迹提升为同一未柯里化函数头下的逐参数同余轨迹。 -/
private def appTraceFrom (symbol : CoreSyntax.Search.FunctionSymbol)
    (before : List Term) : List BetaEtaTrace → BetaEtaTrace
  | [] => .refl (.app symbol before)
  | argument :: rest =>
      .trans
        (.appArgument symbol before argument
          (rest.map HODAGCertificate.BetaEta.Trace.source))
        (appTraceFrom symbol (before ++ [argument.target]) rest)

mutual
  /-- 镜像搜索层 fuel 归一化并生成原生 HO βη 回放轨迹。 -/
  partial def betaEtaTraceWith? :
      Nat → CoreSyntax.Search.Term → Option BetaEtaTrace
    | 0, input =>
        some (.refl (term input))
    | _fuel + 1, input@(.var _) =>
        some (.refl (term input))
    | _fuel + 1, input@(.bvar ..) =>
        some (.refl (term input))
    | _fuel + 1, input@(.fvar ..) =>
        some (.refl (term input))
    | fuel + 1, .app symbol arguments => do
        let traces ← betaEtaTraceListWith? fuel arguments
        let trace := appTraceFrom symbol [] traces
        if trace.check then some trace else none
    | fuel + 1, .apply function argument => do
        let functionTrace ← betaEtaTraceWith? fuel function
        let argumentTrace ← betaEtaTraceWith? fuel argument
        let congruence : BetaEtaTrace :=
          .trans
            (.applyFunction functionTrace argumentTrace.source)
            (.applyArgument functionTrace.target argumentTrace)
        let normalizedFunction :=
          CoreSyntax.Search.normalizeBetaEtaWith fuel function
        let normalizedArgument :=
          CoreSyntax.Search.normalizeBetaEtaWith fuel argument
        let trace ←
          match normalizedFunction with
          | .lam domain codomain body => do
              let reduct :=
                CoreSyntax.Search.Term.instantiate normalizedArgument body
              let reductTrace ← betaEtaTraceWith? fuel reduct
              some
                (.trans congruence
                  (.trans
                    (.beta (simpleType domain) (simpleType codomain)
                      (term body) (term normalizedArgument))
                    reductTrace))
          | _ =>
              some congruence
        if trace.check then some trace else none
    | fuel + 1, .lam domain codomain body => do
        let bodyTrace ← betaEtaTraceWith? fuel body
        let congruence : BetaEtaTrace :=
          .lam (simpleType domain) (simpleType codomain) bodyTrace
        let normalizedBody := CoreSyntax.Search.normalizeBetaEtaWith fuel body
        let trace ←
          match CoreSyntax.Search.BetaEta.etaContract? domain normalizedBody with
          | some contracted => do
              let contractedTrace ← betaEtaTraceWith? fuel contracted
              some
                (.trans congruence
                  (.trans
                    (.eta (simpleType domain) (simpleType codomain)
                      (term contracted))
                    contractedTrace))
          | none =>
              some congruence
        if trace.check then some trace else none

  /-- 对参数列表逐项生成 βη 回放轨迹。 -/
  partial def betaEtaTraceListWith? :
      Nat → List CoreSyntax.Search.Term → Option (List BetaEtaTrace)
    | _fuel, [] =>
        some []
    | fuel, argument :: rest => do
        let argumentTrace ← betaEtaTraceWith? fuel argument
        let restTraces ← betaEtaTraceListWith? fuel rest
        some (argumentTrace :: restTraces)
end

/-- 生成完整 fuel 的 βη 轨迹，并复核起点与确定性终点。 -/
def betaEtaTrace? (input : CoreSyntax.Search.Term) : Option BetaEtaTrace := do
  let trace ← betaEtaTraceWith? (input.size * 4 + 16) input
  let expected := term (CoreSyntax.Search.normalizeBetaEta input)
  if trace.check &&
      HODAGCertificate.StructuralEq.term trace.source (term input) &&
        HODAGCertificate.StructuralEq.term trace.target expected then
    some trace
  else
    none

/-! ## 原生 HO 整图材料化 -/

/-- 把一组搜索子句材料化为 HO 初始问题。 -/
def problem? (inputs : Array CoreSyntax.Search.Clause) : Option Problem := do
  let initialClauses ← inputs.mapM clause?
  some { initialClauses := initialClauses }

/-- 初始问题的 canonical source 节点数组。 -/
def sourceNodes (problem : Problem) : Array Node :=
  problem.initialClauses.mapIdx fun index _clause => {
    id := index
    parents := #[]
    payload := .source index
  }

/-- 只含 source 节点的原生 HO DAG。 -/
def sourceDAG (problem : Problem) (root : Nat) : DAG where
  problem := problem
  root := root
  nodes := sourceNodes problem

/-- 材料化 source-only HO DAG 并立即运行整图 checker。 -/
def checkedSourceDAG? (inputs : Array CoreSyntax.Search.Clause)
    (root : Nat) : Option CheckedDAG := do
  let problem ← problem? inputs
  HODAGCertificate.CheckedDAG.mk? (sourceDAG problem root)

/-- AVATAR split 后交给 HO 搜索器的 guarded source。 -/
structure GuardedSourceInput where
  guards : GuardSet := #[]
  clause : CoreSyntax.Search.Clause

/-- 从 guarded source 数组构造原生 HO-DAG；最终 checker 在闭合节点接入后运行。 -/
def guardedSourceDAG? (inputs : Array GuardedSourceInput)
    (root : Nat := 0) : Option DAG := do
  let initialClauses ← inputs.mapM fun input => clause? input.clause
  let problem : Problem := { initialClauses := initialClauses }
  let nodes := inputs.mapIdx fun index input => {
    id := index
    parents := #[]
    guards := HODAGCertificate.canonicalGuards input.guards
    payload := .source index
  }
  some { problem := problem, root := root, nodes := nodes }

/-! ## HO-AVATAR split/component 材料化 -/

/-- 已材料化 HO clause 的结构相等查找。 -/
private def findClause? (clauses : Array Clause) (needle : Clause) :
    Option Nat := Id.run do
  for hIndex : index in [:clauses.size] do
    if clauses[index].eq needle then
      return some index
  return none

/-- 在原生 HO atom 表中查找结构相同的对象原子。 -/
private def findAvatarAtom? (atoms : Array Atom) (needle : Atom) :
    Option Nat := Id.run do
  for hIndex : index in [:atoms.size] do
    if atoms[index].eq needle then
      return some index
  return none

/-- 初始问题中的对象原子数量；selector 从该边界之后分配。 -/
private def avatarObjectAtomCount (problem : Problem) : Nat := Id.run do
  let mut atoms : Array Atom := #[]
  for clause in problem.initialClauses do
    for literal in clause.literals do
      if (findAvatarAtom? atoms literal.atom).isNone then
        atoms := atoms.push literal.atom
  return atoms.size

/-- 为一个 component 复用全局 selector，否则追加新 selector。 -/
private def internAvatarComponent (guardBase : Nat) (components : Array Clause)
    (selectors : Array PropResolution.Lit) (component : Clause) :
    Array Clause × Array PropResolution.Lit × Nat := Id.run do
  match findClause? components component with
  | some index =>
      return (components, selectors, index)
  | none =>
      let index := components.size
      let selector : PropResolution.Lit := {
        var := guardBase + index
        positive := true
      }
      return (components.push component, selectors.push selector, index)

/-- 为原生 HO source 表建立稳定的 component 与 selector 表。 -/
private def avatarPartitions (problem : Problem) :
    Array (Array (Array Nat) × Array Clause × Array PropResolution.Lit) := Id.run do
  let guardBase := avatarObjectAtomCount problem
  let mut components : Array Clause := #[]
  let mut selectors : Array PropResolution.Lit := #[]
  let mut result :
      Array (Array (Array Nat) × Array Clause × Array PropResolution.Lit) := #[]
  for source in problem.initialClauses do
    let mut partitions : Array (Array Nat) := #[]
    let mut localComponents : Array Clause := #[]
    let mut localSelectors : Array PropResolution.Lit := #[]
    for split in HODAGCertificate.Avatar.splitClause source do
      let (nextComponents, nextSelectors, componentIndex) :=
        internAvatarComponent guardBase components selectors split.2
      components := nextComponents
      selectors := nextSelectors
      partitions := partitions.push split.1
      localComponents := localComponents.push split.2
      localSelectors := localSelectors.push selectors[componentIndex]!
    result := result.push (partitions, localComponents, localSelectors)
  return result

/-- 向 HO-DAG 追加一个 split descriptor。 -/
def pushAvatarSplit? (dag : DAG) (sourceId : Nat)
    (partitions : Array (Array Nat))
    (selectors : PropResolution.Clause) : Option (DAG × Nat) := do
  let sourceNode ← dag.node? sourceId
  let sourceClause ← sourceNode.conclusion? dag.problem
  if !sourceNode.unguarded then
    none
  else
    let payload : HODAGCertificate.AvatarSplitPayload SearchSignature := {
      source := { id := sourceId, clause := sourceClause }
      partitions := partitions
      selectors := selectors
    }
    let node : Node := {
      id := dag.nodes.size
      parents := #[sourceId]
      guards := #[]
      payload := .avatarSplit payload
    }
    if node.check dag.problem && dag.localNodeGuardsOk node then
      let id := node.id
      some ({ dag with nodes := dag.nodes.push node }, id)
    else
      none

/-- 向 HO-DAG 追加一个 split 对应的 singleton-guard component。 -/
def pushAvatarComponent? (dag : DAG) (splitId componentIndex : Nat) :
    Option (DAG × Nat) := do
  let splitNode ← dag.node? splitId
  match splitNode.payload with
  | .avatarSplit splitPayload =>
      let indices ← splitPayload.partitions[componentIndex]?
      let selector ←
        AvatarSplit.selectorAt?
          splitPayload.selectors componentIndex
      let component :=
        HODAGCertificate.Avatar.clauseAtIndices splitPayload.source.clause indices
      let splitClause ← splitNode.conclusion? dag.problem
      let payload : HODAGCertificate.AvatarComponentPayload SearchSignature := {
        split := { id := splitId, clause := splitClause }
        componentIndex := componentIndex
        component := component
        selector := selector
      }
      let node : Node := {
        id := dag.nodes.size
        parents := #[splitId]
        guards := #[selector]
        payload := .avatarComponent payload
      }
      if node.check dag.problem && dag.localNodeGuardsOk node then
        let id := node.id
        some ({ dag with nodes := dag.nodes.push node }, id)
      else
        none
  | _ =>
      none

/-- 从 canonical HO source 自动生成 split/component 节点。 -/
def avatarSourceDAG? (inputs : Array CoreSyntax.Search.Clause)
    (root : Nat := 0) : Option DAG := do
  let dag ← sourceDAG (← problem? inputs) root
  let descriptors := avatarPartitions dag.problem
  if descriptors.size != dag.problem.initialClauses.size then
    none
  else
    let mut state := dag
    for _hIndex : index in [:descriptors.size] do
      let descriptor := descriptors[index]!
      let splitPayloadPartitions := descriptor.1
      let selectors := descriptor.2.2
      let (next, splitId) ←
        pushAvatarSplit? state index splitPayloadPartitions selectors
      state := next
      for _hComponent : componentIndex in [:selectors.size] do
        let (next, _) ← pushAvatarComponent? state splitId componentIndex
        state := next
    some state

/-- 对已经构造的 HO-AVATAR DAG 运行基础与全局 registry 两层 checker。 -/
def checkedAvatarDAG? (dag : DAG) :
    Option (HODAGCertificate.CheckedAvatarDAG (σ := SearchSignature)) := do
  let checked ← HODAGCertificate.CheckedDAG.mk? dag
  HODAGCertificate.CheckedAvatarDAG.mk? checked

/-- 向原生 HO DAG 追加一个 β 节点；根编号保持不变。 -/
def pushBeta (dag : DAG) (payload : BetaPayload) : DAG :=
  { dag with
    nodes := dag.nodes.push {
      id := dag.nodes.size
      parents := #[]
      payload := .beta payload
    }
  }

/-- 从搜索项材料化 β payload 并追加到原生 HO DAG。 -/
def pushBeta? (dag : DAG) (input : CoreSyntax.Search.Term) : Option DAG := do
  let checked ← checkedBetaPayload? input
  some (pushBeta dag checked.payload)

/-- 向原生 HO DAG 追加一个 η 节点；根编号保持不变。 -/
def pushEta (dag : DAG) (payload : EtaPayload) : DAG :=
  { dag with
    nodes := dag.nodes.push {
      id := dag.nodes.size
      parents := #[]
      payload := .eta payload
    }
  }

/-- 从搜索项材料化 η payload 并追加到原生 HO DAG。 -/
def pushEta? (dag : DAG) (input : CoreSyntax.Search.Term) : Option DAG := do
  let checked ← checkedEtaPayload? input
  some (pushEta dag checked.payload)

/-- 为本地 HO 推理节点机械计算父 guard 并集。 -/
def derivedNode? (dag : DAG) (parents : Array Nat) (payload : Payload) :
    Option Node := do
  let guards ← dag.parentGuardUnion? parents
  some {
    id := dag.nodes.size
    parents := parents
    guards := guards
    payload := payload
  }

/-! ## Typed substitution 与 standardize-apart 材料化 -/

/-- 从真实父节点恢复并检查 typed substitution 证据。 -/
def substitutionEvidence? (dag : DAG) (parentId : Nat)
    (parentInput? : Option CoreSyntax.Search.Clause)
    (substitution : CoreSyntax.Search.Substitution) :
    Option SubstitutionEvidence := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  match parentInput? with
  | some parentInput =>
      let materializedParent ← clause? parentInput
      if materializedParent.eq parentClause then
        pure ()
      else
        none
  | none =>
      pure ()
  let typedSubstitution ← termSubstitution? substitution
  let evidence : SubstitutionEvidence := {
    parent := { id := parentId, clause := parentClause }
    substitution := typedSubstitution
  }
  if evidence.check #[parentId] then
    some evidence
  else
    none

/-- 向原生 HO DAG 追加一个 typed substitution 节点。 -/
def pushSubstitution (dag : DAG) (evidence : SubstitutionEvidence) : Option DAG := do
  let node ← derivedNode? dag #[evidence.parent.id] (.substitution evidence)
  if node.check dag.problem && dag.parentSnapshotChecked evidence.parent then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/-- 从 typed 搜索 substitution 追加原生 HO substitution 节点，并返回新父节点编号。 -/
def pushSubstitutionFromSearch? (dag : DAG) (parentId : Nat)
    (parentInput? : Option CoreSyntax.Search.Clause)
    (substitution : CoreSyntax.Search.Substitution) : Option (DAG × Nat) := do
  let evidence ← substitutionEvidence? dag parentId parentInput? substitution
  let newId := dag.nodes.size
  let dag ← pushSubstitution dag evidence
  some (dag, newId)

/-- 从真实父节点和单侧 metadata 恢复 standardize-apart 证据。 -/
def standardizeApartEvidence? (dag : DAG) (ref : ResourceTrace.ClauseRef)
    (side : ResourceTrace.StandardizeApartSideMetadata) :
    Option StandardizeApartEvidence := do
  let parentNode ← dag.node? ref.id
  let parentClause ← parentNode.conclusion? dag.problem
  match ref.clause? with
  | some parentInput =>
      let materializedParent ← clause? parentInput
      if materializedParent.eq parentClause then
        pure ()
      else
        none
  | none =>
      pure ()
  let original ← clause? side.original
  if !original.eq parentClause then
    none
  let renamed ← clause? side.renamed
  let evidence : StandardizeApartEvidence := {
    parent := { id := ref.id, clause := parentClause }
    offset := side.offset
  }
  if evidence.conclusion.eq renamed && evidence.check #[ref.id] then
    some evidence
  else
    none

/-- 向原生 HO DAG 追加一个 standardize-apart 节点。 -/
def pushStandardizeApart (dag : DAG)
    (evidence : StandardizeApartEvidence) : Option DAG := do
  let node ← derivedNode? dag #[evidence.parent.id] (.standardizeApart evidence)
  if node.check dag.problem && dag.parentSnapshotChecked evidence.parent then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/-- 消费单侧 metadata，追加改名节点并返回新父编号。 -/
def pushStandardizeApartSide? (dag : DAG) (ref : ResourceTrace.ClauseRef)
    (side : ResourceTrace.StandardizeApartSideMetadata) : Option (DAG × Nat) := do
  let evidence ← standardizeApartEvidence? dag ref side
  let newId := dag.nodes.size
  let dag ← pushStandardizeApart dag evidence
  some (dag, newId)

/-- 二元 standardize-apart 后可供后续局部规则引用的两个新父节点。 -/
structure StandardizedParents where
  dag : DAG
  left : Nat
  right : Nat

/-- 把二元 metadata 物化为两条显式 standardize-apart 图边。 -/
def pushStandardizeApartPair? (dag : DAG)
    (leftRef rightRef : ResourceTrace.ClauseRef)
    (metadata : ResourceTrace.StandardizeApartMetadata) :
    Option StandardizedParents := do
  let (dag, left) ← pushStandardizeApartSide? dag leftRef metadata.left
  let (dag, right) ← pushStandardizeApartSide? dag rightRef metadata.right
  some { dag := dag, left := left, right := right }

/-! ## Resolution / Factoring / Equality Resolution 材料化 -/

/-- 从真实父节点恢复字句，并按需复核搜索层携带的父快照。 -/
def parentClause? (dag : DAG) (parentId : Nat)
    (parentInput? : Option CoreSyntax.Search.Clause) : Option Clause := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  match parentInput? with
  | some parentInput =>
      let materializedParent ← clause? parentInput
      if materializedParent.eq parentClause then
        some parentClause
      else
        none
  | none =>
      some parentClause

/-- 原生 HO 项是否包含给定 typed 自由变量。 -/
partial def termContainsFreeVariable (sort : SimpleType BaseSort) (id : Nat) : Term → Bool
  | .var (.bvar _ _) => false
  | .var (.fvar freeSort freeId) => freeSort == sort && freeId == id
  | .app _ arguments => arguments.any (termContainsFreeVariable sort id)
  | .apply function argument =>
      termContainsFreeVariable sort id function ||
        termContainsFreeVariable sort id argument
  | .lam _ _ body => termContainsFreeVariable sort id body

/-- 原生 HO 原子是否包含给定 typed 自由变量。 -/
def atomContainsFreeVariable (sort : SimpleType BaseSort) (id : Nat) : Atom → Bool
  | .rel _ arguments => arguments.any (termContainsFreeVariable sort id)
  | .equal _ left right =>
      termContainsFreeVariable sort id left || termContainsFreeVariable sort id right

/-- 原生 HO 字句是否包含给定 typed 自由变量。 -/
def clauseContainsFreeVariable
    (sort : SimpleType BaseSort) (id : Nat) (clause : Clause) : Bool :=
  clause.literals.any fun literal => atomContainsFreeVariable sort id literal.atom

/-- 只保留实际作用到当前父字句的 typed substitution binding。 -/
def relevantSubstitution (parent : Clause)
    (substitution : CoreSyntax.Search.Substitution) : CoreSyntax.Search.Substitution :=
  substitution.filter fun binding =>
    clauseContainsFreeVariable (simpleType binding.key.sort) binding.key.id parent

/--
按当前父字句裁剪搜索 substitution；裁剪后为空时保留原父编号，否则追加独立 typed 节点。
-/
def pushRelevantSubstitutionFromSearch? (dag : DAG) (parentId : Nat)
    (parentInput? : Option CoreSyntax.Search.Clause)
    (substitution : CoreSyntax.Search.Substitution) : Option (DAG × Nat) := do
  let parent ← parentClause? dag parentId parentInput?
  let relevant := relevantSubstitution parent substitution
  if relevant.isEmpty then
    some (dag, parentId)
  else
    pushSubstitutionFromSearch? dag parentId parentInput? relevant

/-- 从两个已完成改名与 substitution 的真实父节点恢复 resolution 证据。 -/
def resolutionEvidence? (dag : DAG) (leftId rightId leftIndex rightIndex : Nat)
    (resultInput : CoreSyntax.Search.Clause) : Option ResolutionEvidence := do
  let leftClause ← parentClause? dag leftId none
  let rightClause ← parentClause? dag rightId none
  let leftLiteral ← leftClause.literals[leftIndex]?
  let rightLiteral ← rightClause.literals[rightIndex]?
  if rightLiteral.matchesAtom (!leftLiteral.polarity) leftLiteral.atom then
    let result ← clause? resultInput
    let evidence : ResolutionEvidence := {
      left := { id := leftId, clause := leftClause }
      right := { id := rightId, clause := rightClause }
      pivot := leftLiteral.atom
      leftPolarity := leftLiteral.polarity
    }
    if evidence.conclusion.eq result && evidence.check #[leftId, rightId] then
      some evidence
    else
      none
  else
    none

/-- 向原生 HO DAG 追加一个 resolution 节点。 -/
def pushResolution (dag : DAG) (evidence : ResolutionEvidence) : Option DAG := do
  let node ←
    derivedNode? dag #[evidence.left.id, evidence.right.id] (.resolution evidence)
  if node.check dag.problem &&
      dag.parentSnapshotChecked evidence.left &&
        dag.parentSnapshotChecked evidence.right then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/-- 消费搜索层 resolution witness，并显式追加改名、替换与 resolution 三段图边。 -/
def pushResolutionResource? (dag : DAG)
    (resource : ResourceTrace.ResolutionResource) : Option DAG := do
  let parents ←
    match resource.standardizeApart? with
    | some metadata =>
        pushStandardizeApartPair? dag resource.left resource.right metadata
    | none =>
        some { dag := dag, left := resource.left.id, right := resource.right.id }
  let leftInput? :=
    match resource.standardizeApart? with
    | some _ => none
    | none => resource.left.clause?
  let rightInput? :=
    match resource.standardizeApart? with
    | some _ => none
    | none => resource.right.clause?
  let (dag, leftId) ←
    pushRelevantSubstitutionFromSearch? parents.dag parents.left leftInput?
      resource.substitution
  let (dag, rightId) ←
    pushRelevantSubstitutionFromSearch? dag parents.right rightInput?
      resource.substitution
  let leftIndex ← resource.leftLiteralIndex?
  let rightIndex ← resource.rightLiteralIndex?
  let evidence ← resolutionEvidence? dag leftId rightId leftIndex rightIndex resource.result
  pushResolution dag evidence

/-- 从已完成 substitution 的真实父节点恢复 factoring 证据。 -/
def factoringEvidence? (dag : DAG) (parentId firstIndex secondIndex : Nat)
    (resultInput : CoreSyntax.Search.Clause) : Option FactoringEvidence := do
  if firstIndex == secondIndex then
    none
  let parentClause ← parentClause? dag parentId none
  let _ ← parentClause.literals[firstIndex]?
  let _ ← parentClause.literals[secondIndex]?
  let result ← clause? resultInput
  let evidence : FactoringEvidence := {
    parent := { id := parentId, clause := parentClause }
    conclusion := result
  }
  if evidence.check #[parentId] then
    some evidence
  else
    none

/-- 向原生 HO DAG 追加一个 factoring 节点。 -/
def pushFactoring (dag : DAG) (evidence : FactoringEvidence) : Option DAG := do
  let node ← derivedNode? dag #[evidence.parent.id] (.factoring evidence)
  if node.check dag.problem && dag.parentSnapshotChecked evidence.parent then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/-- factoring witness 的公共材料化主体；规则族分派由外层入口负责。 -/
private def pushFactoringResourceCore? (dag : DAG)
    (resource : ResourceTrace.UnaryResource) : Option DAG := do
  let firstIndex ← resource.literalIndex?
  let secondIndex ← resource.otherLiteralIndex?
  let (dag, parentId) ←
    pushRelevantSubstitutionFromSearch? dag resource.parent.id
      resource.parent.clause? resource.substitution
  let evidence ← factoringEvidence? dag parentId firstIndex secondIndex resource.result
  pushFactoring dag evidence

/-- 消费 ordinary/equality factoring witness，并把非空 substitution 放到独立前驱节点。 -/
def pushFactoringResource? (dag : DAG)
    (resource : ResourceTrace.UnaryResource) : Option DAG :=
  match resource.kind with
  | .ordinaryFactoring => pushFactoringResourceCore? dag resource
  | .equalityFactoring => pushFactoringResourceCore? dag resource
  | _ => none

/-- 从已完成 substitution 的真实父节点恢复 equality-resolution 证据。 -/
def equalityResolutionEvidence? (dag : DAG) (parentId literalIndex : Nat)
    (resultInput : CoreSyntax.Search.Clause) : Option EqualityResolutionEvidence := do
  let parentClause ← parentClause? dag parentId none
  let literal ← parentClause.literals[literalIndex]?
  match literal.polarity, literal.atom with
  | false, .equal sort left right =>
      if HODAGCertificate.StructuralEq.term left right then
        let result ← clause? resultInput
        let evidence : EqualityResolutionEvidence := {
          parent := { id := parentId, clause := parentClause }
          sort := sort
          left := left
          right := right
        }
        if evidence.conclusion.eq result && evidence.check #[parentId] then
          some evidence
        else
          none
      else
        none
  | _, _ =>
      none

/-- 向原生 HO DAG 追加一个 equality-resolution 节点。 -/
def pushEqualityResolution (dag : DAG)
    (evidence : EqualityResolutionEvidence) : Option DAG := do
  let node ←
    derivedNode? dag #[evidence.parent.id] (.equalityResolution evidence)
  if node.check dag.problem && dag.parentSnapshotChecked evidence.parent then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/-- 消费 equality-resolution witness，并把非空 substitution 放到独立前驱节点。 -/
def pushEqualityResolutionResource? (dag : DAG)
    (resource : ResourceTrace.UnaryResource) : Option DAG := do
  match resource.kind with
  | .equalityResolution =>
      let literalIndex ← resource.literalIndex?
      let (dag, parentId) ←
        pushRelevantSubstitutionFromSearch? dag resource.parent.id
          resource.parent.clause? resource.substitution
      let evidence ←
        equalityResolutionEvidence? dag parentId literalIndex resource.result
      pushEqualityResolution dag evidence
  | _ =>
      none

/-! ## Boolean Extensionality 材料化 -/

/--
从真实父节点与搜索层选中文字恢复 Boolean Extensionality 证据。

左右项必须都是 `bool`；归一化终点由 `betaEtaTrace?` 重新计算，搜索 result 只接受
与原生机械结论完全一致的子句。
-/
def booleanExtensionalityEvidence? (dag : DAG) (parentId literalIndex : Nat)
    (resultInput : CoreSyntax.Search.Clause) :
    Option BooleanExtensionalityEvidence := do
  let parentClause ← parentClause? dag parentId none
  let parentLiteral ← parentClause.literals[literalIndex]?
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
      let result ← clause? resultInput
      if evidence.conclusion.eq result && evidence.check #[parentId] then
        some evidence
      else
        none
  | _ =>
    none

/-- 向原生 HO DAG 追加一个已完全复核的 Boolean Extensionality 节点。 -/
def pushBooleanExtensionality (dag : DAG)
    (evidence : BooleanExtensionalityEvidence) : Option DAG := do
  let node ←
    derivedNode? dag #[evidence.parent.id] (.booleanExtensionality evidence)
  if node.check dag.problem && dag.parentSnapshotChecked evidence.parent then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/--
消费搜索 journal 的 Boolean Extensionality unary witness。

非空 substitution 先进入独立 typed substitution 节点；随后从替换后的搜索父字句
重建左右 βη 轨迹。
-/
def pushBooleanExtensionalityResource? (dag : DAG)
    (resource : ResourceTrace.UnaryResource) : Option DAG := do
  match resource.kind, resource.literalIndex?, resource.otherLiteralIndex? with
  | .booleanExtensionality, some literalIndex, none =>
      let (dag, parentId) ←
        pushRelevantSubstitutionFromSearch? dag resource.parent.id
          resource.parent.clause? resource.substitution
      let evidence ←
        booleanExtensionalityEvidence? dag parentId literalIndex resource.result
      pushBooleanExtensionality dag evidence
  | _, _, _ =>
      none

/-! ## Demodulation / Superposition 与原生 HO 项上下文材料化 -/

/-- 安全拆分列表，返回目标前缀、目标元素与后缀。 -/
private def splitAt? {α : Type} : List α → Nat → Option (List α × α × List α)
  | [], _ => none
  | head :: rest, 0 => some ([], head, rest)
  | head :: rest, index + 1 => do
      let (before, value, suffix) ← splitAt? rest index
      some (head :: before, value, suffix)

/--
按搜索路径恢复原生 HO 一孔项上下文及洞中原项。

`app` 的路径编号选择普通参数；`apply` 的 `0/1` 分别选择函数位与实参位；
`lam` 只接受 `0` 进入 body。
-/
partial def termContextAt? (input : CoreSyntax.Search.Term)
    (path : ResourceTrace.TermPath) : Option (TermContext × CoreSyntax.Search.Term) := do
  match path with
  | [] =>
      some (.hole, input)
  | index :: rest =>
      match input with
      | .app symbol arguments =>
          let (before, selected, suffix) ← splitAt? arguments index
          let (context, hole) ← termContextAt? selected rest
          some (.app symbol (before.map term) context (suffix.map term), hole)
      | .apply function argument =>
          match index with
          | 0 =>
              let (context, hole) ← termContextAt? function rest
              some (.applyFunction context (term argument), hole)
          | 1 =>
              let (context, hole) ← termContextAt? argument rest
              some (.applyArgument (term function) context, hole)
          | _ =>
              none
      | .lam domain codomain body =>
          match index with
          | 0 =>
              let (context, hole) ← termContextAt? body rest
              some (.lam (simpleType domain) (simpleType codomain) context, hole)
          | _ =>
              none
      | _ =>
          none

/-- 从搜索 literal 与目标位置恢复原生 HO 原子上下文。 -/
def atomContextAt? (targetLiteral : CoreSyntax.Search.Literal)
    (position : ResourceTrace.PositionedTerm) :
    Option (AtomContext × Term × Bool) := do
  match targetLiteral.predicate with
  | .equal =>
      let leftSort ← targetLiteral.left.inferSort?
      let rightSort ← targetLiteral.right.inferSort?
      if leftSort != rightSort then
        none
      match position.side with
      | .left =>
          let (context, hole) ← termContextAt? targetLiteral.left position.path
          some
            (.equalLeft (simpleType leftSort) context (term targetLiteral.right),
              term hole, targetLiteral.positive)
      | .right =>
          let (context, hole) ← termContextAt? targetLiteral.right position.path
          some
            (.equalRight (simpleType leftSort) (term targetLiteral.left) context,
              term hole, targetLiteral.positive)
  | .member =>
      match position.side with
      | .left =>
          let (context, hole) ← termContextAt? targetLiteral.left position.path
          some (.rel .member [] context [term targetLiteral.right],
            term hole, targetLiteral.positive)
      | .right =>
          let (context, hole) ← termContextAt? targetLiteral.right position.path
          some (.rel .member [term targetLiteral.left] context [],
            term hole, targetLiteral.positive)
  | .boolHolds =>
      match position.side with
      | .left =>
          let (context, hole) ← termContextAt? targetLiteral.left position.path
          some (.rel .boolHolds [] context [], term hole, targetLiteral.positive)
      | .right =>
          none
  | .definition id arity =>
      match position.side with
      | .left =>
          let (context, hole) ← termContextAt? targetLiteral.left position.path
          some (.rel (.definition id arity) [] context [],
            term hole, targetLiteral.positive)
      | .right =>
          none
  | .predicate symbol =>
      match position.side, position.path with
      | .left, index :: rest =>
          let arguments ← projectedPredicateArguments? symbol targetLiteral.left
          let (before, selected, suffix) ← splitAt? arguments index
          let (context, hole) ← termContextAt? selected rest
          some (.rel (.predicate symbol) (before.map term) context (suffix.map term),
            term hole, targetLiteral.positive)
      | .left, [] =>
          none
      | .right, _ =>
          none

/-- 从搜索资源恢复当前 HO 证书支持的重写规则类别。 -/
def rewriteKind? (resource : ResourceTrace.RewriteResource) :
    Option HODAGCertificate.RewriteKind :=
  if resource.contextual then
    none
  else
    match resource.kind with
    | .demodulation =>
        some .demodulation
    | .positiveSuperposition =>
        if resource.targetPolarity? == some .positive then
          some .positiveSuperposition
        else
          none
    | .negativeSuperposition =>
        if resource.targetPolarity? == some .negative then
          some .negativeSuperposition
        else
          none
    | .extensionalParamodulation =>
        if resource.targetPolarity? == some .positive then
          some .extensionalParamodulation
        else
          none
    | _ =>
        none

/-- 从已完成改名与 typed substitution 的真实父节点恢复公共重写证据。 -/
def rewriteEvidence? (dag : DAG) (kind : HODAGCertificate.RewriteKind)
    (equalityId targetId : Nat)
    (resource : ResourceTrace.RewriteResource) : Option RewriteEvidence := do
  let equalityClause ← parentClause? dag equalityId none
  let targetClause ← parentClause? dag targetId none
  let rawTargetBase ←
    match resource.standardizeApart? with
    | some metadata => some metadata.right.renamed
    | none => resource.target.clause?
  let rawTarget :=
    CoreSyntax.Search.Substitution.applyClause resource.substitution rawTargetBase
  let rawTargetLiteral ← rawTarget[resource.targetLiteral]?
  let targetLiteral ← targetClause.literals[resource.targetLiteral]?
  let materializedTargetLiteral ← literal? rawTargetLiteral
  if !targetLiteral.eq materializedTargetLiteral then
    none
  let (context, hole, polarity) ←
    atomContextAt? rawTargetLiteral resource.targetPosition
  let expectedHole :=
    term
      (CoreSyntax.Search.Substitution.applyTerm resource.substitution
        resource.targetPosition.term)
  if !HODAGCertificate.StructuralEq.term expectedHole hole then
    none
  let lhs :=
    term
      (CoreSyntax.Search.Substitution.applyTerm resource.substitution
        resource.orientedLhs)
  let rhs :=
    term
      (CoreSyntax.Search.Substitution.applyTerm resource.substitution
        resource.orientedRhs)
  if !HODAGCertificate.StructuralEq.term hole lhs then
    none
  let sort ← lhs.inferSort?
  if rhs.inferSort? != some sort then
    none
  let equalityLiteral ← equalityClause.literals[resource.equalityLiteral]?
  let equalityReversed ←
    if equalityLiteral.matchesAtom true (.equal sort lhs rhs) then
      some false
    else if equalityLiteral.matchesAtom true (.equal sort rhs lhs) then
      some true
    else
      none
  let result ← clause? resource.result
  let evidence : RewriteEvidence := {
    equality := { id := equalityId, clause := equalityClause }
    target := { id := targetId, clause := targetClause }
    context := context
    sort := sort
    lhs := lhs
    rhs := rhs
    equalityReversed := equalityReversed
    targetPolarity := polarity
  }
  if evidence.conclusion.eq result &&
      evidence.check kind #[equalityId, targetId] then
    some evidence
  else
    none

/-- 向原生 HO DAG 追加一个已完全复核的上下文重写节点。 -/
def pushRewrite (dag : DAG) (kind : HODAGCertificate.RewriteKind)
    (evidence : RewriteEvidence) : Option DAG := do
  let payload : Payload :=
    match kind with
    | .demodulation => .demodulation evidence
    | .positiveSuperposition => .positiveSuperposition evidence
    | .negativeSuperposition => .negativeSuperposition evidence
    | .extensionalParamodulation => .extensionalParamodulation evidence
  let node ←
    derivedNode? dag #[evidence.equality.id, evidence.target.id] payload
  if node.check dag.problem &&
      dag.parentSnapshotChecked evidence.equality &&
        dag.parentSnapshotChecked evidence.target then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/--
消费搜索层 demodulation/superposition witness，并显式追加 standardize-apart、
typed substitution 与最终上下文重写节点。
-/
def pushRewriteResource? (dag : DAG)
    (resource : ResourceTrace.RewriteResource) : Option DAG := do
  let kind ← rewriteKind? resource
  let parents ←
    match resource.standardizeApart? with
    | some metadata =>
        pushStandardizeApartPair? dag resource.equality resource.target metadata
    | none =>
        some {
          dag := dag
          left := resource.equality.id
          right := resource.target.id
        }
  let equalityInput? :=
    match resource.standardizeApart? with
    | some _ => none
    | none => resource.equality.clause?
  let targetInput? :=
    match resource.standardizeApart? with
    | some _ => none
    | none => resource.target.clause?
  let (dag, equalityId) ←
    pushRelevantSubstitutionFromSearch? parents.dag parents.left equalityInput?
      resource.substitution
  let (dag, targetId) ←
    pushRelevantSubstitutionFromSearch? dag parents.right targetInput?
      resource.substitution
  let evidence ← rewriteEvidence? dag kind equalityId targetId resource
  pushRewrite dag kind evidence

/-- 当前已支持消元与上下文重写规则的 ResourceTrace 统一材料化入口。 -/
def pushEliminationWitness? (dag : DAG)
    (witness : ResourceTrace.LocalStepWitness) : Option DAG := do
  match witness with
  | .resolution resource =>
      pushResolutionResource? dag resource
  | .unary resource =>
      match resource.kind with
      | .ordinaryFactoring =>
          pushFactoringResource? dag resource
      | .equalityFactoring =>
          pushFactoringResource? dag resource
      | .equalityResolution =>
          pushEqualityResolutionResource? dag resource
      | .booleanExtensionality =>
          pushBooleanExtensionalityResource? dag resource
      | _ =>
          none
  | .rewrite resource =>
      pushRewriteResource? dag resource

/-! ## Argument Congruence 材料化 -/

/--
从真实父节点和搜索 result 中恢复一参数 Argument Congruence 证据。

搜索 result 只用于提取显式实参；最终结果仍由 HO evidence 重新计算并进行结构比较。
-/
def argumentCongruenceEvidence? (dag : DAG) (parentId literalIndex : Nat)
    (parentInput? : Option CoreSyntax.Search.Clause)
    (resultInput : CoreSyntax.Search.Clause) :
    Option ArgumentCongruenceEvidence := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  match parentInput? with
  | some parentInput =>
      let materializedParent ← clause? parentInput
      if materializedParent.eq parentClause then
        pure ()
      else
        none
  | none =>
      pure ()
  let resultClause ← clause? resultInput
  let parentLiteral ← parentClause.literals[literalIndex]?
  let resultLiteral ← resultClause.literals[literalIndex]?
  match parentLiteral.polarity, parentLiteral.atom,
      resultLiteral.polarity, resultLiteral.atom with
  | true, .equal (.arrow domain codomain) left right,
      true, .equal resultSort (.apply resultLeft argument)
        (.apply resultRight argument') =>
      if decide (resultSort = codomain) &&
          HODAGCertificate.StructuralEq.term left resultLeft &&
            HODAGCertificate.StructuralEq.term right resultRight &&
              HODAGCertificate.StructuralEq.term argument argument' then
        let evidence : ArgumentCongruenceEvidence := {
          parent := { id := parentId, clause := parentClause }
          domain := domain
          codomain := codomain
          left := left
          right := right
          argument := argument
        }
        if evidence.conclusion.eq resultClause && evidence.check #[parentId] then
          some evidence
        else
          none
      else
        none
  | _, _, _, _ =>
      none

/-- 向原生 HO DAG 追加一个已恢复的 Argument Congruence 节点。 -/
def pushArgumentCongruence (dag : DAG)
    (evidence : ArgumentCongruenceEvidence) : Option DAG := do
  let node ←
    derivedNode? dag #[evidence.parent.id] (.argumentCongruence evidence)
  if node.check dag.problem && dag.parentSnapshotChecked evidence.parent then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/--
消费旧搜索 journal 的 `argumentCongruence` unary witness。

非空 substitution 先物化为独立 typed substitution 节点，再让 congruence 引用新父节点。
-/
def pushArgumentCongruenceResource? (dag : DAG)
    (resource : ResourceTrace.UnaryResource) : Option DAG := do
  match resource.kind with
  | .argumentCongruence =>
      match resource.literalIndex?, resource.otherLiteralIndex? with
      | some literalIndex, none =>
          if resource.substitution.isEmpty then
            let evidence ← argumentCongruenceEvidence? dag resource.parent.id literalIndex
              resource.parent.clause? resource.result
            pushArgumentCongruence dag evidence
          else
            let (dag, parentId) ← pushSubstitutionFromSearch? dag resource.parent.id
              resource.parent.clause? resource.substitution
            let evidence ← argumentCongruenceEvidence? dag parentId literalIndex
              none resource.result
            pushArgumentCongruence dag evidence
      | _, _ =>
          none
  | _ =>
      none

/-! ## Function Extensionality 材料化 -/

/--
从搜索结果恢复带显式 `diff` 符号的 Function Extensionality 证据。

结果两侧必须应用同一个见证项，且该项必须精确为 `witnessSymbol(left, right)`；
任意自由变量或与父函数无关的参数都不会被证书层接受。
-/
def functionExtensionalityEvidence? (dag : DAG) (parentId literalIndex : Nat)
    (parentInput? : Option CoreSyntax.Search.Clause)
    (resultInput : CoreSyntax.Search.Clause) :
    Option FunctionExtensionalityEvidence := do
  let parentNode ← dag.node? parentId
  let parentClause ← parentNode.conclusion? dag.problem
  match parentInput? with
  | some parentInput =>
      let materializedParent ← clause? parentInput
      if materializedParent.eq parentClause then
        pure ()
      else
        none
  | none =>
      pure ()
  let resultClause ← clause? resultInput
  let parentLiteral ← parentClause.literals[literalIndex]?
  let resultLiteral ← resultClause.literals[literalIndex]?
  match parentLiteral.polarity, parentLiteral.atom,
      resultLiteral.polarity, resultLiteral.atom with
  | false, .equal (.arrow domain codomain) left right,
      false, .equal resultSort (.apply resultLeft witness)
        (.apply resultRight witness') =>
      if decide (resultSort = codomain) &&
          HODAGCertificate.StructuralEq.term left resultLeft &&
            HODAGCertificate.StructuralEq.term right resultRight &&
              HODAGCertificate.StructuralEq.term witness witness' then
        match witness with
        | .app witnessSymbol [witnessLeft, witnessRight] =>
            if HODAGCertificate.StructuralEq.term left witnessLeft &&
                HODAGCertificate.StructuralEq.term right witnessRight then
              let evidence : FunctionExtensionalityEvidence := {
                parent := { id := parentId, clause := parentClause }
                domain := domain
                codomain := codomain
                left := left
                right := right
                witnessSymbol := witnessSymbol
              }
              if evidence.conclusion.eq resultClause && evidence.check #[parentId] then
                some evidence
              else
                none
            else
              none
        | _ =>
            none
      else
        none
  | _, _, _, _ =>
      none

/-- 向原生 HO DAG 追加一个已恢复的 Function Extensionality 节点。 -/
def pushFunctionExtensionality (dag : DAG)
    (evidence : FunctionExtensionalityEvidence) : Option DAG := do
  let node ←
    derivedNode? dag #[evidence.parent.id] (.functionExtensionality evidence)
  if node.check dag.problem && dag.parentSnapshotChecked evidence.parent then
    some { dag with nodes := dag.nodes.push node }
  else
    none

/--
消费旧搜索 journal 的 `functionExtensionality` unary witness。

非空 substitution 先物化为独立 typed substitution 节点，再检查 canonical `diff` 规则。
-/
def pushFunctionExtensionalityResource? (dag : DAG)
    (resource : ResourceTrace.UnaryResource) : Option DAG := do
  match resource.kind with
  | .functionExtensionality =>
      match resource.literalIndex?, resource.otherLiteralIndex? with
      | some literalIndex, none =>
          if resource.substitution.isEmpty then
            let evidence ← functionExtensionalityEvidence? dag resource.parent.id literalIndex
              resource.parent.clause? resource.result
            pushFunctionExtensionality dag evidence
          else
            let (dag, parentId) ← pushSubstitutionFromSearch? dag resource.parent.id
              resource.parent.clause? resource.substitution
            let evidence ← functionExtensionalityEvidence? dag parentId literalIndex
              none resource.result
            pushFunctionExtensionality dag evidence
      | _, _ =>
          none
  | _ =>
      none

/--
统一消费搜索器产生的原生高阶资源。

β/η 直接生成自包含公理节点；其他资源通过现有专用 checker 材料化，搜索层不能绕过
typed substitution、父快照或规则结果复算。
-/
def pushHigherOrderResource? (dag : DAG)
    (resource : ResourceTrace.HigherOrderResource) : Option DAG := do
  match resource with
  | .beta redex =>
      pushBeta? dag redex
  | .eta redex =>
      pushEta? dag redex
  | .local witness =>
      match witness with
      | .unary unary =>
          match unary.kind with
          | .argumentCongruence =>
              pushArgumentCongruenceResource? dag unary
          | .functionExtensionality =>
              pushFunctionExtensionalityResource? dag unary
          | _ =>
              pushEliminationWitness? dag witness
      | _ =>
          pushEliminationWitness? dag witness

/-! ## AVATAR theory conflict 与 residual CDCL 材料化 -/

/-- 在 HO atom map 中查找结构相同原子的编号。 -/
private def atomIndexList? (needle : Atom) :
    List Atom → Nat → Option Nat
  | [], _ => none
  | atom :: rest, index =>
      if HODAGCertificate.Atom.eq needle atom then
        some index
      else
        atomIndexList? needle rest (index + 1)

/-- 复用已有 HO atom 编号，或在尾部登记新原子。 -/
private def internAtom (atoms : Array Atom) (atom : Atom) : Nat × Array Atom :=
  match atomIndexList? atom atoms.toList 0 with
  | some index => (index, atoms)
  | none => (atoms.size, atoms.push atom)

/-- 命题化一个真实 HO 字句，并返回可回放的逐文字链接。 -/
def propLiteralLinks (atoms : Array Atom) (clause : Clause) :
    Array PropLiteralLink × Array Atom := Id.run do
  let mut atoms := atoms
  let mut links : Array PropLiteralLink := #[]
  for literal in clause.literals do
    let (var, atoms') := internAtom atoms literal.atom
    atoms := atoms'
    links := links.push {
      prop := { var := var, positive := literal.polarity }
      object := literal
    }
  return (links, atoms)

/-- residual 父边按节点编号去重。 -/
private def pushParentUnique (parents : Array Nat) (parent : Nat) : Array Nat :=
  if parents.contains parent then parents else parents.push parent

/-- 把一个 guarded empty HO 节点显式提升为 theory conflict 节点。 -/
def pushTheoryConflict? (dag : DAG) (conflictId : Nat) : Option (DAG × Nat) := do
  let conflictNode ← dag.node? conflictId
  let conflictClause ← conflictNode.conclusion? dag.problem
  if !conflictNode.theoryConflict dag.problem then
    none
  else
    match conflictNode.payload with
    | .theoryConflict _ =>
        some (dag, conflictId)
    | _ =>
        let payload : TheoryConflictPayload := {
          conflict := { id := conflictId, clause := conflictClause }
        }
        let node ← derivedNode? dag #[conflictId] (.theoryConflict payload)
        if node.check dag.problem &&
            dag.parentSnapshotChecked payload.conflict &&
              dag.localNodeGuardsOk node then
          let newId := node.id
          some ({ dag with nodes := dag.nodes.push node }, newId)
        else
          none

/-- 从显式 theory conflict 物化命题 learned clause `¬Γ`。 -/
def pushPropositionalLearnedClause? (dag : DAG)
    (conflictId : Nat) : Option (DAG × Nat) := do
  let conflictNode ← dag.node? conflictId
  match conflictNode.payload with
  | .theoryConflict _ =>
      let payload : PropositionalLearnedClausePayload := {
        conflict := conflictId
        learned := HODAGCertificate.learnedClauseOfGuards conflictNode.guards
      }
      let node : Node := {
        id := dag.nodes.size
        parents := #[conflictId]
        guards := conflictNode.guards
        payload := .propositionalLearnedClause payload
      }
      if node.check dag.problem && dag.localNodeGuardsOk node then
        let newId := node.id
        some ({ dag with nodes := dag.nodes.push node }, newId)
      else
        none
  | _ =>
      none

/-- residual CDCL 自动材料化的中间状态。 -/
private structure ResidualBuildState where
  dag : DAG
  atomMap : Array Atom := #[]
  parents : Array Nat := #[]
  justifications : Array PropInitialJustification := #[]

/-- 普通无 guard 父节点生成 parent initial。 -/
private def addParentInitial? (state : ResidualBuildState)
    (sourceId : Nat) (sourceNode : Node) (sourceClause : Clause)
    (initial : PropResolution.InitialClause) : Option ResidualBuildState := do
  let (links, atomMap) := propLiteralLinks state.atomMap sourceClause
  let link : PropParentClauseLink := {
    parent := { id := sourceId, clause := sourceClause }
    literalLinks := links
  }
  if !PropResolution.clauseEq initial.clause link.encodedClause then
    none
  else if !sourceNode.unguarded then
    none
  else
    some {
      state with
      atomMap := atomMap
      parents := pushParentUnique state.parents sourceId
      justifications := state.justifications.push (.parentClause link)
    }

/-- guarded 非空父节点生成 activation initial。 -/
private def addGuardActivationInitial? (state : ResidualBuildState)
    (sourceId : Nat) (sourceNode : Node) (sourceClause : Clause)
    (initial : PropResolution.InitialClause) : Option ResidualBuildState := do
  let (links, atomMap) := propLiteralLinks state.atomMap sourceClause
  let link : PropGuardActivationLink := {
    parent := { id := sourceId, clause := sourceClause }
    guards := HODAGCertificate.canonicalGuards sourceNode.guards
    literalLinks := links
  }
  if sourceNode.unguarded ||
      !PropResolution.clauseEq initial.clause link.encodedClause then
    none
  else
    some {
      state with
      atomMap := atomMap
      parents := pushParentUnique state.parents sourceId
      justifications := state.justifications.push (.guardActivationClause link)
    }

/-- AVATAR split 节点生成 selector skeleton initial。 -/
private def addAvatarSkeletonInitial? (state : ResidualBuildState)
    (sourceId : Nat) (sourceNode : Node)
    (initial : PropResolution.InitialClause) : Option ResidualBuildState := do
  let skeleton ←
    match sourceNode.payload with
    | .avatarSplit payload => some (PropResolution.canonicalClause payload.selectors)
    | _ => none
  let link : PropAvatarSkeletonLink := {
    parent := sourceId
    skeleton := skeleton
  }
  if !PropResolution.clauseEq initial.clause skeleton then
    none
  else
    some {
      state with
      parents := pushParentUnique state.parents sourceId
      justifications := state.justifications.push (.avatarSkeleton link)
    }

/-- guarded empty 父节点先产生 conflict/learned 节点，再生成 learned initial。 -/
private def addLearnedInitial? (state : ResidualBuildState)
    (sourceId : Nat) (initial : PropResolution.InitialClause) :
    Option ResidualBuildState := do
  let (dag, conflictId) ← pushTheoryConflict? state.dag sourceId
  let (dag, learnedId) ← pushPropositionalLearnedClause? dag conflictId
  let learnedNode ← dag.node? learnedId
  let learned ←
    match learnedNode.payload with
    | .propositionalLearnedClause payload => some payload.learned
    | _ => none
  let link : PropLearnedClauseLink := {
    parent := learnedId
    guards := learnedNode.guards
    clause := learned
  }
  if !PropResolution.clauseEq initial.clause learned then
    none
  else
    some {
      state with
      dag := dag
      parents := pushParentUnique state.parents learnedId
      justifications := state.justifications.push (.propLearnedClause link)
    }

/-- 已物化 learned 节点可直接作为 residual initial 来源。 -/
private def addExistingLearnedInitial? (state : ResidualBuildState)
    (learnedId : Nat) (learnedNode : Node)
    (learned : PropResolution.Clause)
    (initial : PropResolution.InitialClause) : Option ResidualBuildState := do
  let link : PropLearnedClauseLink := {
    parent := learnedId
    guards := learnedNode.guards
    clause := learned
  }
  if !PropResolution.clauseEq initial.clause learned then
    none
  else
    some {
      state with
      parents := pushParentUnique state.parents learnedId
      justifications := state.justifications.push (.propLearnedClause link)
    }

/--
按 checked certificate 的 initial 顺序，把 HO-DAG source 节点自动分类为三类 residual 输入。

无 guard 节点生成普通 parent initial；guarded 非空节点生成 activation initial；
guarded empty 节点显式生成 theory conflict 与 learned-clause artifact。
-/
def residualCdclFromSources? (dag : DAG) (sourceIds : Array Nat)
    (certificate : PropResolution.CheckedUnsatCertificate) : Option DAG := do
  if sourceIds.size != certificate.initialClauses.size then
    none
  let mut state : ResidualBuildState := { dag := dag }
  for h : slot in [:sourceIds.size] do
    let sourceId := sourceIds[slot]
    let sourceNode ← state.dag.node? sourceId
    let sourceClause ← sourceNode.conclusion? state.dag.problem
    let initial ← certificate.initialClauses[slot]?
    match sourceNode.payload with
    | .propositionalLearnedClause payload =>
        state ←
          addExistingLearnedInitial? state sourceId sourceNode payload.learned initial
    | .avatarSplit _ =>
        state ← addAvatarSkeletonInitial? state sourceId sourceNode initial
    | _ =>
        if sourceNode.theoryConflict state.dag.problem then
          state ← addLearnedInitial? state sourceId initial
        else if sourceNode.unguarded then
          state ← addParentInitial? state sourceId sourceNode sourceClause initial
        else
          state ←
            addGuardActivationInitial? state sourceId sourceNode sourceClause initial
  if state.parents.isEmpty then
    none
  else
    let payload :=
      HODAGCertificate.PropositionalClosurePayload.ofCheckedUnsat certificate
        state.atomMap state.justifications
    let node : Node := {
      id := state.dag.nodes.size
      parents := state.parents
      guards := #[]
      payload := .residualCdcl payload
    }
    let dag : DAG := {
      state.dag with
      root := node.id
      nodes := state.dag.nodes.push node
    }
    if dag.check then some dag else none

/-- 自动材料化 residual CDCL，并返回通过整图 checker 的 HO-DAG。 -/
def checkedResidualCdclFromSources? (dag : DAG) (sourceIds : Array Nat)
    (certificate : PropResolution.CheckedUnsatCertificate) : Option CheckedDAG := do
  let dag ← residualCdclFromSources? dag sourceIds certificate
  HODAGCertificate.CheckedDAG.mk? dag

end HOSearchMaterialization
end Automation
end YesMetaZFC
