import Lean

/-!
# 宿主表达式的保守总重化

本模块把普通 Lean 命题重化为多排序、局部无名的宿主快照。可识别的一阶应用、
等式、逻辑联结与对象 binder 保留结构；lambda、依赖证明 binder、捕获对象 binder
等暂未覆盖片段退化为带类型 opaque 节点，而不是拒绝整个目标。

快照中的 `Expr` 只允许在单次 Meta 事务内使用。进入表中的 binder 局部变量会先抽象
回 de Bruijn 变量，因此快照不会保留由重化过程临时创建的 FVar。
-/

namespace YesMetaZFC
namespace Automation
namespace HostReification

open Lean Meta

abbrev SortId := Nat
abbrev SymbolId := Nat
abbrev OpaqueTermId := Nat
abbrev OpaqueFormulaId := Nat

/-- 多排序宿主项。 -/
inductive Term where
  | bvar (sort : SortId) (index : Nat)
  | app (sort : SortId) (symbol : SymbolId) (arguments : Array Term)
  | opaque (sort : SortId) (entry : OpaqueTermId)
deriving Repr, Inhabited

namespace Term

/-- 项节点携带的结果排序。 -/
def sort : Term → SortId
  | .bvar sort _ => sort
  | .app sort _ _ => sort
  | .opaque sort _ => sort

end Term

/-- 多排序宿主命题。 -/
inductive Formula where
  | falsum
  | truth
  | atom (symbol : SymbolId) (arguments : Array Term)
  | opaque (entry : OpaqueFormulaId)
  | equal (sort : SortId) (left right : Term)
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | imp (left right : Formula)
  | iff (left right : Formula)
  | forallE (sort : SortId) (binderInfo : BinderInfo) (body : Formula)
  | existsE (sort : SortId) (body : Formula)
deriving Repr, Inhabited

/-- 排序表达式按其出现的 binder 深度保存。 -/
structure SortEntry where
  expression : Expr
  binderDepth : Nat

/--
宿主函数或谓词头。

`outputSort? = none` 表示谓词；否则表示函数及其结果排序。
-/
structure Symbol where
  head : Expr
  inputSorts : Array SortId
  outputSort? : Option SortId
  binderDepth : Nat

/-- 无法继续结构化的宿主项。 -/
structure OpaqueTerm where
  expression : Expr
  type : Expr
  sort : SortId
  binderDepth : Nat

/-- 无法继续结构化的宿主命题。 -/
structure OpaqueFormula where
  expression : Expr
  binderDepth : Nat

/-- 一次总重化的审计计数。 -/
structure Stats where
  nodes : Nat := 0
  termNodes : Nat := 0
  formulaNodes : Nat := 0
  structuralApplications : Nat := 0
  binders : Nat := 0
  opaqueTerms : Nat := 0
  opaqueFormulas : Nat := 0
  wholeFormulaFallbacks : Nat := 0
  wholeFormulaFallbackReason? : Option String := none
deriving Repr, Inhabited

/--
事务内 typed raw 快照。

表中的表达式可以引用调用方已有的局部常量，但不得跨目标、分支或 tactic 调用缓存。
-/
structure Snapshot where
  source : Expr
  root : Formula
  sorts : Array SortEntry := #[]
  symbols : Array Symbol := #[]
  opaqueTerms : Array OpaqueTerm := #[]
  opaqueFormulas : Array OpaqueFormula := #[]
  stats : Stats := {}

private structure ReifyState where
  sorts : Array SortEntry := #[]
  symbols : Array Symbol := #[]
  opaqueTerms : Array OpaqueTerm := #[]
  opaqueFormulas : Array OpaqueFormula := #[]
  bound : Array (FVarId × SortId) := #[]
  stats : Stats := {}

private abbrev ReifyM := StateRefT ReifyState MetaM

private def stripLambdas : Nat → Expr → Expr
  | 0, expression => expression
  | depth + 1, .lam _ _ body _ => stripLambdas depth body
  | _, expression => expression

/--
把当前重化过程创建的 binder FVar 抽象回 loose de Bruijn 变量。

调用方已有的局部 FVar 不在 `bound` 中，因此仍原样保留。
-/
private def closeCurrentBinders (expression : Expr) : ReifyM Expr := do
  let state ← get
  if state.bound.isEmpty then
    return expression
  let binders := state.bound.map fun entry => mkFVar entry.1
  let closed ← mkLambdaFVars binders expression
  return stripLambdas binders.size closed

private def modifyStats (update : Stats → Stats) : ReifyM Unit :=
  modify fun state => { state with stats := update state.stats }

private def recordTerm : ReifyM Unit :=
  modifyStats fun stats => {
    stats with
    nodes := stats.nodes + 1
    termNodes := stats.termNodes + 1
  }

private def recordFormula : ReifyM Unit :=
  modifyStats fun stats => {
    stats with
    nodes := stats.nodes + 1
    formulaNodes := stats.formulaNodes + 1
  }

private def internSort (type : Expr) : ReifyM SortId := do
  let expression ← closeCurrentBinders type
  let state ← get
  let binderDepth := state.bound.size
  if let some index := state.sorts.findIdx? fun entry =>
      entry.binderDepth == binderDepth && entry.expression == expression then
    return index
  let id := state.sorts.size
  set {
    state with
    sorts := state.sorts.push { expression, binderDepth }
  }
  return id

private def internSymbol (head : Expr) (inputSorts : Array SortId)
    (outputSort? : Option SortId) : ReifyM SymbolId := do
  let head ← closeCurrentBinders head
  let state ← get
  let binderDepth := state.bound.size
  if let some index := state.symbols.findIdx? fun entry =>
      entry.binderDepth == binderDepth &&
        entry.head == head &&
          entry.inputSorts == inputSorts &&
            entry.outputSort? == outputSort? then
    return index
  let id := state.symbols.size
  set {
    state with
    symbols := state.symbols.push {
      head
      inputSorts
      outputSort?
      binderDepth
    }
  }
  return id

private def internOpaqueTerm (expression type : Expr)
    (sort : SortId) : ReifyM OpaqueTermId := do
  let expression ← closeCurrentBinders expression
  let type ← closeCurrentBinders type
  let state ← get
  let id := state.opaqueTerms.size
  set {
    state with
    opaqueTerms := state.opaqueTerms.push {
      expression
      type
      sort
      binderDepth := state.bound.size
    }
  }
  modifyStats fun stats => {
    stats with opaqueTerms := stats.opaqueTerms + 1
  }
  return id

private def internOpaqueFormula
    (expression : Expr) : ReifyM OpaqueFormulaId := do
  let expression ← closeCurrentBinders expression
  let state ← get
  let id := state.opaqueFormulas.size
  set {
    state with
    opaqueFormulas := state.opaqueFormulas.push {
      expression
      binderDepth := state.bound.size
    }
  }
  modifyStats fun stats => {
    stats with opaqueFormulas := stats.opaqueFormulas + 1
  }
  return id

private def boundVariable? (fvarId : FVarId) :
    ReifyM (Option (SortId × Nat)) := do
  let state ← get
  let some position := state.bound.findIdx? fun entry => entry.1 == fvarId
    | return none
  return some (state.bound[position]!.2, state.bound.size - position - 1)

private def capturesCurrentBinder (expression : Expr) : ReifyM Bool := do
  let state ← get
  return state.bound.any fun entry => expression.containsFVar entry.1

private def structuralHead?
    (expression : Expr) : ReifyM (Option Expr) := do
  let head := expression.getAppFn
  match head with
  | .const .. =>
      if ← capturesCurrentBinder head then
        return none
      else
        return some head
  | .fvar fvarId =>
      if (← boundVariable? fvarId).isSome ||
          (← capturesCurrentBinder head) then
        return none
      else
        return some head
  | _ =>
      return none

private def withObjectBinder {α : Type}
    (name : Name) (binderInfo : BinderInfo) (domain : Expr) (sort : SortId)
    (action : Expr → ReifyM α) : ReifyM α := do
  let previousBound := (← get).bound
  withLocalDecl name binderInfo domain fun binder => do
    modify fun state => {
      state with bound := state.bound.push (binder.fvarId!, sort)
    }
    let result ← action binder
    modify fun state => { state with bound := previousBound }
    return result

mutual

  private partial def reifyTerm (expression : Expr) : ReifyM Term := do
    recordTerm
    let expression ← instantiateMVars expression
    let expression := expression.consumeMData
    let type ← instantiateMVars (← inferType expression)
    let sort ← internSort type
    match expression with
    | .fvar fvarId =>
        if let some (boundSort, index) ← boundVariable? fvarId then
          return .bvar boundSort index
        let some head ← structuralHead? expression
          | return .opaque sort
              (← internOpaqueTerm expression type sort)
        let symbol ← internSymbol head #[] (some sort)
        modifyStats fun stats => {
          stats with
          structuralApplications := stats.structuralApplications + 1
        }
        return .app sort symbol #[]
    | .letE _ _ value body _ =>
        reifyTerm (body.instantiate1 value)
    | _ =>
        let some head ← structuralHead? expression
          | return .opaque sort
              (← internOpaqueTerm expression type sort)
        let arguments ← expression.getAppArgs.mapM reifyTerm
        let inputSorts := arguments.map Term.sort
        let symbol ← internSymbol head inputSorts (some sort)
        modifyStats fun stats => {
          stats with
          structuralApplications := stats.structuralApplications + 1
        }
        return .app sort symbol arguments

  private partial def reifyFormula (expression : Expr) :
      ReifyM Formula := do
    recordFormula
    let expression ← instantiateMVars expression
    let expression := expression.consumeMData
    if expression.isConstOf ``False then
      return .falsum
    if expression.isConstOf ``True then
      return .truth
    if expression.isAppOfArity ``Not 1 then
      return .neg (← reifyFormula expression.getAppArgs[0]!)
    if expression.isAppOfArity ``And 2 then
      return .conj
        (← reifyFormula expression.getAppArgs[0]!)
        (← reifyFormula expression.getAppArgs[1]!)
    if expression.isAppOfArity ``Or 2 then
      return .disj
        (← reifyFormula expression.getAppArgs[0]!)
        (← reifyFormula expression.getAppArgs[1]!)
    if expression.isAppOfArity ``Iff 2 then
      return .iff
        (← reifyFormula expression.getAppArgs[0]!)
        (← reifyFormula expression.getAppArgs[1]!)
    if expression.isAppOfArity ``Eq 3 then
      let equalitySort ← internSort expression.getAppArgs[0]!
      let left ← reifyTerm expression.getAppArgs[1]!
      let right ← reifyTerm expression.getAppArgs[2]!
      if left.sort == equalitySort && right.sort == equalitySort then
        return .equal equalitySort left right
      return .opaque (← internOpaqueFormula expression)
    if expression.isAppOfArity ``Exists 2 then
      let domain := expression.getAppArgs[0]!
      let sort ← internSort domain
      let predicate := expression.getAppArgs[1]!
      let reduced ← whnf predicate
      let body ←
        match reduced with
        | .lam binderName binderDomain rawBody binderInfo =>
            if binderDomain != domain then
              pure none
            else
              withObjectBinder binderName binderInfo domain sort fun binder => do
                pure <| some <|
                  ← reifyFormula (rawBody.instantiate1 binder)
        | _ =>
            withObjectBinder `witness .default domain sort fun binder => do
              pure <| some <| ← reifyFormula (mkApp predicate binder)
      let some body := body
        | return .opaque (← internOpaqueFormula expression)
      modifyStats fun stats => {
        stats with binders := stats.binders + 1
      }
      return .existsE sort body
    match expression with
    | .forallE binderName domain body binderInfo =>
        if ← isProp domain then
          if body.hasLooseBVar 0 then
            return .opaque (← internOpaqueFormula expression)
          return .imp
            (← reifyFormula domain)
            (← reifyFormula body)
        let sort ← internSort domain
        let body ←
          withObjectBinder binderName binderInfo domain sort fun binder =>
            reifyFormula (body.instantiate1 binder)
        modifyStats fun stats => {
          stats with binders := stats.binders + 1
        }
        return .forallE sort binderInfo body
    | .letE _ _ value body _ =>
        reifyFormula (body.instantiate1 value)
    | _ =>
        unless ← isProp expression do
          return .opaque (← internOpaqueFormula expression)
        let some head ← structuralHead? expression
          | return .opaque (← internOpaqueFormula expression)
        let arguments ← expression.getAppArgs.mapM reifyTerm
        let inputSorts := arguments.map Term.sort
        let symbol ← internSymbol head inputSorts none
        modifyStats fun stats => {
          stats with
          structuralApplications := stats.structuralApplications + 1
        }
        return .atom symbol arguments

end

private def fallbackSnapshot (source : Expr) (reason : String) :
    MetaM Snapshot := do
  let (root, state) ←
    (do
      recordFormula
      let entry ← internOpaqueFormula source
      modifyStats fun stats => {
        stats with
        wholeFormulaFallbacks := stats.wholeFormulaFallbacks + 1
        wholeFormulaFallbackReason? := some reason
      }
      return Formula.opaque entry).run {}
  return {
    source
    root
    sorts := state.sorts
    symbols := state.symbols
    opaqueTerms := state.opaqueTerms
    opaqueFormulas := state.opaqueFormulas
    stats := state.stats
  }

/--
对一个宿主命题执行保守总重化。

局部结构化失败时返回整个命题的 opaque 快照；只有输入本身不是 Prop 时才拒绝。
-/
def snapshot (source : Expr) : MetaM Snapshot := do
  let source ← instantiateMVars source
  unless ← isProp source do
    throwError "host reification expected a proposition, got{indentExpr source}"
  try
    let (root, state) ← reifyFormula source |>.run {}
    return {
      source
      root
      sorts := state.sorts
      symbols := state.symbols
      opaqueTerms := state.opaqueTerms
      opaqueFormulas := state.opaqueFormulas
      stats := state.stats
    }
  catch error =>
    fallbackSnapshot source (← error.toMessageData.toString)

private def sortExists (snapshot : Snapshot) (sort : SortId) : Bool :=
  snapshot.sorts[sort]?.isSome

private def boundSort?
    (bound : Array SortId) (index : Nat) : Option SortId :=
  if index < bound.size then
    bound[bound.size - index - 1]?
  else
    none

namespace Term

mutual

  /-- 项节点是否满足排序、符号和 binder 索引不变量。 -/
  partial def check (term : Term) (snapshot : Snapshot)
      (bound : Array SortId := #[]) : Bool :=
    match term with
    | .bvar sort index =>
        sortExists snapshot sort && boundSort? bound index == some sort
    | .app sort symbol arguments =>
        sortExists snapshot sort &&
          match snapshot.symbols[symbol]? with
          | some entry =>
              entry.outputSort? == some sort &&
                checkArguments snapshot bound arguments entry.inputSorts
          | none =>
              false
    | .opaque sort entry =>
        sortExists snapshot sort &&
          match snapshot.opaqueTerms[entry]? with
          | some opaqueEntry => opaqueEntry.sort == sort
          | none => false

  private partial def checkArguments (snapshot : Snapshot)
      (bound : Array SortId) (arguments : Array Term)
      (expected : Array SortId) : Bool :=
    arguments.size == expected.size &&
      (arguments.zip expected).all fun entry =>
        entry.1.sort == entry.2 && entry.1.check snapshot bound

end

end Term

namespace Formula

private def checkAtomArguments (snapshot : Snapshot)
    (bound : Array SortId) (arguments : Array Term)
    (expected : Array SortId) : Bool :=
  arguments.size == expected.size &&
    (arguments.zip expected).all fun entry =>
      entry.1.sort == entry.2 && entry.1.check snapshot bound

/-- 命题节点是否满足排序、符号和 binder 索引不变量。 -/
partial def check (formula : Formula) (snapshot : Snapshot)
    (bound : Array SortId := #[]) : Bool :=
  match formula with
  | .falsum | .truth =>
      true
  | .atom symbol arguments =>
      match snapshot.symbols[symbol]? with
      | some entry =>
          entry.outputSort?.isNone &&
            checkAtomArguments snapshot bound arguments entry.inputSorts
      | none =>
          false
  | .opaque entry =>
      snapshot.opaqueFormulas[entry]?.isSome
  | .equal sort left right =>
      sortExists snapshot sort &&
        left.sort == sort && right.sort == sort &&
          left.check snapshot bound && right.check snapshot bound
  | .neg body =>
      body.check snapshot bound
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      left.check snapshot bound && right.check snapshot bound
  | .forallE sort _ body
  | .existsE sort body =>
      sortExists snapshot sort && body.check snapshot (bound.push sort)

end Formula

/-- 快照的纯结构检查。 -/
def Snapshot.check (snapshot : Snapshot) : Bool :=
  snapshot.root.check snapshot

private def sortExpression
    (snapshot : Snapshot) (sort : SortId) : MetaM Expr := do
  let some entry := snapshot.sorts[sort]?
    | throwError "host reification lost sort #{sort}"
  return entry.expression

mutual

  private partial def rebuildTerm
      (snapshot : Snapshot) : Term → MetaM Expr
    | .bvar _ index =>
        return .bvar index
    | .app _ symbol arguments => do
        let some entry := snapshot.symbols[symbol]?
          | throwError "host reification lost symbol #{symbol}"
        let arguments ← arguments.mapM (rebuildTerm snapshot)
        return mkAppN entry.head arguments
    | .opaque _ opaqueId => do
        let some entry := snapshot.opaqueTerms[opaqueId]?
          | throwError "host reification lost opaque term #{opaqueId}"
        return entry.expression

  private partial def rebuildFormula
      (snapshot : Snapshot) : Formula → MetaM Expr
    | .falsum =>
        return mkConst ``False
    | .truth =>
        return mkConst ``True
    | .atom symbol arguments => do
        let some entry := snapshot.symbols[symbol]?
          | throwError "host reification lost predicate #{symbol}"
        let arguments ← arguments.mapM (rebuildTerm snapshot)
        return mkAppN entry.head arguments
    | .opaque opaqueId => do
        let some entry := snapshot.opaqueFormulas[opaqueId]?
          | throwError "host reification lost opaque formula #{opaqueId}"
        return entry.expression
    | .equal _ left right => do
        let left ← rebuildTerm snapshot left
        let right ← rebuildTerm snapshot right
        mkEq left right
    | .neg body =>
        return mkApp (mkConst ``Not) (← rebuildFormula snapshot body)
    | .conj left right =>
        return mkApp2 (mkConst ``And)
          (← rebuildFormula snapshot left)
          (← rebuildFormula snapshot right)
    | .disj left right =>
        return mkApp2 (mkConst ``Or)
          (← rebuildFormula snapshot left)
          (← rebuildFormula snapshot right)
    | .imp left right => do
        let left ← rebuildFormula snapshot left
        let right ← rebuildFormula snapshot right
        return .forallE `_ left (right.liftLooseBVars 0 1) .default
    | .iff left right =>
        return mkApp2 (mkConst ``Iff)
          (← rebuildFormula snapshot left)
          (← rebuildFormula snapshot right)
    | .forallE sort binderInfo body => do
        let domain ← sortExpression snapshot sort
        return .forallE `object domain
          (← rebuildFormula snapshot body) binderInfo
    | .existsE sort body => do
        let domain ← sortExpression snapshot sort
        let predicate := Expr.lam `witness domain
          (← rebuildFormula snapshot body) .default
        mkAppM ``Exists #[predicate]

end

/-- 从 typed raw 快照重建宿主命题。 -/
def Snapshot.rebuild (snapshot : Snapshot) : MetaM Expr :=
  rebuildFormula snapshot snapshot.root

private def expressionContextClosed (expression : Expr) : MetaM Bool := do
  let (_, freeVariables) ← expression.collectFVars.run {}
  let localContext ← getLCtx
  return freeVariables.fvarIds.all fun fvarId =>
    localContext.contains fvarId

/-- 快照中没有重化过程泄漏出的临时 FVar。 -/
def Snapshot.contextClosed (snapshot : Snapshot) : MetaM Bool := do
  if !(← expressionContextClosed snapshot.source) then
    return false
  for entry in snapshot.sorts do
    if !(← expressionContextClosed entry.expression) then
      return false
  for entry in snapshot.symbols do
    if !(← expressionContextClosed entry.head) then
      return false
  for entry in snapshot.opaqueTerms do
    if !(← expressionContextClosed entry.expression) ||
        !(← expressionContextClosed entry.type) then
      return false
  for entry in snapshot.opaqueFormulas do
    if !(← expressionContextClosed entry.expression) then
      return false
  return true

/--
验证快照结构、局部上下文闭包和 source/rebuild 的定义等价 round-trip。
-/
def Snapshot.validate (snapshot : Snapshot) : MetaM Unit := do
  unless snapshot.check do
    throwError "host reification produced an invalid typed raw snapshot"
  unless ← snapshot.contextClosed do
    throwError "host reification leaked a temporary local declaration"
  let rebuilt ← snapshot.rebuild
  let equivalent ← withoutModifyingState <|
    withTransparency .reducible <| isDefEq snapshot.source rebuilt
  unless equivalent do
    throwError
      "host reification round-trip changed the proposition:\n\
      source:{indentExpr snapshot.source}\nrebuilt:{indentExpr rebuilt}"

end HostReification
end Automation
end YesMetaZFC
