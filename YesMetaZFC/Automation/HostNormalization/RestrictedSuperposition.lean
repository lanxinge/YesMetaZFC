import Lean.Meta.DiscrTree
import YesMetaZFC.Automation.HostNormalization.RuleCompiler

/-!
# 宿主正规化的受限叠加演算候选层

本模块只实现单位等式、命题等价与定义展开的 demodulation 候选索引。它复用 Lean
Meta 的 discrimination tree，不执行可信推理：

* theorem 左端按实际方向进入四阶段模式索引；
* definition 按声明根进入精确索引；
* 过于一般或索引失败的规则进入阶段 fallback；
* 查询只返回可能命中的规则，最终成立性与证明项仍由 `EqualityClosure` 回放检查。

因此这里是可替换的不可信搜索层，不是第二套证明内核，也不接管完整字句饱和。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization
namespace RestrictedSuperposition

open Lean Meta

abbrev RuleId := Nat

/-- 单阶段的单位 demodulation 候选索引。 -/
structure PhaseIndex where
  theoremPatterns : DiscrTree RuleId := {}
  theoremRoots : NameMap Bool := {}
  definitionRoots : NameMap (Array RuleId) := {}
  fallback : Array RuleId := #[]
  allRules : Array RuleId := #[]

/-- 索引构建覆盖统计。 -/
structure BuildStats where
  rules : Nat := 0
  theoremRules : Nat := 0
  definitionRules : Nat := 0
  indexedTheorems : Nat := 0
  rootedDefinitions : Nat := 0
  fallbackRules : Nat := 0
  skippedRules : Nat := 0
deriving Repr, Inhabited

/-- 四阶段受限叠加演算索引；规则数组保持调用方给定的稳定顺序。 -/
structure Index where
  rules : Array RuleCompiler.Rule := #[]
  definitionExposure : PhaseIndex := {}
  indexAlgebra : PhaseIndex := {}
  semanticAlignment : PhaseIndex := {}
  logicalCleanup : PhaseIndex := {}
  stats : BuildStats := {}

/-- 一次候选查询的观察统计。 -/
structure QueryStats where
  expressions : Nat := 0
  treeQueries : Nat := 0
  rootQueries : Nat := 0
  indexedCandidates : Nat := 0
  rootCandidates : Nat := 0
  fallbackCandidates : Nat := 0
  prunedRules : Nat := 0
  queryFailures : Nat := 0
deriving Repr, Inhabited

/-- 一个阶段对当前宿主表达式给出的保守规则候选。 -/
structure QueryResult where
  ruleIds : Array RuleId := #[]
  stats : QueryStats := {}
deriving Repr, Inhabited

private def Index.phaseIndex (index : Index) : Phase → PhaseIndex
  | .definitionExposure => index.definitionExposure
  | .indexAlgebra => index.indexAlgebra
  | .semanticAlignment => index.semanticAlignment
  | .logicalCleanup => index.logicalCleanup

private def Index.setPhaseIndex
    (index : Index) (phase : Phase) (phaseIndex : PhaseIndex) : Index :=
  match phase with
  | .definitionExposure => { index with definitionExposure := phaseIndex }
  | .indexAlgebra => { index with indexAlgebra := phaseIndex }
  | .semanticAlignment => { index with semanticAlignment := phaseIndex }
  | .logicalCleanup => { index with logicalCleanup := phaseIndex }

private def Index.setStats (index : Index) (stats : BuildStats) : Index :=
  { index with stats }

private def instantiatedTheoremPattern?
    (rule : RuleCompiler.Rule) : MetaM (Option Expr) := do
  let info ← getConstInfo rule.declaration
  let (_, _, body) ← forallMetaTelescopeReducing info.type
  let body := body.consumeMData
  let left? :=
    if body.isAppOfArity ``Eq 3 then
      let arguments := body.getAppArgs
      some arguments[1]!
    else if body.isAppOfArity ``Iff 2 then
      let arguments := body.getAppArgs
      some arguments[0]!
    else
      none
  return left?

private def insertRoot
    (roots : NameMap (Array RuleId)) (declaration : Name) (ruleId : RuleId) :
    NameMap (Array RuleId) :=
  let bucket := roots.find? declaration |>.getD #[]
  roots.insert declaration (bucket.push ruleId)

private def generalPattern (keys : Array DiscrTree.Key) : Bool :=
  keys == #[.star]

private def rootDeclaration? (expression : Expr) : Option Name :=
  match expression.consumeMData.getAppFn with
  | .const declaration _ => some declaration
  | _ => none

private def insertTheorem
    (phaseIndex : PhaseIndex) (ruleId : RuleId) (rule : RuleCompiler.Rule) :
    MetaM (PhaseIndex × Bool) := do
  let saved ← saveState
  try
    let some pattern ← instantiatedTheoremPattern? rule
      | saved.restore
        return ({ phaseIndex with fallback := phaseIndex.fallback.push ruleId }, false)
    let keys ← DiscrTree.mkPath pattern
    if generalPattern keys then
      saved.restore
      return ({ phaseIndex with fallback := phaseIndex.fallback.push ruleId }, false)
    let some root := rootDeclaration? pattern
      | saved.restore
        return ({ phaseIndex with fallback := phaseIndex.fallback.push ruleId }, false)
    let theoremPatterns ← phaseIndex.theoremPatterns.insert pattern ruleId
    let theoremRoots := phaseIndex.theoremRoots.insert root true
    saved.restore
    return ({ phaseIndex with theoremPatterns, theoremRoots }, true)
  catch _ =>
    saved.restore
    return ({ phaseIndex with fallback := phaseIndex.fallback.push ruleId }, false)

private def insertRule
    (index : Index) (ruleId : RuleId) (rule : RuleCompiler.Rule) :
    MetaM Index := do
  let phase := rule.phase
  let phaseIndex := index.phaseIndex phase
  let phaseIndex := { phaseIndex with allRules := phaseIndex.allRules.push ruleId }
  let stats := { index.stats with rules := index.stats.rules + 1 }
  match rule.kind with
  | .theorem _ =>
      let stats := { stats with theoremRules := stats.theoremRules + 1 }
      let (phaseIndex, indexed) ← insertTheorem phaseIndex ruleId rule
      let stats :=
        if indexed then
          { stats with indexedTheorems := stats.indexedTheorems + 1 }
        else
          { stats with fallbackRules := stats.fallbackRules + 1 }
      return (index.setPhaseIndex phase phaseIndex) |>.setStats stats
  | .definition =>
      let stats := { stats with definitionRules := stats.definitionRules + 1 }
      let phaseIndex := {
        phaseIndex with
        definitionRoots :=
          insertRoot phaseIndex.definitionRoots rule.declaration ruleId
      }
      let stats := { stats with rootedDefinitions := stats.rootedDefinitions + 1 }
      return (index.setPhaseIndex phase phaseIndex) |>.setStats stats
  | .unsupported =>
      let stats := { stats with skippedRules := stats.skippedRules + 1 }
      return (index.setPhaseIndex phase phaseIndex) |>.setStats stats

/--
从稳定排序的 proof-free 规则数组构建四阶段受限叠加演算索引。

索引值只保存数组编号，不缓存 theorem proof。
-/
def Index.build (rules : Array RuleCompiler.Rule) : MetaM Index := do
  let mut index : Index := { rules }
  for h : ruleId in [:rules.size] do
    index ← insertRule index ruleId rules[ruleId]
  return index

private structure QueryState where
  seen : Array Bool
  ruleIds : Array RuleId := #[]
  stats : QueryStats := {}

private def QueryState.insert
    (state : QueryState) (ruleId : RuleId)
    (record : QueryStats → QueryStats) : QueryState :=
  if h : ruleId < state.seen.size then
    if state.seen[ruleId] then
      state
    else
      {
        state with
        seen := state.seen.set ruleId true
        ruleIds := state.ruleIds.push ruleId
        stats := record state.stats
      }
  else
    state

private def QueryState.insertIndexed
    (state : QueryState) (ruleId : RuleId) : QueryState :=
  state.insert ruleId fun stats => {
    stats with indexedCandidates := stats.indexedCandidates + 1
  }

private def QueryState.insertRoot
    (state : QueryState) (ruleId : RuleId) : QueryState :=
  state.insert ruleId fun stats => {
    stats with rootCandidates := stats.rootCandidates + 1
  }

private def QueryState.insertFallback
    (state : QueryState) (ruleId : RuleId) : QueryState :=
  state.insert ruleId fun stats => {
    stats with fallbackCandidates := stats.fallbackCandidates + 1
  }

private partial def queryExpression
    (phaseIndex : PhaseIndex) (expression : Expr) (state : QueryState) :
    MetaM QueryState := do
  let expression := expression.consumeMData
  let root? := rootDeclaration? expression
  let shouldQueryTree :=
    root?.any fun root => (phaseIndex.theoremRoots.find? root).isSome
  let matchedRuleIds ←
    if shouldQueryTree then
      phaseIndex.theoremPatterns.getMatch expression
    else
      pure #[]
  let mut state := {
    state with
    stats := {
      state.stats with
      expressions := state.stats.expressions + 1
      treeQueries := state.stats.treeQueries + if shouldQueryTree then 1 else 0
      rootQueries := state.stats.rootQueries + 1
    }
  }
  for ruleId in matchedRuleIds do
    state := state.insertIndexed ruleId
  if let some declaration := root? then
    for ruleId in phaseIndex.definitionRoots.find? declaration |>.getD #[] do
      state := state.insertRoot ruleId
  match expression with
  | .app function argument =>
      let nextState ← queryExpression phaseIndex function state
      queryExpression phaseIndex argument nextState
  | .lam binderName domain body binderInfo =>
      let nextState ← queryExpression phaseIndex domain state
      withLocalDecl binderName binderInfo domain fun binder =>
        queryExpression phaseIndex (body.instantiate1 binder) nextState
  | .forallE binderName domain body binderInfo =>
      let nextState ← queryExpression phaseIndex domain state
      withLocalDecl binderName binderInfo domain fun binder =>
        queryExpression phaseIndex (body.instantiate1 binder) nextState
  | .letE _ type value body _ =>
      let nextState ← queryExpression phaseIndex type state
      let nextState' ← queryExpression phaseIndex value nextState
      queryExpression phaseIndex (body.instantiate1 value) nextState'
  | .proj _ _ structureExpr =>
      queryExpression phaseIndex structureExpr state
  | _ =>
      return state

/--
查询当前阶段可能在任意子表达式位置执行单位 demodulation 的规则。

判别树查询异常时退回该阶段全部规则；这种退化只损失性能，不损失原有覆盖。
-/
def Index.query
    (index : Index) (phase : Phase) (expression : Expr) : MetaM QueryResult := do
  let phaseIndex := index.phaseIndex phase
  let initial : QueryState := {
    seen := (List.replicate index.rules.size false).toArray
  }
  try
    let mut state ← queryExpression phaseIndex expression initial
    for ruleId in phaseIndex.fallback do
      state := state.insertFallback ruleId
    let ruleIds := state.ruleIds.qsort (· < ·)
    return {
      ruleIds
      stats := {
        state.stats with
        prunedRules := phaseIndex.allRules.size - ruleIds.size
      }
    }
  catch _ =>
    return {
      ruleIds := phaseIndex.allRules
      stats := {
        fallbackCandidates := phaseIndex.allRules.size
        queryFailures := 1
      }
    }

end RestrictedSuperposition
end HostNormalization
end Automation
end YesMetaZFC
