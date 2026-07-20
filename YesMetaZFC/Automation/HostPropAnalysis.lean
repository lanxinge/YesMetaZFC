import Lean

/-!
# 宿主命题分析核

本模块提供 `prove_auto` 各搜索核心可共享的轻量反射层，但暂不接入任何现有调度器。

分析核只编译命题形状、局部资源图、目标需求和策略信号。它不构造证明、不关闭目标，
也不属于可信边界。后续搜索核心只能把查询结果当成候选排序与调度依据；实际规则应用
仍须重新经过现有 checked 执行层和 Lean 内核。

缓存生命周期严格限制在一次分析会话内：

* 命题形状与结构投影使用会话级有界缓存；
* 局部上下文使用父 frame 加增量索引，不复制完整资源表；
* 目标查询按 `(frame, target)` 记忆；
* 含 metavariable 的表达式不进入缓存；
* `FVarId`、proof `Expr` 和局部对象绝不跨 tactic 会话保存。

缓存采用有界、不驱逐策略。一次证明搜索具有很强的时间局部性，LRU 会额外制造写放大，
而超过容量后直接停止缓存仍保持完整分析能力。
-/

namespace YesMetaZFC
namespace Automation
namespace HostPropAnalysis

open Lean Meta

/-- 单次分析会话的缓存与 frame 护栏。 -/
structure Config where
  maxShapes : Nat := 4096
  maxExpansions : Nat := 1024
  maxQueries : Nat := 2048
  maxFrames : Nat := 4096
  maxFrameDepth : Nat := 256
deriving Repr

/-- 命题根部的稳定逻辑形状。 -/
inductive RootKind where
  | falsum
  | truth
  | negation
  | conjunction
  | disjunction
  | implication
  | equivalence
  | existential
  | universal
  | equality
  | heterogeneousEquality
  | structure
  | inductive
  | atom
deriving Repr, Inhabited, BEq, DecidableEq, Hashable

/-- 命题及对象表达式暴露给通用策略的相关性锚点。 -/
structure Profile where
  heads : Array Name := #[]
  propositionFVars : Array FVarId := #[]
  objectFVars : Array FVarId := #[]
  appliedFVars : Array FVarId := #[]
deriving Repr, Inhabited

private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private def pushFVarUnique
    (variables : Array FVarId) (fvar : FVarId) : Array FVarId :=
  if variables.contains fvar then variables else variables.push fvar

private def pushExprUnique (expressions : Array Expr) (expression : Expr) :
    Array Expr :=
  if expressions.contains expression then expressions else expressions.push expression

private def pushRootUnique
    (roots : Array RootKind) (root : RootKind) : Array RootKind :=
  if roots.contains root then roots else roots.push root

/-- 合并 profile 并保持首次出现顺序。 -/
def Profile.merge (left right : Profile) : Profile := {
  heads := right.heads.foldl pushNameUnique left.heads
  propositionFVars :=
    right.propositionFVars.foldl pushFVarUnique left.propositionFVars
  objectFVars :=
    right.objectFVars.foldl pushFVarUnique left.objectFVars
  appliedFVars :=
    right.appliedFVars.foldl pushFVarUnique left.appliedFVars
}

private def sharedNameCount (left right : Array Name) : Nat :=
  left.foldl
    (fun count name => if right.contains name then count + 1 else count) 0

private def sharedFVarCount (left right : Array FVarId) : Nat :=
  left.foldl
    (fun count fvar => if right.contains fvar then count + 1 else count) 0

/--
通用相关性只影响顺序，不决定资源是否存在或是否允许参与搜索。

已应用的局部函数变量权重最高，其次是命题变量、对象变量和声明头。
-/
def Profile.score (target candidate : Profile) : Nat :=
  sharedFVarCount target.appliedFVars candidate.appliedFVars * 80 +
    sharedFVarCount target.propositionFVars candidate.propositionFVars * 40 +
    sharedFVarCount target.objectFVars candidate.objectFVars * 20 +
    sharedNameCount target.heads candidate.heads * 5

private def ignoredHead (name : Name) : Bool :=
  name == ``False || name == ``True || name == ``Not ||
    name == ``And || name == ``Or || name == ``Iff ||
    name == ``Eq || name == ``HEq || name == ``Exists

private partial def collectProfileAux
    (expression : Expr) (fuel : Nat) (profile : Profile) :
    MetaM Profile := do
  if fuel == 0 then
    return profile
  let expression := expression.consumeMData
  let mut profile := profile
  match expression.getAppFn with
  | .const declaration _ =>
      unless ignoredHead declaration do
        profile := {
          profile with heads := pushNameUnique profile.heads declaration
        }
  | .fvar fvar =>
      if expression.isApp then
        profile := {
          profile with appliedFVars := pushFVarUnique profile.appliedFVars fvar
        }
  | _ =>
      pure ()
  match expression with
  | .fvar fvar =>
      if ← isProp expression then
        return {
          profile with
          propositionFVars := pushFVarUnique profile.propositionFVars fvar
        }
      else
        return {
          profile with objectFVars := pushFVarUnique profile.objectFVars fvar
        }
  | .forallE _ domain body _ =>
      let afterDomain ← collectProfileAux domain (fuel - 1) profile
      collectProfileAux body (fuel - 1) afterDomain
  | .lam _ domain body _ =>
      let afterDomain ← collectProfileAux domain (fuel - 1) profile
      collectProfileAux body (fuel - 1) afterDomain
  | .letE _ type value body _ =>
      let afterType ← collectProfileAux type (fuel - 1) profile
      let afterValue ← collectProfileAux value (fuel - 1) afterType
      collectProfileAux body (fuel - 1) afterValue
  | .proj _ _ body =>
      collectProfileAux body (fuel - 1) profile
  | _ =>
      expression.getAppArgs.foldlM
        (init := profile) fun current argument =>
          collectProfileAux argument (fuel - 1) current

/-- 收集单个稳定表达式的相关性 profile。 -/
def collectProfile (expression : Expr) : MetaM Profile := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then
    throwError
      "host proposition analysis cannot cache a profile containing metavariables"
  collectProfileAux expression 64 {}

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
    | .proj _ _ body =>
        expressionSize body
    | _ => 0

private partial def expressionHasLambda (expression : Expr) : Bool :=
  let expression := expression.consumeMData
  match expression with
  | .lam .. => true
  | .app function argument =>
      expressionHasLambda function || expressionHasLambda argument
  | .forallE _ domain body _ =>
      expressionHasLambda domain || expressionHasLambda body
  | .letE _ type value body _ =>
      expressionHasLambda type || expressionHasLambda value ||
        expressionHasLambda body
  | .proj _ _ body =>
      expressionHasLambda body
  | _ => false

private partial def expressionEqualityCount (expression : Expr) : Nat :=
  let expression := expression.consumeMData
  let here :=
    if expression.isAppOfArity ``Eq 3 ||
        expression.isAppOfArity ``HEq 4 then
      1
    else
      0
  here +
    match expression with
    | .app function argument =>
        expressionEqualityCount function + expressionEqualityCount argument
    | .lam _ domain body _ =>
        expressionEqualityCount domain + expressionEqualityCount body
    | .forallE _ domain body _ =>
        expressionEqualityCount domain + expressionEqualityCount body
    | .letE _ type value body _ =>
        expressionEqualityCount type +
          expressionEqualityCount value +
          expressionEqualityCount body
    | .proj _ _ body =>
        expressionEqualityCount body
    | _ => 0

private def expressionHead? (expression : Expr) : Option Expr :=
  match expression.consumeMData.getAppFn with
  | head@(.const ..) => some head
  | head@(.fvar ..) => some head
  | head@(.sort ..) => some head
  | head@(.lit ..) => some head
  | _ => none

private def classifyRoot (expression : Expr) : MetaM RootKind := do
  let expression ← instantiateMVars expression
  if expression.isConstOf ``False then
    return .falsum
  if expression.isConstOf ``True then
    return .truth
  if expression.isAppOfArity ``Not 1 then
    return .negation
  if expression.isAppOfArity ``And 2 then
    return .conjunction
  if expression.isAppOfArity ``Or 2 then
    return .disjunction
  if expression.isAppOfArity ``Iff 2 then
    return .equivalence
  if expression.isAppOfArity ``Exists 2 then
    return .existential
  if expression.isAppOfArity ``Eq 3 then
    return .equality
  if expression.isAppOfArity ``HEq 4 then
    return .heterogeneousEquality
  match expression with
  | .forallE _ domain _ _ =>
      if ← isProp domain then
        return .implication
      else
        return .universal
  | _ =>
      let reduced ← whnf expression
      let some declaration := reduced.getAppFn.constName?
        | return .atom
      if (getStructureInfo? (← getEnv) declaration).isSome then
        return .structure
      if (← isInductivePredicate? declaration).isSome then
        return .inductive
      return .atom

private def casesConstructorCount (proposition : Expr) : MetaM Nat := do
  let proposition ← instantiateMVars (← whnf proposition)
  let some inductiveName := proposition.getAppFn.constName?
    | return 0
  if inductiveName == ``Exists || inductiveName == ``Eq ||
      inductiveName == ``HEq then
    return 0
  let some inductiveInfo ← isInductivePredicate? inductiveName
    | return 0
  if inductiveInfo.isUnsafe || inductiveInfo.numIndices != 0 ||
      proposition.getAppNumArgs != inductiveInfo.numParams ||
      inductiveInfo.ctors.isEmpty then
    return 0
  for constructorName in inductiveInfo.ctors do
    if (← getConstInfo constructorName).isUnsafe then
      return 0
  return inductiveInfo.ctors.length

/-- 单个命题经反射后供所有搜索核心共享的稳定形状。 -/
structure Shape where
  root : RootKind
  conclusionRoot : RootKind
  conclusionHead? : Option Expr := none
  premiseHeads : Array Expr := #[]
  objectBinders : Nat := 0
  explicitPropPremises : Nat := 0
  implicitPropPremises : Nat := 0
  instanceBinders : Nat := 0
  constructorCount : Nat := 0
  expressionSize : Nat := 0
  equalityCount : Nat := 0
  hasLambda : Bool := false
  profile : Profile := {}
deriving Repr

/-- 形状可否作为无猜测的前向 producer。 -/
def Shape.forwardEligible (shape : Shape) : Bool :=
  shape.explicitPropPremises > 0 &&
    shape.implicitPropPremises == 0 &&
    shape.instanceBinders == 0

/-- 形状可否由有限 CASES 消去。 -/
def Shape.casesEligible (shape : Shape) : Bool :=
  shape.constructorCount > 0 &&
    shape.root != .existential &&
    shape.root != .equality &&
    shape.root != .heterogeneousEquality

private def compileShape (proposition : Expr) : MetaM Shape := do
  let proposition ← instantiateMVars proposition
  if proposition.hasMVar then
    throwError
      "host proposition analysis cannot cache a shape containing metavariables"
  let savedState ← saveState
  try
    let root ← classifyRoot proposition
    let (arguments, binderInfos, conclusion) ←
      forallMetaTelescopeReducing proposition
    let mut objectBinders := 0
    let mut explicitPropPremises := 0
    let mut implicitPropPremises := 0
    let mut instanceBinders := 0
    let mut premiseHeads := #[]
    for index in [0 : arguments.size] do
      let binderInfo := binderInfos[index]!
      if binderInfo.isInstImplicit then
        instanceBinders := instanceBinders + 1
      let argumentType ← instantiateMVars (← inferType arguments[index]!)
      if ← isProp argumentType then
        if binderInfo.isExplicit then
          explicitPropPremises := explicitPropPremises + 1
        else
          implicitPropPremises := implicitPropPremises + 1
        if let some head := expressionHead? argumentType then
          unless head.hasMVar do
            premiseHeads := pushExprUnique premiseHeads head
      else
        objectBinders := objectBinders + 1
    let conclusion ← instantiateMVars conclusion
    let conclusionRoot ← classifyRoot conclusion
    let conclusionHead? :=
      match expressionHead? conclusion with
      | some head => if head.hasMVar then none else some head
      | none => none
    let shape : Shape := {
      root := root
      conclusionRoot := conclusionRoot
      conclusionHead? := conclusionHead?
      premiseHeads := premiseHeads
      objectBinders := objectBinders
      explicitPropPremises := explicitPropPremises
      implicitPropPremises := implicitPropPremises
      instanceBinders := instanceBinders
      constructorCount := ← casesConstructorCount proposition
      expressionSize := expressionSize proposition
      equalityCount := expressionEqualityCount proposition
      hasLambda := expressionHasLambda proposition
      profile := ← collectProfile proposition
    }
    savedState.restore
    return shape
  catch error =>
    savedState.restore
    throw error

/-- 局部 proof 进入分析 frame 前的稳定来源。 -/
inductive SeedOrigin where
  | local
  | explicit
  | generated
deriving Repr, Inhabited, BEq

/-- 一个尚未展开结构字段的 proof 资源。 -/
structure ResourceSeed where
  label : Name
  proof : Expr
  origin : SeedOrigin := .explicit

/-- 一个可作为对象参数的局部 typed 资源。 -/
structure ObjectSeed where
  label : Name
  expression : Expr
  type : Expr

/-- 会话资源与对象使用 packed Nat ID。 -/
structure ResourceId where
  index : Nat
deriving Repr, Inhabited, BEq, DecidableEq, Hashable

structure ObjectId where
  index : Nat
deriving Repr, Inhabited, BEq, DecidableEq, Hashable

structure Frame where
  id : Nat
deriving Repr, Inhabited, BEq, DecidableEq, Hashable

/-- 已编译且可由后续执行层按 ID 取回的单个 proof 资源。 -/
structure Resource where
  id : ResourceId
  frame : Frame
  label : Name
  sourceLabel : Name
  proof : Expr
  proposition : Expr
  projectionPath : Array Name := #[]
  origin : SeedOrigin
  shape : Shape
deriving Repr

/-- 已编译的局部对象。 -/
structure Object where
  id : ObjectId
  frame : Frame
  label : Name
  expression : Expr
  type : Expr
deriving Repr

private structure ExpansionKey where
  proof : Expr
  label : Name
deriving BEq, Hashable

private structure ExpandedProof where
  label : Name
  proof : Expr
  proposition : Expr
  projectionPath : Array Name := #[]

private partial def expandProofAux
    (proof : Expr) (label : Name) (path : Array Name)
    (seen : PHashMap Expr Bool) :
    MetaM (PHashMap Expr Bool × Array ExpandedProof) := do
  let proposition ← instantiateMVars (← inferType proof)
  if proposition.hasMVar then
    return (seen, #[])
  if seen.contains proposition then
    return (seen, #[])
  let seen := seen.insert proposition true
  let mut result := #[{
    label := label
    proof := proof
    proposition := proposition.consumeMData
    projectionPath := path
  }]
  let reduced ← whnf proposition
  let some structureName := reduced.getAppFn.constName?
    | return (seen, result)
  let some structureInfo := getStructureInfo? (← getEnv) structureName
    | return (seen, result)
  let mut seen := seen
  for fieldName in structureInfo.fieldNames do
    let projection ← mkProjection proof fieldName
    let projectionType ← instantiateMVars (← inferType projection)
    if projectionType.hasMVar || !(← isProp projectionType) then
      continue
    let (nextSeen, expanded) ←
      expandProofAux projection fieldName (path.push fieldName) seen
    seen := nextSeen
    result := result ++ expanded
  return (seen, result)

private def expandProofUncached
    (seed : ResourceSeed) : MetaM (Array ExpandedProof) := do
  return (← expandProofAux seed.proof seed.label #[] {}).2

private structure PendingResource where
  label : Name
  sourceLabel : Name
  proof : Expr
  proposition : Expr
  projectionPath : Array Name
  origin : SeedOrigin
  shape : Shape

private structure PendingObject where
  label : Name
  expression : Expr
  type : Expr

private structure DeltaIndex where
  exact : PHashMap Expr (Array ResourceId) := {}
  conclusionHeads : PHashMap Expr (Array ResourceId) := {}
  premiseHeads : PHashMap Expr (Array ResourceId) := {}
  cases : Array ResourceId := #[]
  choose : Array ResourceId := #[]
  forward : Array ResourceId := #[]
  contradictionProducers : Array ResourceId := #[]
  equalities : Array ResourceId := #[]
  structures : Array ResourceId := #[]

private def insertBucket
    (map : PHashMap Expr (Array ResourceId))
    (key : Expr) (id : ResourceId) :
    PHashMap Expr (Array ResourceId) :=
  map.insert key ((map.find? key).getD #[] |>.push id)

private def DeltaIndex.insert
    (index : DeltaIndex) (resource : Resource) : DeltaIndex :=
  let shape := resource.shape
  let exact := insertBucket index.exact resource.proposition resource.id
  let conclusionHeads :=
    match shape.conclusionHead? with
    | some head => insertBucket index.conclusionHeads head resource.id
    | none => index.conclusionHeads
  let premiseHeads :=
    shape.premiseHeads.foldl
      (fun map head => insertBucket map head resource.id)
      index.premiseHeads
  {
    exact := exact
    conclusionHeads := conclusionHeads
    premiseHeads := premiseHeads
    cases :=
      if shape.casesEligible then index.cases.push resource.id else index.cases
    choose :=
      if shape.root == .existential then
        index.choose.push resource.id
      else
        index.choose
    forward :=
      if shape.forwardEligible then
        index.forward.push resource.id
      else
        index.forward
    contradictionProducers :=
      if shape.forwardEligible && shape.conclusionRoot == .falsum then
        index.contradictionProducers.push resource.id
      else
        index.contradictionProducers
    equalities :=
      if shape.conclusionRoot == .equality ||
          shape.conclusionRoot == .heterogeneousEquality ||
          shape.conclusionRoot == .equivalence then
        index.equalities.push resource.id
      else
        index.equalities
    structures :=
      if shape.root == .structure then
        index.structures.push resource.id
      else
        index.structures
  }

/--
一个 frame 及其全部祖先资源的累计属性。

这对应 Vampire `Property` 一类会话内问题属性快照：查询策略可据此跳过确定为空的
分支族，但实际候选仍来自精确索引，属性本身不充当证明或删除依据。
-/
structure ContextSummary where
  resources : Nat := 0
  objects : Nat := 0
  cases : Nat := 0
  choose : Nat := 0
  forward : Nat := 0
  contradiction : Nat := 0
  equalities : Nat := 0
  structures : Nat := 0
  higherOrderSurface : Bool := false
deriving Repr, Inhabited, BEq

private def ContextSummary.addDelta
    (summary : ContextSummary) (index : DeltaIndex)
    (resources objects : Nat) (higherOrderSurface : Bool) :
    ContextSummary := {
  resources := summary.resources + resources
  objects := summary.objects + objects
  cases := summary.cases + index.cases.size
  choose := summary.choose + index.choose.size
  forward := summary.forward + index.forward.size
  contradiction := summary.contradiction + index.contradictionProducers.size
  equalities := summary.equalities + index.equalities.size
  structures := summary.structures + index.structures.size
  higherOrderSurface := summary.higherOrderSurface || higherOrderSurface
}

private structure FrameData where
  parent? : Option Frame := none
  depth : Nat := 0
  resources : Array ResourceId := #[]
  objects : Array ObjectId := #[]
  index : DeltaIndex := {}
  summary : ContextSummary := {}

/-- 分析与缓存的可观测计数。 -/
structure Stats where
  shapeLookups : Nat := 0
  shapeHits : Nat := 0
  shapeMisses : Nat := 0
  expansionLookups : Nat := 0
  expansionHits : Nat := 0
  expansionMisses : Nat := 0
  queryLookups : Nat := 0
  queryHits : Nat := 0
  queryMisses : Nat := 0
  cacheCapacityPrunes : Nat := 0
  frames : Nat := 0
  resources : Nat := 0
  objects : Nat := 0
  duplicateResources : Nat := 0
  unstableResources : Nat := 0
  queryResourceVisits : Nat := 0
  maxFrameDepth : Nat := 0
deriving Repr, Inhabited

private structure QueryKey where
  frame : Frame
  target : Expr
deriving BEq, Hashable

/-- 目标在可逆连接词下暴露出的需求。 -/
structure DemandSet where
  expressions : Array Expr := #[]
  heads : Array Expr := #[]
  roots : Array RootKind := #[]
deriving Repr

/-- 一个按需求和相关性稳定排序的资源。 -/
structure RankedResource where
  resource : ResourceId
  score : Nat
deriving Repr

/--
分析核发布给策略调度器的通用信号。

这些信号只表达“存在可尝试的局部路线”，不能单独证明路线成功。
-/
structure StrategySignals where
  exactClosure : Bool := false
  invertibleTarget : Bool := false
  constructorTarget : Bool := false
  casesAvailable : Bool := false
  chooseAvailable : Bool := false
  forwardAvailable : Bool := false
  contradictionAvailable : Bool := false
  equalityAvailable : Bool := false
  higherOrderSurface : Bool := false
  terminalShouldDefer : Bool := false
deriving Repr

/-- 单个 `(frame, target)` 的 proof-free 查询结果。 -/
structure View where
  frame : Frame
  target : Expr
  targetShape : Shape
  context : ContextSummary
  demands : DemandSet
  resources : Array ResourceId := #[]
  exact : Array ResourceId := #[]
  apply : Array RankedResource := #[]
  cases : Array RankedResource := #[]
  choose : Array RankedResource := #[]
  forward : Array RankedResource := #[]
  contradiction : Array RankedResource := #[]
  equalities : Array RankedResource := #[]
  signals : StrategySignals := {}
deriving Repr

private structure State where
  config : Config
  shapeCache : PHashMap Expr Shape := {}
  shapeCacheCount : Nat := 0
  expansionCache : PHashMap ExpansionKey (Array ExpandedProof) := {}
  expansionCacheCount : Nat := 0
  queryCache : PHashMap QueryKey View := {}
  queryCacheCount : Nat := 0
  frames : Array FrameData := #[]
  resources : Array Resource := #[]
  objects : Array Object := #[]
  stats : Stats := {}

/--
一次 `prove_auto` 调用可共享的分析会话。

内部 `IO.Ref` 只保存不可信缓存；所有公开 frame 均不可变。
-/
structure Session where
  private state : IO.Ref State

/-- 创建一个空分析会话。 -/
def Session.create (config : Config := {}) : IO Session := do
  return { state := ← IO.mkRef { config := config } }

private def Session.cachedShape?
    (session : Session) (expression : Expr) : IO (Option Shape) :=
  session.state.modifyGet fun state =>
    let cached? := state.shapeCache.find? expression
    let stats := {
      state.stats with
      shapeLookups := state.stats.shapeLookups + 1
      shapeHits := state.stats.shapeHits + if cached?.isSome then 1 else 0
      shapeMisses := state.stats.shapeMisses + if cached?.isSome then 0 else 1
    }
    (cached?, { state with stats := stats })

/-- 编译或读取一个稳定命题形状。 -/
def Session.shape (session : Session) (proposition : Expr) : MetaM Shape := do
  let proposition ← instantiateMVars proposition
  if proposition.hasMVar then
    throwError
      "host proposition analysis cannot query a shape containing metavariables"
  let proposition := proposition.consumeMData
  if let some shape ← session.cachedShape? proposition then
    return shape
  let shape ← compileShape proposition
  session.state.modify fun state =>
    if (state.shapeCache.find? proposition).isSome then
      state
    else if state.shapeCacheCount < state.config.maxShapes then
      {
        state with
        shapeCache := state.shapeCache.insert proposition shape
        shapeCacheCount := state.shapeCacheCount + 1
      }
    else
      {
        state with
        stats := {
          state.stats with
          cacheCapacityPrunes := state.stats.cacheCapacityPrunes + 1
        }
      }
  return shape

private def Session.expansion
    (session : Session) (seed : ResourceSeed) :
    MetaM (Array ExpandedProof) := do
  let key : ExpansionKey := { proof := seed.proof, label := seed.label }
  let cached? ← session.state.modifyGet fun state =>
    let cached? := state.expansionCache.find? key
    let stats := {
      state.stats with
      expansionLookups := state.stats.expansionLookups + 1
      expansionHits :=
        state.stats.expansionHits + if cached?.isSome then 1 else 0
      expansionMisses :=
        state.stats.expansionMisses + if cached?.isSome then 0 else 1
    }
    (cached?, { state with stats := stats })
  if let some expansion := cached? then
    return expansion
  let expansion ← expandProofUncached seed
  session.state.modify fun state =>
    if (state.expansionCache.find? key).isSome then
      state
    else if state.expansionCacheCount < state.config.maxExpansions then
      {
        state with
        expansionCache := state.expansionCache.insert key expansion
        expansionCacheCount := state.expansionCacheCount + 1
      }
    else
      {
        state with
        stats := {
          state.stats with
          cacheCapacityPrunes := state.stats.cacheCapacityPrunes + 1
        }
      }
  return expansion

private def frameData? (state : State) (frame : Frame) : Option FrameData :=
  state.frames[frame.id]?

private def frameChain (state : State) (frame : Frame) :
    Array Frame := Id.run do
  let mut reversed := #[]
  let mut current? := some frame
  for _ in [:state.frames.size + 1] do
    match current? with
    | none =>
        return reversed.reverse
    | some current =>
        let some data := frameData? state current
          | return #[]
        reversed := reversed.push current
        current? := data.parent?
  return #[]

private def resourceOnChain
    (state : State) (chain : Array Frame) (proposition : Expr) : Bool :=
  chain.any fun current =>
    match frameData? state current with
    | some data => (data.index.exact.find? proposition).isSome
    | none => false

private def objectOnChain
    (state : State) (chain : Array Frame) (expression type : Expr) : Bool :=
  chain.any fun current =>
    match frameData? state current with
    | none => false
    | some data =>
        data.objects.any fun id =>
          match state.objects[id.index]? with
          | some object =>
              object.expression == expression && object.type == type
          | none => false

private def Session.compilePendingResources
    (session : Session) (parent? : Option Frame)
    (seeds : Array ResourceSeed) :
    MetaM (Array PendingResource × Nat × Nat) := do
  let state ← session.state.get
  let parentChain :=
    match parent? with
    | some parent => frameChain state parent
    | none => #[]
  let mut seen : PHashMap Expr Bool := {}
  let mut result := #[]
  let mut duplicates := 0
  let mut unstable := 0
  for seed in seeds do
    let expansion ← session.expansion seed
    for expanded in expansion do
      let proposition ← instantiateMVars expanded.proposition
      if proposition.hasMVar then
        unstable := unstable + 1
        continue
      let proposition := proposition.consumeMData
      let duplicateParent :=
        resourceOnChain state parentChain proposition
      if duplicateParent || seen.contains proposition then
        duplicates := duplicates + 1
        continue
      seen := seen.insert proposition true
      result := result.push {
        label := expanded.label
        sourceLabel := seed.label
        proof := expanded.proof
        proposition := proposition
        projectionPath := expanded.projectionPath
        origin := seed.origin
        shape := ← session.shape proposition
      }
  return (result, duplicates, unstable)

private def Session.compilePendingObjects
    (session : Session) (parent? : Option Frame)
    (seeds : Array ObjectSeed) :
    MetaM (Array PendingObject) := do
  let state ← session.state.get
  let parentChain :=
    match parent? with
    | some parent => frameChain state parent
    | none => #[]
  let mut seen : PHashMap Expr Bool := {}
  let mut result := #[]
  for seed in seeds do
    let expression ← instantiateMVars seed.expression
    let type ← instantiateMVars seed.type
    if expression.hasMVar || type.hasMVar then
      continue
    let duplicateParent :=
      objectOnChain state parentChain expression type
    if duplicateParent || seen.contains expression then
      continue
    seen := seen.insert expression true
    result := result.push {
      label := seed.label
      expression := expression
      type := type
    }
  return result

/--
从父 frame 增量加入 proof 与对象资源。

父 frame 和兄弟 frame 不会被修改；新增 frame 只保存 delta index。
-/
def Session.extend
    (session : Session) (parent? : Option Frame)
    (proofs : Array ResourceSeed := #[])
    (objects : Array ObjectSeed := #[]) :
    MetaM Frame := do
  let current ← session.state.get
  if current.frames.size >= current.config.maxFrames then
    throwError
      "host proposition analysis exhausted frame budget; frames={current.frames.size}; \
      maxFrames={current.config.maxFrames}"
  let (parentDepth, parentSummary) ←
    match parent? with
    | none => pure (0, ({} : ContextSummary))
    | some parent =>
        match current.frames[parent.id]? with
        | some data => pure (data.depth + 1, data.summary)
        | none =>
            throwError
              "host proposition analysis received an unknown parent frame {parent.id}"
  if parentDepth > current.config.maxFrameDepth then
    throwError
      "host proposition analysis exhausted frame depth; depth={parentDepth}; \
      maxFrameDepth={current.config.maxFrameDepth}"
  let (pendingResources, duplicates, unstable) ←
    session.compilePendingResources parent? proofs
  let pendingObjects ← session.compilePendingObjects parent? objects
  session.state.modifyGet fun state => Id.run do
    let frame : Frame := { id := state.frames.size }
    let mut resources := state.resources
    let mut resourceIds := #[]
    let mut index : DeltaIndex := {}
    for pending in pendingResources do
      let id : ResourceId := { index := resources.size }
      let resource : Resource := {
        id := id
        frame := frame
        label := pending.label
        sourceLabel := pending.sourceLabel
        proof := pending.proof
        proposition := pending.proposition
        projectionPath := pending.projectionPath
        origin := pending.origin
        shape := pending.shape
      }
      resources := resources.push resource
      resourceIds := resourceIds.push id
      index := index.insert resource
    let mut storedObjects := state.objects
    let mut objectIds := #[]
    for pending in pendingObjects do
      let id : ObjectId := { index := storedObjects.size }
      storedObjects := storedObjects.push {
        id := id
        frame := frame
        label := pending.label
        expression := pending.expression
        type := pending.type
      }
      objectIds := objectIds.push id
    let data : FrameData := {
      parent? := parent?
      depth := parentDepth
      resources := resourceIds
      objects := objectIds
      index := index
      summary :=
        parentSummary.addDelta index resourceIds.size objectIds.size <|
          pendingResources.any fun pending =>
            pending.shape.hasLambda ||
              !pending.shape.profile.appliedFVars.isEmpty
    }
    let stats := {
      state.stats with
      frames := state.stats.frames + 1
      resources := state.stats.resources + resourceIds.size
      objects := state.stats.objects + objectIds.size
      duplicateResources := state.stats.duplicateResources + duplicates
      unstableResources := state.stats.unstableResources + unstable
      maxFrameDepth := Nat.max state.stats.maxFrameDepth parentDepth
    }
    (frame, {
      state with
      frames := state.frames.push data
      resources := resources
      objects := storedObjects
      stats := stats
    })

/-- 从当前 Lean 局部上下文收集 proof 与 typed object 种子。 -/
def collectLocalSeeds :
    MetaM (Array ResourceSeed × Array ObjectSeed) := do
  let mut proofs := #[]
  let mut objects := #[]
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet || localDecl.binderInfo.isInstImplicit then
      continue
    let type ← instantiateMVars localDecl.type
    if type.hasMVar then
      continue
    if ← isProp type then
      proofs := proofs.push {
        label := localDecl.userName
        proof := localDecl.toExpr
        origin := .local
      }
    else
      objects := objects.push {
        label := localDecl.userName
        expression := localDecl.toExpr
        type := type
      }
  return (proofs, objects)

/-- 创建一个包含当前 Lean 局部上下文的根 frame。 -/
def Session.fromLocalContext (session : Session) : MetaM Frame := do
  let (proofs, objects) ← collectLocalSeeds
  session.extend none proofs objects

private partial def collectDemands
    (session : Session) (expression : Expr)
    (demands : DemandSet) : MetaM DemandSet := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then
    return demands
  let expression := expression.consumeMData
  let shape ← session.shape expression
  let mut demands := {
    expressions := pushExprUnique demands.expressions expression
    heads :=
      match shape.conclusionHead? with
      | some head => pushExprUnique demands.heads head
      | none => demands.heads
    roots := pushRootUnique demands.roots shape.root
  }
  if expression.isAppOfArity ``And 2 ||
      expression.isAppOfArity ``Or 2 ||
      expression.isAppOfArity ``Iff 2 then
    for argument in expression.getAppArgs do
      demands ← collectDemands session argument demands
  else if expression.isAppOfArity ``Not 1 then
    demands ← collectDemands session expression.getAppArgs[0]! demands
    demands := {
      demands with roots := pushRootUnique demands.roots .falsum
    }
  return demands

private def resourceScore
    (targetShape : Shape) (demands : DemandSet)
    (resource : Resource) : Nat :=
  let shape := resource.shape
  let headScore :=
    match shape.conclusionHead? with
    | some head => if demands.heads.contains head then 200 else 0
    | none => 0
  let rootScore :=
    if demands.roots.contains shape.conclusionRoot then 100 else 0
  let contradictionScore :=
    if targetShape.root == .falsum &&
        shape.conclusionRoot == .falsum then
      500
    else
      0
  contradictionScore + headScore + rootScore +
    Profile.score targetShape.profile shape.profile

private def rankResources
    (state : State) (targetShape : Shape) (demands : DemandSet)
    (ids : Array ResourceId) : Array RankedResource :=
  (ids.map fun id =>
      let score :=
        match state.resources[id.index]? with
        | some resource => resourceScore targetShape demands resource
        | none => 0
      { resource := id, score := score })
    |>.qsort fun left right =>
      if left.score == right.score then
        left.resource.index < right.resource.index
      else
        left.score > right.score

private def collectIndexArray
    (state : State) (chain : Array Frame)
    (select : DeltaIndex → Array ResourceId) :
    Array ResourceId :=
  chain.foldl
    (fun result frame =>
      match frameData? state frame with
      | some data => result ++ select data.index
      | none => result)
    #[]

private def collectResources
    (state : State) (chain : Array Frame) :
    Array ResourceId :=
  chain.foldl
    (fun result frame =>
      match frameData? state frame with
      | some data => result ++ data.resources
      | none => result)
    #[]

private def collectExact
    (state : State) (chain : Array Frame) (target : Expr) :
    Array ResourceId :=
  chain.foldl
    (fun result frame =>
      match frameData? state frame with
      | some data => result ++ (data.index.exact.find? target).getD #[]
      | none => result)
    #[]

private def collectConclusionHead
    (state : State) (chain : Array Frame) (head? : Option Expr) :
    Array ResourceId :=
  match head? with
  | none => #[]
  | some head =>
      chain.foldl
        (fun result frame =>
          match frameData? state frame with
          | some data =>
              result ++ (data.index.conclusionHeads.find? head).getD #[]
          | none => result)
        #[]

private def Session.cachedQuery?
    (session : Session) (key : QueryKey) : IO (Option View) :=
  session.state.modifyGet fun state =>
    let cached? := state.queryCache.find? key
    let stats := {
      state.stats with
      queryLookups := state.stats.queryLookups + 1
      queryHits := state.stats.queryHits + if cached?.isSome then 1 else 0
      queryMisses := state.stats.queryMisses + if cached?.isSome then 0 else 1
    }
    (cached?, { state with stats := stats })

/-- 查询一个 frame 上的目标需求、资源候选与通用策略信号。 -/
def Session.query
    (session : Session) (frame : Frame) (target : Expr) :
    MetaM View := do
  let target ← instantiateMVars target
  if target.hasMVar then
    throwError
      "host proposition analysis cannot query a target containing metavariables"
  let target := target.consumeMData
  let key : QueryKey := { frame := frame, target := target }
  if let some view ← session.cachedQuery? key then
    return view
  let targetShape ← session.shape target
  let demands ← collectDemands session target {}
  let state ← session.state.get
  let chain := frameChain state frame
  if chain.isEmpty then
    throwError "host proposition analysis received an unknown frame {frame.id}"
  let some frameData := frameData? state frame
    | throwError "host proposition analysis received an unknown frame {frame.id}"
  let context := frameData.summary
  let resourceIds := collectResources state chain
  let exact := collectExact state chain target
  let applyIds :=
    collectConclusionHead state chain targetShape.conclusionHead?
  let caseIds := collectIndexArray state chain (·.cases)
  let chooseIds := collectIndexArray state chain (·.choose)
  let forwardIds := collectIndexArray state chain (·.forward)
  let contradictionIds :=
    collectIndexArray state chain (·.contradictionProducers)
  let equalityIds := collectIndexArray state chain (·.equalities)
  let apply := rankResources state targetShape demands applyIds
  let cases := rankResources state targetShape demands caseIds
  let choose := rankResources state targetShape demands chooseIds
  let forward := rankResources state targetShape demands forwardIds
  let contradiction :=
    rankResources state targetShape demands contradictionIds
  let equalities := rankResources state targetShape demands equalityIds
  let higherOrderSurface :=
    targetShape.hasLambda || !targetShape.profile.appliedFVars.isEmpty ||
      context.higherOrderSurface
  let invertibleTarget :=
    targetShape.root == .implication ||
      targetShape.root == .universal ||
      targetShape.root == .conjunction ||
      targetShape.root == .equivalence
  let localProgress :=
    !exact.isEmpty || invertibleTarget ||
      targetShape.constructorCount > 0 || !apply.isEmpty ||
      !cases.isEmpty || !choose.isEmpty ||
      !forward.isEmpty || !contradiction.isEmpty
  let signals : StrategySignals := {
    exactClosure := !exact.isEmpty
    invertibleTarget := invertibleTarget
    constructorTarget := targetShape.constructorCount > 0
    casesAvailable := !cases.isEmpty
    chooseAvailable := !choose.isEmpty
    forwardAvailable := !forward.isEmpty
    contradictionAvailable :=
      targetShape.root == .falsum && !contradiction.isEmpty
    equalityAvailable :=
      targetShape.equalityCount > 0 || !equalities.isEmpty
    higherOrderSurface := higherOrderSurface
    terminalShouldDefer := localProgress
  }
  let view : View := {
    frame := frame
    target := target
    targetShape := targetShape
    context := context
    demands := demands
    resources := resourceIds
    exact := exact
    apply := apply
    cases := cases
    choose := choose
    forward := forward
    contradiction := contradiction
    equalities := equalities
    signals := signals
  }
  session.state.modify fun state =>
    let stats := {
      state.stats with
      queryResourceVisits :=
        state.stats.queryResourceVisits + exact.size + applyIds.size +
          caseIds.size +
          chooseIds.size + forwardIds.size + contradictionIds.size +
          equalityIds.size
    }
    if (state.queryCache.find? key).isSome then
      { state with stats := stats }
    else if state.queryCacheCount < state.config.maxQueries then
      {
        state with
        queryCache := state.queryCache.insert key view
        queryCacheCount := state.queryCacheCount + 1
        stats := stats
      }
    else
      {
        state with
        stats := {
          stats with
          cacheCapacityPrunes := stats.cacheCapacityPrunes + 1
        }
      }
  return view

/-- 按 ID 读取单个资源。 -/
def Session.resource?
    (session : Session) (id : ResourceId) : IO (Option Resource) := do
  return (← session.state.get).resources[id.index]?

/-- 按 ID 读取单个对象。 -/
def Session.object?
    (session : Session) (id : ObjectId) : IO (Option Object) := do
  return (← session.state.get).objects[id.index]?

/-- 按 frame 读取不依赖具体目标的累计上下文属性。 -/
def Session.contextSummary?
    (session : Session) (frame : Frame) : IO (Option ContextSummary) := do
  return (← session.state.get).frames[frame.id]?.map (·.summary)

/-- 当前会话的缓存与 frame 统计快照。 -/
def Session.stats (session : Session) : IO Stats := do
  return (← session.state.get).stats

/-- 当前会话中的 frame、资源、对象和缓存规模。 -/
structure Snapshot where
  frames : Nat
  resources : Nat
  objects : Nat
  shapeCache : Nat
  expansionCache : Nat
  queryCache : Nat
  stats : Stats
deriving Repr

def Session.snapshot (session : Session) : IO Snapshot := do
  let state ← session.state.get
  return {
    frames := state.frames.size
    resources := state.resources.size
    objects := state.objects.size
    shapeCache := state.shapeCacheCount
    expansionCache := state.expansionCacheCount
    queryCache := state.queryCacheCount
    stats := state.stats
  }

/--
验证 frame 拓扑、资源归属与 delta exact index。

这是分析层自检，不替代任何证明证书 checker。
-/
def Session.validateFrame
    (session : Session) (frame : Frame) : IO (Except String Unit) := do
  let state ← session.state.get
  let some _ := state.frames[frame.id]?
    | return .error s!"unknown frame {frame.id}"
  let chain := frameChain state frame
  if chain.isEmpty then
    return .error s!"broken frame chain at {frame.id}"
  let mut expectedSummary : ContextSummary := {}
  let mut expectedDepth := 0
  for current in chain do
    let some data := state.frames[current.id]?
      | return .error s!"missing frame {current.id}"
    if data.depth != expectedDepth then
      return .error
        s!"frame {current.id} has depth {data.depth}, expected {expectedDepth}"
    if let some parent := data.parent? then
      if parent.id >= current.id then
        return .error
          s!"non-topological frame edge {current.id} -> {parent.id}"
    let mut rebuiltIndex : DeltaIndex := {}
    let mut higherOrderSurface := false
    for id in data.resources do
      let some resource := state.resources[id.index]?
        | return .error s!"frame {current.id} references missing resource {id.index}"
      if resource.frame != current then
        return .error
          s!"resource {id.index} belongs to frame {resource.frame.id}, \
          expected {current.id}"
      let exact := (data.index.exact.find? resource.proposition).getD #[]
      unless exact.contains id do
        return .error
          s!"resource {id.index} is missing from its exact index"
      rebuiltIndex := rebuiltIndex.insert resource
      higherOrderSurface :=
        higherOrderSurface || resource.shape.hasLambda ||
          !resource.shape.profile.appliedFVars.isEmpty
    if rebuiltIndex.cases != data.index.cases ||
        rebuiltIndex.choose != data.index.choose ||
        rebuiltIndex.forward != data.index.forward ||
        rebuiltIndex.contradictionProducers != data.index.contradictionProducers ||
        rebuiltIndex.equalities != data.index.equalities ||
        rebuiltIndex.structures != data.index.structures then
      return .error s!"frame {current.id} has inconsistent candidate indexes"
    for id in data.objects do
      let some object := state.objects[id.index]?
        | return .error s!"frame {current.id} references missing object {id.index}"
      if object.frame != current then
        return .error
          s!"object {id.index} belongs to frame {object.frame.id}, \
          expected {current.id}"
    let rebuiltSummary :=
      expectedSummary.addDelta rebuiltIndex data.resources.size data.objects.size
        higherOrderSurface
    if rebuiltSummary != data.summary then
      return .error s!"frame {current.id} has an inconsistent context summary"
    expectedSummary := rebuiltSummary
    expectedDepth := expectedDepth + 1
  return .ok ()

end HostPropAnalysis
end Automation
end YesMetaZFC
