import Lean
import YesMetaZFC.Automation.HostNormalization.CoreRules
import YesMetaZFC.Automation.HostSequent
import YesMetaZFC.Automation.LogicSoundness
import YesMetaZFC.Automation.SourcePreprocessing

/-!
# 新 `prove_auto` 请求层

这一层是后 MF1 的新请求边界。自动化主线直接消费深嵌入
`LogicSoundness.SetLevel.CheckedCertificate` / `CheckedValidCertificate`，不再把浅嵌入
`BridgeResult` 当成默认入口。

当前入口：

* `prove_auto CERT cert`
* `prove_auto VALID cert`
* `prove_auto BACKEND success`
* `prove_auto INTRO`
* `prove_auto FIX x`
* `prove_auto APPLY h`
* `prove_auto INDUCT x`
* `prove_auto SPLIT`
* `prove_auto CASES h`
* `prove_auto CHOOSE h AS x, hx`
* `prove_auto SPECIALIZE h AT (t₁, ..., tₙ)`
* `prove_auto WITNESS t`
* `prove_auto TRANSPORT FROM a TO b BY h`
* `prove_auto PROOF [..., AUTO]`
* `register_prove_auto_sequent_rule theorem PRIORITY n`

搜索器后续应产出上述 checked certificate 对象，或新的 proof-carrying
`BackendSuccess` 对象；tactic 只负责把证书 soundness 交给 Lean 内核闭合当前目标。
-/

namespace YesMetaZFC

open Lean Elab Tactic Meta

namespace Automation
namespace ProveAutoRequest

universe x

private def closeByProof (name : Name) (proof : Expr) : TacticM Unit := do
  closeMainGoal name (← instantiateMVars proof)

/--
`prove_auto` 的 Lean 元层资源作用域。

继承调用点的心跳预算，使搜索、预处理与 CDCL 除了各自的 fuel 和 arena 预算外，
也始终受 Lean 的全局 `maxHeartbeats` 约束。Lean 没有无穷递归深度哨兵，因此只把
递归深度上限提升到实际不可达的范围。
-/
def withProveAutoResources (action : TacticM α) : TacticM α :=
  withTheReader Core.Context
    (fun context =>
      let recursionLimit := Nat.max 1_000_000 context.maxRecDepth
      let options := Lean.maxRecDepth.set context.options recursionLimit
      { context with
        options
        maxRecDepth := recursionLimit })
    action

/-! ## 上下文相关性与 provider 扩展 -/

/--
给高层公式定义指定一个伪类型式的 unfold key。

key 使用层级名字，例如 `setTheory.ordinal.comparison`。上下文收集器只把 key 相等，
或处于同一祖先/后代链上的局部引理视为强相关。
-/
initialize proveAutoUnfoldAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `prove_auto_unfold
    descr := "hierarchical unfold key used by prove_auto context relevance"
    getParam := fun _ stx => do
      let identifier ← Attribute.Builtin.getIdent stx
      pure identifier.getId.eraseMacroScopes
  }

/-- 查询声明携带的 `prove_auto_unfold` key。 -/
def unfoldKey? (env : Environment) (declaration : Name) : Option Name :=
  proveAutoUnfoldAttr.getParam? env declaration

register_option prove_auto.context.maxFacts : Nat := {
  defValue := 16
  descr := "maximum number of strongly relevant local facts collected by prove_auto"
}

initialize registerTraceClass `YesMetaZFC.proveAuto.context
initialize registerTraceClass `YesMetaZFC.proveAuto.proof
initialize registerTraceClass `YesMetaZFC.proveAuto.sequent

namespace ContextRelevance

/-- 一个命题表达式暴露给上下文相关性过滤器的稳定锚点。 -/
structure Profile where
  heads : Array Name := #[]
  propositionFVars : Array FVarId := #[]
  keys : Array Name := #[]

private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private def pushFVarUnique (variables : Array FVarId)
    (fvar : FVarId) : Array FVarId :=
  if variables.contains fvar then variables else variables.push fvar

/-- 合并相关性锚点并保持首次出现顺序。 -/
def Profile.merge (left right : Profile) : Profile := {
  heads := right.heads.foldl pushNameUnique left.heads
  propositionFVars :=
    right.propositionFVars.foldl pushFVarUnique left.propositionFVars
  keys := right.keys.foldl pushNameUnique left.keys
}

private def ignoredHead (name : Name) : Bool :=
  name == ``False || name == ``True || name == ``Not ||
    name == ``And || name == ``Or || name == ``Iff ||
    name == ``Eq || name == ``Exists

private partial def collectAux (env : Environment)
    (expression : Expr) (fuel : Nat) (forceFVar : Bool)
    (visited : Array Name) (profile : Profile) :
    MetaM (Array Name × Profile) := do
  if fuel == 0 then
    return (visited, profile)
  let expression := expression.consumeMData
  let mut visited := visited
  let mut profile := profile
  match expression.getAppFn with
  | .const declaration _ =>
      if !ignoredHead declaration then
        profile := {
          profile with
          heads := pushNameUnique profile.heads declaration
        }
      if let some key := unfoldKey? env declaration then
        profile := {
          profile with
          keys := pushNameUnique profile.keys key
        }
        if !visited.contains declaration then
          visited := visited.push declaration
          if let some unfolded ← unfoldDefinition? expression true then
            (visited, profile) ←
              collectAux env unfolded (fuel - 1) forceFVar visited profile
  | .fvar fvar =>
      if expression.isApp then
        profile := {
          profile with
          propositionFVars :=
            pushFVarUnique profile.propositionFVars fvar
        }
  | _ =>
      pure ()
  match expression with
  | .fvar fvar =>
      if forceFVar || (← isProp expression) then
        profile := {
          profile with
          propositionFVars :=
            pushFVarUnique profile.propositionFVars fvar
        }
      return (visited, profile)
  | .forallE _ domain body _ =>
      (visited, profile) ←
        collectAux env domain (fuel - 1) false visited profile
      collectAux env body (fuel - 1) false visited profile
  | .lam _ domain body _ =>
      (visited, profile) ←
        collectAux env domain (fuel - 1) false visited profile
      collectAux env body (fuel - 1) false visited profile
  | .letE _ type value body _ =>
      (visited, profile) ←
        collectAux env type (fuel - 1) false visited profile
      (visited, profile) ←
        collectAux env value (fuel - 1) false visited profile
      collectAux env body (fuel - 1) false visited profile
  | .proj _ _ body =>
      collectAux env body (fuel - 1) forceFVar visited profile
  | _ =>
      let equalitySides :=
        expression.getAppFn.constName? == some ``Eq
      expression.getAppArgs.foldlM
        (init := (visited, profile)) fun state argument =>
          collectAux env argument (fuel - 1) equalitySides
            state.1 state.2

/-- 收集目标头、量词体、等式两侧与层级 unfold key。 -/
def collect (expression : Expr) : MetaM Profile := do
  let expression ← instantiateMVars expression
  let env ← getEnv
  return (← collectAux env expression 64 false #[] {}).2

/-- 只收集表达式中的层级 unfold key。 -/
def collectUnfoldKeys (expression : Expr) : MetaM (Array Name) := do
  return (← collect expression).keys

private def keyScore (target candidate : Name) : Nat :=
  if target == candidate then
    3
  else if target.isPrefixOf candidate then
    2
  else if candidate.isPrefixOf target then
    1
  else
    0

/-- 两组层级 key 的最强祖先/后代相关性。 -/
def unfoldScore (targetKeys candidateKeys : Array Name) : Nat :=
  targetKeys.foldl
    (fun best target =>
      candidateKeys.foldl
        (fun best candidate => Nat.max best (keyScore target candidate))
        best)
    0

private def sharedNameCount (left right : Array Name) : Nat :=
  left.foldl
    (fun count name => if right.contains name then count + 1 else count)
    0

private def sharedFVarCount (left right : Array FVarId) : Nat :=
  left.foldl
    (fun count fvar =>
      if right.contains fvar then count + 1 else count)
    0

/--
相关性分数优先层级 unfold key，其次命题自由变量，最后公式/项头。

逻辑连接词和等词本身不作为头；等式两侧的真实函数、谓词和局部函数变量会进入锚点。
-/
def score (target candidate : Profile) : Nat :=
  unfoldScore target.keys candidate.keys * 100 +
    sharedFVarCount target.propositionFVars candidate.propositionFVars * 20 +
    sharedNameCount target.heads candidate.heads * 5

/--
结构 proposition 的类型参数通常覆盖许多无关命题变量，不能借此挤占叶字段。
只有层级 key 或结构头本身被目标/已选规则引用时，结构 proof 才获得高相关性。
-/
def structureScore (target candidate : Profile) : Nat :=
  unfoldScore target.keys candidate.keys * 100 +
    sharedNameCount target.heads candidate.heads * 50

end ContextRelevance

/--
一个上下文闭合入口消费的原始请求。

`useFacts` 只保存用户或结构 proof 节点显式给出的 proof term。局部候选扫描、相关性
选择和最终 checked facts 都在统一准备阶段完成，避免每个 provider 重复展开同一事实面。
-/
structure ContextRequest where
  goal : Expr
  useFacts : Array Expr := #[]

/-- provider 消费通用相关事实，或完全自行管理其上下文来源。 -/
inductive ContextPreparation where
  | relevantFacts
  | providerManaged
deriving BEq, Repr

/-- provider 可接受全部请求，或只接受含宿主对象语法的通用事实请求。 -/
inductive ContextProviderRequirement where
  | any
  | hostObjectSyntax
deriving BEq, Repr

/-- 一个已经展开并完成相关性 profile 的局部 proof 候选。 -/
structure ContextCandidate where
  label : Name
  proposition : Expr
  proof : Expr
  profile : ContextRelevance.Profile
  isStructure : Bool

/-- 相继式前端用于索引定向 APPLY 的稳定结论头。 -/
inductive HostSequentConclusionHead where
  | const (declaration : Name)
  | fvar (fvarId : FVarId)
  | sort (level : Level)
  | lit (literal : Literal)
deriving BEq, Repr

private def hostSequentConclusionHead? (expression : Expr) :
    Option HostSequentConclusionHead :=
  match expression.consumeMData.getAppFn with
  | .const declaration _ => some (.const declaration)
  | .fvar fvarId => some (.fvar fvarId)
  | .sort level => some (.sort level)
  | .lit literal => some (.lit literal)
  | _ => none

/--
注册规则优先保留结论的表面声明头。

可约的命名命题若先 `whnf`，会退化成 `And`、`Forall` 等逻辑头，使精确规则无法在
结构分解前命中。表面没有稳定常量头时才回落到规约后的结论头。
-/
def registeredHostSequentConclusionHead?
    (proposition : Expr) : MetaM (Option Name) := do
  let savedState ← saveState
  try
    let (_, _, conclusion) ←
      forallMetaTelescope proposition
    let conclusion ← instantiateMVars conclusion
    let result ←
      match hostSequentConclusionHead? conclusion with
      | some (.const declaration) =>
          pure (some declaration)
      | _ =>
          let conclusion ← whnf conclusion
          pure <|
            match hostSequentConclusionHead? conclusion with
            | some (.const declaration) => some declaration
            | _ => none
    savedState.restore
    return result
  catch error =>
    savedState.restore
    throw error

/--
提取注册规则显式命题前提的稳定结论头。

该信息在声明注册时只计算一次，节点准备时先做廉价全覆盖过滤；没有稳定声明头的
高阶前提留给后续完整统一检查，避免以近似索引损失能力。
-/
private def registeredHostSequentPremiseHeads
    (proposition : Expr) : MetaM (Array Name) := do
  let savedState ← saveState
  let heads ←
    try
      let (arguments, binderInfos, _) ←
        forallMetaTelescopeReducing proposition
      let mut heads := #[]
      for index in [0 : arguments.size] do
        let binderInfo := binderInfos[index]!
        if binderInfo.isInstImplicit || !binderInfo.isExplicit then
          continue
        let domain ← instantiateMVars (← inferType arguments[index]!)
        unless ← isProp domain do
          continue
        if let some head ← registeredHostSequentConclusionHead? domain then
          unless heads.contains head do
            heads := heads.push head
      pure heads
    catch _ =>
      pure #[]
  savedState.restore
  return heads

/-- 单个 proof proposition 的相继式形状，只在索引构造时计算一次。 -/
private structure HostSequentPropositionShape where
  conclusionHead? : Option HostSequentConclusionHead := none
  objectBinders : Nat := 0
  explicitPropPremises : Nat := 0
  hasInstanceBinder : Bool := false
  hasImplicitPropPremise : Bool := false
  rootIsExists : Bool := false
  rootIsEq : Bool := false
  rootIsHEq : Bool := false

private def analyzeHostSequentProposition
    (proposition : Expr) : MetaM HostSequentPropositionShape := do
  let savedState ← saveState
  try
    let root ← whnf proposition
    let (arguments, binderInfos, conclusion) ←
      forallMetaTelescopeReducing proposition
    let mut explicitPropPremises := 0
    let mut objectBinders := 0
    let mut hasInstanceBinder := false
    let mut hasImplicitPropPremise := false
    for index in [0 : arguments.size] do
      let binderInfo := binderInfos[index]!
      hasInstanceBinder := hasInstanceBinder || binderInfo.isInstImplicit
      let argumentType ← instantiateMVars (← inferType arguments[index]!)
      if ← isProp argumentType then
        if binderInfo.isExplicit then
          explicitPropPremises := explicitPropPremises + 1
        else
          hasImplicitPropPremise := true
      else
        objectBinders := objectBinders + 1
    let conclusion ← whnf (← instantiateMVars conclusion)
    let shape : HostSequentPropositionShape := {
      conclusionHead? := hostSequentConclusionHead? conclusion
      objectBinders := objectBinders
      explicitPropPremises := explicitPropPremises
      hasInstanceBinder := hasInstanceBinder
      hasImplicitPropPremise := hasImplicitPropPremise
      rootIsExists := root.isAppOfArity ``Exists 2
      rootIsEq := root.isAppOfArity ``Eq 3
      rootIsHEq := root.isAppOfArity ``HEq 4
    }
    savedState.restore
    return shape
  catch error =>
    savedState.restore
    throw error

/-- 显式注册的声明级相继式规则；只保存可审计的定向索引信息。 -/
structure RegisteredHostSequentRule where
  declaration : Name
  rank : Nat
  conclusionHead : Name
  premiseHeads : Array Name := #[]
  profile : ContextRelevance.Profile

private def insertRegisteredHostSequentRule
    (index : NameMap (Array RegisteredHostSequentRule))
    (rule : RegisteredHostSequentRule) :
    NameMap (Array RegisteredHostSequentRule) :=
  let bucket := index.find? rule.conclusionHead |>.getD #[]
  if bucket.any fun existing => existing.declaration == rule.declaration then
    index
  else
    index.insert rule.conclusionHead (bucket.push rule)

private def flattenRegisteredHostSequentRules
    (index : NameMap (Array RegisteredHostSequentRule)) :
    Array RegisteredHostSequentRule :=
  index.foldl (fun rules _ bucket => rules ++ bucket) #[]

initialize hostSequentRuleExtension :
    PersistentEnvExtension
      RegisteredHostSequentRule RegisteredHostSequentRule
      (NameMap (Array RegisteredHostSequentRule)) ←
  registerPersistentEnvExtension {
    name := `YesMetaZFC.Automation.ProveAutoRequest.hostSequentRuleExtension
    mkInitial := pure {}
    addImportedFn := fun imported =>
      pure <| imported.foldl
        (fun index entries =>
          entries.foldl insertRegisteredHostSequentRule index) {}
    addEntryFn := insertRegisteredHostSequentRule
    exportEntriesFn := flattenRegisteredHostSequentRules
    statsFn := fun index =>
      s!"prove_auto registered sequent heads: {index.size}"
  }

/-- 按当前目标的稳定结论头读取已注册相继式规则，并按 rank 稳定排序。 -/
def registeredHostSequentRulesForTarget
    (target : Expr) : MetaM (Array RegisteredHostSequentRule) := do
  let target ← instantiateMVars target
  let mut targetHeads := #[]
  if let some (.const targetHead) := hostSequentConclusionHead? target then
    targetHeads := targetHeads.push targetHead
  let reduced ← whnf target
  if let some (.const targetHead) := hostSequentConclusionHead? reduced then
    unless targetHeads.contains targetHead do
      targetHeads := targetHeads.push targetHead
  let index := hostSequentRuleExtension.getState (← getEnv)
  let mut registered := #[]
  for targetHead in targetHeads do
    for rule in index.find? targetHead |>.getD #[] do
      unless registered.any fun existing =>
          existing.declaration == rule.declaration do
        registered := registered.push rule
  pure <|
    (registered.mapIdx fun position rule => (position, rule))
      |>.qsort (fun left right =>
        if left.2.rank == right.2.rank then
          left.1 < right.1
        else
          left.2.rank > right.2.rank)
      |>.map (·.2)

/--
按稳定结论头读取可用于前向实例化的声明规则。

调用者仍须用当前显式 proof 池完整确定所有命题前提；这里只提供已注册桶的稳定顺序。
-/
def registeredHostSequentRulesForConclusionHead
    (conclusionHead : Name) :
    MetaM (Array RegisteredHostSequentRule) := do
  let index := hostSequentRuleExtension.getState (← getEnv)
  let registered := index.find? conclusionHead |>.getD #[]
  pure <|
    (registered.mapIdx fun position rule => (position, rule))
      |>.qsort (fun left right =>
        if left.2.rank == right.2.rank then
          left.1 < right.1
        else
          left.2.rank > right.2.rank)
      |>.map (·.2)

private def registeredHostSequentRule
    (declaration : Name) (ruleRank : Nat) :
    MetaM RegisteredHostSequentRule := do
  let some declarationInfo := (← getEnv).find? declaration
    | throwError "unknown declaration `{declaration}`"
  unless declarationInfo.isTheorem do
    throwError
      "prove_auto sequent rule `{declaration}` must be a theorem declaration"
  let proof ← mkConstWithFreshMVarLevels declaration
  let proposition ← instantiateMVars (← inferType proof)
  let shape ← analyzeHostSequentProposition proposition
  if shape.explicitPropPremises == 0 then
    throwError
      "prove_auto sequent rule `{declaration}` has no explicit proposition premise; \
      direct closure rules belong in checked AUTO facts"
  if shape.hasInstanceBinder then
    throwError
      "prove_auto sequent rule `{declaration}` has a typeclass binder; \
      register an explicitly instantiated theorem instead"
  if shape.hasImplicitPropPremise then
    throwError
      "prove_auto sequent rule `{declaration}` has an implicit proof premise; \
      sequent premises must be explicit checked leaves"
  let some conclusionHead ←
      registeredHostSequentConclusionHead? proposition
    | throwError
        "prove_auto sequent rule `{declaration}` needs a stable declaration head \
        in its conclusion"
  return {
    declaration := declaration
    rank := ruleRank
    conclusionHead := conclusionHead
    premiseHeads := ← registeredHostSequentPremiseHeads proposition
    profile := ← ContextRelevance.collect proposition
  }

syntax (name := registerProveAutoSequentRule)
  "register_prove_auto_sequent_rule " ident : command
syntax (name := registerProveAutoSequentRulePriority)
  "register_prove_auto_sequent_rule " ident " PRIORITY " num : command

private def registerHostSequentRuleCommand
    (identifier : Ident) (ruleRank : Nat) :
    Lean.Elab.Command.CommandElabM Unit := do
  let declaration ← resolveGlobalConstNoOverload identifier
  let rule ← Lean.Elab.Command.liftTermElabM <|
    registeredHostSequentRule declaration ruleRank
  let current := hostSequentRuleExtension.getState (← getEnv)
  let duplicate :=
    current.find? rule.conclusionHead |>.getD #[]
      |>.any fun existing => existing.declaration == declaration
  if duplicate then
    throwErrorAt identifier
      "prove_auto sequent rule `{declaration}` is already registered"
  modifyEnv fun env =>
    hostSequentRuleExtension.addEntry env rule

elab_rules : command
  | `(register_prove_auto_sequent_rule $rule:ident) =>
      registerHostSequentRuleCommand rule 100
  | `(register_prove_auto_sequent_rule $rule:ident PRIORITY $rank:num) =>
      registerHostSequentRuleCommand rule rank.getNat

/--
按需二元合取生成器。

这类声明必须以两个显式对象参数生成
`∃ generated, ∀ value, relation value generated ↔ left value ∧ right value`。
注册项不进入普通候选池，只在相继式已经提出对应 overlap demand 后实例化。
-/
structure RegisteredHostSequentBinaryConjunctionGenerator where
  declaration : Name
  rank : Nat
  leftPosition : Nat
  rightPosition : Nat

private def insertRegisteredHostSequentBinaryConjunctionGenerator
    (generators : Array RegisteredHostSequentBinaryConjunctionGenerator)
    (generator : RegisteredHostSequentBinaryConjunctionGenerator) :
    Array RegisteredHostSequentBinaryConjunctionGenerator :=
  if generators.any fun existing =>
      existing.declaration == generator.declaration then
    generators
  else
    generators.push generator

initialize hostSequentBinaryConjunctionGeneratorExtension :
    PersistentEnvExtension
      RegisteredHostSequentBinaryConjunctionGenerator
      RegisteredHostSequentBinaryConjunctionGenerator
      (Array RegisteredHostSequentBinaryConjunctionGenerator) ←
  registerPersistentEnvExtension {
    name :=
      `YesMetaZFC.Automation.ProveAutoRequest.hostSequentBinaryConjunctionGeneratorExtension
    mkInitial := pure #[]
    addImportedFn := fun imported =>
      pure <| imported.foldl
        (fun generators entries =>
          entries.foldl
            insertRegisteredHostSequentBinaryConjunctionGenerator generators)
        #[]
    addEntryFn := insertRegisteredHostSequentBinaryConjunctionGenerator
    exportEntriesFn := id
    statsFn := fun generators =>
      s!"prove_auto binary conjunction generators: {generators.size}"
  }

private def validateBinaryConjunctionGeneratorConclusion
    (declaration : Name) (conclusion : Expr) : MetaM Unit := do
  let conclusion ← whnf conclusion
  unless conclusion.isAppOfArity ``Exists 2 do
    throwError
      "prove_auto binary conjunction generator `{declaration}` must conclude with Exists"
  let generatedPredicate := conclusion.getAppArgs[1]!
  let (_, _, generatedBody) ← lambdaMetaTelescope generatedPredicate (some 1)
  let (_, _, generatedBody) ←
    forallMetaTelescopeReducing generatedBody (some 1)
  let generatedBody ← whnf generatedBody
  unless generatedBody.isAppOfArity ``Iff 2 do
    throwError
      "prove_auto binary conjunction generator `{declaration}` must expose an Iff definition"
  let right := generatedBody.getAppArgs[1]!
  let right ← whnf right
  unless right.isAppOfArity ``And 2 do
    throwError
      "prove_auto binary conjunction generator `{declaration}` must define a binary conjunction"

private def registeredHostSequentBinaryConjunctionGenerator
    (declaration : Name) (rank : Nat) :
    MetaM RegisteredHostSequentBinaryConjunctionGenerator := do
  let some declarationInfo := (← getEnv).find? declaration
    | throwError "unknown declaration `{declaration}`"
  unless declarationInfo.isTheorem do
    throwError
      "prove_auto binary conjunction generator `{declaration}` must be a theorem"
  let proof ← mkConstWithFreshMVarLevels declaration
  let proposition ← instantiateMVars (← inferType proof)
  let (arguments, binderInfos, conclusion) ←
    forallMetaTelescopeReducing proposition
  let mut objectPositions := #[]
  for index in [0 : arguments.size] do
    let binderInfo := binderInfos[index]!
    if binderInfo.isInstImplicit then
      throwError
        "prove_auto binary conjunction generator `{declaration}` cannot use typeclass binders"
    if binderInfo.isExplicit then
      let argumentType ← instantiateMVars (← inferType arguments[index]!)
      unless ← isProp argumentType do
        objectPositions := objectPositions.push index
  unless objectPositions.size == 2 do
    throwError
      "prove_auto binary conjunction generator `{declaration}` needs exactly two explicit object parameters"
  validateBinaryConjunctionGeneratorConclusion declaration conclusion
  return {
    declaration
    rank
    leftPosition := objectPositions[0]!
    rightPosition := objectPositions[1]!
  }

syntax (name := registerProveAutoBinaryConjunctionGenerator)
  "register_prove_auto_binary_conjunction_generator " ident : command
syntax (name := registerProveAutoBinaryConjunctionGeneratorPriority)
  "register_prove_auto_binary_conjunction_generator " ident " PRIORITY " num : command

private def registerHostSequentBinaryConjunctionGeneratorCommand
    (identifier : Ident) (rank : Nat) :
    Lean.Elab.Command.CommandElabM Unit := do
  let declaration ← resolveGlobalConstNoOverload identifier
  let generator ← Lean.Elab.Command.liftTermElabM <|
    registeredHostSequentBinaryConjunctionGenerator declaration rank
  let current :=
    hostSequentBinaryConjunctionGeneratorExtension.getState (← getEnv)
  if current.any fun existing => existing.declaration == declaration then
    throwErrorAt identifier
      "prove_auto binary conjunction generator `{declaration}` is already registered"
  modifyEnv fun env =>
    hostSequentBinaryConjunctionGeneratorExtension.addEntry env generator

elab_rules : command
  | `(register_prove_auto_binary_conjunction_generator $generator:ident) =>
      registerHostSequentBinaryConjunctionGeneratorCommand generator 100
  | `(register_prove_auto_binary_conjunction_generator
        $generator:ident PRIORITY $rank:num) =>
      registerHostSequentBinaryConjunctionGeneratorCommand generator rank.getNat

/-- 稳定读取按需二元合取生成器；普通相继式候选索引不会调用此接口。 -/
def registeredHostSequentBinaryConjunctionGenerators :
    CoreM (Array RegisteredHostSequentBinaryConjunctionGenerator) := do
  let generators :=
    hostSequentBinaryConjunctionGeneratorExtension.getState (← getEnv)
  pure <|
    (generators.mapIdx fun position generator => (position, generator))
      |>.qsort (fun left right =>
        if left.2.rank == right.2.rank then
          left.1 < right.1
        else
          left.2.rank > right.2.rank)
      |>.map (·.2)

/--
用两个已确定对象和局部 proof 资源实例化一个按需生成器。

对象位置由注册时的形状检查固定；命题参数只允许由当前 proof 资源精确填充。
-/
def instantiateHostSequentBinaryConjunctionGenerator?
    (generator : RegisteredHostSequentBinaryConjunctionGenerator)
    (left right : Expr) (resources : Array FVarId) :
    MetaM (Option Expr) := do
  let savedState ← saveState
  let result? ←
    try
      let proof ← mkConstWithFreshMVarLevels generator.declaration
      let proposition ← instantiateMVars (← inferType proof)
      let (arguments, binderInfos, _) ←
        forallMetaTelescopeReducing proposition
      if generator.leftPosition >= arguments.size ||
          generator.rightPosition >= arguments.size then
        pure none
      else
        unless ← isDefEq arguments[generator.leftPosition]! left do
          throwError "left generator argument does not match"
        unless ← isDefEq arguments[generator.rightPosition]! right do
          throwError "right generator argument does not match"
        let mut complete := true
        for index in [0 : arguments.size] do
          let argument := arguments[index]!
          let argumentId := argument.mvarId!
          if ← argumentId.isAssigned then
            continue
          let argumentType ← instantiateMVars (← inferType argument)
          if !(← isProp argumentType) || !binderInfos[index]!.isExplicit then
            complete := false
            break
          let mut assigned := false
          for resource in resources do
            let resourceState ← saveState
            let resourceType ← instantiateMVars (← resource.getType)
            if ← isDefEq argumentType resourceType then
              argumentId.assign (mkFVar resource)
              assigned := true
              break
            resourceState.restore
          unless assigned do
            complete := false
            break
        if !complete then
          pure none
        else
          let application ← instantiateMVars (mkAppN proof arguments)
          if !(← getMVarsNoDelayed application).isEmpty then
            pure none
          else
            pure (some application)
    catch _ =>
      pure none
  let result? ← result?.mapM instantiateMVars
  savedState.restore
  return result?

/-- 单次通用上下文准备的可观测计数。 -/
structure ContextPreparationStats where
  explicitRaw : Nat := 0
  explicitExpanded : Nat := 0
  localCandidates : Nat := 0
  contextSelected : Nat := 0
  contextRejected : Nat := 0
  totalFacts : Nat := 0
  terminalPropositions : Nat := 0
deriving Repr

/-- provider 共享的 proof-free terminal 快照。 -/
structure ContextTerminalSnapshot where
  factPropositions : Array Expr := #[]
  hasHostObjectSyntax : Bool := false

/-- 失败时才渲染的上下文资源摘要。 -/
structure ContextResourceSummary where
  present : Bool := false
  providerManaged : Bool := false
  explicitRaw : Nat := 0
  explicitExpanded : Nat := 0
  selected : Array Name := #[]
  rejected : Nat := 0

def ContextResourceSummary.render (summary : ContextResourceSummary) : String :=
  if summary.providerManaged then
    s!"provider-managed; explicitRaw={summary.explicitRaw}"
  else
    s!"explicit={summary.explicitExpanded}; explicitRaw={summary.explicitRaw}; " ++
      s!"auto={summary.selected.size}; selected={summary.selected}; " ++
      s!"rejected={summary.rejected}"

/--
同一叶子上供所有通用 provider 共享的准备结果。

`facts` 是 provider 实际送入 checked source 的唯一事实面；`candidates` 保留相继式
前端选择 APPLY/CASES 等规则需要的 proof-carrying 候选及其相关性 profile。
-/
structure PreparedContextRequest where
  goal : Expr
  useFacts : Array Expr := #[]
  facts : Array Expr := #[]
  candidates : Array ContextCandidate := #[]
  goalProfile : ContextRelevance.Profile := {}
  terminal : ContextTerminalSnapshot := {}
  resourceSummary : ContextResourceSummary := {}
  stats : ContextPreparationStats := {}

/-- 相继式候选来自局部 proof 或显式注册的声明规则。 -/
inductive HostSequentCandidateOrigin where
  | local
  | registered
deriving BEq, Repr

/-- 当前目标桶中的单个定向候选。 -/
structure IndexedHostSequentCandidate where
  candidate : ContextCandidate
  relevance : Nat
  rank : Nat := 0
  origin : HostSequentCandidateOrigin := .local

/-- 局部归纳命题 proof 的有限 CASES 描述符；不持有 proof 或 Meta 状态。 -/
structure HostSequentCasesDescriptor where
  inductiveName : Name
  constructors : Array Name
  expectedBranches : Nat
  deriving Repr

/-- 已通过有限 CASES 准入的局部 proof 候选。 -/
structure IndexedHostSequentCases where
  descriptor : HostSequentCasesDescriptor
  candidate : ContextCandidate
  unlockScore : Nat := 0
  preserveForForward : Bool := false
  relevance : Nat

/-- 当前目标归纳命题的一个 proof-free 构造子描述符。 -/
structure HostSequentConstructorDescriptor where
  inductiveName : Name
  constructorName : Name
  position : Nat
  deriving Repr

/-- 目标唯一确定全部对象参数的局部全称 proof。 -/
structure IndexedHostSequentSpecialization where
  candidate : ContextCandidate
  arguments : Array Expr
  relevance : Nat

/-- 一个可确定执行的前向事实描述符；只保存命题与参数布局。 -/
structure HostSequentForwardDescriptor where
  sourceLabel : Name
  objectArguments : Nat
  propositionPremises : Nat
  result : Expr
  deriving Repr

/-- 已由当前 typed object/proof pool 完整实例化的前向候选。 -/
structure IndexedHostSequentForward where
  descriptor : HostSequentForwardDescriptor
  candidate : ContextCandidate
  arguments : Array Expr
  premises : Array Expr
  closesTarget : Bool := false
  demandScore : Nat
  weight : Nat
  age : Nat
  relevance : Nat

/-- 存在目标的一个 proof-free typed witness 描述符。 -/
structure HostSequentWitnessDescriptor where
  label : Name
  position : Nat := 0
  witnessType : Expr
  witness : Expr
  instanceProposition : Expr
  deriving Repr

/-- 已按稳定来源顺序接纳的存在见证；source 只提供已有实例 proof。 -/
structure IndexedHostSequentWitness where
  descriptor : HostSequentWitnessDescriptor
  support : Option ContextCandidate := none
  relevance : Nat

/--
一个已事务验证的有限反证计划。

描述符只保存当前局部上下文中的既有对象/FVar 及环境声明名；执行时重新构造 APPLY、
WITNESS 和 CONSTRUCTOR proof，不保存预检产生的 metavariable 或 SavedState。
-/
structure HostSequentContradictionDescriptor where
  witnessLabel : Name
  witness : Expr
  constructorName : Name
  initialResources : Array FVarId
  expectedChildren : Nat

/-- 已通过严格有限反证准入的局部 producer。 -/
structure IndexedHostSequentContradiction where
  producer : ContextCandidate
  descriptor : HostSequentContradictionDescriptor
  relevance : Nat

/-- 唯一等式方向及改写后精确匹配的 proof-carrying 事实。 -/
structure IndexedHostSequentTransport where
  equality : ContextCandidate
  support : ContextCandidate
  source : Expr
  destination : Expr
  reverseProof : Bool
  relevance : Nat

/--
聚焦相继式单叶消费的安全分支索引。

索引只在当前叶子内使用；其中的 proof/FVar 不得跨上下文缓存。
-/
structure HostSequentBranchIndex where
  choose : Array IndexedHostSequentCandidate := #[]
  specialize : Array IndexedHostSequentSpecialization := #[]
  forward : Array IndexedHostSequentForward := #[]
  witness : Array IndexedHostSequentWitness := #[]
  transport : Array IndexedHostSequentTransport := #[]
  cases : Array IndexedHostSequentCases := #[]
  constructors : Array HostSequentConstructorDescriptor := #[]
  contradictions : Array IndexedHostSequentContradiction := #[]

private structure HostSequentTransportTarget where
  source : Expr
  destination : Expr
  rewritten : Expr
  reverseProof : Bool

private structure HostSequentTransportDiscovery where
  rules : Array IndexedHostSequentTransport := #[]
  directedElaborations : Nat := 0
  directedAmbiguities : Nat := 0

/-- 每叶 相继式索引构造的可观测工作量。 -/
structure HostSequentCandidateIndexStats where
  candidateElaborations : Nat := 0
  candidateFilters : Nat := 0
  indexHits : Nat := 0
  indexMisses : Nat := 0
  registeredCandidates : Nat := 0
  registeredPremisePrunes : Nat := 0
  directedElaborations : Nat := 0
  directedAmbiguities : Nat := 0
  casesDescriptorCandidates : Nat := 0
  casesDescriptorHits : Nat := 0
  casesDescriptorMisses : Nat := 0
  forwardDescriptorCandidates : Nat := 0
  forwardDescriptorHits : Nat := 0
  forwardDescriptorMisses : Nat := 0
  forwardDuplicatePrunes : Nat := 0
  forwardAmbiguities : Nat := 0
  forwardBudgetPrunes : Nat := 0
  witnessDescriptorCandidates : Nat := 0
  witnessDescriptorHits : Nat := 0
  witnessDescriptorMisses : Nat := 0
  witnessDuplicatePrunes : Nat := 0
  witnessBudgetPrunes : Nat := 0
  constructorCandidates : Nat := 0
deriving Repr

/-- 已按当前目标头和相关性收缩的 相继式候选桶。 -/
structure HostSequentCandidateIndex where
  apply : Array IndexedHostSequentCandidate := #[]
  cases : Array IndexedHostSequentCases := #[]
  choose : Array IndexedHostSequentCandidate := #[]
  specialize : Array IndexedHostSequentSpecialization := #[]
  forward : Array IndexedHostSequentForward := #[]
  witness : Array IndexedHostSequentWitness := #[]
  transport : Array IndexedHostSequentTransport := #[]
  constructors : Array HostSequentConstructorDescriptor := #[]
  stats : HostSequentCandidateIndexStats := {}

/-- 通用 checked 请求与其按需 相继式索引的单叶共享边界。 -/
structure PreparedHostSequentContext where
  request : PreparedContextRequest
  index : HostSequentCandidateIndex

/--
一个可插拔的上下文请求构造器。

`.relevantFacts` provider 共享同一 `PreparedContextRequest`；`.providerManaged` provider
只接收原始目标和显式资源，自行构造专用上下文。两类 provider 都只能返回
proof-carrying `GoalAttempt`，不能直接生成当前目标的证明项。
-/
structure ContextProvider where
  priority : Nat := 0
  preparation : ContextPreparation := .relevantFacts
  requirement : ContextProviderRequirement := .any
  build? : PreparedContextRequest → MetaM (Option Expr)

private def pushNameUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

initialize contextProviderExtension :
    PersistentEnvExtension Name Name (Array Name) ←
  registerPersistentEnvExtension {
    name := `YesMetaZFC.Automation.ProveAutoRequest.contextProviderExtension
    mkInitial := pure #[]
    addImportedFn := fun imported =>
      pure <| imported.foldl
        (fun providers entries =>
          entries.foldl pushNameUnique providers) #[]
    addEntryFn := pushNameUnique
    exportEntriesFn := id
    statsFn := fun providers =>
      s!"prove_auto context providers: {providers.size}"
  }

/-- 注册一个 `ContextProvider` 声明。 -/
syntax (name := registerProveAutoContextProvider)
  "register_prove_auto_context_provider " ident : command

elab_rules : command
  | `(register_prove_auto_context_provider $provider:ident) => do
      let providerName ← resolveGlobalConstNoOverload provider
      let providerType ← Lean.Elab.Command.liftTermElabM <|
        inferType (mkConst providerName)
      let expectedType := mkConst ``ContextProvider
      unless ← Lean.Elab.Command.liftTermElabM <|
          isDefEq providerType expectedType do
        throwErrorAt provider
          "context provider `{providerName}` has type{indentExpr providerType}, \
          expected `{expectedType}`"
      modifyEnv fun env =>
        contextProviderExtension.addEntry env providerName

private structure ProofExpansionState where
  propositions : Array Expr := #[]
  proofs : Array Expr := #[]

private abbrev ProofExpansionM := StateRefT ProofExpansionState MetaM

private def registerProofResource (proof : Expr) :
    ProofExpansionM Bool := do
  let proposition ← instantiateMVars (← inferType proof)
  unless ← isProp proposition do
    throwError
      "prove_auto expected a proof resource, but got{indentExpr proposition}"
  let state ← get
  if state.propositions.any fun seen => seen == proposition then
    return false
  set (show ProofExpansionState from {
    propositions := state.propositions.push proposition
    proofs := state.proofs.push proof
  })
  return true

private partial def expandProofResource (proof : Expr) :
    ProofExpansionM Unit := do
  unless ← registerProofResource proof do
    return
  let proposition ← instantiateMVars (← inferType proof)
  let reduced ← whnf proposition
  let .const structureName _ := reduced.getAppFn
    | return
  let some structureInfo := getStructureInfo? (← getEnv) structureName
    | return
  for fieldName in structureInfo.fieldNames do
    let projection ← mkProjection proof fieldName
    let projectionType ← instantiateMVars (← inferType projection)
    if ← isProp projectionType then
      expandProofResource projection

/--
递归展开 proof-valued 结构字段，并按命题去重。

显式 `USE` 与自动局部上下文必须共用这个入口，避免两种资源看到不同的结构表面。
-/
def expandProofResources (proofs : Array Expr) : MetaM (Array Expr) := do
  let (_, state) ←
    (proofs.forM expandProofResource).run {}
  return state.proofs

private def propositionIsStructure (proposition : Expr) : MetaM Bool := do
  let reduced ← whnf proposition
  let .const structureName _ := reduced.getAppFn
    | return false
  return (getStructureInfo? (← getEnv) structureName).isSome

private def proofResourceLabel (origin : Name) (proof : Expr) : MetaM Name := do
  match proof.consumeMData with
  | .proj structureName fieldIndex _ =>
      let some structureInfo := getStructureInfo? (← getEnv) structureName
        | return origin
      return structureInfo.fieldNames[fieldIndex]?.getD origin
  | _ =>
      return proof.getAppFn.constName?.getD origin

private def localProofCandidates : MetaM (Array ContextCandidate) := do
  let mut candidates := #[]
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let proposition ← instantiateMVars localDecl.type
    unless ← isProp proposition do
      continue
    let resources ← expandProofResources #[localDecl.toExpr]
    for proof in resources do
      let proposition ← instantiateMVars (← inferType proof)
      unless candidates.any fun candidate =>
          candidate.proposition == proposition do
        candidates := candidates.push {
          label := ← proofResourceLabel localDecl.userName proof
          proposition := proposition
          proof := proof
          profile := ← ContextRelevance.collect proposition
          isStructure := ← propositionIsStructure proposition
        }
  return candidates

private def localContextHasStableEqualityProof : MetaM Bool := do
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let proposition ← instantiateMVars (← whnf localDecl.type)
    if proposition.isAppOfArity ``Eq 3 &&
        (← getMVarsNoDelayed proposition).isEmpty then
      return true
  return false

/--
保守识别通用 provider 是否会看到宿主对象语法。

`false` 只覆盖纯命题连接词、命题蕴涵和零参数命题 atom；未知应用、对象量词、存在式
与等式都返回 `true`，因此该门只会少做优化，不会把潜在 FO/HO 请求误送走。
-/
private partial def expressionHasHostObjectSyntaxAux
    (expression : Expr) : MetaM Bool := do
  let expression ← whnf (← instantiateMVars expression)
  if expression.isConstOf ``False || expression.isConstOf ``True then
    return false
  if expression.isAppOfArity ``Not 1 then
    return ← expressionHasHostObjectSyntaxAux expression.getAppArgs[0]!
  if expression.isAppOfArity ``And 2 ||
      expression.isAppOfArity ``Or 2 ||
      expression.isAppOfArity ``Iff 2 then
    for argument in expression.getAppArgs do
      if ← expressionHasHostObjectSyntaxAux argument then
        return true
    return false
  if expression.isAppOfArity ``Eq 3 ||
      expression.isAppOfArity ``Exists 2 then
    return true
  match expression with
  | .forallE _ domain body _ =>
      if !(← isProp domain) then
        return true
      return (← expressionHasHostObjectSyntaxAux domain) ||
        (← expressionHasHostObjectSyntaxAux body)
  | .letE _ _ value body _ =>
      expressionHasHostObjectSyntaxAux (body.instantiate1 value)
  | .app _ _ =>
      return true
  | _ =>
      return false

private def expressionHasHostObjectSyntax
    (expression : Expr) : MetaM Bool := do
  try
    expressionHasHostObjectSyntaxAux expression
  catch _ =>
    return true

private def makeContextTerminalSnapshot
    (goal : Expr) (factPropositions : Array Expr) :
    MetaM ContextTerminalSnapshot := do
  let mut hasHostObjectSyntax ← expressionHasHostObjectSyntax goal
  if !hasHostObjectSyntax then
    for proposition in factPropositions do
      if ← expressionHasHostObjectSyntax proposition then
        hasHostObjectSyntax := true
        break
  return {
    factPropositions
    hasHostObjectSyntax
  }

def prepareContextRequest
    (request : ContextRequest) : MetaM PreparedContextRequest := do
  let explicitResources ← expandProofResources request.useFacts
  let explicitPropositions ← explicitResources.mapM fun proof => do
    instantiateMVars (← inferType proof)
  let goalProfile ← ContextRelevance.collect request.goal
  let mut frontier := goalProfile
  for proposition in explicitPropositions do
    frontier := frontier.merge (← ContextRelevance.collect proposition)
  let allCandidates ← localProofCandidates
  let mut remaining :=
    allCandidates.filter fun candidate =>
      !explicitPropositions.any fun proposition =>
        proposition == candidate.proposition
  let maxFacts : Nat :=
    (← getOptions).get `prove_auto.context.maxFacts 16
  let mut selected : Array ContextCandidate := #[]
  while selected.size < maxFacts do
    let mut bestIndex? : Option Nat := none
    let mut bestScore := 0
    let mut bestIsStructure := true
    for index in [0 : remaining.size] do
      let some candidate := remaining[index]?
        | continue
      let exactTarget ←
        withTransparency .reducible <|
          isDefEq candidate.proposition request.goal
      let score :=
        if exactTarget then
          10_000
        else if candidate.isStructure then
          ContextRelevance.structureScore frontier candidate.profile
        else
          ContextRelevance.score frontier candidate.profile
      if score > bestScore ||
          (score == bestScore && bestIndex?.isSome &&
            bestIsStructure && !candidate.isStructure) then
        bestScore := score
        bestIsStructure := candidate.isStructure
        bestIndex? := some index
    let some bestIndex := bestIndex?
      | break
    let some candidate := remaining[bestIndex]?
      | break
    selected := selected.push candidate
    frontier := frontier.merge candidate.profile
    remaining := remaining.eraseIdx! bestIndex
  let selectedNames := selected.map ContextCandidate.label
  let facts := explicitResources ++ selected.map ContextCandidate.proof
  let factPropositions :=
    explicitPropositions ++ selected.map ContextCandidate.proposition
  let terminal ←
    makeContextTerminalSnapshot request.goal factPropositions
  let stats : ContextPreparationStats := {
    explicitRaw := request.useFacts.size
    explicitExpanded := explicitResources.size
    localCandidates := allCandidates.size
    contextSelected := selected.size
    contextRejected := remaining.size
    totalFacts := facts.size
    terminalPropositions := factPropositions.size
  }
  let summary : ContextResourceSummary := {
    present := true
    explicitRaw := request.useFacts.size
    explicitExpanded := explicitResources.size
    selected := selectedNames
    rejected := remaining.size
  }
  trace[YesMetaZFC.proveAuto.context]
    "prepared once; {summary.render}; localCandidates={allCandidates.size}; \
    total={facts.size}; keys={frontier.keys}; heads={frontier.heads}"
  return {
    goal := request.goal
    useFacts := request.useFacts
    facts := facts
    candidates := allCandidates
    goalProfile := goalProfile
    terminal := terminal
    resourceSummary := summary
    stats := stats
  }

/-- provider 自管上下文时不触发通用局部候选扫描。 -/
def ContextRequest.prepareProviderManaged
    (request : ContextRequest) : PreparedContextRequest := {
  goal := request.goal
  useFacts := request.useFacts
  resourceSummary := {
    present := true
    providerManaged := true
    explicitRaw := request.useFacts.size
  }
  stats := {
    explicitRaw := request.useFacts.size
  }
}

private def inferHostSequentSpecialization?
    (candidate : ContextCandidate) (target : Expr) :
    MetaM (Option (Array Expr)) := do
  unless candidate.proof.isFVar do
    return none
  let savedState ← saveState
  let result? ←
    try
      let (arguments, binderInfos, conclusion) ←
        forallMetaTelescopeReducing candidate.proposition
      if arguments.isEmpty then
        pure none
      else
        let mut supported := true
        for index in [0 : arguments.size] do
          let binderInfo := binderInfos[index]!
          let domain ← instantiateMVars (← inferType arguments[index]!)
          if binderInfo.isInstImplicit || (← isProp domain) then
            supported := false
        if !supported || !(← isDefEqGuarded conclusion target) then
          pure none
        else
          let mut specializedArguments := #[]
          for argument in arguments do
            let argument ← instantiateMVars argument
            unless (← getMVarsNoDelayed argument).isEmpty do
              supported := false
            specializedArguments := specializedArguments.push argument
          if !supported then
            pure none
          else
            let proposition ←
              instantiateMVars
                (← inferType (mkAppN candidate.proof specializedArguments))
            if ← isDefEqGuarded proposition target then
              pure (some specializedArguments)
            else
              pure none
    catch _ =>
      pure none
  savedState.restore
  return result?

private def inferHostSequentWitnessDescriptor?
    (candidate : ContextCandidate) (target : Expr) :
    MetaM (Option HostSequentWitnessDescriptor) := do
  unless candidate.proof.isFVar do
    return none
  let target ← whnf target
  unless target.isAppOfArity ``Exists 2 do
    return none
  let savedState ← saveState
  let result? ←
    try
      let arguments := target.getAppArgs
      let witness ← mkFreshExprMVar arguments[0]!
      let body ← whnf (mkApp arguments[1]! witness)
      if !(← isDefEqGuarded body candidate.proposition) then
        pure none
      else
        let witness ← instantiateMVars witness
        let witnessType ← instantiateMVars arguments[0]!
        let instanceProposition ← instantiateMVars body
        if (← getMVarsNoDelayed witness).isEmpty &&
            (← getMVarsNoDelayed witnessType).isEmpty &&
            (← getMVarsNoDelayed instanceProposition).isEmpty then
          pure <| some {
            label := candidate.label
            witnessType := witnessType
            witness := witness
            instanceProposition := instanceProposition
          }
        else
          pure none
    catch _ =>
      pure none
  savedState.restore
  return result?

private def inferHostSequentTransportTargets
    (candidate : ContextCandidate) (target : Expr) :
    TacticM (Array HostSequentTransportTarget) := do
  unless candidate.proof.isFVar do
    return #[]
  let equality ← instantiateMVars (← whnf candidate.proposition)
  unless equality.isAppOfArity ``Eq 3 do
    return #[]
  unless (← getMVarsNoDelayed equality).isEmpty do
    return #[]
  let arguments := equality.getAppArgs
  let left := arguments[1]!
  let right := arguments[2]!
  let probe (rewriteSymm reverseProof : Bool)
      (source destination : Expr) :
      TacticM (Option HostSequentTransportTarget) := do
    let savedState ← saveState
    let result? ←
      try
      let result ←
          (← getMainGoal).rewrite target candidate.proof
            (symm := rewriteSymm)
      if !result.mvarIds.isEmpty then
        pure none
      else
        let rewritten ← instantiateMVars result.eNew
        let unchanged ← isDefEqGuarded rewritten target
        if unchanged || !(← getMVarsNoDelayed rewritten).isEmpty then
          pure none
        else
          pure <| some {
            source := source
            destination := destination
            rewritten := rewritten
            reverseProof := reverseProof
          }
      catch _ =>
        pure none
    savedState.restore
    return result?
  let mut result := #[]
  if let some target ← probe true false left right then
    result := result.push target
  if let some target ← probe false true right left then
    result := result.push target
  return result

private def expressionsDefEq (left right : Expr) : MetaM Bool := do
  let savedState ← saveState
  let result ←
    try
      isDefEqGuarded left right
    catch _ =>
      pure false
  savedState.restore
  return result

/-- FORWARD 不保留不会改变局部上下文的自反等式。 -/
private def hostSequentForwardResultIsReflexiveEquality
    (result : Expr) : MetaM Bool := do
  let some (_, lhs, rhs) ← matchEq? result
    | return false
  expressionsDefEq lhs rhs

/--
FORWARD 的等式结果按无向对象对去重；普通命题仍只按定义等价去重。

等式方向只影响后续替换时的 `symm` 选择，不应重复占用生成预算和搜索深度。
-/
private def hostSequentForwardResultsEquivalent
    (left right : Expr) : MetaM Bool := do
  if ← expressionsDefEq left right then
    return true
  let some (leftType, leftLhs, leftRhs) ← matchEq? left
    | return false
  let some (rightType, rightLhs, rightRhs) ← matchEq? right
    | return false
  unless ← expressionsDefEq leftType rightType do
    return false
  unless ← expressionsDefEq leftLhs rightRhs do
    return false
  expressionsDefEq leftRhs rightLhs

/--
按局部候选稳定顺序枚举双向等式改写，并且只接纳唯一的 equality/support 对。

provider 事实选择不参与本层；等式和支持都必须是当前局部 FVar，改写后的目标必须与
支持命题定义等价。两个方向或两个支持同时可行时视为歧义并整体拒绝。
-/
private def discoverHostSequentTransports
    (prepared : PreparedContextRequest) (target : Expr) :
    TacticM HostSequentTransportDiscovery := do
  let mut candidates : Array IndexedHostSequentTransport := #[]
  let mut directedElaborations := 0
  for equality in prepared.candidates do
    unless equality.proof.isFVar do
      continue
    let proposition ← instantiateMVars (← whnf equality.proposition)
    unless proposition.isAppOfArity ``Eq 3 &&
        (← getMVarsNoDelayed proposition).isEmpty do
      continue
    directedElaborations := directedElaborations + 1
    for oriented in ← inferHostSequentTransportTargets equality target do
      for support in prepared.candidates do
        unless support.proof.isFVar do
          continue
        let supportProposition ← instantiateMVars support.proposition
        unless (← getMVarsNoDelayed supportProposition).isEmpty do
          continue
        if ← expressionsDefEq supportProposition oriented.rewritten then
          candidates := candidates.push {
            equality := equality
            support := support
            source := oriented.source
            destination := oriented.destination
            reverseProof := oriented.reverseProof
            relevance :=
              ContextRelevance.score prepared.goalProfile support.profile
          }
  if candidates.size == 1 then
    return {
      rules := candidates
      directedElaborations := directedElaborations
    }
  return {
    directedElaborations := directedElaborations
    directedAmbiguities := if candidates.size > 1 then 1 else 0
  }

/-- 当前局部上下文中的一个稳定 typed object 槽。 -/
private structure HostSequentTypedObject where
  label : Name
  expression : Expr
  type : Expr

/-- typed local object 形成一个无需预先实例 proof 的存在见证候选。 -/
private def typedHostSequentWitnessDescriptor?
    (target : Expr) (object : HostSequentTypedObject) :
    MetaM (Option HostSequentWitnessDescriptor) := do
  let target ← instantiateMVars (← whnf target)
  unless target.isAppOfArity ``Exists 2 do
    return none
  let arguments := target.getAppArgs
  unless ← expressionsDefEq object.type arguments[0]! do
    return none
  let savedState ← saveState
  let result? ←
    try
      let witness ← instantiateMVars object.expression
      let witnessType ← instantiateMVars arguments[0]!
      let instanceProposition ←
        instantiateMVars (← whnf (mkApp arguments[1]! witness))
      if !(← isProp instanceProposition) ||
          !(← getMVarsNoDelayed witness).isEmpty ||
          !(← getMVarsNoDelayed witnessType).isEmpty ||
          !(← getMVarsNoDelayed instanceProposition).isEmpty then
        pure none
      else
        pure <| some {
          label := object.label
          witnessType := witnessType
          witness := witness
          instanceProposition := instanceProposition
        }
    catch _ =>
      pure none
  savedState.restore
  return result?

/-- 一个已由局部 proof 与显式命题前提确定的前向实例。 -/
private structure HostSequentForwardInstance where
  descriptor : HostSequentForwardDescriptor
  candidateProof : Expr
  arguments : Array Expr
  premises : Array Expr

/-- 前向实例化的有界结果；搜索期只保留稳定的 proof-carrying 应用。 -/
private structure HostSequentForwardInference where
  instances : Array HostSequentForwardInstance := #[]
  ambiguousBranches : Nat := 0
  duplicatePrunes : Nat := 0
  budgetPrunes : Nat := 0

/-- 当前局部上下文中可作为显式对象参数的稳定 typed pool。 -/
private def localHostSequentObjects :
    MetaM (Array HostSequentTypedObject) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.binderInfo.isInstImplicit then
      continue
    let type ← instantiateMVars localDecl.type
    if type.hasMVar || (← isProp type) then
      continue
    result := result.push {
      label := localDecl.userName
      expression := localDecl.toExpr
      type := type
    }
  return result

/-- 对象参数只在 typed pool 中有唯一匹配时自动选择。 -/
private def uniqueHostSequentForwardObject?
    (domain : Expr) (objects : Array HostSequentTypedObject) :
    MetaM (Option Expr × Bool) := do
  let mut result? : Option Expr := none
  for object in objects do
    if ← expressionsDefEq object.type domain then
      if result?.isSome then
        return (none, true)
      result? := some object.expression
  return (result?, false)

/-- 收集当前目标在可逆命题连接词下暴露出的前向结论需求。 -/
private partial def hostSequentForwardDemands
    (target : Expr) : MetaM (Array Expr) := do
  let target ← whnf (← instantiateMVars target)
  let mut result := #[target]
  if target.isAppOfArity ``And 2 ||
      target.isAppOfArity ``Or 2 ||
      target.isAppOfArity ``Iff 2 then
    for argument in target.getAppArgs do
      for demand in ← hostSequentForwardDemands argument do
        unless result.any fun existing => existing == demand do
          result := result.push demand
  else if target.isAppOfArity ``Not 1 then
    for demand in ← hostSequentForwardDemands target.getAppArgs[0]! do
      unless result.any fun existing => existing == demand do
        result := result.push demand
  return result

/--
目标本身优先于其逻辑子需求；零分候选仍保留为完整搜索的后备。
-/
private def hostSequentForwardDemandScore
    (demands : Array Expr)
    (generated : Array Expr)
    (premises : Array Expr)
    (result : Expr) : MetaM (Nat × Bool) := do
  for index in [0 : demands.size] do
    if ← expressionsDefEq result demands[index]! then
      return (demands.size - index + 2, index == 0)
  -- 等式新事实可立即收缩局部对象上下文，必须高于普通 support 生成；
  -- 否则低权重成员事实会在对象统一前提前展开无关闭包。
  if (← matchEq? result).isSome then
    return (2, false)
  let mut consumesGenerated := false
  for premise in premises do
    for generatedProposition in generated do
      if ← expressionsDefEq premise generatedProposition then
        consumesGenerated := true
        break
    if consumesGenerated then
      break
  if consumesGenerated && result.isAppOfArity ``Exists 2 then
    return (2, false)
  return (0, false)

/--
提取一条候选规则所有显式命题前提的结论头。

这里只保留 proof-free 的头标识；telescope 产生的 metavariable 在返回前整体回滚。
-/
private def explicitHostSequentPremiseHeads
    (proposition : Expr) :
    MetaM (Array HostSequentConclusionHead) := do
  let savedState ← saveState
  let heads ←
    try
      let (arguments, binderInfos, _) ←
        forallMetaTelescopeReducing proposition
      let mut heads := #[]
      for index in [0 : arguments.size] do
        let binderInfo := binderInfos[index]!
        if binderInfo.isInstImplicit || !binderInfo.isExplicit then
          continue
        let domain ← instantiateMVars (← inferType arguments[index]!)
        unless ← isProp domain do
          continue
        if let some head := hostSequentConclusionHead? domain then
          unless heads.contains head do
            heads := heads.push head
      pure heads
    catch _ =>
      pure #[]
  savedState.restore
  return heads

/--
计算一层可逆 And 分解能直接暴露多少个已注册 FORWARD 前提头。

该分数只参与调度，不改变 CASES 准入或证明构造；嵌套结构必须逐层重新索引。
-/
private def hostSequentCasesUnlockScore
    (premiseHeads : Array HostSequentConclusionHead)
    (proposition : Expr) : MetaM Nat := do
  -- 已经能整体充当注册规则前提的结构 proof 必须先保留，不能为追求内部字段而拆散。
  if let some head := hostSequentConclusionHead? proposition then
    if premiseHeads.contains head then
      return 0
  let proposition ← whnf proposition
  unless proposition.isAppOfArity ``And 2 do
    return 0
  let mut score := 0
  for field in proposition.getAppArgs do
    if let some head := hostSequentConclusionHead? field then
      if premiseHeads.contains head then
        score := score + 1
  return score

/-- 当前完整命题是否应优先保留给注册 FORWARD 规则消费。 -/
private def preserveHostSequentPropositionForForward
    (premiseHeads : Array HostSequentConclusionHead)
    (proposition : Expr) : Bool :=
  match hostSequentConclusionHead? proposition with
  | some head => premiseHeads.contains head
  | none => false

/--
用当前已有的显式 proposition proof 反向确定对象参数，并前向应用局部规则。

本函数不调用 provider，也不产生 premise goal。搜索只枚举当前 proof pool 中能与显式
premise 精确统一的组合；未被 premise 确定的对象仍要求 typed pool 唯一，并受全局
`maxForwardCandidates` 的剩余预算约束。
-/
private def inferHostSequentForward
    (candidate : ContextCandidate)
    (proofCandidates : Array ContextCandidate)
    (objects : Array HostSequentTypedObject)
    (maxResults : Nat) :
    MetaM HostSequentForwardInference := do
  if maxResults == 0 then
    return { budgetPrunes := 1 }
  let savedState ← saveState
  let result ←
    try
      let (arguments, binderInfos, _) ←
        forallMetaTelescopeReducing candidate.proposition
      let mut objectArguments : Nat := 0
      let mut propositionPremises : Nat := 0
      let mut rejected : Bool := false
      for index in [0 : arguments.size] do
        let binderInfo := binderInfos[index]!
        let domain ← instantiateMVars (← inferType arguments[index]!)
        if binderInfo.isInstImplicit then
          rejected := true
        else if ← isProp domain then
          if binderInfo.isExplicit then
            propositionPremises := propositionPremises + 1
          else
            rejected := true
        else
          objectArguments := objectArguments + 1
      if rejected || propositionPremises == 0 then
        pure {}
      else
        let rec search :
            Nat → Nat → Nat → Array Expr → MetaM HostSequentForwardInference
          | 0, _, _, _ => pure { budgetPrunes := 1 }
          | fuel + 1, index, remaining, premises => do
              if remaining == 0 then
                return { budgetPrunes := 1 }
              if index == arguments.size then
                let leafState ← saveState
                let mut leafRejected := false
                let mut ambiguousBranches := 0
                for argument in arguments do
                  let argumentId := argument.mvarId!
                  if ← argumentId.isAssigned then
                    continue
                  let domain ← instantiateMVars (← inferType argument)
                  if ← isProp domain then
                    leafRejected := true
                    continue
                  let (argument?, isAmbiguous) ←
                    uniqueHostSequentForwardObject? domain objects
                  if isAmbiguous then
                    ambiguousBranches := ambiguousBranches + 1
                    leafRejected := true
                    continue
                  let some argument := argument?
                    | leafRejected := true
                      continue
                  argumentId.assign argument
                if leafRejected then
                  leafState.restore
                  return { ambiguousBranches := ambiguousBranches }
                let instantiatedArguments ←
                  arguments.mapM instantiateMVars
                if instantiatedArguments.any fun argument => argument.hasMVar then
                  leafState.restore
                  return {}
                let instantiatedPremises ← premises.mapM instantiateMVars
                if instantiatedPremises.any fun premise => premise.hasMVar then
                  leafState.restore
                  return {}
                let application ←
                  instantiateMVars (mkAppN candidate.proof instantiatedArguments)
                let proposition ←
                  instantiateMVars (← whnf (← inferType application))
                if proposition.hasMVar || !(← isProp proposition) then
                  leafState.restore
                  return {}
                let candidateProof ← instantiateMVars candidate.proof
                unless (← getMVarsNoDelayed candidateProof).isEmpty do
                  leafState.restore
                  return {}
                if ← hostSequentForwardResultIsReflexiveEquality proposition then
                  leafState.restore
                  return { duplicatePrunes := 1 }
                let mut duplicate := false
                for existing in proofCandidates do
                  if ← hostSequentForwardResultsEquivalent
                      existing.proposition proposition then
                    duplicate := true
                    break
                let result :=
                  if duplicate then
                    { duplicatePrunes := 1 }
                  else
                    {
                      instances := #[{
                        descriptor := {
                          sourceLabel := candidate.label
                          objectArguments := objectArguments
                          propositionPremises := propositionPremises
                          result := proposition
                        }
                        candidateProof := candidateProof
                        arguments := instantiatedArguments
                        premises := instantiatedPremises
                      }]
                    }
                leafState.restore
                return result
              let argument := arguments[index]!
              let domain ← instantiateMVars (← inferType argument)
              if !(← isProp domain) then
                return ← search fuel (index + 1) remaining premises
              let mut result : HostSequentForwardInference := {}
              for proofCandidate in proofCandidates do
                if result.instances.size >= remaining then
                  result := {
                    result with
                    budgetPrunes := result.budgetPrunes + 1
                  }
                  break
                let branchState ← saveState
                let matched ←
                  try
                    isDefEqGuarded domain proofCandidate.proposition
                  catch _ =>
                    pure false
                if matched then
                  argument.mvarId!.assign proofCandidate.proof
                  let premise ← instantiateMVars proofCandidate.proposition
                  let branch ← search fuel (index + 1)
                    (remaining - result.instances.size) (premises.push premise)
                  for forwardInstance in branch.instances do
                    if result.instances.size >= remaining then
                      result := {
                        result with
                        budgetPrunes := result.budgetPrunes + 1
                      }
                      break
                    let mut duplicate := false
                    for existing in result.instances do
                      if ← hostSequentForwardResultsEquivalent
                          existing.descriptor.result forwardInstance.descriptor.result then
                        duplicate := true
                        break
                    if duplicate then
                      result := {
                        result with
                        duplicatePrunes := result.duplicatePrunes + 1
                      }
                    else
                      result := {
                        result with
                        instances := result.instances.push forwardInstance
                      }
                  result := {
                    result with
                    ambiguousBranches :=
                      result.ambiguousBranches + branch.ambiguousBranches
                    duplicatePrunes :=
                      result.duplicatePrunes + branch.duplicatePrunes
                    budgetPrunes := result.budgetPrunes + branch.budgetPrunes
                  }
                branchState.restore
              return result
        -- 递归模式先消耗一个 fuel；额外保留一格才能进入
        -- `index == arguments.size` 的叶子并生成完整前向实例。
        search (arguments.size + 1) 0 maxResults #[]
    catch _ =>
      pure {}
  savedState.restore
  return result

private def hasExactHostSequentUseFact
    (prepared : PreparedContextRequest) (target : Expr) : MetaM Bool := do
  for proof in prepared.useFacts do
    let proposition ← instantiateMVars (← inferType proof)
    if ← expressionsDefEq proposition target then
      return true
  return false

/-- 有限 CASES 候选的准入结果；拒绝项会进入可观测 miss 计数。 -/
private inductive HostSequentCasesAdmission where
  | notApplicable
  | rejected
  | accepted (descriptor : HostSequentCasesDescriptor)

/--
识别一个可安全自动消去的局部归纳命题。

indexed 命题可能在 `cases` 时消去不可达构造子，因此本层暂不自动接纳；对象字段及依赖
于对象字段的 proof 字段仍可留在普通非 indexed 构造子中，由分支上下文承载。
-/
private def admitHostSequentCases
    (proposition : Expr) : MetaM HostSequentCasesAdmission := do
  let proposition ← instantiateMVars (← whnf proposition)
  unless (← getMVarsNoDelayed proposition).isEmpty do
    return .rejected
  unless ← isProp proposition do
    return .notApplicable
  let some inductiveName := proposition.getAppFn.constName?
    | return .notApplicable
  if inductiveName == ``Exists || inductiveName == ``Eq ||
      inductiveName == ``HEq then
    return .notApplicable
  let some inductiveInfo ← isInductivePredicate? inductiveName
    | return .notApplicable
  if inductiveInfo.isUnsafe || inductiveInfo.numIndices != 0 ||
      proposition.getAppNumArgs != inductiveInfo.numParams ||
      inductiveInfo.ctors.isEmpty then
    return .rejected
  let constructors := inductiveInfo.ctors.toArray
  for constructorName in constructors do
    if (← getConstInfo constructorName).isUnsafe then
      return .rejected
  return .accepted {
    inductiveName := inductiveName
    constructors := constructors
    expectedBranches := constructors.size
  }

/--
按环境声明顺序提取当前归纳命题目标的安全构造子。

这里只保存声明名和位置；构造子是否能在不猜测对象参数的前提下形成当前目标，
仍由执行层的 checked APPLY 准入统一判定。
-/
def targetHostSequentConstructors
    (target : Expr) : MetaM (Array HostSequentConstructorDescriptor) := do
  let target ← instantiateMVars (← whnf target)
  unless ← isProp target do
    return #[]
  let some inductiveName := target.getAppFn.constName?
    | return #[]
  unless ← isInductivePredicate inductiveName do
    return #[]
  let inductiveInfo ← getConstInfoInduct inductiveName
  if inductiveInfo.isUnsafe then
    return #[]
  let constructors := inductiveInfo.ctors.toArray
  let mut result := #[]
  for position in [:constructors.size] do
    let constructorName := constructors[position]!
    let constructorInfo ← getConstInfo constructorName
    unless constructorInfo.isUnsafe do
      result := result.push {
        inductiveName := inductiveName
        constructorName := constructorName
        position := position
      }
  return result

/--
只在 相继式前端真正需要规则时构造当前叶子的候选索引。

局部 proof 每个只拆一次 telescope；声明规则先按注册时固化的结论头取桶，未命中的
声明不会实例化、重算 profile 或进入候选排序。
-/
def prepareHostSequentContext
    (prepared : PreparedContextRequest)
    (maxForwardCandidates : Nat := 64)
    (maxWitnessCandidates : Nat := 64)
    (generated : Array Expr := #[]) :
    TacticM PreparedHostSequentContext := do
  let target ← whnf prepared.goal
  let targetHead? := hostSequentConclusionHead? target
  let forwardDemands ← hostSequentForwardDemands target
  let hasExactUseFact ← hasExactHostSequentUseFact prepared target
  let mut applyRules : Array IndexedHostSequentCandidate := #[]
  let mut caseRules : Array IndexedHostSequentCases := #[]
  let mut chooseRules : Array IndexedHostSequentCandidate := #[]
  let mut specializeRules : Array IndexedHostSequentSpecialization := #[]
  let mut forwardRules : Array IndexedHostSequentForward := #[]
  let transportDiscovery ← discoverHostSequentTransports prepared target
  let mut indexStats : HostSequentCandidateIndexStats := {
    directedElaborations := transportDiscovery.directedElaborations
    directedAmbiguities := transportDiscovery.directedAmbiguities
  }
  let mut witnessRules : Array IndexedHostSequentWitness := #[]
  let mut witnessSeen : Array Expr := #[]
  let mut inferredWitnesses :
      Array (HostSequentWitnessDescriptor × ContextCandidate) := #[]
  let forwardObjects ← localHostSequentObjects
  let explicitResources ← expandProofResources prepared.useFacts
  -- 所有局部命题规则共用同一候选池；否则 FORWARD 生成的显式新事实
  -- 只能被 FORWARD 看到，CASES/CHOOSE/APPLY 却无法消费它。
  let mut proofCandidates := prepared.candidates
  for proof in explicitResources do
    let proposition ← instantiateMVars (← inferType proof)
    unless proofCandidates.any fun candidate =>
        candidate.proposition == proposition do
      proofCandidates := proofCandidates.push {
        label := ← proofResourceLabel `explicit proof
        proposition := proposition
        proof := proof
        profile := ← ContextRelevance.collect proposition
        isStructure := ← propositionIsStructure proposition
      }
  -- 从当前局部规则的显式前提头准备注册桶；Eq 额外承担对象收缩。
  -- 声明规则只有在当前 proof 池能完整实例化全部命题前提时才进入本节点索引。
  let mut neededConclusionHeads := #[]
  let mut availableProofHeads := #[]
  for candidate in proofCandidates do
    if let some head ←
        registeredHostSequentConclusionHead? candidate.proposition then
      unless availableProofHeads.contains head do
        availableProofHeads := availableProofHeads.push head
    for head in ← explicitHostSequentPremiseHeads candidate.proposition do
      unless neededConclusionHeads.contains head do
        neededConclusionHeads := neededConclusionHeads.push head
  let equalityHead := HostSequentConclusionHead.const ``Eq
  unless neededConclusionHeads.contains equalityHead do
    neededConclusionHeads := neededConclusionHeads.push equalityHead
  let mut supportRulesLoaded := 0
  for head in neededConclusionHeads do
    if supportRulesLoaded >= maxForwardCandidates then
      break
    match head with
    | HostSequentConclusionHead.const declaration =>
        for rule in ←
            registeredHostSequentRulesForConclusionHead declaration do
          if supportRulesLoaded >= maxForwardCandidates then
            break
          unless proofCandidates.any fun candidate =>
              candidate.label == rule.declaration do
            unless rule.premiseHeads.all fun premiseHead =>
                availableProofHeads.contains premiseHead do
              indexStats := {
                indexStats with
                registeredPremisePrunes :=
                  indexStats.registeredPremisePrunes + 1
              }
              continue
            let proof ← mkConstWithFreshMVarLevels rule.declaration
            let candidate : ContextCandidate := {
              label := rule.declaration
              proposition := ← instantiateMVars (← inferType proof)
              proof := proof
              profile := rule.profile
              isStructure := false
            }
            let coverage ←
              inferHostSequentForward candidate proofCandidates
                forwardObjects 1
            unless coverage.instances.isEmpty do
              proofCandidates := proofCandidates.push candidate
              supportRulesLoaded := supportRulesLoaded + 1
              indexStats := {
                indexStats with
                registeredCandidates :=
                  indexStats.registeredCandidates + 1
              }
    | _ =>
        pure ()
  let constructors ← targetHostSequentConstructors target
  indexStats := {
    indexStats with
    constructorCandidates := constructors.size
  }
  for candidate in proofCandidates do
    indexStats := {
      indexStats with
      candidateElaborations := indexStats.candidateElaborations + 1
    }
    let shape? ←
      try
        some <$> analyzeHostSequentProposition candidate.proposition
      catch _ =>
        pure none
    let some shape := shape?
      | indexStats := {
          indexStats with
          candidateFilters := indexStats.candidateFilters + 1
        }
        continue
    let relevance :=
      ContextRelevance.score prepared.goalProfile candidate.profile
    if shape.objectBinders > 0 &&
        shape.explicitPropPremises > 0 &&
        !shape.hasInstanceBinder &&
        !shape.hasImplicitPropPremise then
      indexStats := {
        indexStats with
        forwardDescriptorCandidates :=
          indexStats.forwardDescriptorCandidates + 1
      }
      if forwardRules.size >= maxForwardCandidates then
        indexStats := {
          indexStats with
          forwardDescriptorMisses :=
            indexStats.forwardDescriptorMisses + 1
          forwardBudgetPrunes := indexStats.forwardBudgetPrunes + 1
        }
      else
        let inference ←
          inferHostSequentForward candidate proofCandidates
            forwardObjects (maxForwardCandidates - forwardRules.size)
        indexStats := {
          indexStats with
          forwardAmbiguities :=
            indexStats.forwardAmbiguities + inference.ambiguousBranches
          forwardDuplicatePrunes :=
            indexStats.forwardDuplicatePrunes + inference.duplicatePrunes
          forwardBudgetPrunes :=
            indexStats.forwardBudgetPrunes + inference.budgetPrunes
        }
        if inference.instances.isEmpty then
          indexStats := {
            indexStats with
            forwardDescriptorMisses :=
              indexStats.forwardDescriptorMisses + 1
          }
        else
          for forwardInstance in inference.instances do
            let (demandScore, closesTarget) ←
              hostSequentForwardDemandScore
                forwardDemands generated forwardInstance.premises
                  forwardInstance.descriptor.result
            let age := forwardRules.size
            forwardRules := forwardRules.push {
              descriptor := forwardInstance.descriptor
              candidate := {
                candidate with
                proof := forwardInstance.candidateProof
              }
              arguments := forwardInstance.arguments
              premises := forwardInstance.premises
              closesTarget := closesTarget
              demandScore := demandScore
              weight := forwardInstance.descriptor.result.approxDepth.toNat
              age := age
              relevance := relevance
            }
          indexStats := {
            indexStats with
            forwardDescriptorHits :=
              indexStats.forwardDescriptorHits + inference.instances.size
          }
    if !hasExactUseFact &&
        shape.objectBinders > 0 &&
        shape.explicitPropPremises == 0 &&
        !shape.hasInstanceBinder &&
        !shape.hasImplicitPropPremise then
      indexStats := {
        indexStats with
        directedElaborations := indexStats.directedElaborations + 1
      }
      if let some arguments ←
          inferHostSequentSpecialization? candidate target then
        specializeRules := specializeRules.push {
          candidate := candidate
          arguments := arguments
          relevance := relevance
        }
    if target.isAppOfArity ``Exists 2 then
      indexStats := {
        indexStats with
        directedElaborations := indexStats.directedElaborations + 1
        witnessDescriptorCandidates :=
          indexStats.witnessDescriptorCandidates + 1
      }
      match ← inferHostSequentWitnessDescriptor? candidate target with
      | none =>
          indexStats := {
            indexStats with
            witnessDescriptorMisses :=
              indexStats.witnessDescriptorMisses + 1
          }
      | some descriptor =>
          inferredWitnesses :=
            inferredWitnesses.push (descriptor, candidate)
    -- 相关性只参与稳定排序，不能决定真实局部资源是否存在。
    if candidate.proof.isFVar &&
        !shape.rootIsExists && !shape.rootIsEq && !shape.rootIsHEq then
      match ← admitHostSequentCases candidate.proposition with
      | .notApplicable =>
          pure ()
      | .rejected =>
          indexStats := {
            indexStats with
            casesDescriptorCandidates :=
              indexStats.casesDescriptorCandidates + 1
            casesDescriptorMisses := indexStats.casesDescriptorMisses + 1
          }
      | .accepted descriptor =>
          let preserveForForward :=
            preserveHostSequentPropositionForForward
              neededConclusionHeads candidate.proposition
          caseRules := caseRules.push {
            descriptor := descriptor
            candidate := candidate
            unlockScore := ←
              hostSequentCasesUnlockScore
                neededConclusionHeads candidate.proposition
            preserveForForward := preserveForForward
            relevance := relevance
          }
          indexStats := {
            indexStats with
            casesDescriptorCandidates :=
              indexStats.casesDescriptorCandidates + 1
            casesDescriptorHits := indexStats.casesDescriptorHits + 1
          }
    if shape.rootIsExists &&
        candidate.proof.isFVar then
      chooseRules := chooseRules.push {
        candidate := candidate
        relevance := relevance
      }
    if shape.explicitPropPremises == 0 ||
        shape.hasInstanceBinder ||
        shape.hasImplicitPropPremise ||
        shape.conclusionHead?.isNone then
      indexStats := {
        indexStats with
        candidateFilters := indexStats.candidateFilters + 1
      }
      continue
    if shape.conclusionHead? == targetHead? then
      applyRules := applyRules.push {
        candidate := candidate
        relevance := relevance
      }
      indexStats := {
        indexStats with
        indexHits := indexStats.indexHits + 1
      }
    else
      indexStats := {
        indexStats with
        indexMisses := indexStats.indexMisses + 1
      }
  if target.isAppOfArity ``Exists 2 then
    for object in forwardObjects do
      if let some descriptor ←
          typedHostSequentWitnessDescriptor? target object then
        indexStats := {
          indexStats with
          witnessDescriptorCandidates :=
            indexStats.witnessDescriptorCandidates + 1
        }
        let mut duplicate := false
        for witness in witnessSeen do
          if ← expressionsDefEq witness descriptor.witness then
            duplicate := true
            break
        if duplicate then
          indexStats := {
            indexStats with
            witnessDescriptorMisses :=
              indexStats.witnessDescriptorMisses + 1
            witnessDuplicatePrunes :=
              indexStats.witnessDuplicatePrunes + 1
          }
        else
          let descriptor := {
            descriptor with
            position := witnessSeen.size
          }
          witnessSeen := witnessSeen.push descriptor.witness
          if witnessRules.size >= maxWitnessCandidates then
            indexStats := {
              indexStats with
              witnessDescriptorMisses :=
                indexStats.witnessDescriptorMisses + 1
              witnessBudgetPrunes :=
                indexStats.witnessBudgetPrunes + 1
            }
          else
            witnessRules := witnessRules.push {
              descriptor := descriptor
              relevance := 0
            }
            indexStats := {
              indexStats with
              witnessDescriptorHits :=
                indexStats.witnessDescriptorHits + 1
            }
    for inferred in inferredWitnesses do
      let descriptor := inferred.1
      let candidate := inferred.2
      let mut duplicateIndex? : Option Nat := none
      for index in [0 : witnessSeen.size] do
        if ← expressionsDefEq witnessSeen[index]! descriptor.witness then
          duplicateIndex? := some index
          break
      match duplicateIndex? with
      | some seenIndex =>
          indexStats := {
            indexStats with
            witnessDescriptorMisses :=
              indexStats.witnessDescriptorMisses + 1
            witnessDuplicatePrunes :=
              indexStats.witnessDuplicatePrunes + 1
          }
          if let some rule := witnessRules[seenIndex]? then
            if rule.support.isNone then
              witnessRules := witnessRules.set! seenIndex {
                rule with
                descriptor := {
                  descriptor with
                  position := rule.descriptor.position
                }
                support := some candidate
              }
      | none =>
          let descriptor := {
            descriptor with
            position := witnessSeen.size
          }
          witnessSeen := witnessSeen.push descriptor.witness
          if witnessRules.size >= maxWitnessCandidates then
            indexStats := {
              indexStats with
              witnessDescriptorMisses :=
                indexStats.witnessDescriptorMisses + 1
              witnessBudgetPrunes :=
                indexStats.witnessBudgetPrunes + 1
            }
          else
            witnessRules := witnessRules.push {
              descriptor := descriptor
              support := some candidate
              relevance := 0
            }
            indexStats := {
              indexStats with
              witnessDescriptorHits :=
                indexStats.witnessDescriptorHits + 1
            }
  let transportRules := transportDiscovery.rules
  let sortedForwardRules :=
    (forwardRules.mapIdx fun position rule => (position, rule))
      |>.qsort (fun left right =>
        if left.2.demandScore == right.2.demandScore then
          if left.2.weight == right.2.weight then
            if left.2.relevance == right.2.relevance then
              if left.2.age == right.2.age then
                left.1 < right.1
              else
                left.2.age < right.2.age
            else
              left.2.relevance > right.2.relevance
          else
            left.2.weight < right.2.weight
        else
          left.2.demandScore > right.2.demandScore)
      |>.map (·.2)
  let registered ← registeredHostSequentRulesForTarget target
  for rule in registered do
    unless rule.premiseHeads.all fun premiseHead =>
        availableProofHeads.contains premiseHead do
      indexStats := {
        indexStats with
        registeredPremisePrunes :=
          indexStats.registeredPremisePrunes + 1
      }
      continue
    let proof ← mkConstWithFreshMVarLevels rule.declaration
    let proposition ← instantiateMVars (← inferType proof)
    let candidate : ContextCandidate := {
      label := rule.declaration
      proposition := proposition
      proof := proof
      profile := rule.profile
      isStructure := false
    }
    applyRules := applyRules.push {
      candidate := candidate
      relevance :=
        ContextRelevance.score prepared.goalProfile rule.profile
      rank := rule.rank
      origin := .registered
    }
    indexStats := {
      indexStats with
      candidateElaborations := indexStats.candidateElaborations + 1
      indexHits := indexStats.indexHits + 1
      registeredCandidates := indexStats.registeredCandidates + 1
    }
  let index : HostSequentCandidateIndex := {
    apply := applyRules
    cases := caseRules
    choose := chooseRules
    specialize := specializeRules
    forward := sortedForwardRules
    witness := witnessRules
    transport := transportRules
    constructors := constructors
    stats := indexStats
  }
  trace[YesMetaZFC.proveAuto.sequent]
    "candidate.index target={repr targetHead?}; \
    apply={index.apply.size}; cases={index.cases.size}; \
    choose={index.choose.size}; specialize={index.specialize.size}; \
    forward={index.forward.size}; \
    witness={index.witness.size}; transport={index.transport.size}; \
    constructors={index.constructors.size}; \
    casesDescriptorCandidates={index.stats.casesDescriptorCandidates}; \
    casesDescriptorHits={index.stats.casesDescriptorHits}; \
    casesDescriptorMisses={index.stats.casesDescriptorMisses}; \
    forwardDescriptorCandidates={index.stats.forwardDescriptorCandidates}; \
    forwardDescriptorHits={index.stats.forwardDescriptorHits}; \
    forwardDescriptorMisses={index.stats.forwardDescriptorMisses}; \
    forwardDuplicatePrunes={index.stats.forwardDuplicatePrunes}; \
    forwardAmbiguities={index.stats.forwardAmbiguities}; \
    forwardBudgetPrunes={index.stats.forwardBudgetPrunes}; \
    witnessDescriptorCandidates={index.stats.witnessDescriptorCandidates}; \
    witnessDescriptorHits={index.stats.witnessDescriptorHits}; \
    witnessDescriptorMisses={index.stats.witnessDescriptorMisses}; \
    witnessDuplicatePrunes={index.stats.witnessDuplicatePrunes}; \
    witnessBudgetPrunes={index.stats.witnessBudgetPrunes}; \
    elaborations={index.stats.candidateElaborations}; \
    filters={index.stats.candidateFilters}; hits={index.stats.indexHits}; \
    misses={index.stats.indexMisses}; \
    registered={index.stats.registeredCandidates}; \
    registeredPremisePrunes={index.stats.registeredPremisePrunes}; \
    directedElaborations={index.stats.directedElaborations}; \
    directedAmbiguities={index.stats.directedAmbiguities}; \
    constructorCandidates={index.stats.constructorCandidates}"
  return {
    request := prepared
    index := index
  }

/-- 以当前 Lean 目标为索引的可执行闭合状态与 soundness 合同。 -/
structure GoalAttempt (goal : Prop) where
  closed : Bool
  summary : String
  sound : closed = true → goal

namespace GoalAttempt

/-- 构造不会闭合目标的结构化失败结果。 -/
def failure {goal : Prop} (summary : String) : GoalAttempt goal where
  closed := false
  summary := summary
  sound := by simp

/-- 请求的可计算 closed 标记足以安全闭合当前目标。 -/
theorem soundOfClosed {goal : Prop} (request : GoalAttempt goal)
    (hClosed : request.closed = true) : goal :=
  request.sound hClosed

/-- 任意模型 universe 的 proof-carrying backend attempt 闭合时给出语义蕴涵。 -/
theorem backendSoundOfClosedAt (problem : SourcePreprocessing.DeepProblem)
    (attempt : LogicSoundness.SetLevel.BackendAttemptAt.{x} problem)
    (hClosed : LogicSoundness.SetLevel.BackendAttemptAt.closed attempt = true) :
    LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
      problem.theory problem.target := by
  cases hAttempt : attempt with
  | success success =>
      exact success.sound
  | failure diagnostic =>
      simp [LogicSoundness.SetLevel.BackendAttemptAt.closed, hAttempt] at hClosed

/-- 现有零 universe backend attempt 的 closed 标记给出语义蕴涵。 -/
theorem backendSoundOfClosed (problem : SourcePreprocessing.DeepProblem)
    (attempt : LogicSoundness.SetLevel.BackendAttempt problem)
    (hClosed : attempt.closed = true) :
    LogicSoundness.SetLevel.SemanticallyEntails
      problem.theory problem.target :=
  backendSoundOfClosedAt problem attempt hClosed

end GoalAttempt

private structure ContextDispatchResult where
  attempt? : Option Expr := none
  resourceSummary : ContextResourceSummary := {}

private structure ScheduledContextProvider where
  name : Name
  provider : ContextProvider

private abbrev ContextProviderSchedule :=
  Array ScheduledContextProvider

/-- provider 声明求值与优先级排序在一次相继式叶组中只做一次。 -/
private unsafe def prepareContextProviderSchedule :
    TacticM ContextProviderSchedule := do
  let env ← getEnv
  let mut providers : Array (Nat × Name × ContextProvider) := #[]
  for providerName in contextProviderExtension.getState env do
    let provider ←
      evalExpr ContextProvider (mkConst ``ContextProvider)
        (mkConst providerName)
    providers := providers.push (provider.priority, providerName, provider)
  return (providers.qsort fun left right =>
    decide (left.1 > right.1)).map fun provider => {
      name := provider.2.1
      provider := provider.2.2
    }

private structure ContextDispatchObserver where
  providerVisited : Name → TacticM Unit := fun _ => pure ()
  providerBuilt :
    Name → ContextPreparation → TacticM Unit := fun _ _ => pure ()
  providerSkipped : Name → TacticM Unit := fun _ => pure ()
  prepared : PreparedContextRequest → TacticM Unit := fun _ => pure ()
  summaryEvaluated : TacticM Unit := pure ()

private unsafe def contextualAttempt? (request : ContextRequest)
    (preparedSeed? : Option PreparedContextRequest := none)
    (schedule? : Option ContextProviderSchedule := none)
    (observer : ContextDispatchObserver := {}) :
    TacticM ContextDispatchResult := do
  let schedule ←
    match schedule? with
    | some schedule => pure schedule
    | none => prepareContextProviderSchedule
  let mut prepared? := preparedSeed?
  let mut resourceSummary :=
    preparedSeed?.map (·.resourceSummary) |>.getD {}
  for scheduled in schedule do
    let providerName := scheduled.name
    let provider := scheduled.provider
    let prepared ←
      match provider.preparation with
      | .providerManaged =>
          pure request.prepareProviderManaged
      | .relevantFacts =>
          match prepared? with
          | some prepared =>
              trace[YesMetaZFC.proveAuto.context]
                "reuse prepared context for provider `{providerName}`"
              pure prepared
          | none =>
              let prepared ← prepareContextRequest request
              observer.prepared prepared
              prepared? := some prepared
              resourceSummary := prepared.resourceSummary
              pure prepared
    trace[YesMetaZFC.proveAuto.context]
      "provider `{providerName}` preparation={repr provider.preparation}; \
      facts={prepared.facts.size}; candidates={prepared.candidates.size}"
    observer.providerVisited providerName
    if provider.requirement == .hostObjectSyntax &&
        !prepared.terminal.hasHostObjectSyntax then
      observer.providerSkipped providerName
      trace[YesMetaZFC.proveAuto.context]
        "provider `{providerName}` skipped: no host object syntax"
      continue
    observer.providerBuilt providerName provider.preparation
    if let some attempt ← provider.build? prepared then
      let expectedType := mkApp (mkConst ``GoalAttempt) request.goal
      let actualType ← inferType attempt
      unless ← isDefEq actualType expectedType do
        throwError
          "prove_auto context provider `{providerName}` returned{indentExpr actualType}, \
          expected{indentExpr expectedType}"
      return {
        attempt? := some attempt
        resourceSummary := prepared.resourceSummary
      }
  return {
    resourceSummary := resourceSummary
  }

/-- 裸 `prove_auto` 消费的目标索引请求类。 -/
class GoalRequest (goal : Prop) where
  run : GoalAttempt goal

namespace GoalRequest

/-- 从任意模型 universe 的 deep backend attempt 建立目标请求。 -/
@[reducible] def ofAttemptAt (problem : SourcePreprocessing.DeepProblem)
    (attempt : LogicSoundness.SetLevel.BackendAttemptAt.{x} problem) :
    GoalRequest
      (LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        problem.theory problem.target) where
  run := {
    closed := LogicSoundness.SetLevel.BackendAttemptAt.closed attempt
    summary := LogicSoundness.SetLevel.BackendAttemptAt.summary attempt
    sound := GoalAttempt.backendSoundOfClosedAt problem attempt
  }

/-- 从现有零 universe deep backend attempt 建立目标请求。 -/
@[reducible] def ofAttempt (problem : SourcePreprocessing.DeepProblem)
    (attempt : LogicSoundness.SetLevel.BackendAttempt problem) :
    GoalRequest
      (LogicSoundness.SetLevel.SemanticallyEntails
        problem.theory problem.target) :=
  ofAttemptAt problem attempt

/-- 从 checked source problem 与同 universe 反模型桥建立默认 FO/HO routed 请求。 -/
@[reducible] def ofSourceAt (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (bridge : SourcePreprocessing.ProblemBridgeAt.{x} sourceProblem problem)
    (settings : SourcePreprocessing.Settings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (hoConfig : SourcePreprocessing.HOAvatarConfig := {})
    (label : String := "bare prove_auto") :
    GoalRequest
      (LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        problem.theory problem.target) :=
  ofAttemptAt problem <|
    SourcePreprocessing.runRoutedProviderAt
      sourceProblem problem bridge settings avatarConfig hoConfig label

/-- 从 checked source problem 与零 universe 反模型桥建立默认 FO/HO routed 请求。 -/
@[reducible] def ofSource (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (bridge : SourcePreprocessing.ProblemBridge sourceProblem problem)
    (settings : SourcePreprocessing.Settings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (hoConfig : SourcePreprocessing.HOAvatarConfig := {})
    (label : String := "bare prove_auto") :
    GoalRequest
      (LogicSoundness.SetLevel.SemanticallyEntails
        problem.theory problem.target) :=
  ofSourceAt sourceProblem problem bridge settings avatarConfig hoConfig label

/-- 从纯一阶 source 与同 universe 反模型桥建立 AVATAR/DAG routed 请求。 -/
@[reducible] def ofFirstOrderSourceAt
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (bridge :
      SourcePreprocessing.FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "bare first-order prove_auto") :
    GoalRequest
      (LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        problem.theory problem.target) :=
  ofAttemptAt problem <|
    SourcePreprocessing.runFirstOrderProviderAt
      sourceProblem problem bridge settings avatarConfig label

/-- 从纯一阶 source 与零 universe 反模型桥建立 AVATAR/DAG routed 请求。 -/
@[reducible] def ofFirstOrderSource
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (bridge : SourcePreprocessing.FirstOrderProblemBridge sourceProblem problem)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "bare first-order prove_auto") :
    GoalRequest
      (LogicSoundness.SetLevel.SemanticallyEntails
        problem.theory problem.target) :=
  ofFirstOrderSourceAt
    sourceProblem problem bridge settings avatarConfig label

end GoalRequest

/-- 回放一般深嵌入问题的 checked certificate。 -/
syntax (name := proveAutoCheckedCertificate)
  "prove_auto " "CERT " term : tactic

@[tactic proveAutoCheckedCertificate] unsafe def evalProveAutoCheckedCertificate : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let cert ← elabTerm stx[2] none
        let proof ← mkAppM ``LogicSoundness.SetLevel.CheckedCertificate.sound #[cert]
        closeByProof `prove_auto_cert proof

/-- 回放已经通过新语义核可信边界闭合的后端成功对象。 -/
syntax (name := proveAutoBackendSuccess)
  "prove_auto " "BACKEND " term : tactic

@[tactic proveAutoBackendSuccess] unsafe def evalProveAutoBackendSuccess : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let success ← elabTerm stx[2] none
        let proof ← mkAppM ``LogicSoundness.SetLevel.BackendSuccess.sound #[success]
        closeByProof `prove_auto_backend proof

/-- 回放空理论深嵌入目标的 checked certificate。 -/
syntax (name := proveAutoCheckedValidCertificate)
  "prove_auto " "VALID " term : tactic

@[tactic proveAutoCheckedValidCertificate]
unsafe def evalProveAutoCheckedValidCertificate : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let cert ← elabTerm stx[2] none
        let proof ← mkAppM ``LogicSoundness.SetLevel.CheckedValidCertificate.sound #[cert]
        closeByProof `prove_auto_valid proof

/--
在当前局部上下文中证明一个计算 Bool 为真。

调用方必须先把 closed 投影规约到 proof-free 计算表达式；这里只检查结果，
不对完整证书做全递归正规化。
-/
private unsafe def proveBoolTrue? (expression : Expr) : TacticM (Option Expr) := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then
    throwError "internal kernel replay check retained metavariables{indentExpr expression}"
  if expression.hasFVar then
    throwError "internal kernel replay check retained free variables{indentExpr expression}"
  let trueExpr := mkConst ``Bool.true
  let proofType ← mkEq expression trueExpr
  if ← withTransparency .all <| isDefEq expression trueExpr then
    return some (← mkEqRefl trueExpr)
  let proof ← mkFreshExprMVar (some proofType)
  let savedState ← saveState
  let savedGoals ← getGoals
  setGoals [proof.mvarId!]
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| first | rfl | decide +kernel))
    unless (← getGoals).isEmpty do
      savedState.restore
      return none
    let result ← instantiateMVars proof
    setGoals savedGoals
    return some result
  catch _ =>
    savedState.restore
    return none

private unsafe def closeGoalAttempt (routed : Expr)
    (resourceSummary : ContextResourceSummary := {})
    (onSummary : TacticM Unit := pure ()) : TacticM Unit := do
  let goal ← getMainTarget
  let closedRaw := mkApp2 (mkConst ``GoalAttempt.closed) goal routed
  let closed ← withTransparency .all <| whnf closedRaw
  let (_, closedFreeVariables) ← closed.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in closedFreeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal prove_auto closed replay leaked free variable `{freeVariable.name}`"
    let localDecl := localContext.get! freeVariable
    if localDecl.isImplementationDetail then
      throwError
        "internal prove_auto closed replay retained implementation-detail free variable \
        `{freeVariable.name}` of type{indentExpr localDecl.type}"
  if let some closedProof ← proveBoolTrue? closed then
    let proof ← instantiateMVars <|
      mkApp3 (mkConst ``GoalAttempt.soundOfClosed) goal routed closedProof
    let (_, freeVariables) ← proof.collectFVars.run {}
    for freeVariable in freeVariables.fvarIds do
      unless localContext.contains freeVariable do
        throwError
          "internal prove_auto proof leaked free variable `{freeVariable.name}`"
      let localDecl := localContext.get! freeVariable
      if localDecl.isImplementationDetail then
        throwError
          "internal prove_auto proof retained implementation-detail free variable \
          `{freeVariable.name}` of type{indentExpr localDecl.type}"
    closeByProof `prove_auto_routed proof
  else
    onSummary
    let summaryRaw := mkApp2 (mkConst ``GoalAttempt.summary) goal routed
    let summaryExpr ← withTransparency .all <| whnf summaryRaw
    let label ← evalExpr String (mkConst ``String) summaryExpr
    if !resourceSummary.present then
      throwError "prove_auto routed backend failed: {label}"
    else
      throwError
        "prove_auto routed backend failed: {label}\n\
        context resources: {resourceSummary.render}"

/-- 裸 `prove_auto` 优先消费强相关上下文，再回落到目标索引请求。 -/
syntax (name := proveAutoRouted) "prove_auto" : tactic

private unsafe def runContextRequest (request : ContextRequest)
    (prepared? : Option PreparedContextRequest := none)
    (schedule? : Option ContextProviderSchedule := none)
    (observer : ContextDispatchObserver := {}) :
    TacticM Unit := do
  let dispatch ←
    contextualAttempt? request prepared? schedule? observer
  if let some contextual := dispatch.attempt? then
    closeGoalAttempt contextual dispatch.resourceSummary
      observer.summaryEvaluated
  else
    let requestType := mkApp (mkConst ``GoalRequest) request.goal
    let routed ←
      try
        let goalRequest ← synthInstance requestType
        pure <| mkApp2 (mkConst ``GoalRequest.run) request.goal goalRequest
      catch _ =>
        throwError
          "prove_auto could not synthesize a proof-carrying `GoalRequest` for the current \
          target and no context provider accepted the request; provide a local instance via \
          `GoalRequest.ofSource`, add supported `USE` facts, or use \
          `prove_auto CERT/BACKEND/VALID`."
    closeGoalAttempt routed dispatch.resourceSummary
      observer.summaryEvaluated

/-- 宿主结构规划器与人工 proof 语言共用的动作标签。 -/
inductive HostProofStep where
  | intro
  | fixBinder
  | applyRule
  | construct
  | induct
  | split
  | cases
  | choose
  | specialize
  | forward
  | witness
  | transport
  | exfalso

def HostProofStep.label : HostProofStep → String
  | .intro => "INTRO"
  | .fixBinder => "FIX"
  | .applyRule => "APPLY"
  | .construct => "CONSTRUCTOR"
  | .induct => "INDUCT"
  | .split => "SPLIT"
  | .cases => "CASES"
  | .choose => "CHOOSE"
  | .specialize => "SPECIALIZE"
  | .forward => "FORWARD"
  | .witness => "WITNESS"
  | .transport => "TRANSPORT"
  | .exfalso => "EXFALSO"

/-- 一个宿主结构叶子及其沿父子节点累积的显式 proof 资源。 -/
structure HostProofLeaf where
  goal : MVarId
  resources : Array FVarId := #[]

/-- 单叶 checked terminal 调度的观测统计；不进入任何证明证书。 -/
structure HostTerminalStats where
  providerCalls : Nat := 0
  providerBuilds : Nat := 0
  providerSkips : Nat := 0
  contextPreparations : Nat := 0
  summaryEvaluations : Nat := 0
deriving Repr, Inhabited

/-- 单叶 checked terminal 的事务结果。失败分支已经恢复调用前的完整 Meta 状态。 -/
inductive HostTerminalResult where
  | closed (stats : HostTerminalStats)
  | failed (stats : HostTerminalStats) (message : MessageData)

/-- 从当前 tactic goals 建立不带额外资源的宿主结构叶子。 -/
def currentHostProofLeaves : TacticM (Array HostProofLeaf) := do
  return (← getGoals).toArray.map fun goal => { goal := goal }

private def localFVarIds : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    result := result.push localDecl.fvarId
  return result

private def pushHostProofResource
    (resources : Array FVarId) (resource : FVarId) : Array FVarId :=
  if resources.contains resource then resources else resources.push resource

private def addHostProofResources
    (leaves : Array HostProofLeaf)
    (proofSyntaxes : Array (TSyntax `term)) :
    TacticM (Array HostProofLeaf) := do
  let mut result := #[]
  for index in [0 : leaves.size] do
    let some leaf := leaves[index]?
      | continue
    let mut goal := leaf.goal
    let mut resources := leaf.resources
    for proofSyntax in proofSyntaxes do
      setGoals [goal]
      let proof ← withMainContext do
        let proof ← instantiateMVars (← elabTerm proofSyntax none)
        let proposition ← instantiateMVars (← inferType proof)
        unless ← isProp proposition do
          throwError
            "prove_auto PROOF USE expected a proof resource, got\
            {indentExpr proposition}"
        pure proof
      if proof.isFVar then
        resources := pushHostProofResource resources proof.fvarId!
      else
        let name ← mkFreshUserName `used
        let (resource, child) ← goal.note name proof
        goal := child
        resources := pushHostProofResource resources resource
    setGoals [goal]
    let resourceNames ← withMainContext do
      let mut names := #[]
      for localDecl in (← getLCtx) do
        if resources.contains localDecl.fvarId then
          names := names.push localDecl.userName
      pure names
    trace[YesMetaZFC.proveAuto.proof]
      "resources.added leaf={index + 1}/{leaves.size}; resources={resourceNames}"
    result := result.push { goal := goal, resources := resources }
  setGoals (result.map fun leaf => leaf.goal).toList
  return result

/--
在每个父叶子上执行同一个结构动作，并把新产生的 Prop 局部量登记为 child proof 资源。
-/
def expandHostProofStep
    (parents : Array HostProofLeaf) (step : HostProofStep)
    (structureAction : TacticM Unit) :
    TacticM (Array HostProofLeaf) := do
  let mut allChildren := #[]
  for parentIndex in [0 : parents.size] do
    let some parent := parents[parentIndex]?
      | continue
    setGoals [parent.goal]
    let (parentTarget, parentFVars) ← withMainContext do
      return (← getMainTarget, ← localFVarIds)
    structureAction
    let children := (← getGoals).toArray
    let mut childTargets := #[]
    for childIndex in [0 : children.size] do
      let some child := children[childIndex]?
        | continue
      setGoals [child]
      let (childTarget, childResources, generatedNames) ← withMainContext do
        let localContext ← getLCtx
        let childFVars ← localFVarIds
        let mut resources :=
          parent.resources.filter fun resource => childFVars.contains resource
        let mut generatedNames := #[]
        for localDecl in localContext do
          if parentFVars.contains localDecl.fvarId then
            continue
          let proposition ← instantiateMVars localDecl.type
          if ← isProp proposition then
            resources := pushHostProofResource resources localDecl.fvarId
            generatedNames := generatedNames.push localDecl.userName
        return (← getMainTarget, resources, generatedNames)
      childTargets := childTargets.push childTarget
      allChildren := allChildren.push {
        goal := child
        resources := childResources
      }
      trace[YesMetaZFC.proveAuto.proof]
        "child.resources step={step.label}; child={childIndex + 1}/{children.size}; \
        generated={generatedNames}; total={childResources.size}"
    trace[YesMetaZFC.proveAuto.proof]
      "node.expanded step={step.label}; parent={parentIndex + 1}/{parents.size}; \
      target={parentTarget}; children={childTargets}"
  setGoals (allChildren.map fun child => child.goal).toList
  return allChildren

private unsafe def closeHostProofLeaf
    (origin : String) (index count : Nat) (leaf : HostProofLeaf)
    (prepared? : Option PreparedContextRequest := none)
    (schedule? : Option ContextProviderSchedule := none)
    (observer : ContextDispatchObserver := {}) :
    TacticM Unit := do
  setGoals [leaf.goal]
  withMainContext do
    let target ← getMainTarget
    let mut resourceNames := #[]
    for localDecl in (← getLCtx) do
      if leaf.resources.contains localDecl.fvarId then
        resourceNames := resourceNames.push localDecl.userName
    trace[YesMetaZFC.proveAuto.proof]
      "leaf.start origin={origin}; leaf={index + 1}/{count}; target={target}; \
      resources={resourceNames}"
    try
      runContextRequest {
        goal := target
        useFacts := leaf.resources.map mkFVar
      } prepared? schedule? observer
    catch error =>
      throwError
        "prove_auto {origin} leaf {index + 1}/{count} failed for\
        {indentExpr target}\nleaf resources: {resourceNames}\n\
        {error.toMessageData}"
    trace[YesMetaZFC.proveAuto.proof]
      "leaf.closed origin={origin}; leaf={index + 1}/{count}"

/--
把一个已经机械分解的宿主叶子交给现有 checked provider 调度。

成功时关闭该叶；失败时恢复调用前状态并返回诊断，使非可信上层可以继续回溯。
-/
unsafe def tryCloseHostProofTerminal
    (origin : String) (leaf : HostProofLeaf) :
    TacticM HostTerminalResult := do
  let savedState ← saveState
  let providerCalls ← IO.mkRef 0
  let providerBuilds ← IO.mkRef 0
  let providerSkips ← IO.mkRef 0
  let contextPreparations ← IO.mkRef 0
  let summaryEvaluations ← IO.mkRef 0
  let observer : ContextDispatchObserver := {
    providerVisited := fun _ => providerCalls.modify (· + 1)
    providerBuilt := fun _ _ => providerBuilds.modify (· + 1)
    providerSkipped := fun _ => providerSkips.modify (· + 1)
    prepared := fun _ => contextPreparations.modify (· + 1)
    summaryEvaluated := summaryEvaluations.modify (· + 1)
  }
  let stats : TacticM HostTerminalStats := do
    return {
      providerCalls := ← providerCalls.get
      providerBuilds := ← providerBuilds.get
      providerSkips := ← providerSkips.get
      contextPreparations := ← contextPreparations.get
      summaryEvaluations := ← summaryEvaluations.get
    }
  try
    let schedule ← prepareContextProviderSchedule
    closeHostProofLeaf origin 0 1 leaf none (some schedule) observer
    setGoals []
    return .closed (← stats)
  catch error =>
    let result ← stats
    savedState.restore
    return .failed result error.toMessageData

/-- 把全部宿主结构叶子统一交回 checked context provider。 -/
unsafe def closeHostProofLeaves
    (origin : String) (leaves : Array HostProofLeaf) :
    TacticM Unit := do
  let schedule ← prepareContextProviderSchedule
  for index in [0 : leaves.size] do
    let some leaf := leaves[index]?
      | continue
    closeHostProofLeaf origin index leaves.size leaf none (some schedule)
  setGoals []

/-- 以完整事务运行一个结构节点；动作或任一 checked 叶子失败时恢复父状态。 -/
unsafe def runHostProofNode
    (step : HostProofStep) (structureAction : TacticM Unit) :
    TacticM Unit := do
  let savedState ← saveState
  try
    let leaves ← currentHostProofLeaves
    let leaves ← expandHostProofStep leaves step structureAction
    closeHostProofLeaves step.label leaves
  catch error =>
    savedState.restore
    throw error

private def isHostImplicationTarget : TacticM Bool := withMainContext do
  let target ← whnf (← getMainTarget)
  let .forallE _ domain body _ := target
    | return false
  return (← isProp domain) && !body.hasLooseBVars

/-- 引入一个非依赖 Prop premise；所得 proof 由父子资源差分登记。 -/
def introduceHostImplication : TacticM Unit := do
  unless ← isHostImplicationTarget do
    throwError
      "prove_auto INTRO expected a nondependent proposition implication target"
  let (_, child) ← (← getMainGoal).intro1P
  setGoals [child]

private def introduceHostImplications : TacticM Unit := do
  let mut introduced := false
  while ← isHostImplicationTarget do
    introduceHostImplication
    introduced := true
  unless introduced do
    throwError
      "prove_auto INTRO expected a nondependent proposition implication target"

private def ensureFreshHostBinderName
    (step : String) (name : Name) : MetaM Unit := do
  for localDecl in (← getLCtx) do
    if localDecl.userName == name then
      throwError
        "prove_auto {step} binder name `{name}` is already used in the local context"

private def ensureFixTarget (name : Name) : TacticM Unit := withMainContext do
  ensureFreshHostBinderName "FIX" name
  let target ← whnf (← getMainTarget)
  unless ← isProp target do
    throwError
      "prove_auto FIX expected a proposition-valued `Forall` target, got\
      {indentExpr target}"
  let .forallE _ domain _ _ := target
    | throwError
        "prove_auto FIX expected a proposition-valued `Forall` target, got\
        {indentExpr target}"
  if ← isProp domain then
    throwError
      "prove_auto FIX expected an object binder, but its domain is a proposition; \
      use `INTRO`"

/-- 引入一个命名对象 binder；新对象本身不构成 proof 资源。 -/
def fixHostBinderName (name : Name) : TacticM Unit := do
  ensureFixTarget name
  let (_, child) ← (← getMainGoal).intro name
  setGoals [child]

private def fixHostBinder (name : Ident) : TacticM Unit :=
  fixHostBinderName name.getId

private partial def containsExplicitApplySyntax (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.explicit ||
    stx.getArgs.any containsExplicitApplySyntax

private def consumesInstanceArgument (expression : Expr) : MetaM Bool := do
  let expression := expression.consumeMData
  let arguments := expression.getAppArgs
  let mut functionType ← inferType expression.getAppFn
  for index in [0 : arguments.size] do
    functionType ← whnf functionType
    let .forallE _ _ body binderInfo := functionType
      | return false
    if binderInfo.isInstImplicit then
      return true
    functionType := body.instantiate1 arguments[index]!
  return false

private def validateApplySyntax
    (ruleSyntax : TSyntax `term) (rawRule : Expr) : MetaM Unit := do
  if ← consumesInstanceArgument rawRule then
    unless containsExplicitApplySyntax ruleSyntax.raw do
      throwError
        "prove_auto APPLY does not synthesize typeclass arguments for theorem \
        applications; supply every argument with an explicit `@...` term"

/--
按前提到结论的方向应用一个已 elaborated theorem expression。

只有尚未解决的显式 Prop premise 会成为 child；其余参数必须在进入动作前确定。
-/
structure HostApplyPlan where
  application : Expr
  children : Array MVarId

def prepareHostApply
    (rawRule target : Expr) : MetaM HostApplyPlan := do
  let ruleHead := rawRule.consumeMData.getAppFn
  unless ruleHead.isFVar || ruleHead.isConst do
    throwError
      "prove_auto APPLY expected a local theorem or an explicit theorem \
      application"
  unless (← getMVarsNoDelayed rawRule).isEmpty do
    throwError
      "prove_auto APPLY proof term contains unresolved implicit or synthetic \
      metavariables; instantiate it explicitly"
  let rule ← instantiateMVars rawRule
  let ruleType ← instantiateMVars (← inferType rule)
  unless ← isProp ruleType do
    throwError
      "prove_auto APPLY expected a proof-valued theorem, got\
      {indentExpr ruleType}"
  let argumentCount ← getExpectedNumArgs ruleType
  let targetArgumentCount ← getExpectedNumArgs target
  let firstCount := argumentCount - targetArgumentCount
  let mut count := firstCount
  let mut application? : Option (Array Expr × Array BinderInfo) := none
  while count <= argumentCount && application?.isNone do
    let savedState ← saveState
    let (arguments, binderInfos, conclusion) ←
      forallMetaTelescopeReducing ruleType (some count)
    if ← isDefEqGuarded conclusion target then
      application? := some (arguments, binderInfos)
    else
      savedState.restore
    count := count + 1
  let some (arguments, binderInfos) := application?
    | throwError
        "prove_auto APPLY theorem conclusion does not match the current target; \
        APPLY is directed from premises to conclusion\n\
        theorem type:{indentExpr ruleType}\n\
        target:{indentExpr target}"
  let mut children := #[]
  for index in [0 : arguments.size] do
    let argument := arguments[index]!
    let argumentId := argument.mvarId!
    if ← argumentId.isAssigned then
      continue
    let premise ← instantiateMVars (← inferType argument)
    let binderInfo := binderInfos[index]!
    if binderInfo.isInstImplicit then
      throwError
        "prove_auto APPLY left an unresolved typeclass argument\
        {indentExpr premise}\n\
        supply it explicitly in the proof term"
    unless binderInfo.isExplicit do
      throwError
        "prove_auto APPLY does not expose an implicit premise as a checked leaf\
        {indentExpr premise}\n\
        instantiate it explicitly before APPLY"
    unless ← isProp premise do
      throwError
        "prove_auto APPLY left an unresolved object argument\
        {indentExpr premise}\n\
        specialize it explicitly before APPLY"
    children := children.push argumentId
  if children.isEmpty then
    throwError
      "prove_auto APPLY would close the target without a checked premise; \
      use `USE` or `AUTO` for a direct proof"
  let application ← instantiateMVars (mkAppN rule arguments)
  for metavariable in ← getMVarsNoDelayed application do
    unless children.contains metavariable || (← metavariable.isAssigned) do
      throwError
        "prove_auto APPLY produced an unresolved metavariable outside its \
        proposition premises; instantiate the proof term explicitly"
  return { application, children }

def applyHostProofExpr
    (rawRule : Expr) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let plan ← prepareHostApply rawRule target
  goal.assign plan.application
  plan.children.forM (·.headBetaType)
  setGoals plan.children.toList

/--
事务式检查 APPLY 产生的每个显式命题子目标是否都能由相继式初始规则闭合。

返回 `none` 表示规则不匹配当前目标；预检只保留 proof-free 分类，所有 metavariable
赋值和临时子目标在返回前完整恢复。资源槽位沿用 leaf 的稳定顺序，执行期仍由
`HostSequent.InitialRuleStep` 在当前 child 上重新准入并立即消费。
-/
private def hostApplyInitialChildren?
    (proof target : Expr) (resources : Array FVarId) :
    MetaM (Option Bool) := do
  let savedState ← saveState
  let result ←
    try
      let plan ← prepareHostApply proof target
      let mut initialChildren := true
      for child in plan.children do
        let childTarget ← instantiateMVars (← child.getType)
        if childTarget.hasMVar then
          initialChildren := false
          break
        if (← HostSequent.admitInitialRule {
              goal := child
              resources := resources
            }).isNone then
          initialChildren := false
          break
      pure (some initialChildren)
    catch _ =>
      pure none
  savedState.restore
  return result

private def initialHostSequentResourceIds?
    (children : Array MVarId) (candidates : Array ContextCandidate) :
    MetaM (Option (Array FVarId)) := do
  let candidateResources :=
    candidates.foldl
      (fun resources candidate =>
        if candidate.proof.isFVar then
          pushHostProofResource resources candidate.proof.fvarId!
        else
          resources)
      #[]
  let mut resources := #[]
  for child in children do
    let some step ← HostSequent.admitInitialRule {
          goal := child
          resources := candidateResources
        }
      | return none
    resources := pushHostProofResource resources step.resource
  return some resources

/--
寻找一条完全由既有 proof 决定的有限反证链：

`EXFALSO -> APPLY producer -> WITNESS object -> CONSTRUCTOR -> initial rules`。
任一步需要猜测对象、实例、隐式命题或留下非精确 child 都会拒绝。
-/
private def inferHostSequentContradictionDescriptor?
    (producer : ContextCandidate) (target : Expr)
    (candidates : Array ContextCandidate)
    (objects : Array HostSequentTypedObject) :
    MetaM (Option HostSequentContradictionDescriptor) := do
  unless producer.proof.isFVar do
    return none
  let savedState ← saveState
  let result? ←
    try
      let falsePlan ← prepareHostApply producer.proof (mkConst ``False)
      if falsePlan.children.size != 1 then
        pure none
      else
        let premise ← instantiateMVars (← falsePlan.children[0]!.getType)
        if ← expressionsDefEq premise target then
          pure none
        else
          let premise ← whnf premise
          if !premise.isAppOfArity ``Exists 2 then
            pure none
          else
            let mut result? : Option HostSequentContradictionDescriptor := none
            for object in objects do
              if result?.isSome then
                break
              let some witness ←
                  typedHostSequentWitnessDescriptor? premise object
                | continue
              let constructors ←
                targetHostSequentConstructors witness.instanceProposition
              for constructor in constructors do
                let constructorProof ←
                  mkConstWithFreshMVarLevels constructor.constructorName
                let constructorPlan? ←
                  try
                    some <$> prepareHostApply constructorProof
                      witness.instanceProposition
                  catch _ =>
                    pure none
                let some constructorPlan := constructorPlan?
                  | continue
                let some initialResources ←
                    initialHostSequentResourceIds?
                      constructorPlan.children candidates
                  | continue
                result? := some {
                  witnessLabel := witness.label
                  witness := witness.witness
                  constructorName := constructor.constructorName
                  initialResources := initialResources
                  expectedChildren := constructorPlan.children.size
                }
                break
            pure result?
    catch _ =>
      pure none
  savedState.restore
  return result?

/--
为聚焦相继式准备当前叶子的有限 CASES、目标构造子和确定性反证候选。

该接口复用相继式候选准入器，但不运行 provider。
-/
def prepareHostSequentBranchIndex
    (target : Expr) (resources : Array FVarId)
    (maxForwardCandidates : Nat := 64)
    (maxWitnessCandidates : Nat := 64)
    (generated : Array Expr := #[]) :
    TacticM HostSequentBranchIndex := withMainContext do
  let target ← instantiateMVars (← whnf target)
  let prepared ← prepareContextRequest {
      goal := target
      useFacts := resources.map mkFVar
    }
  let planned ←
    prepareHostSequentContext prepared
      maxForwardCandidates maxWitnessCandidates generated
  let mut contradictions := #[]
  unless target.isConstOf ``False do
    let objects ← localHostSequentObjects
    for producer in planned.request.candidates do
      let relevance :=
        ContextRelevance.score planned.request.goalProfile producer.profile
      if relevance == 0 then
        continue
      if let some descriptor ←
          inferHostSequentContradictionDescriptor?
            producer target planned.request.candidates objects then
        contradictions := contradictions.push {
          producer
          descriptor
          relevance
        }
  return {
    choose := planned.index.choose
    specialize := planned.index.specialize
    forward := planned.index.forward
    witness := planned.index.witness
    transport := planned.index.transport
    cases := planned.index.cases
    constructors := planned.index.constructors
    contradictions
  }

private def applyHostProof
    (ruleSyntax : TSyntax `term) : TacticM Unit := withMainContext do
  let rawRule ← elabTermForApply ruleSyntax
  validateApplySyntax ruleSyntax rawRule
  applyHostProofExpr rawRule

private def inductiveMajorInfo
    (majorId : FVarId) : TacticM Name := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless ← isProp target do
    throwError
      "prove_auto INDUCT expected a proposition-valued target, got\
      {indentExpr target}"
  let majorType ← instantiateMVars (← whnf (← inferType (mkFVar majorId)))
  let some inductiveName := majorType.getAppFn.constName?
    | throwError
        "prove_auto INDUCT expected a local value or proof of an inductive type, got\
        {indentExpr majorType}"
  if inductiveName == ``Exists then
    throwError
      "prove_auto INDUCT does not eliminate `Exists`; use `CHOOSE`"
  if inductiveName == ``Eq || inductiveName == ``HEq then
    throwError
      "prove_auto INDUCT does not eliminate equality; use `TRANSPORT`"
  unless ← isInductive inductiveName do
    throwError
      "prove_auto INDUCT expected a local value or proof of an inductive type, got\
      {indentExpr majorType}"
  let recursorName := inductiveName.appendCore `rec
  unless (← getEnv).contains recursorName do
    throwError
      "prove_auto INDUCT could not find the built-in recursor \
      `{recursorName}`"
  let recursorInfo ← mkRecursorInfo recursorName
  if recursorInfo.paramsPos.any fun parameter => parameter.isNone then
    throwError
      "prove_auto INDUCT built-in recursor requires a synthesized typeclass \
      parameter; this shape is unsupported"
  return recursorName

private def ensureInductionBranch
    (branch : MVarId) : TacticM Unit := do
  setGoals [branch]
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    unless ← isProp target do
      throwError
        "prove_auto INDUCT produced a non-proposition branch\
        {indentExpr target}"
    unless (← getMVarsNoDelayed target).isEmpty do
      throwError
        "prove_auto INDUCT produced a branch target with unresolved \
        metavariables"
    for localDecl in (← getLCtx) do
      unless (← getMVarsNoDelayed localDecl.type).isEmpty do
        throwError
          "prove_auto INDUCT produced a branch context with unresolved \
          metavariables"

/-- 用 major 类型的内建 recursor 建立 proof-carrying 归纳分支。 -/
def inductHostMajorId (majorId : FVarId) : TacticM Unit := do
  let recursorName ← inductiveMajorInfo majorId
  let goal ← getMainGoal
  let subgoals ← withMainContext do
    goal.induction majorId recursorName
  if subgoals.isEmpty then
    throwError
      "prove_auto INDUCT produced no checked branches; empty eliminations are \
      not accepted"
  let children := subgoals.map fun subgoal => subgoal.mvarId
  for child in children do
    ensureInductionBranch child
  setGoals children.toList

private def inductHostMajor (major : Ident) : TacticM Unit := do
  let majorId ←
    try
      getFVarId major.raw
    catch _ =>
      throwError
        "prove_auto INDUCT expected a local inductive variable"
  inductHostMajorId majorId

private def ensureSplitTarget : TacticM Unit := withMainContext do
  let target ← whnf (← getMainTarget)
  let head := target.getAppFn.constName?
  unless head == some ``And || head == some ``Iff do
    throwError
      "prove_auto SPLIT expected a top-level `And` or `Iff` target, got\
      {indentExpr target}"

/-- 用目标的首个适用构造子建立 And/Iff proof children。 -/
def splitHostTarget : TacticM Unit := do
  ensureSplitTarget
  let children ← (← getMainGoal).constructor
  setGoals children

private def ensureCasesMajor (major : Expr) : MetaM Unit := do
  let type ← whnf (← inferType major)
  unless ← isProp type do
    throwError
      "prove_auto CASES expected a proof-valued major premise, got\
      {indentExpr type}"
  let some head := type.getAppFn.constName?
    | throwError
        "prove_auto CASES expected an inductive proposition, got\
        {indentExpr type}"
  if head == ``Exists then
    throwError
      "prove_auto CASES does not eliminate `Exists`; use the forthcoming \
      `CHOOSE` proof step"
  if head == ``Eq || head == ``HEq then
    throwError
      "prove_auto CASES does not eliminate equality; use directed proof \
      transport"
  unless ← isInductivePredicate head do
    throwError
      "prove_auto CASES expected an inductive proposition, got\
      {indentExpr type}"

private def ensureLocalProof (step : String) (proof : Expr) : MetaM Unit := do
  unless proof.isFVar do
    throwError
      "prove_auto {step} expected a local proof variable"
  unless ← isProp (← inferType proof) do
    throwError
      "prove_auto {step} expected a proof-valued local variable"

private def ensureExistsMajor (major : Expr) : MetaM Unit := do
  ensureLocalProof "CHOOSE" major
  let type ← whnf (← inferType major)
  unless type.isAppOfArity ``Exists 2 do
    throwError
      "prove_auto CHOOSE expected a local `Exists` proof, got\
      {indentExpr type}"

private def specializationDomain (specialized : Expr) : MetaM Expr := do
  let type ← whnf (← inferType specialized)
  let .forallE _ domain _ _ := type
    | throwError
        "prove_auto SPECIALIZE exhausted the quantified proof at\
        {indentExpr type}"
  if ← isProp domain then
    throwError
      "prove_auto SPECIALIZE does not apply implication premises; \
      use checked search or `INTRO`"
  return domain

/-- 沿对象 binder 专门化局部全称 proof，并把所得 proof note 到当前 leaf。 -/
def specializeHostProofExpr
    (major : Expr) (arguments : Array Expr) : TacticM Unit := withMainContext do
  ensureLocalProof "SPECIALIZE" major
  let mut specialized := major
  for argument in arguments do
    let domain ← specializationDomain specialized
    let argumentType ← inferType argument
    unless ← isDefEq argumentType domain do
      throwError
        "prove_auto SPECIALIZE argument has type\
        {indentExpr argumentType}\nexpected:{indentExpr domain}"
    specialized := mkApp specialized argument
    discard <| inferType specialized
  specialized ← instantiateMVars specialized
  unless (← getMVarsNoDelayed specialized).isEmpty do
    throwError
      "prove_auto SPECIALIZE produced unresolved metavariables; \
      instantiate every object argument explicitly"
  let proposition ← instantiateMVars (← inferType specialized)
  unless ← isProp proposition do
    throwError
      "prove_auto SPECIALIZE did not produce a proposition, got\
      {indentExpr proposition}"
  let name ← mkFreshUserName `specialized
  let (_, child) ← (← getMainGoal).note name specialized
  setGoals [child]

/-- 用已检查的对象与 proof 参数生成一个新的前向局部事实。 -/
private def ensureCheckedProof (step : String) (proof : Expr) : MetaM Unit := do
  unless (← getMVarsNoDelayed proof).isEmpty do
    throwError
      "prove_auto {step} received a proof term with unresolved metavariables"
  unless ← isProp (← inferType proof) do
    throwError
      "prove_auto {step} expected a proof-valued term"

def forwardHostSequentExpr
    (descriptor : HostSequentForwardDescriptor)
    (candidate : ContextCandidate)
    (arguments : Array Expr) : TacticM Unit := withMainContext do
  ensureCheckedProof "FORWARD" candidate.proof
  unless arguments.size ==
      descriptor.objectArguments + descriptor.propositionPremises do
    throwError
      "prove_auto FORWARD received an inconsistent argument layout"
  for argument in arguments do
    unless (← getMVarsNoDelayed argument).isEmpty do
      throwError
        "prove_auto FORWARD argument contains unresolved metavariables"
  let application ← instantiateMVars (mkAppN candidate.proof arguments)
  unless (← getMVarsNoDelayed application).isEmpty do
    throwError
      "prove_auto FORWARD application contains unresolved metavariables"
  let proposition ← instantiateMVars (← whnf (← inferType application))
  unless ← isProp proposition do
    throwError
      "prove_auto FORWARD did not produce a proposition, got\
      {indentExpr proposition}"
  unless ← expressionsDefEq proposition descriptor.result do
    throwError
      "prove_auto FORWARD result no longer matches its indexed descriptor"
  let name ← mkFreshUserName `forwarded
  let (_, child) ← (← getMainGoal).note name application
  setGoals [child]

private def elaborateSpecialization
    (majorSyntax : TSyntax `term)
    (argumentSyntax : Array (TSyntax `term)) :
    TacticM (Expr × Array Expr) := withMainContext do
  let major ← elabTerm majorSyntax none
  let mut specialized := major
  let mut arguments := #[]
  for argumentSyntax in argumentSyntax do
    let domain ← specializationDomain specialized
    let argument ← elabTerm argumentSyntax (some domain)
    arguments := arguments.push argument
    specialized := mkApp specialized argument
    discard <| inferType specialized
  return (major, arguments)

private def specializeHostProof
    (majorSyntax : TSyntax `term)
    (argumentSyntax : Array (TSyntax `term)) : TacticM Unit := do
  let (major, arguments) ← elaborateSpecialization majorSyntax argumentSyntax
  specializeHostProofExpr major arguments

private def ensureWitnessTarget (witness : Expr) : TacticM Unit := withMainContext do
  let target ← whnf (← getMainTarget)
  unless target.isAppOfArity ``Exists 2 do
    throwError
        "prove_auto WITNESS expected a top-level `Exists` target, got\
        {indentExpr target}"
  let domain := target.getAppArgs[0]!
  let witnessType ← inferType witness
  unless ← isDefEq witnessType domain do
    throwError
      "prove_auto WITNESS term has type\
      {indentExpr witnessType}\nexpected:{indentExpr domain}"
  unless (← getMVarsNoDelayed witness).isEmpty do
    throwError
      "prove_auto WITNESS contains unresolved metavariables"

private def ensureTransport
    (source destination proof : Expr) :
    TacticM Unit := withMainContext do
  let equality ← whnf (← inferType proof)
  unless equality.isAppOfArity ``Eq 3 do
    throwError
      "prove_auto TRANSPORT expected an equality proof, got\
      {indentExpr equality}"
  let arguments := equality.getAppArgs
  let type := arguments[0]!
  let left := arguments[1]!
  let right := arguments[2]!
  let sourceType ← inferType source
  let destinationType ← inferType destination
  unless ← isDefEq sourceType type do
    throwError
      "prove_auto TRANSPORT source has type\
      {indentExpr sourceType}\nexpected:{indentExpr type}"
  unless ← isDefEq destinationType type do
    throwError
      "prove_auto TRANSPORT target has type\
      {indentExpr destinationType}\nexpected:{indentExpr type}"
  unless ← isDefEq left source do
    throwError
      "prove_auto TRANSPORT source does not match the equality left side:\
      {indentExpr left}"
  unless ← isDefEq right destination do
    throwError
      "prove_auto TRANSPORT target does not match the equality right side:\
      {indentExpr right}"

/-- 检查 CASES 分支没有把未解析 metavariable 带入目标或局部上下文。 -/
private def ensureHostCasesSubgoalStable
    (subgoal : CasesSubgoal) : MetaM Unit := subgoal.mvarId.withContext do
  let target ← instantiateMVars (← subgoal.mvarId.getType)
  unless (← getMVarsNoDelayed target).isEmpty do
    throwError
      "prove_auto CASES produced a branch target with unresolved metavariables"
  for localDecl in (← getLCtx) do
    let type ← instantiateMVars localDecl.type
    unless (← getMVarsNoDelayed type).isEmpty do
      throwError
        "prove_auto CASES produced a branch context with unresolved metavariables"
    if let some value := localDecl.value? then
      let value ← instantiateMVars value
      unless (← getMVarsNoDelayed value).isEmpty do
        throwError
          "prove_auto CASES produced a branch let-value with unresolved metavariables"

/-- 对一个已 elaborated 的归纳命题 proof 建立分支并返回 Lean 的构造子标签。 -/
private def casesHostProofSubgoals
    (major : Expr) : TacticM (Array CasesSubgoal) := withMainContext do
  ensureCasesMajor major
  unless (← getMVarsNoDelayed major).isEmpty do
    throwError
      "prove_auto CASES proof term contains unresolved metavariables"
  let goal ← getMainGoal
  let (majorId, goal) ←
    if major.isFVar then
      pure (major.fvarId!, goal)
    else
      let name ← mkFreshUserName `casesMajor
      goal.note name major
  let subgoals ← goal.cases majorId
  for subgoal in subgoals do
    ensureHostCasesSubgoalStable subgoal
  return subgoals

/-- 对一个已 elaborated 的归纳命题 proof 建立分支。 -/
def casesHostProofExpr (major : Expr) : TacticM Unit := do
  let subgoals ← casesHostProofSubgoals major
  setGoals (subgoals.map fun subgoal => subgoal.mvarId).toList

/-- 自动 CASES 必须与索引阶段保存的完整构造子顺序逐项一致。 -/
def casesHostProofExprExpected
    (descriptor : HostSequentCasesDescriptor) (major : Expr) :
    TacticM Unit := do
  unless descriptor.expectedBranches == descriptor.constructors.size do
    throwError
      "prove_auto CASES received an inconsistent finite-cases descriptor"
  let subgoals ← casesHostProofSubgoals major
  unless subgoals.size == descriptor.expectedBranches do
    throwError
      "prove_auto CASES expected {descriptor.expectedBranches} branches for \
      `{descriptor.inductiveName}`, got {subgoals.size}"
  for index in [0 : subgoals.size] do
    let some subgoal := subgoals[index]?
      | throwError "prove_auto CASES lost branch {index + 1}"
    let expected := descriptor.constructors[index]!
    unless subgoal.ctorName == some expected do
      throwError
        "prove_auto CASES branch {index + 1} expected constructor `{expected}`, \
        got {repr subgoal.ctorName}"
  setGoals (subgoals.map fun subgoal => subgoal.mvarId).toList

private def casesHostProof
    (majorSyntax : TSyntax `term) : TacticM Unit := withMainContext do
  casesHostProofExpr (← elabTerm majorSyntax none)

/-- 消去局部 Exists proof，并显式命名见证和实例 proof。 -/
def chooseHostProofId
    (majorId : FVarId) (witness proof : Name) : TacticM Unit := withMainContext do
  ensureExistsMajor (mkFVar majorId)
  ensureFreshHostBinderName "CHOOSE" witness
  ensureFreshHostBinderName "CHOOSE" proof
  if witness == proof then
    throwError
      "prove_auto CHOOSE witness and proof names must be distinct"
  let goal ← getMainGoal
  let names : Array AltVarNames := #[{
    explicit := true
    varNames := [witness, proof]
  }]
  let subgoals ← goal.cases majorId names
  let some subgoal := subgoals[0]?
    | throwError
        "prove_auto CHOOSE expected exactly one existential branch"
  if subgoals.size != 1 then
    throwError
      "prove_auto CHOOSE expected exactly one existential branch"
  setGoals [subgoal.mvarId]

private def chooseHostProof
    (major witness proof : Ident) : TacticM Unit := do
  let majorId ←
    try
      getFVarId major.raw
    catch _ =>
      throwError
        "prove_auto CHOOSE expected a local `Exists` proof"
  chooseHostProofId majorId witness.getId proof.getId

/-- 为顶层 Exists 目标固定对象见证，只留下实例命题 child。 -/
def witnessHostTargetExpr (witness : Expr) : TacticM Unit := do
  ensureWitnessTarget witness
  let child ← (← getMainGoal).existsIntro witness
  setGoals [child]

def applyHostContradiction
    (producer : ContextCandidate)
    (descriptor : HostSequentContradictionDescriptor) :
    TacticM Unit := do
  let falseGoal ← withMainContext do
    (← getMainGoal).exfalso
  setGoals [falseGoal]
  applyHostProofExpr producer.proof
  let premises := (← getGoals).toArray
  unless premises.size == 1 do
    throwError
      "prove_auto contradiction producer generated {premises.size} premises"
  witnessHostTargetExpr descriptor.witness
  let constructorProof ←
    mkConstWithFreshMVarLevels descriptor.constructorName
  applyHostProofExpr constructorProof
  let children := (← getGoals).toArray
  unless children.size == descriptor.expectedChildren do
    throwError
      "prove_auto contradiction constructor expected \
      {descriptor.expectedChildren} children, produced {children.size}"

private def witnessHostTarget
    (witnessSyntax : TSyntax `term) : TacticM Unit := withMainContext do
  let target ← whnf (← getMainTarget)
  unless target.isAppOfArity ``Exists 2 do
    throwError
      "prove_auto WITNESS expected a top-level `Exists` target, got\
      {indentExpr target}"
  let domain := target.getAppArgs[0]!
  witnessHostTargetExpr (← elabTerm witnessSyntax (some domain))

/-- 按 source = destination 从右向左重写目标，留下关于 source 的 checked child。 -/
def transportHostTargetExpr
    (source destination proof : Expr) : TacticM Unit := withMainContext do
  ensureTransport source destination proof
  unless (← getMVarsNoDelayed proof).isEmpty do
    throwError
      "prove_auto TRANSPORT equality proof contains unresolved metavariables"
  let goal ← getMainGoal
  let result ← goal.rewrite (← getMainTarget) proof (symm := true)
  unless result.mvarIds.isEmpty do
    throwError
      "prove_auto TRANSPORT equality proof produced unresolved side goals"
  let child ← goal.replaceTargetEq result.eNew result.eqProof
  setGoals [child]

private def transportHostTarget
    (sourceSyntax destinationSyntax proofSyntax : TSyntax `term) :
    TacticM Unit := withMainContext do
  let proof ← elabTerm proofSyntax none
  let equality ← whnf (← inferType proof)
  unless equality.isAppOfArity ``Eq 3 do
    throwError
      "prove_auto TRANSPORT expected an equality proof, got\
      {indentExpr equality}"
  let type := equality.getAppArgs[0]!
  let source ← elabTerm sourceSyntax (some type)
  let destination ← elabTerm destinationSyntax (some type)
  transportHostTargetExpr source destination proof

/-- 显式提供普通 Lean proof term；其语义由接受请求的 provider 负责重化。 -/
syntax (name := proveAutoRoutedUsing)
  "prove_auto" " USE " term,+ : tactic

@[tactic proveAutoRoutedUsing] unsafe def evalProveAutoRoutedUsing : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let goal ← getMainTarget
        let facts ← stx[2].getSepArgs.mapM fun fact =>
          elabTerm fact none
        runContextRequest {
          goal := goal
          useFacts := facts
        }

/--
连续引入非依赖命题前提，并把最终叶子交回 checked search。

引入产生的局部 proof 会经过与 `USE` 相同的相关性选择和 source 重化。
-/
syntax (name := proveAutoHostIntro)
  "prove_auto" " INTRO" : tactic

@[tactic proveAutoHostIntro] unsafe def evalProveAutoHostIntro : Tactic :=
  fun _ => do
    withProveAutoResources do
      runHostProofNode .intro introduceHostImplications

/--
引入一个对象 `Forall` binder；对象只进入 child context，不作为 proof source。
-/
syntax (name := proveAutoHostFix)
  "prove_auto" " FIX " ident : tactic

@[tactic proveAutoHostFix] unsafe def evalProveAutoHostFix : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| prove_auto FIX $name:ident) =>
        withProveAutoResources do
          runHostProofNode .fixBinder <| fixHostBinder name
    | _ =>
        throwUnsupportedSyntax

/--
按“前提到结论”的方向应用一个显式 proof term。

只有尚未解决的显式命题前提会成为 child 叶子；对象、隐式与实例参数必须先显式确定。
-/
syntax (name := proveAutoHostApply)
  "prove_auto" " APPLY " term : tactic

@[tactic proveAutoHostApply] unsafe def evalProveAutoHostApply : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| prove_auto APPLY $rule:term) =>
        withProveAutoResources do
          runHostProofNode .applyRule <|
            applyHostProof rule
    | _ =>
        throwUnsupportedSyntax

/--
按局部 major 的内建 recursor 建立归纳父节点；分支参数和归纳假设进入 child context。
-/
syntax (name := proveAutoHostInduct)
  "prove_auto" " INDUCT " ident : tactic

@[tactic proveAutoHostInduct] unsafe def evalProveAutoHostInduct : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| prove_auto INDUCT $major:ident) =>
        withProveAutoResources do
          runHostProofNode .induct <|
            inductHostMajor major
    | _ =>
        throwUnsupportedSyntax

/--
用 Lean 构造子拆分顶层 `And` 或 `Iff`，每个子目标独立回到 checked search。
-/
syntax (name := proveAutoHostSplit)
  "prove_auto" " SPLIT" : tactic

@[tactic proveAutoHostSplit] unsafe def evalProveAutoHostSplit : Tactic :=
  fun _ => do
    withProveAutoResources do
      runHostProofNode .split splitHostTarget

/--
对非存在、非等式的归纳命题作宿主分支，并让每个分支回到 checked search。

`Exists` 见证和等式 transport 保留给专用 proof step，避免把量词语义隐藏在通用分支里。
-/
syntax (name := proveAutoHostCases)
  "prove_auto" " CASES " term : tactic

@[tactic proveAutoHostCases] unsafe def evalProveAutoHostCases : Tactic :=
  fun stx => do
    withProveAutoResources do
      let majorSyntax : TSyntax `term := ⟨stx[2]⟩
      runHostProofNode .cases <|
        casesHostProof majorSyntax

/--
消去一个局部存在证明，并用用户给出的名字暴露见证与实例 proof。
-/
syntax (name := proveAutoHostChoose)
  "prove_auto" " CHOOSE " ident " AS " ident ", " ident : tactic

@[tactic proveAutoHostChoose] unsafe def evalProveAutoHostChoose : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| prove_auto CHOOSE $major:ident AS $witness:ident, $proof:ident) =>
        withProveAutoResources do
          runHostProofNode .choose <|
            chooseHostProof major witness proof
    | _ =>
        throwUnsupportedSyntax

/--
沿一个局部全称 proof 的嵌套 binder 依次专门化，并把所得 proof 加入 checked 叶子资源。
-/
syntax (name := proveAutoHostSpecialize)
  "prove_auto" " SPECIALIZE " ident " AT " "(" term,+ ")" : tactic

@[tactic proveAutoHostSpecialize]
unsafe def evalProveAutoHostSpecialize : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| prove_auto SPECIALIZE $major:ident AT ($arguments:term,*)) =>
        withProveAutoResources do
          let majorSyntax : TSyntax `term := ⟨major.raw⟩
          runHostProofNode .specialize <|
            specializeHostProof majorSyntax arguments.getElems
    | _ =>
        throwUnsupportedSyntax

/--
为顶层存在目标指定数学见证；实例目标仍由 checked search 证明。
-/
syntax (name := proveAutoHostWitness)
  "prove_auto" " WITNESS " term : tactic

@[tactic proveAutoHostWitness] unsafe def evalProveAutoHostWitness : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| prove_auto WITNESS $witness:term) =>
        withProveAutoResources do
          runHostProofNode .witness <|
            witnessHostTarget witness
    | _ =>
        throwUnsupportedSyntax

/--
按给定等式从左端向右端搬运宿主命题。

步骤验证 `h : from = to`，随后只把目标中的 `to` 反向还原为 `from`；
所得叶子继续由 checked search 消费已有 proof。
-/
syntax (name := proveAutoHostTransport)
  "prove_auto" " TRANSPORT " "FROM " term " TO " term " BY " term : tactic

@[tactic proveAutoHostTransport]
unsafe def evalProveAutoHostTransport : Tactic :=
  fun stx => do
    match stx with
    | `(tactic|
        prove_auto TRANSPORT FROM $source:term TO $destination:term BY $proof:term) =>
        withProveAutoResources do
          runHostProofNode .transport <|
            transportHostTarget source destination proof
    | _ =>
        throwUnsupportedSyntax

/-! ## 可组合宿主 proof 计划 -/

declare_syntax_cat proveAutoHostPlanStep
syntax "USE " "(" term,+ ")" : proveAutoHostPlanStep
syntax "INTRO" : proveAutoHostPlanStep
syntax "FIX " ident : proveAutoHostPlanStep
syntax "APPLY " term : proveAutoHostPlanStep
syntax "INDUCT " ident : proveAutoHostPlanStep
syntax "SPLIT" : proveAutoHostPlanStep
syntax "CASES " ident : proveAutoHostPlanStep
syntax "CHOOSE " ident " AS " ident ", " ident : proveAutoHostPlanStep
syntax "SPECIALIZE " ident " AT " "(" term,+ ")" : proveAutoHostPlanStep
syntax "WITNESS " term : proveAutoHostPlanStep
syntax "TRANSPORT " "FROM " term " TO " term " BY " term :
  proveAutoHostPlanStep
syntax "AUTO" : proveAutoHostPlanStep

private def isHostAutoStep (step : TSyntax `proveAutoHostPlanStep) : Bool :=
  match step with
  | `(proveAutoHostPlanStep| AUTO) => true
  | _ => false

private unsafe def expandHostPlanSyntax
    (leaves : Array HostProofLeaf)
    (step : TSyntax `proveAutoHostPlanStep) :
    TacticM (Array HostProofLeaf) := do
  match step with
  | `(proveAutoHostPlanStep| USE ($proofs:term,*)) =>
      addHostProofResources leaves proofs.getElems
  | `(proveAutoHostPlanStep| INTRO) =>
      expandHostProofStep leaves .intro introduceHostImplications
  | `(proveAutoHostPlanStep| FIX $name:ident) =>
      expandHostProofStep leaves .fixBinder <| fixHostBinder name
  | `(proveAutoHostPlanStep| APPLY $rule:term) =>
      expandHostProofStep leaves .applyRule <| applyHostProof rule
  | `(proveAutoHostPlanStep| INDUCT $major:ident) =>
      expandHostProofStep leaves .induct <| inductHostMajor major
  | `(proveAutoHostPlanStep| SPLIT) =>
      expandHostProofStep leaves .split splitHostTarget
  | `(proveAutoHostPlanStep| CASES $major:ident) =>
      let majorSyntax : TSyntax `term := ⟨major.raw⟩
      expandHostProofStep leaves .cases <|
        casesHostProof majorSyntax
  | `(proveAutoHostPlanStep|
      CHOOSE $major:ident AS $witness:ident, $proof:ident) =>
      expandHostProofStep leaves .choose <|
        chooseHostProof major witness proof
  | `(proveAutoHostPlanStep|
      SPECIALIZE $major:ident AT ($arguments:term,*)) =>
      let majorSyntax : TSyntax `term := ⟨major.raw⟩
      expandHostProofStep leaves .specialize <|
        specializeHostProof majorSyntax arguments.getElems
  | `(proveAutoHostPlanStep| WITNESS $witness:term) =>
      expandHostProofStep leaves .witness <|
        witnessHostTarget witness
  | `(proveAutoHostPlanStep|
      TRANSPORT FROM $source:term TO $destination:term BY $proof:term) =>
      expandHostProofStep leaves .transport <|
        transportHostTarget source destination proof
  | `(proveAutoHostPlanStep| AUTO) =>
      throwError "`AUTO` must be the final host proof step"
  | _ =>
      throwUnsupportedSyntax

/--
顺序组合宿主结构节点，并以显式 `AUTO` 把全部最终叶子交回 checked search。

`USE (...)` 一次登记所有当前叶子共享的 proof-carrying 资源；后续结构节点只继承仍在
对应 child context 中的资源。
分支步骤作用于当前全部叶子；任一节点或叶子失败都会恢复整个计划。
-/
syntax (name := proveAutoHostProof)
  "prove_auto" " PROOF " "[" proveAutoHostPlanStep,* "]" : tactic

@[tactic proveAutoHostProof] unsafe def evalProveAutoHostProof : Tactic :=
  fun stx => do
    match stx with
    | `(tactic| prove_auto PROOF [$steps:proveAutoHostPlanStep,*]) =>
        withProveAutoResources do
          let savedState ← saveState
          let stepArray := steps.getElems
          try
            if stepArray.isEmpty || !isHostAutoStep stepArray.back! then
              throwError
                "prove_auto PROOF must end with an explicit `AUTO` step"
            let mut leaves ← currentHostProofLeaves
            for index in [0 : stepArray.size - 1] do
              leaves ← expandHostPlanSyntax leaves stepArray[index]!
            closeHostProofLeaves "PROOF" leaves
          catch error =>
            savedState.restore
            throw error
    | _ =>
        throwUnsupportedSyntax

end ProveAutoRequest
end Automation
end YesMetaZFC
