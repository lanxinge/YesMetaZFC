import YesMetaZFC.Automation.HostNormalization.RuleRegistry
import YesMetaZFC.Automation.HostReification

/-!
# `prove_auto_norm` proof-free 规则编译

本模块从独立的四阶段持久注册表读取稳定声明名，并编译为不携带证明项的
Eq/Iff/definition 描述。生产正规化器仍使用原 `SimpTheorems`；这里提供后续等式闭包、
受限叠加演算和证书回放共同消费的规则面，不把 `simp` 的内部索引当作长期事实源，
也不依赖上下文无关的保守规约核。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization
namespace RuleCompiler

open Lean Meta

/-- 可由等式闭包直接消费的关系种类。 -/
inductive Relation where
  | equality
  | equivalence
deriving Repr, BEq, DecidableEq, Inhabited

/-- proof-free 规则的编译结果。 -/
inductive Kind where
  | theorem (relation : Relation)
  | definition
  | unsupported
deriving Repr, BEq, DecidableEq, Inhabited

/-- 端点根索引；后续 discrimination tree 不需要先读取证明项。 -/
inductive RootKey where
  | declaration (name : Name)
  | binder
  | application
  | opaque
deriving Repr, BEq, DecidableEq, Inhabited

/-- 保留 binder 形状的全局声明 telescope。 -/
structure Telescope where
  binderTypes : Array Expr := #[]
  binderInfos : Array BinderInfo := #[]
  body : Expr
deriving Inhabited

/--
单条 proof-free 正规化规则。

`left?`/`right?` 与 `definitionValue?` 都来自全局常量信息，不含局部 FVar 或证明表达式。
-/
structure Rule where
  declaration : Name
  phase : Phase
  kind : Kind
  telescope : Telescope
  /--
  `simp` 可能把 definition 编译成 equation declarations；证书回放必须在不读取
  `SimpTheorems` 内部结构的前提下识别这些实际使用的声明。
  -/
  simpDeclarations : Array Name := #[]
  left? : Option Expr := none
  right? : Option Expr := none
  definitionValue? : Option Expr := none
  root : RootKey := .opaque

/-- 编译规则面的审计计数。 -/
structure Stats where
  total : Nat := 0
  equality : Nat := 0
  equivalence : Nat := 0
  definitions : Nat := 0
  unsupported : Nat := 0
  definitionPhase : Nat := 0
  indexPhase : Nat := 0
  semanticPhase : Nat := 0
  logicalPhase : Nat := 0
deriving Repr, Inhabited

/-- 后续正规化后端共享的 proof-free 规则包。 -/
structure Package where
  rules : Array Rule := #[]
  stats : Stats := {}

private partial def peelTelescopeLoop (expression : Expr)
    (types : Array Expr) (infos : Array BinderInfo) : Telescope :=
  match expression.consumeMData with
  | .forallE _ type body binderInfo =>
      peelTelescopeLoop body (types.push type) (infos.push binderInfo)
  | body =>
      { binderTypes := types, binderInfos := infos, body }

private def peelTelescope (expression : Expr) : Telescope :=
  peelTelescopeLoop expression #[] #[]

private def rootKey (expression : Expr) : RootKey :=
  match expression.consumeMData with
  | .forallE .. =>
      .binder
  | expression =>
      match expression.getAppFn with
      | .const name _ => .declaration name
      | .app .. => .application
      | _ => .opaque

private def phaseIncrement (stats : Stats) : Phase → Stats
  | .definitionExposure => {
      stats with definitionPhase := stats.definitionPhase + 1
    }
  | .indexAlgebra => {
      stats with indexPhase := stats.indexPhase + 1
    }
  | .semanticAlignment => {
      stats with semanticPhase := stats.semanticPhase + 1
    }
  | .logicalCleanup => {
      stats with logicalPhase := stats.logicalPhase + 1
    }

private def recordRule (stats : Stats) (rule : Rule) : Stats :=
  let stats := phaseIncrement { stats with total := stats.total + 1 }
    rule.phase
  match rule.kind with
  | .theorem .equality =>
      { stats with equality := stats.equality + 1 }
  | .theorem .equivalence =>
      { stats with equivalence := stats.equivalence + 1 }
  | .definition =>
      { stats with definitions := stats.definitions + 1 }
  | .unsupported =>
      { stats with unsupported := stats.unsupported + 1 }

private def compileTheorem
    (declaration : Name) (phase : Phase)
    (type : Expr) : Rule :=
  let telescope := peelTelescope type
  let body := telescope.body.consumeMData
  if body.isAppOfArity ``Eq 3 then
    let arguments := body.getAppArgs
    {
      declaration
      phase
      kind := .theorem .equality
      telescope
      simpDeclarations := #[declaration]
      left? := some arguments[1]!
      right? := some arguments[2]!
      root := rootKey arguments[1]!
    }
  else if body.isAppOfArity ``Iff 2 then
    let arguments := body.getAppArgs
    {
      declaration
      phase
      kind := .theorem .equivalence
      telescope
      simpDeclarations := #[declaration]
      left? := some arguments[0]!
      right? := some arguments[1]!
      root := rootKey arguments[0]!
    }
  else
    {
      declaration
      phase
      kind := .unsupported
      telescope
      simpDeclarations := #[declaration]
    }

private def compileDefinition
    (declaration : Name) (phase : Phase)
    (type : Expr) (value? : Option Expr)
    (equations : Array Name) : Rule :=
  {
    declaration
    phase
    kind := .definition
    telescope := peelTelescope type
    simpDeclarations := #[declaration] ++ equations
    definitionValue? := value?
    root := .declaration declaration
  }

private def compileDeclaration (registered : RegisteredRule) :
    MetaM Rule := do
  let info ← getConstInfo registered.declaration
  if ← isProp info.type then
    return compileTheorem registered.declaration registered.phase info.type
  let equations := (← getEqnsFor? registered.declaration).getD #[]
  return compileDefinition registered.declaration registered.phase
    info.type info.value? equations

private def pushRuleUnique (rules : Array Rule) (rule : Rule) : Array Rule :=
  if rules.any fun existing =>
      existing.declaration == rule.declaration &&
        existing.phase == rule.phase then
    rules
  else
    rules.push rule

private def appendPhase
    (rules : Array Rule) (phase : Phase)
    (registered : Array RegisteredRule) : MetaM (Array Rule) := do
  let mut result := rules
  for entry in registered do
    if entry.phase == phase then
      result := pushRuleUnique result (← compileDeclaration entry)
  return result

/--
从当前环境的 `prove_auto_norm` 注册面编译 proof-free 规则包。

规则按四个稳定阶段及声明名稳定排序；不读取或缓存任何 theorem proof，也不枚举
生产 `simp` 索引。
-/
def compile : MetaM Package := do
  let environment ← getEnv
  let registered := HostNormalization.registeredRules environment
  let rules ← appendPhase #[] .definitionExposure registered
  let rules ← appendPhase rules .indexAlgebra registered
  let rules ← appendPhase rules .semanticAlignment registered
  let rules ← appendPhase rules .logicalCleanup registered
  let stats := rules.foldl recordRule {}
  return { rules, stats }

/-- 规则模板不允许携带局部 FVar 或未解析 metavariable。 -/
def Rule.closed (rule : Rule) : Bool :=
  let expressions :=
    rule.telescope.binderTypes ++
      #[rule.telescope.body] ++
        rule.left?.toArray ++
          rule.right?.toArray ++
            rule.definitionValue?.toArray
  expressions.all fun expression =>
    !expression.hasFVar && !expression.hasMVar

private def Rule.simpCoverageValid (rule : Rule) : Bool :=
  !rule.simpDeclarations.isEmpty &&
    rule.simpDeclarations[0]! == rule.declaration &&
      rule.simpDeclarations.all fun declaration =>
        declaration != .anonymous

/-- 整个 proof-free 规则包的基本不变量。 -/
def Package.check (package : Package) : Bool :=
  package.rules.all (fun rule =>
    rule.closed && rule.simpCoverageValid) &&
    package.stats.total == package.rules.size &&
      package.stats.total ==
        package.stats.equality +
          package.stats.equivalence +
            package.stats.definitions +
              package.stats.unsupported &&
        package.stats.total ==
          package.stats.definitionPhase +
            package.stats.indexPhase +
              package.stats.semanticPhase +
                package.stats.logicalPhase

end RuleCompiler
end HostNormalization
end Automation
end YesMetaZFC
