import Lean

/-!
# 公共自动化证书内核

本文件定义所有自动化后端共用的证书骨架。它不依赖 CDCL、Skolem 或超消元叠加演算
的具体数据结构；各后端只需要把自己的 checked payload 映射到这里的节点和摘要即可。

设计原则：
* 搜索轨迹可以很大，但公共证书只暴露可检查 payload 和压缩摘要；
* `Checked` 是后端 checker 的通用封装，后续 CDCL 与超消元证书都复用它；
* 诊断信息带有后端和阶段标签，避免失败时只得到“搜索超时”。
-/

namespace YesMetaZFC
namespace Automation
namespace Certificate

universe u

/-- 自动化证书所属的后端。 -/
inductive Backend where
  | propositionalCdcl
  | clausification
  | coreNormalForm
  | foolClausification
  | skolemization
  | superposition
  | hoLambdaSuperposition
  | firstOrderPlanner
  | sourceReplay
  | equalityKernel
  | residualCdcl
  | dagReflection
  | composite
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

namespace Backend

/-- 面向审计日志的后端名称。 -/
def label : Backend → String
  | propositionalCdcl => "CDCL"
  | clausification => "clausification"
  | coreNormalForm => "core normal form"
  | foolClausification => "FOOL clausification"
  | skolemization => "skolemization"
  | superposition => "superposition"
  | hoLambdaSuperposition => "HO/lambda superposition"
  | firstOrderPlanner => "first-order planner"
  | sourceReplay => "source replay"
  | equalityKernel => "equality kernel"
  | residualCdcl => "residual CDCL"
  | dagReflection => "DAG reflection"
  | composite => "composite"

end Backend

/-- 自动化证书的检查阶段。 -/
inductive Phase where
  | input
  | normalization
  | frontendNormalization
  | clausification
  | foolClausification
  | skolemization
  | saturation
  | hoSaturation
  | residualSplit
  | sourceMaterialization
  | equalityReplay
  | dagCheck
  | backendCheck
  | replay
  | composition
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

namespace Phase

/-- 面向审计日志的阶段名称。 -/
def label : Phase → String
  | input => "input"
  | normalization => "normalization"
  | frontendNormalization => "frontend normalization"
  | clausification => "clausification"
  | foolClausification => "FOOL clausification"
  | skolemization => "skolemization"
  | saturation => "saturation"
  | hoSaturation => "HO/lambda saturation"
  | residualSplit => "residual split"
  | sourceMaterialization => "source materialization"
  | equalityReplay => "equality replay"
  | dagCheck => "DAG check"
  | backendCheck => "backend check"
  | replay => "replay"
  | composition => "composition"

end Phase

/-- 公共证书里用于审计具体规则族的稳定标签。 -/
inductive RuleTag where
  | preprocessing
  | coreNormalFormTrace
  | foolFormulaArgumentIntro
  | foolBoolDefinition
  | foolBoolQuantifier
  | foolClausification
  | skolemization
  | firstOrderResolution
  | firstOrderSuperposition
  | demodulation
  | betaEta
  | lambdaExtensionality
  | booleanExtensionality
  | hoLambdaSuperposition
  | residualCdcl
  | sourceLocalClause
  | sourceContextClause
  | sourceFact
  | sourceOrigin
  | sourceFrame
  | sourceTheoryAssumption
  | theoryFact
  | localFact
  | termEquality
  | equalityPath
  | equalityEdge
  | formulaEquivalence
  | formulaCongruence
  | equalityNormalization
  | congruenceClosure
  | replaceFreeCongruence
  | quantifierCongruence
  | freshness
  | binderResource
  | formulaParam
  | definitionEnv
  | definitionRecipe
  | interpretationEnv
  | formulaParamExpr
  | boolDefinitionExpr
  | frameDischarge
  | frameTermBinding
  | frameSourceProof
  | frameSourceFact
  | frameBaseProof
  | alignmentResource
  | egraphExplanation
  | antiPrenex
  | guardedPrenex
  | composedObligation
  | decompositionStep
  | localRuleWitness
  | parentCdclSkeleton
  | argumentCongruence
  | functionExtensionality
  | dagTopology
  | replayChecker
  | theoryConflict
  | propositionalLearnedClause
  | composite
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace RuleTag

/-- 面向审计日志的规则族名称。 -/
def label : RuleTag → String
  | preprocessing => "preprocessing"
  | coreNormalFormTrace => "core normal form trace"
  | foolFormulaArgumentIntro => "FOOL formula-argument intro"
  | foolBoolDefinition => "FOOL bool definition"
  | foolBoolQuantifier => "FOOL bool quantifier"
  | foolClausification => "FOOL clausification"
  | skolemization => "skolemization"
  | firstOrderResolution => "first-order resolution"
  | firstOrderSuperposition => "first-order superposition"
  | demodulation => "demodulation"
  | betaEta => "beta/eta"
  | lambdaExtensionality => "lambda extensionality"
  | booleanExtensionality => "boolean extensionality"
  | hoLambdaSuperposition => "HO/lambda superposition"
  | residualCdcl => "residual CDCL"
  | sourceLocalClause => "source local clause"
  | sourceContextClause => "source context clause"
  | sourceFact => "source fact"
  | sourceOrigin => "source origin"
  | sourceFrame => "source frame"
  | sourceTheoryAssumption => "source theory assumption"
  | theoryFact => "theory fact"
  | localFact => "local fact"
  | termEquality => "term equality"
  | equalityPath => "equality path"
  | equalityEdge => "equality edge"
  | formulaEquivalence => "formula equivalence"
  | formulaCongruence => "formula congruence"
  | equalityNormalization => "equality normalization"
  | congruenceClosure => "congruence closure"
  | replaceFreeCongruence => "replaceFree congruence"
  | quantifierCongruence => "quantifier congruence"
  | freshness => "freshness"
  | binderResource => "binder resource"
  | formulaParam => "formula parameter"
  | definitionEnv => "definition environment"
  | definitionRecipe => "definition recipe"
  | interpretationEnv => "interpretation environment"
  | formulaParamExpr => "formula parameter Expr"
  | boolDefinitionExpr => "Bool definition Expr"
  | frameDischarge => "frame discharge"
  | frameTermBinding => "frame term binding"
  | frameSourceProof => "frame source proof"
  | frameSourceFact => "frame source fact"
  | frameBaseProof => "frame base proof"
  | alignmentResource => "alignment resource"
  | egraphExplanation => "e-graph explanation"
  | antiPrenex => "anti-prenex"
  | guardedPrenex => "guarded prenex"
  | composedObligation => "composed obligation"
  | decompositionStep => "decomposition step"
  | localRuleWitness => "local rule witness"
  | parentCdclSkeleton => "parent CDCL skeleton"
  | argumentCongruence => "argument congruence"
  | functionExtensionality => "function extensionality"
  | dagTopology => "DAG topology"
  | replayChecker => "replay checker"
  | theoryConflict => "theory conflict"
  | propositionalLearnedClause => "propositional learned clause"
  | composite => "composite"

end RuleTag

/-- Scheduler 与 replay bridge 共同使用的闭合来源。 -/
inductive ClosureKind where
  | frontendNormalization
  | foolClausification
  | firstOrderSuperposition
  | hoLambdaSuperposition
  | residualCdcl
  | dagReflection
  | composite
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace ClosureKind

/-- 面向审计日志的闭合来源名称。 -/
def label : ClosureKind → String
  | frontendNormalization => "frontend normalization closed"
  | foolClausification => "FOOL clausification closed"
  | firstOrderSuperposition => "first-order superposition closed"
  | hoLambdaSuperposition => "HO/lambda superposition closed"
  | residualCdcl => "residual CDCL closed"
  | dagReflection => "DAG reflection closed"
  | composite => "composite closed"

end ClosureKind

/-- 后端证书摘要。所有字段都是局部计数，不参与 soundness。 -/
structure Stats where
  steps : Nat := 0
  clauses : Nat := 0
  literals : Nat := 0
  generated : Nat := 0
  retained : Nat := 0
  verified : Nat := 0
  residuals : Nat := 0
  fuel : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr

namespace Stats

/-- 空摘要。 -/
def empty : Stats := {}

/-- 摘要逐字段相加；用于组合证书节点。 -/
def add (left right : Stats) : Stats :=
  {
    steps := left.steps + right.steps
    clauses := left.clauses + right.clauses
    literals := left.literals + right.literals
    generated := left.generated + right.generated
    retained := left.retained + right.retained
    verified := left.verified + right.verified
    residuals := left.residuals + right.residuals
    fuel := left.fuel + right.fuel
  }

instance : Add Stats where
  add := add

end Stats

/-- 结构化失败信息。 -/
structure Diagnostic where
  backend : Backend
  phase : Phase
  message : String
  fuel? : Option Nat := none
  deriving Repr, Inhabited

namespace Diagnostic

/-- 构造一个普通失败信息。 -/
def ofMessage (backend : Backend) (phase : Phase) (message : String) : Diagnostic :=
  { backend := backend, phase := phase, message := message }

/-- 构造一个带 fuel 信息的失败信息。 -/
def withFuel (backend : Backend) (phase : Phase) (message : String) (fuel : Nat) :
    Diagnostic :=
  { backend := backend, phase := phase, message := message, fuel? := some fuel }

/-- 面向 tactic 错误的短消息。 -/
def label (diagnostic : Diagnostic) : String :=
  let fuelText :=
    match diagnostic.fuel? with
    | some fuel => s!", fuel={fuel}"
    | none => ""
  s!"{diagnostic.backend.label}/{diagnostic.phase.label}: {diagnostic.message}{fuelText}"

end Diagnostic

/-- 后端 checker 的统一结果。 -/
inductive CheckResult where
  | ok (stats : Stats)
  | failed (diagnostic : Diagnostic)
  deriving Repr

namespace CheckResult

/-- checker 是否成功。 -/
def isOk : CheckResult → Bool
  | ok _ => true
  | failed _ => false

/-- 成功结果里的摘要；失败时返回空摘要。 -/
def statsD : CheckResult → Stats
  | ok stats => stats
  | failed _ => Stats.empty

end CheckResult

/--
通过某个可计算 checker 的 payload。

`Checked α check` 只说明 `check payload = true`；具体 soundness 仍由各后端把 payload
回放到对象逻辑证明时给出。
-/
structure Checked (α : Type u) (check : α → Bool) where
  payload : α
  checked : check payload = true

namespace Checked

/-- 计算式构造 checked payload。 -/
def mk? {α : Type u} {check : α → Bool} (payload : α) :
    Option (Checked α check) :=
  if h : check payload = true then
    some { payload := payload, checked := h }
  else
    none

/-- 丢弃 checker 证明，只保留 payload。 -/
def get {α : Type u} {check : α → Bool} (checked : Checked α check) : α :=
  checked.payload

end Checked

/-- 公共证书节点编号。 -/
abbrev NodeId := Nat

/-- 公共证书中的一个压缩节点。 -/
structure Node where
  id : NodeId
  backend : Backend
  phase : Phase
  label : String
  ruleTags : Array RuleTag := #[]
  closureKind? : Option ClosureKind := none
  stats : Stats := {}
  dependencies : Array NodeId := #[]
  deriving Repr, Inhabited, Lean.ToExpr

namespace Node

/-- 一个无依赖节点。 -/
def leaf (id : NodeId) (backend : Backend) (phase : Phase) (label : String)
    (stats : Stats := {}) : Node :=
  { id := id, backend := backend, phase := phase, label := label, stats := stats }

/-- 构造带规则标签的节点。 -/
def taggedLeaf (id : NodeId) (backend : Backend) (phase : Phase) (label : String)
    (ruleTags : Array RuleTag) (stats : Stats := {})
    (closureKind? : Option ClosureKind := none) : Node :=
  {
    id := id
    backend := backend
    phase := phase
    label := label
    ruleTags := ruleTags
    closureKind? := closureKind?
    stats := stats
  }

end Node

/-- 组合证书摘要。后续双核调度器会用它串联 superposition 与 CDCL residual。 -/
structure Composite where
  root : NodeId
  nodes : Array Node
  residuals : Array NodeId := #[]
  deriving Repr, Inhabited, Lean.ToExpr

namespace Composite

/-- 组合证书总摘要。 -/
def stats (cert : Composite) : Stats :=
  Id.run do
    let mut total := Stats.empty
    for node in cert.nodes do
      total := total + node.stats
    return total

/-- 组合证书是否含有某个节点。 -/
def containsNode (cert : Composite) (id : NodeId) : Bool :=
  cert.nodes.any fun node => node.id == id

/-- 查找组合证书中的节点。 -/
def node? (cert : Composite) (id : NodeId) : Option Node := Id.run do
  for node in cert.nodes do
    if node.id == id then
      return some node
  return none

/-- 组合证书根节点。 -/
def rootNode? (cert : Composite) : Option Node :=
  cert.node? cert.root

/-- 组合证书根节点的闭合来源。 -/
def rootClosureKind? (cert : Composite) : Option ClosureKind := do
  let root ← cert.rootNode?
  root.closureKind?

/-- 根节点是否由指定来源闭合。 -/
def rootClosedBy (cert : Composite) (kind : ClosureKind) : Bool :=
  match cert.rootClosureKind? with
  | some actual => actual == kind
  | none => false

/-- 组合证书根节点是否存在。 -/
def rootExists (cert : Composite) : Bool :=
  cert.containsNode cert.root

/-- 组合证书中每条依赖边都指向已有节点。 -/
def dependenciesClosed (cert : Composite) : Bool :=
  Id.run do
    let mut ok := true
    for node in cert.nodes do
      for dependency in node.dependencies do
        if !cert.containsNode dependency then
          ok := false
    return ok

end Composite


end Certificate
end Automation
end YesMetaZFC
