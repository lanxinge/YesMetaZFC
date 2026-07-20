import YesMetaZFC.Automation.Resolution

/-!
# 自动化后端资源轨迹

本模块只保存搜索器额外计算出来的纯数据：规则父节点、fact/source 线索、
重写位置和 CDCL residual 初始字句映射。它不依赖 LCF theorem token，也不生成证明项。

后续的小 checker 应该消费这里的 witness，并在已有父字句已经认证的前提下，只检查
“当前新增 clause 是否由这些父节点和资源合法推出”。
-/

namespace YesMetaZFC
namespace Automation
namespace ResourceTrace

abbrev ClauseId := Nat
abbrev NodeId := Nat
abbrev Clause := CoreSyntax.Search.Clause
abbrev Literal := CoreSyntax.Search.Literal
abbrev Term := CoreSyntax.Search.Term
abbrev Substitution := CoreSyntax.Search.Substitution

/-- 子项路径；空路径表示整个项。 -/
abbrev TermPath := List Nat

/-- 文字中的左右项位置。 -/
inductive LiteralSide where
  | left
  | right
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 带位置的子项。 -/
structure PositionedTerm where
  side : LiteralSide
  path : TermPath
  term : Term
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 对一个 clause 的稳定引用。`clause?` 可在需要自包含审计时填入。 -/
structure ClauseRef where
  id : ClauseId
  clause? : Option Clause := none
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 单个父字句的 standardize-apart 元数据。 -/
structure StandardizeApartSideMetadata where
  original : Clause
  offset : Nat := 0
  renamed : Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/--
二元规则的 standardize-apart 元数据。

resolution 中 `left/right` 表示左右父字句；rewrite/superposition 中表示
`equality/target` 父字句。
-/
structure StandardizeApartMetadata where
  left : StandardizeApartSideMetadata
  right : StandardizeApartSideMetadata
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- source/fact 节点的审计特征；证明内容必须由显式可检查证书承载。 -/
structure FactFeature where
  id : NodeId
  clause : Clause
  originLabel : String := ""
  certificateSummary? : Option String := none
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 一元规则族。 -/
inductive UnaryKind where
  | ordinaryFactoring
  | equalityFactoring
  | equalityResolution
  | booleanExtensionality
  | argumentCongruence
  | functionExtensionality
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace UnaryKind

/-- 审计标签。 -/
def label : UnaryKind → String
  | ordinaryFactoring => "ordinary factoring"
  | equalityFactoring => "equality factoring"
  | equalityResolution => "equality resolution"
  | booleanExtensionality => "boolean extensionality"
  | argumentCongruence => "argument congruence"
  | functionExtensionality => "function extensionality"

end UnaryKind

/-- 重写/叠加规则族。 -/
inductive RewriteKind where
  | demodulation
  | contextualDemodulation
  | positiveSuperposition
  | negativeSuperposition
  | extensionalParamodulation
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace RewriteKind

/-- 审计标签。 -/
def label : RewriteKind → String
  | demodulation => "demodulation"
  | contextualDemodulation => "contextual demodulation"
  | positiveSuperposition => "positive superposition"
  | negativeSuperposition => "negative superposition"
  | extensionalParamodulation => "extensional paramodulation"

end RewriteKind

/-- 超消元目标极性。独立于搜索器内部类型，避免资源证书反向依赖 superposition 模块。 -/
inductive TargetPolarity where
  | positive
  | negative
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace TargetPolarity

/-- 审计标签。 -/
def label : TargetPolarity → String
  | positive => "positive"
  | negative => "negative"

end TargetPolarity

/-- 一元规则的局部 witness。 -/
structure UnaryResource where
  kind : UnaryKind
  parent : ClauseRef
  literalIndex? : Option Nat := none
  otherLiteralIndex? : Option Nat := none
  substitution : Substitution := []
  result : Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 二元 resolution 的局部 witness。 -/
structure ResolutionResource where
  left : ClauseRef
  right : ClauseRef
  leftLiteralIndex? : Option Nat := none
  rightLiteralIndex? : Option Nat := none
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 重写/叠加使用到的等词与目标位置资源。 -/
structure RewriteResource where
  kind : RewriteKind
  equality : ClauseRef
  target : ClauseRef
  equalityLiteral : Nat
  targetLiteral : Nat
  targetPosition : PositionedTerm
  orientedLhs : Term
  orientedRhs : Term
  standardizeApart? : Option StandardizeApartMetadata := none
  substitution : Substitution := []
  result : Clause
  /-- true 表示该资源来自上下文 demodulation，而不是单位等词 demodulation。 -/
  contextual : Bool := false
  /-- superposition 路线保留目标极性；普通 demodulation 置为 none。 -/
  targetPolarity? : Option TargetPolarity := none
  deriving Repr, BEq, Lean.ToExpr

/-- 一个新增 clause 的局部推导 witness。 -/
inductive LocalStepWitness where
  | unary (resource : UnaryResource)
  | resolution (resource : ResolutionResource)
  | rewrite (resource : RewriteResource)
  deriving Repr, BEq, Lean.ToExpr

namespace LocalStepWitness

/-- witness 记录的父节点。 -/
def parents : LocalStepWitness → Array ClauseRef
  | unary resource => #[resource.parent]
  | resolution resource => #[resource.left, resource.right]
  | rewrite resource => #[resource.equality, resource.target]

/-- witness 记录的结果 clause。 -/
def result : LocalStepWitness → Clause
  | unary resource => resource.result
  | resolution resource => resource.result
  | rewrite resource => resource.result

/-- 更新 witness 中记录的结果 clause。用于搜索准入阶段的规范化/去重后同步。 -/
def withResult (witness : LocalStepWitness) (clause : Clause) : LocalStepWitness :=
  match witness with
  | unary resource => unary { resource with result := clause }
  | resolution resource => resolution { resource with result := clause }
  | rewrite resource => rewrite { resource with result := clause }

private def remapRefWith? (remap : ClauseId → Option ClauseId)
    (ref : ClauseRef) : Option ClauseRef := do
  let id ← remap ref.id
  some { ref with id := id }

/--
按调用方给出的总映射重写 witness 中的父节点编号。

该入口用于把 persistent search arena 的 dense clause id 映射回既有 DAG node id；
输入节点和搜索派生节点因此可以共享同一套回放逻辑。
-/
def remapParentsWith? (remap : ClauseId → Option ClauseId) :
    LocalStepWitness → Option LocalStepWitness
  | unary resource => do
      let parent ← remapRefWith? remap resource.parent
      some (unary { resource with parent := parent })
  | resolution resource => do
      let left ← remapRefWith? remap resource.left
      let right ← remapRefWith? remap resource.right
      some (resolution { resource with left := left, right := right })
  | rewrite resource => do
      let equality ← remapRefWith? remap resource.equality
      let target ← remapRefWith? remap resource.target
      some (rewrite { resource with equality := equality, target := target })

/-- proof-chain 裁剪后同步重写 witness 中的父节点编号。 -/
def remapParents? (inputSize : Nat) (mapping : Array (Option ClauseId)) :
    LocalStepWitness → Option LocalStepWitness :=
  remapParentsWith? fun id =>
    if id < inputSize then
      some id
    else
      let index := id - inputSize
      if h : index < mapping.size then
        mapping[index]
      else
        none

/-- witness 与 proof step 的粗一致性检查。完整推导合法性由后续专用 checker 处理。 -/
def resultMatches (witness : LocalStepWitness) (clause : Clause) : Bool :=
  CoreSyntax.Search.clauseEq witness.result clause

end LocalStepWitness

/-! ## 原生高阶搜索资源 -/

/--
高阶搜索器交给 HO-DAG 材料化器的统一资源。

β/η 是无父边的外延公理实例；其余局部推理继续复用 `LocalStepWitness`，从而让
resolution、重写和外延规则共享同一套搜索 journal 形状。
-/
inductive HigherOrderResource where
  | beta (redex : Term)
  | eta (redex : Term)
  | local (witness : LocalStepWitness)
  deriving Repr, BEq, Lean.ToExpr

namespace HigherOrderResource

/-- 高阶资源的审计标签。 -/
def label : HigherOrderResource → String
  | .beta _ => "beta"
  | .eta _ => "eta"
  | .local (.unary resource) => resource.kind.label
  | .local (.resolution _) => "resolution"
  | .local (.rewrite resource) => resource.kind.label

/-- 高阶资源显式引用的父节点。β/η 公理实例没有父节点。 -/
def parents : HigherOrderResource → Array ClauseRef
  | .beta _ => #[]
  | .eta _ => #[]
  | .local witness => witness.parents

/-- 带显式结果的局部资源。β/η 的结果由证书 payload 机械计算。 -/
def result? : HigherOrderResource → Option Clause
  | .beta _ => none
  | .eta _ => none
  | .local witness => some witness.result

end HigherOrderResource

/-- residual CDCL 命题化时，一条初始命题 clause 对应的原 DAG clause。 -/
structure CdclInitialFeature where
  initialIndex : Nat
  clauseId : NodeId
  sourceClause : Clause
  encodedClause : PropResolution.Clause
  originLabel? : Option String := none
  deriving Repr, Inhabited, Lean.ToExpr

/-- residual CDCL 依赖到的初始 clause 切片。 -/
structure CdclResourceSummary where
  phase : String := ""
  initialFeatures : Array CdclInitialFeature := #[]
  usedInitialIndices : Array Nat := #[]
  journalSize : Nat := 0
  learnedClauses : Nat := 0
  resolutionSteps : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr

namespace CdclResourceSummary

/-- 空摘要。 -/
def empty : CdclResourceSummary := {}

/-- CDCL 是否实际使用了某个初始 clause。 -/
def usedInitialFeatures (summary : CdclResourceSummary) : Array CdclInitialFeature :=
  summary.initialFeatures.filter fun feature =>
    summary.usedInitialIndices.contains feature.initialIndex

end CdclResourceSummary

end ResourceTrace
end Automation
end YesMetaZFC
