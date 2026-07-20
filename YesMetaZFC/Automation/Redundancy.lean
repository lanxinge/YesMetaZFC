import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Data.Util
/-!
# MF1 自动化：冗余消除与收缩核心

本模块集中维护超消元搜索中与“剪枝/规范化/收缩”有关的可计算内核：

* 字句规范化：重复文字删除；
* 重言式检测；
* 前向/后向包含消除使用的 subsumption；
* 项序、最大文字与负文字选择；
* 单位等词 demodulation 与上下文 demodulation。

规则生成器只负责给出原始候选；候选进入数据库前统一经过这里的规范化与冗余判定。
-/

namespace YesMetaZFC
namespace Automation
namespace Redundancy

/-- 超消元项索引 backend。bucket 用于回归对照，discriminationTree 是默认路线。 -/
inductive IndexBackendKind where
  | bucket
  | discriminationTree
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace IndexBackendKind

/-- 性能 trace 中的稳定标签。 -/
def label : IndexBackendKind → String
  | bucket => "bucket"
  | discriminationTree => "discrimination-tree"

end IndexBackendKind

/-- 冗余层和 given-clause 搜索共享的运行配置。 -/
structure Config where
  fuel : Nat := 64
  /--
  单次 saturation 运行的细粒度工作预算。

  与 given-clause `fuel` 不同，它在项位置、索引维护与命中、合一、候选检查、包含回溯
  和删除判定等内层边界扣减，防止一条 given 在返回外层循环前执行无界工作。
  -/
  workFuel : Nat := 262144
  maxClauseSize : Nat := 16
  maxTermDepth : Nat := 8
  ageWeightRatio : Nat := 5
  enableSuperposition : Bool := true
  enableNegativeSuperposition : Bool := true
  enableDemodulation : Bool := true
  enableEqualityResolution : Bool := true
  enableEqualityFactoring : Bool := true
  enableTermIndexing : Bool := true
  indexBackend : IndexBackendKind := IndexBackendKind.discriminationTree
  enableNegativeLiteralSelection : Bool := true
  enableSubsumption : Bool := true
  enableContextualDemodulation : Bool := false
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 搜索核细粒度预算的扣费类别。 -/
inductive WorkKind where
  | indexOccurrence
  | indexMaintenance
  | termPosition
  | inferenceAttempt
  | unification
  | generatedCandidate
  | localCheck
  | retention
  | subsumption
  | backwardDeletion
  | forwardSimplification
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 细粒度工作计数；只用于 profile，不进入证明证书。 -/
structure WorkStats where
  consumed : Nat := 0
  indexOccurrences : Nat := 0
  indexMaintenanceSteps : Nat := 0
  termPositions : Nat := 0
  inferenceAttempts : Nat := 0
  unificationAttempts : Nat := 0
  generatedCandidates : Nat := 0
  localChecks : Nat := 0
  retentionChecks : Nat := 0
  subsumptionNodes : Nat := 0
  backwardDeletionChecks : Nat := 0
  forwardSimplificationSteps : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace WorkStats

/-- 记录一次具体类别的搜索工作。 -/
def record (stats : WorkStats) (kind : WorkKind) : WorkStats :=
  match kind with
  | WorkKind.indexOccurrence =>
      { stats with
        consumed := stats.consumed + 1
        indexOccurrences := stats.indexOccurrences + 1 }
  | WorkKind.indexMaintenance =>
      { stats with
        consumed := stats.consumed + 1
        indexMaintenanceSteps := stats.indexMaintenanceSteps + 1 }
  | WorkKind.termPosition =>
      { stats with
        consumed := stats.consumed + 1
        termPositions := stats.termPositions + 1 }
  | WorkKind.inferenceAttempt =>
      { stats with
        consumed := stats.consumed + 1
        inferenceAttempts := stats.inferenceAttempts + 1 }
  | WorkKind.unification =>
      { stats with
        consumed := stats.consumed + 1
        unificationAttempts := stats.unificationAttempts + 1 }
  | WorkKind.generatedCandidate =>
      { stats with
        consumed := stats.consumed + 1
        generatedCandidates := stats.generatedCandidates + 1 }
  | WorkKind.localCheck =>
      { stats with
        consumed := stats.consumed + 1
        localChecks := stats.localChecks + 1 }
  | WorkKind.retention =>
      { stats with
        consumed := stats.consumed + 1
        retentionChecks := stats.retentionChecks + 1 }
  | WorkKind.subsumption =>
      { stats with
        consumed := stats.consumed + 1
        subsumptionNodes := stats.subsumptionNodes + 1 }
  | WorkKind.backwardDeletion =>
      { stats with
        consumed := stats.consumed + 1
        backwardDeletionChecks := stats.backwardDeletionChecks + 1 }
  | WorkKind.forwardSimplification =>
      { stats with
        consumed := stats.consumed + 1
        forwardSimplificationSteps := stats.forwardSimplificationSteps + 1 }

end WorkStats

/-- 一次 saturation 运行共享的剩余工作预算。 -/
structure WorkBudget where
  remaining : Nat
  stats : WorkStats := {}
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace WorkBudget

/-- 从配置建立本轮共享工作预算，并可继续累计既有 profile。 -/
def ofConfig (config : Config) (stats : WorkStats := {}) : WorkBudget :=
  { remaining := config.workFuel, stats := stats }

/-- 尝试扣减一个工作单位；失败表示本轮必须显式停止为 unknown/fuel exhausted。 -/
@[inline]
def charge? (budget : WorkBudget) (kind : WorkKind) : Option WorkBudget :=
  match budget.remaining with
  | 0 => none
  | remaining + 1 =>
      some {
        remaining := remaining
        stats := budget.stats.record kind
      }

end WorkBudget

/-- 预算化纯搜索的显式结果。 -/
inductive WorkResult (α : Type) where
  | complete (value : α) (budget : WorkBudget)
  | exhausted (budget : WorkBudget)
  deriving Inhabited

namespace WorkResult

/-- 预算化结果的最终预算。 -/
def budget : WorkResult α → WorkBudget
  | complete _ budget => budget
  | exhausted budget => budget

/-- 映射完成值，保持耗尽状态。 -/
def map (f : α → β) : WorkResult α → WorkResult β
  | complete value budget => complete (f value) budget
  | exhausted budget => exhausted budget

end WorkResult

/-- 冗余层内部字句直接使用 core search 子句语法。 -/
abbrev Clause := CoreSyntax.Search.Clause

namespace TermOrdering

/-- Nat 的三值比较；避免给自动化层引入额外序包装。 -/
def compareNat (left right : Nat) : Ordering :=
  if left < right then
    Ordering.lt
  else if right < left then
    Ordering.gt
  else
    Ordering.eq

/-- 符号种类优先级。Skolem 函数排在参数符号之后。 -/
def symbolKindRank : CoreSyntax.Search.SymbolKind → Nat
  | CoreSyntax.Search.SymbolKind.parameter => 0
  | CoreSyntax.Search.SymbolKind.skolem => 1
  | CoreSyntax.Search.SymbolKind.definition => 2
  | CoreSyntax.Search.SymbolKind.choice => 3
  | CoreSyntax.Search.SymbolKind.builtin => 4
  | CoreSyntax.Search.SymbolKind.extensionalWitness => 5
  | CoreSyntax.Search.SymbolKind.tuple => 6

/-- 函数符号优先级。 -/
def symbolRank (symbol : CoreSyntax.Search.FunctionSymbol) : Nat :=
  symbolKindRank symbol.kind * 1000000 + symbol.arity * 1000 + symbol.id

/--
项的有限编码，用作 KBO 风格排序的同权重 tie-breaker。

主权重仍是 `Term.size`，编码只在权重相同时提供确定性优先级。
-/
partial def code : CoreSyntax.Search.Term → Nat
  | CoreSyntax.Search.Term.var id => id * 2
  | CoreSyntax.Search.Term.bvar _ index => index * 2 + 3
  | CoreSyntax.Search.Term.fvar _ id => id * 2 + 5
  | CoreSyntax.Search.Term.app symbol args =>
      let argsCode := args.foldl (fun acc term => acc * 131 + code term + 1) 0
      symbolRank symbol * 257 + argsCode * 2 + 1
  | CoreSyntax.Search.Term.apply fn arg =>
      (code fn * 131 + code arg + 1) * 2 + 7
  | CoreSyntax.Search.Term.lam _ _ body =>
      code body * 2 + 11

/-- KBO 风格项比较：先比权重，再比符号/子项编码。 -/
def compare (left right : CoreSyntax.Search.Term) : Ordering :=
  match compareNat (CoreSyntax.Search.Term.size left) (CoreSyntax.Search.Term.size right) with
  | Ordering.eq => compareNat (code left) (code right)
  | other => other

/-- 项序使用的良基键。第一分量是权重，第二分量是确定性编码。 -/
def key (term : CoreSyntax.Search.Term) : Nat × Nat :=
  (CoreSyntax.Search.Term.size term, code term)

/-- 项序的 Prop 版本：自然数字典序的逆像，因此是良基的。 -/
def lt (left right : CoreSyntax.Search.Term) : Prop :=
  Prod.Lex (· < ·) (· < ·) (key left) (key right)

/-- 自然数二元键上的字典序良基性。 -/
theorem pairLexWellFounded : WellFounded (Prod.Lex (· < ·) (· < ·) :
    Nat × Nat → Nat × Nat → Prop) := by
  refine ⟨?_⟩
  intro pair
  cases pair with
  | mk weight code =>
      exact Prod.lexAccessible (Nat.lt_wfRel.wf.apply weight)
        (fun code => Nat.lt_wfRel.wf.apply code) code

/-- 项序的良基性。 -/
theorem wellFoundedLt : WellFounded lt :=
  InvImage.wf key pairLexWellFounded

/-- `left` 是否严格大于 `right`。 -/
def gt (left right : CoreSyntax.Search.Term) : Bool :=
  compare left right == Ordering.gt

/-- `left` 是否大于等于 `right`。 -/
def ge (left right : CoreSyntax.Search.Term) : Bool :=
  match compare left right with
  | Ordering.lt => false
  | _ => true

end TermOrdering

/-- 取文字中项序较大的项。 -/
def literalMajorTerm (literal : CoreSyntax.Search.Literal) : CoreSyntax.Search.Term :=
  if TermOrdering.ge literal.left literal.right then
    literal.left
  else
    literal.right

/-- 取文字中项序较小的项。 -/
def literalMinorTerm (literal : CoreSyntax.Search.Literal) : CoreSyntax.Search.Term :=
  if TermOrdering.ge literal.left literal.right then
    literal.right
  else
    literal.left

/-- 谓词优先级；等词稍高，方便等词推理尽早暴露。 -/
def predicateRank : CoreSyntax.Search.PredicateKind → Nat
  | CoreSyntax.Search.PredicateKind.member => 0
  | CoreSyntax.Search.PredicateKind.equal => 1
  | CoreSyntax.Search.PredicateKind.boolHolds => 2
  | CoreSyntax.Search.PredicateKind.definition id arity => 3 + arity * 1000 + id
  | CoreSyntax.Search.PredicateKind.predicate symbol =>
      let roleRank :=
        match symbol.role with
        | CoreSyntax.PredicateRole.relation => 0
        | CoreSyntax.PredicateRole.equalityProxy => 1
        | CoreSyntax.PredicateRole.membership => 2
        | CoreSyntax.PredicateRole.definition => 3
        | CoreSyntax.PredicateRole.builtin => 4
      10000000 + roleRank * 1000000 + symbol.arity * 1000 + symbol.id

/-- 文字比较，用于最大文字限制。 -/
def literalCompare (left right : CoreSyntax.Search.Literal) : Ordering :=
  match TermOrdering.compare (literalMajorTerm left) (literalMajorTerm right) with
  | Ordering.eq =>
      match TermOrdering.compare (literalMinorTerm left) (literalMinorTerm right) with
      | Ordering.eq =>
          match TermOrdering.compareNat (predicateRank left.predicate)
              (predicateRank right.predicate) with
          | Ordering.eq => TermOrdering.compareNat left.positive.toNat right.positive.toNat
          | other => other
      | other => other
  | other => other

/-- `left` 是否是严格更大的文字。 -/
def literalGreater (left right : CoreSyntax.Search.Literal) : Bool :=
  literalCompare left right == Ordering.gt

/-- 字句中的第 `index` 个文字是否为最大文字。并列最大允许参与推理。 -/
def isMaximalLiteralAt (clause : Clause) (index : Nat) : Bool :=
  if h : index < clause.size then
    let selected := clause[index]
    Id.run do
      let mut maximal := true
      for h' : other in [:clause.size] do
        if literalGreater clause[other] selected then
          maximal := false
      return maximal
  else
    false

/-- 字句是否含有负文字。 -/
def clauseHasNegativeLiteral (clause : Clause) : Bool :=
  clause.any fun literal => !literal.positive

/--
负文字选择策略下的 resolution selected literal。

若策略关闭，则退回 KBO 最大文字限制；若字句含负文字，则只选负文字中的并列最大者，
若字句没有负文字，仍使用 KBO 最大文字。这个选择只服务 resolution/普通 factoring，
不再作为正等词叠加来源的通用门禁。
-/
def selectedForResolution (config : Config) (clause : Clause) (index : Nat) : Bool :=
  if !config.enableNegativeLiteralSelection then
    isMaximalLiteralAt clause index
  else if h : index < clause.size then
    let candidate := clause[index]
    if clauseHasNegativeLiteral clause then
      if candidate.positive then
        false
      else
        Id.run do
          let mut selected := true
          for h' : other in [:clause.size] do
            let otherLiteral := clause[other]
            if !otherLiteral.positive && literalGreater otherLiteral candidate then
              selected := false
          return selected
    else
      isMaximalLiteralAt clause index
  else
    false

/-- 搜索文字是否来自定义性 CNF 引入的定义谓词。 -/
def isDefinitionLiteral (literal : CoreSyntax.Search.Literal) : Bool :=
  match literal.predicate with
  | CoreSyntax.Search.PredicateKind.definition .. => true
  | CoreSyntax.Search.PredicateKind.predicate symbol =>
      symbol.role == CoreSyntax.PredicateRole.definition
  | _ => false

/--
普通 resolution 的完整 eligibility。

定义谓词承担 Tseitin 链接角色，必须允许沿正负两个方向消费；否则普通项序可能因为
实参形状压过谓词优先级，使已经按需开放的定义链接永远无法进入 resolution。这里不
改变 resolution 规则及其 checker，只扩充可生成的主元集合。
-/
def eligibleResolutionLiteral (config : Config) (clause : Clause) (index : Nat) : Bool :=
  selectedForResolution config clause index ||
    if h : index < clause.size then
      isDefinitionLiteral clause[index]
    else
      false

/-- 正等词来源 eligibility：负文字选择不屏蔽正等词，只要求文字最大且可定向。 -/
def eligiblePositiveEquality (clause : Clause) (index : Nat) : Bool :=
  if h : index < clause.size then
    let literal := clause[index]
    literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal &&
      isMaximalLiteralAt clause index &&
      (TermOrdering.gt literal.left literal.right || TermOrdering.gt literal.right literal.left)
  else
    false

/-- 负等词 eligibility：用于 equality resolution 与 negative superposition 目标。 -/
def eligibleNegativeEquality (config : Config) (clause : Clause) (index : Nat) : Bool :=
  if h : index < clause.size then
    let literal := clause[index]
    !literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal &&
      selectedForResolution config clause index
  else
    false

/-- Superposition 目标 eligibility：正目标走最大文字，负等词目标走负等词选择。 -/
def eligibleSuperpositionTarget (config : Config) (clause : Clause) (index : Nat) : Bool :=
  if h : index < clause.size then
    let literal := clause[index]
    if literal.positive then
      isMaximalLiteralAt clause index
    else
      eligibleNegativeEquality config clause index
  else
    false

/-- 删除列表中的第 `skip` 个文字；越界时保持原列表。 -/
def eraseLiteralList : List CoreSyntax.Search.Literal → Nat → List CoreSyntax.Search.Literal
  | [], _ => []
  | _ :: rest, 0 => rest
  | literal :: rest, index + 1 => literal :: eraseLiteralList rest index

/-- 删除字句中的第 `skip` 个文字。 -/
def eraseLiteral (clause : Clause) (skip : Nat) : Clause :=
  (eraseLiteralList clause.toList skip).toArray

/-- 字句是否包含指定文字。 -/
def containsLiteral (clause : Clause) (literal : CoreSyntax.Search.Literal) : Bool :=
  clause.toList.any fun candidate => decide (candidate = literal)

/-- 去掉列表中的重复文字，保留第一次出现。 -/
def dedupLiteralList : List CoreSyntax.Search.Literal → List CoreSyntax.Search.Literal
  | [] => []
  | literal :: rest =>
      if rest.any (fun candidate => decide (candidate = literal)) then
        dedupLiteralList rest
      else
        literal :: dedupLiteralList rest

/-- 去掉重复文字；这是字句规范化的第一步，也是 factoring 的可计算核心。 -/
def dedupClause (clause : Clause) : Clause :=
  (dedupLiteralList clause.toList).toArray

/-- 新字句进入数据库前的规范化入口。 -/
def normalizeClause (clause : Clause) : Clause :=
  dedupClause clause

/-- 子项路径。空路径表示整个项。 -/
abbrev TermPath := List Nat

/-- 文字中的左右项位置。 -/
inductive LiteralSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 带位置的子项。 -/
structure PositionedTerm where
  side : LiteralSide
  path : TermPath
  term : CoreSyntax.Search.Term
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 安全读取列表中的第 `index` 个元素。 -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: rest, index + 1 => listGet? rest index

mutual

  /-- 以前序稳定顺序折叠某个项的全部子项，并允许 visitor 提前停止。 -/
  partial def foldSubtermsFromUntil {α : Type}
      (basePath : TermPath) (term : CoreSyntax.Search.Term) (initial : α)
      (visit : α → TermPath → CoreSyntax.Search.Term → Data.FoldStep α) :
      Data.FoldStep α :=
    match visit initial basePath term with
    | .done result => .done result
    | .next state =>
        match term with
        | CoreSyntax.Search.Term.var _ => .next state
        | CoreSyntax.Search.Term.bvar .. => .next state
        | CoreSyntax.Search.Term.fvar .. => .next state
        | CoreSyntax.Search.Term.app _ args =>
            foldSubtermsFromArgsUntil basePath 0 args state visit
        | CoreSyntax.Search.Term.apply fn arg =>
            match foldSubtermsFromUntil (basePath ++ [0]) fn state visit with
            | .done result => .done result
            | .next state =>
                foldSubtermsFromUntil (basePath ++ [1]) arg state visit
        | CoreSyntax.Search.Term.lam _ _ body =>
            foldSubtermsFromUntil (basePath ++ [0]) body state visit

  /-- 以前序稳定顺序折叠参数列表中的全部子项，并允许 visitor 提前停止。 -/
  partial def foldSubtermsFromArgsUntil {α : Type}
      (basePath : TermPath) (index : Nat) (args : List CoreSyntax.Search.Term)
      (initial : α)
      (visit : α → TermPath → CoreSyntax.Search.Term → Data.FoldStep α) :
      Data.FoldStep α :=
    match args with
    | [] => .next initial
    | arg :: rest =>
        match foldSubtermsFromUntil (basePath ++ [index]) arg initial visit with
        | .done result => .done result
        | .next state =>
            foldSubtermsFromArgsUntil basePath (index + 1) rest state visit

end

/-- 折叠文字中的全部子项位置，并允许 visitor 提前停止。 -/
def foldLiteralSubtermsUntil {α : Type}
    (literal : CoreSyntax.Search.Literal) (initial : α)
    (visit : α → PositionedTerm → Data.FoldStep α) : Data.FoldStep α :=
  match
      foldSubtermsFromUntil [] literal.left initial fun state path term =>
        visit state { side := LiteralSide.left, path := path, term := term } with
  | .done result => .done result
  | .next state =>
      foldSubtermsFromUntil [] literal.right state fun state path term =>
        visit state { side := LiteralSide.right, path := path, term := term }

/-- 以稳定顺序折叠文字中的全部子项位置。 -/
def foldLiteralSubterms {α : Type}
    (literal : CoreSyntax.Search.Literal) (initial : α)
    (visit : α → PositionedTerm → α) : α :=
  (foldLiteralSubtermsUntil literal initial fun state position =>
    .next (visit state position)).value

/-- 收集文字中的所有子项位置。 -/
def literalSubterms (literal : CoreSyntax.Search.Literal) : Array PositionedTerm :=
  foldLiteralSubterms literal #[] Array.push

/-- 替换列表中的第 `index` 个元素。 -/
def replaceListAt? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value =>
      match replaceListAt? rest index value with
      | some rest => some (head :: rest)
      | none => none

/-- 替换指定路径处的子项。 -/
def replaceTermAt? (term : CoreSyntax.Search.Term) (path : TermPath) (replacement : CoreSyntax.Search.Term) :
    Option CoreSyntax.Search.Term :=
  match path with
  | [] => some replacement
  | index :: rest =>
      match term with
      | CoreSyntax.Search.Term.var _ => none
      | CoreSyntax.Search.Term.bvar .. => none
      | CoreSyntax.Search.Term.fvar .. => none
      | CoreSyntax.Search.Term.app symbol args =>
          match listGet? args index with
          | some oldArg =>
              match replaceTermAt? oldArg rest replacement with
              | some newArg =>
                  match replaceListAt? args index newArg with
                  | some args => some (CoreSyntax.Search.Term.app symbol args)
                  | none => none
              | none => none
          | none => none
      | CoreSyntax.Search.Term.apply fn arg =>
          match index with
          | 0 =>
              match replaceTermAt? fn rest replacement with
              | some fn => some (CoreSyntax.Search.Term.apply fn arg)
              | none => none
          | 1 =>
              match replaceTermAt? arg rest replacement with
              | some arg => some (CoreSyntax.Search.Term.apply fn arg)
              | none => none
          | _ => none
      | CoreSyntax.Search.Term.lam domain codomain body =>
          match index with
          | 0 =>
              match replaceTermAt? body rest replacement with
              | some body => some (CoreSyntax.Search.Term.lam domain codomain body)
              | none => none
          | _ => none
termination_by path.length

/-- 读取指定路径处的子项。 -/
def termAt? (term : CoreSyntax.Search.Term) (path : TermPath) : Option CoreSyntax.Search.Term :=
  match path with
  | [] => some term
  | index :: rest =>
      match term with
      | CoreSyntax.Search.Term.var _ => none
      | CoreSyntax.Search.Term.bvar .. => none
      | CoreSyntax.Search.Term.fvar .. => none
      | CoreSyntax.Search.Term.app _ args =>
          match listGet? args index with
          | some arg => termAt? arg rest
          | none => none
      | CoreSyntax.Search.Term.apply fn arg =>
          match index with
          | 0 => termAt? fn rest
          | 1 => termAt? arg rest
          | _ => none
      | CoreSyntax.Search.Term.lam _ _ body =>
          match index with
          | 0 => termAt? body rest
          | _ => none
termination_by path.length

/-- 读取文字指定位置处的子项。 -/
def literalTermAt? (literal : CoreSyntax.Search.Literal) (side : LiteralSide) (path : TermPath) :
    Option CoreSyntax.Search.Term :=
  match side with
  | LiteralSide.left => termAt? literal.left path
  | LiteralSide.right => termAt? literal.right path

/-- 替换文字指定位置的子项。 -/
def replaceLiteralAt? (literal : CoreSyntax.Search.Literal) (side : LiteralSide) (path : TermPath)
    (replacement : CoreSyntax.Search.Term) : Option CoreSyntax.Search.Literal :=
  match side with
  | LiteralSide.left =>
      match replaceTermAt? literal.left path replacement with
      | some left => some { literal with left := left }
      | none => none
  | LiteralSide.right =>
      match replaceTermAt? literal.right path replacement with
      | some right => some { literal with right := right }
      | none => none

/-- 替换字句中的第 `index` 个文字，保持其他文字顺序不变。 -/
def replaceLiteralInClause? (clause : Clause) (index : Nat) (replacement : CoreSyntax.Search.Literal) :
    Option Clause :=
  (replaceListAt? clause.toList index replacement).map List.toArray

/-- 两个文字是否有相同原子部分。等词允许左右交换。 -/
def sameAtom (left right : CoreSyntax.Search.Literal) : Bool :=
  left.predicate == right.predicate &&
    if left.predicate == CoreSyntax.Search.PredicateKind.equal then
      (left.left == right.left && left.right == right.right) ||
        (left.left == right.right && left.right == right.left)
    else
      left.left == right.left && left.right == right.right

/-- 两个文字是否等价。等词允许左右交换，但正负号必须一致。 -/
def equivalentLiteral (left right : CoreSyntax.Search.Literal) : Bool :=
  left.positive == right.positive && sameAtom left right

/-- 字句中是否包含等价文字。 -/
def containsEquivalentLiteral (clause : Clause) (literal : CoreSyntax.Search.Literal) : Bool :=
  clause.any fun candidate => equivalentLiteral candidate literal

/-- 在给定替换下尝试让一个模式文字匹配目标文字。 -/
def matchLiteralWith? (pattern target : CoreSyntax.Search.Literal) (subst : CoreSyntax.Search.Substitution) :
    Option CoreSyntax.Search.Substitution :=
  if pattern.positive == target.positive && pattern.predicate == target.predicate then
    if pattern.predicate == CoreSyntax.Search.PredicateKind.equal then
      match CoreSyntax.Search.matchLoop subst [(pattern.left, target.left), (pattern.right, target.right)] with
      | some subst => some subst
      | none => CoreSyntax.Search.matchLoop subst [(pattern.left, target.right), (pattern.right, target.left)]
    else
      CoreSyntax.Search.matchLoop subst [(pattern.left, target.left), (pattern.right, target.right)]
  else
    none

/-- 子句包含消除的回溯匹配核心。 -/
partial def clauseSubsumesLoop
    (patterns : List CoreSyntax.Search.Literal) (target : Clause) (subst : CoreSyntax.Search.Substitution) :
    Option CoreSyntax.Search.Substitution :=
  match patterns with
  | [] => some subst
  | pattern :: rest =>
      Id.run do
        let mut found : Option CoreSyntax.Search.Substitution := none
        for h : index in [:target.size] do
          if found.isNone then
            match matchLiteralWith? pattern target[index] subst with
            | some subst' =>
                match clauseSubsumesLoop rest target subst' with
                | some finalSubst => found := some finalSubst
                | none => pure ()
            | none => pure ()
        return found

/--
带共享工作预算的 subsumption 回溯核心。

每个实际尝试的 `pattern × target` 文字组合都扣减一次预算；耗尽时不会把“不知道”误报为
不包含，而是向 saturation 外层传播显式停止状态。
-/
partial def clauseSubsumesLoopWithBudget
    (patterns : List CoreSyntax.Search.Literal) (target : Clause)
    (subst : CoreSyntax.Search.Substitution) (budget : WorkBudget) :
    WorkResult (Option CoreSyntax.Search.Substitution) :=
  match patterns with
  | [] => .complete (some subst) budget
  | pattern :: rest =>
      let rec tryTarget (index : Nat) (budget : WorkBudget) :
          WorkResult (Option CoreSyntax.Search.Substitution) :=
        if h : index < target.size then
          match budget.charge? WorkKind.subsumption with
          | none => .exhausted budget
          | some budget =>
              match matchLiteralWith? pattern target[index] subst with
              | some subst' =>
                  match clauseSubsumesLoopWithBudget rest target subst' budget with
                  | .exhausted budget => .exhausted budget
                  | .complete (some finalSubst) budget =>
                      .complete (some finalSubst) budget
                  | .complete none budget => tryTarget (index + 1) budget
              | none => tryTarget (index + 1) budget
        else
          .complete none budget
      tryTarget 0 budget

/--
`pattern` 是否包含 `target`。

这是标准子句 subsumption 的计算版本：存在一个替换使得 `pattern` 的每个文字都出现
在 `target` 中。它用于搜索剪枝，不改变已有推理规则。
-/
def clauseSubsumes? (pattern target : Clause) : Option CoreSyntax.Search.Substitution :=
  if pattern.size <= target.size then
    clauseSubsumesLoop pattern.toList target []
  else
    none

/-- `pattern` 是否包含 `target`，并显式返回更新后的共享工作预算。 -/
def clauseSubsumesWithBudget (pattern target : Clause) (budget : WorkBudget) :
    WorkResult Bool :=
  if pattern.size <= target.size then
    (clauseSubsumesLoopWithBudget pattern.toList target [] budget).map Option.isSome
  else
    .complete false budget

/-- `pattern` 是否包含 `target` 的布尔版本。 -/
def clauseSubsumes (pattern target : Clause) : Bool :=
  (clauseSubsumes? pattern target).isSome

/--
两个文字是否构成真正的重言式互补对。

这里只允许已经相同的原子；“存在 MGU”只能说明某个实例互补，不能把全称闭包字句
`P(x) ∨ ¬P(y)` 判成恒真。
-/
def complementary (left right : CoreSyntax.Search.Literal) : Bool :=
  left.positive != right.positive && sameAtom left right

/-- 两个文字互补时给出的 MGU。 -/
def complementarySubstitution? (left right : CoreSyntax.Search.Literal) : Option CoreSyntax.Search.Substitution :=
  if left.positive != right.positive then
    CoreSyntax.Search.unifyAtom? left right
  else
    none

/-- 字句是否显然为重言式。 -/
def tautological (clause : Clause) : Bool :=
  Id.run do
    let mut found := false
    for h : i in [:clause.size] do
      for h' : j in [:clause.size] do
        if i != j && complementary clause[i] clause[j] then
          found := true
    return found

/-- 字句数组是否已有指定字句。 -/
def containsClause (clauses : Array Clause) (clause : Clause) : Bool :=
  clauses.any fun candidate => candidate == clause

/-- 字句数组中是否已有字句包含 `clause`。 -/
def containsSubsumingClause (clauses : Array Clause) (clause : Clause) : Bool :=
  clauses.any fun candidate => clauseSubsumes candidate clause

/-- 所有字句是否都通过函数元数检查。 -/
def clausesArityOk (clauses : Array Clause) : Bool :=
  clauses.all fun clause =>
    clause.all fun literal =>
      literal.left.arityOk && literal.right.arityOk

/-- 字句是否满足当前搜索边界。 -/
def clauseWithinLimits (config : Config) (clause : Clause) : Bool :=
  clause.size <= config.maxClauseSize &&
    CoreSyntax.Search.Clause.maxDepth clause <= config.maxTermDepth

/-- 字句集是否都满足当前搜索边界。 -/
def clausesWithinLimits (config : Config) (clauses : Array Clause) : Bool :=
  clauses.all (clauseWithinLimits config)

/-- 新字句保留判定的失败原因。 -/
inductive RetentionDecision where
  | accept
  | rejectLimit
  | rejectTautology
  | rejectExistingDuplicate
  | rejectBatchDuplicate
  | rejectForwardSubsumed
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace RetentionDecision

/-- 判定结果是否允许字句进入数据库。 -/
def accepted : RetentionDecision → Bool
  | accept => true
  | _ => false

end RetentionDecision

/-- 字句保留上下文。`liveClauses` 用于包含消除，`clauses` 保留历史精确去重。 -/
structure RetentionContext where
  config : Config
  clauses : Array Clause
  liveClauses : Array Clause
  batchClauses : Array Clause := #[]
  deriving Repr, Lean.ToExpr

namespace RetentionContext

/-- 生成器局部使用的保留上下文；此时尚未区分 live/history。 -/
def fromClauses
    (config : Config) (clauses : Array Clause) (batchClauses : Array Clause) :
    RetentionContext :=
  {
    config := config
    clauses := clauses
    liveClauses := clauses
    batchClauses := batchClauses
  }

/-- 对原始候选字句做规范化，并给出统一保留判定。 -/
def decide (context : RetentionContext) (rawClause : Clause) : Clause × RetentionDecision :=
  let clause := normalizeClause rawClause
  if !clauseWithinLimits context.config clause then
    (clause, RetentionDecision.rejectLimit)
  else if tautological clause then
    (clause, RetentionDecision.rejectTautology)
  else if containsClause context.clauses clause then
    (clause, RetentionDecision.rejectExistingDuplicate)
  else if containsClause context.batchClauses clause then
    (clause, RetentionDecision.rejectBatchDuplicate)
  else if context.config.enableSubsumption &&
      containsSubsumingClause context.liveClauses clause then
    (clause, RetentionDecision.rejectForwardSubsumed)
  else
    (clause, RetentionDecision.accept)

/-- 对原始候选字句执行“规范化 -> 前向剪枝”，成功时返回规范化后的字句。 -/
def retain? (context : RetentionContext) (rawClause : Clause) : Option Clause :=
  let (clause, decision) := context.decide rawClause
  if decision.accepted then
    some clause
  else
    none

end RetentionContext

/-- `retained` 是否正是 `raw` 经统一规范化后得到的入库字句。 -/
def sameRetainedClause (raw retained : Clause) : Bool :=
  decide (normalizeClause raw = retained)

/-- 后向包含删除判定：新保留字句是否使旧 live 字句冗余。 -/
def backwardSubsumes (config : Config) (newClause oldClause : Clause) : Bool :=
  config.enableSubsumption && clauseSubsumes newClause oldClause

/-- 按编号安全读取字句。Redundancy 不关心编号的具体别名，只把它看成 `Nat`。 -/
def clauseById? (clauses : Array Clause) (id : Nat) : Option Clause :=
  if h : id < clauses.size then
    some clauses[id]
  else
    none

/-- 后向包含后，某个旧 live id 是否仍应保留。无效 id 直接丢弃。 -/
def keepIdAfterBackwardSubsumption
    (config : Config) (clauses : Array Clause) (newId : Nat) (newClause : Clause)
    (oldId : Nat) : Bool :=
  match clauseById? clauses oldId with
  | some oldClause => oldId == newId || !backwardSubsumes config newClause oldClause
  | none => false

/-- 对任意携带 clause id 的条目执行后向包含过滤。 -/
def filterBackwardSubsumedEntries {α : Type} (getId : α → Nat)
    (config : Config) (clauses : Array Clause) (newId : Nat) (newClause : Clause)
    (entries : Array α) : Array α :=
  Id.run do
    let mut out := #[]
    for entry in entries do
      if keepIdAfterBackwardSubsumption config clauses newId newClause (getId entry) then
        out := out.push entry
    return out

/-- 已按项序定向的正等词。 -/
structure OrientedEquality where
  literalIndex : Nat
  lhs : CoreSyntax.Search.Term
  rhs : CoreSyntax.Search.Term
  deriving Repr, Lean.ToExpr

/-- 尝试把一个最大正等词文字定向为 `lhs > rhs`。 -/
def orientedEqualityAt? (clause : Clause) (index : Nat) : Option OrientedEquality :=
  if h : index < clause.size then
    let literal := clause[index]
    if literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal &&
        isMaximalLiteralAt clause index then
      if TermOrdering.gt literal.left literal.right then
        some { literalIndex := index, lhs := literal.left, rhs := literal.right }
      else if TermOrdering.gt literal.right literal.left then
        some { literalIndex := index, lhs := literal.right, rhs := literal.left }
      else
        none
    else
      none
  else
    none

/-- 尝试把一个 eligible 正等词文字定向为 `lhs > rhs`，用于 ordered superposition。 -/
def selectedOrientedEqualityAt? (clause : Clause) (index : Nat) : Option OrientedEquality :=
  if h : index < clause.size then
    let literal := clause[index]
    if literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal &&
        eligiblePositiveEquality clause index then
      if TermOrdering.gt literal.left literal.right then
        some { literalIndex := index, lhs := literal.left, rhs := literal.right }
      else if TermOrdering.gt literal.right literal.left then
        some { literalIndex := index, lhs := literal.right, rhs := literal.left }
      else
        none
    else
      none
  else
    none

/-- 尝试把一个单位正等词字句定向为 demodulator。 -/
def orientedUnitEquality? (clause : Clause) : Option OrientedEquality :=
  if clause.size == 1 then
    orientedEqualityAt? clause 0
  else
    none

/--
关系谓词的 tuple 根只是搜索层参数封装，不是对象语言项。demodulation 只能进入其中的
真实参数，不能把整个 tuple 包装重写掉。
-/
def demodulationPositionAllowed
    (literal : CoreSyntax.Search.Literal) (position : PositionedTerm) : Bool :=
  match literal.predicate, position.side, position.path with
  | CoreSyntax.Search.PredicateKind.predicate _, LiteralSide.left, _ :: _ => true
  | CoreSyntax.Search.PredicateKind.predicate _, _, _ => false
  | _, _, _ => true

/--
在原槽位替换字句文字。

本地重写证书按目标位置回放；保持 literal 槽位不变既避免证书结果发生无关重排，也只需
为最终字句分配一次数组更新。
-/
def replaceClauseLiteralAt?
    (clause : Clause) (index : Nat) (literal : CoreSyntax.Search.Literal) :
    Option Clause :=
  if h : index < clause.size then
    some (clause.set index literal h)
  else
    none

/--
对单个目标文字尝试一次 demodulation。

这里使用匹配而不是合一，并且只替换命中的子项，避免把目标字句中的其他变量
顺手实例化掉；这让它作为收缩规则更接近传统重写。
-/
def demodulateLiteral?
    (targetClause : Clause) (equality : OrientedEquality)
    (targetIndex : Nat) (position : PositionedTerm) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if hTarget : targetIndex < targetClause.size then
    if !demodulationPositionAllowed targetClause[targetIndex] position ||
        CoreSyntax.Search.Term.isVar position.term then
      none
    else
      if (match literalTermAt? targetClause[targetIndex] position.side position.path with
          | some term => CoreSyntax.Search.termEqBetaEta position.term term
          | none => false) then
      match CoreSyntax.Search.matchTerm? equality.lhs position.term with
      | some subst =>
          -- 显式检查匹配后置条件；规则层允许 βη 后相等。
          if CoreSyntax.Search.termEqBetaEta
              (CoreSyntax.Search.Substitution.applyTerm subst equality.lhs) position.term then
            let replacement := CoreSyntax.Search.Substitution.applyTerm subst equality.rhs
            match replaceLiteralAt? targetClause[targetIndex] position.side position.path replacement with
            | some newLiteral =>
                match replaceClauseLiteralAt? targetClause targetIndex newLiteral with
                | some clause =>
                    let candidate := normalizeClause clause
                    if candidate == targetClause then
                      none
                    else
                      some (candidate, subst)
                | none => none
            | none => none
          else
            none
      | none => none
      else
        none
  else
    none

/-- 给定替换后，等词来源字句的上下文是否已经由目标字句覆盖。 -/
def demodulationContextCovered
    (subst : CoreSyntax.Search.Substitution) (sourceContext targetRest : Clause) : Bool :=
  sourceContext.all fun literal =>
    containsEquivalentLiteral targetRest (CoreSyntax.Search.Substitution.applyLiteral subst literal)

/--
对单个目标文字尝试一次上下文 demodulation。

若来源为 `Γ ∨ l = r`，只有当 `Γθ` 已经包含在目标剩余字句中时，才允许把目标中的
`lθ` 改写为 `rθ`。这是一种收缩规则，而不是 ordered superposition 扩展。
-/
def contextualDemodulateLiteral?
    (equalityClause targetClause : Clause) (equality : OrientedEquality)
    (targetIndex : Nat) (position : PositionedTerm) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if hTarget : targetIndex < targetClause.size then
    if !demodulationPositionAllowed targetClause[targetIndex] position ||
        CoreSyntax.Search.Term.isVar position.term then
      none
    else
      if (match literalTermAt? targetClause[targetIndex] position.side position.path with
          | some term => CoreSyntax.Search.termEqBetaEta position.term term
          | none => false) then
      match CoreSyntax.Search.matchTerm? equality.lhs position.term with
      | some subst =>
          if CoreSyntax.Search.termEqBetaEta
              (CoreSyntax.Search.Substitution.applyTerm subst equality.lhs) position.term then
            let sourceContext := eraseLiteral equalityClause equality.literalIndex
            let targetRest := eraseLiteral targetClause targetIndex
            if demodulationContextCovered subst sourceContext targetRest then
              let replacement := CoreSyntax.Search.Substitution.applyTerm subst equality.rhs
              match replaceLiteralAt? targetClause[targetIndex] position.side position.path replacement with
              | some newLiteral =>
                  match replaceClauseLiteralAt? targetClause targetIndex newLiteral with
                  | some clause =>
                      let candidate := normalizeClause clause
                      if candidate == targetClause then
                        none
                      else
                        some (candidate, subst)
                  | none => none
              | none => none
            else
              none
          else
            none
      | none => none
      else
        none
  else
    none

/-- 按当前配置寻找两个字句之间的第一个 demodulation 候选。 -/
def firstDemodulationBetweenWith? (config : Config) (equalityClause targetClause : Clause) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  Id.run do
    let mut found : Option (Clause × CoreSyntax.Search.Substitution) := none
    match orientedUnitEquality? equalityClause with
    | some equality =>
        for hTarget : targetIndex in [:targetClause.size] do
          if found.isNone then
            for position in literalSubterms targetClause[targetIndex] do
              if found.isNone then
                match demodulateLiteral? targetClause equality targetIndex position with
                | some result => found := some result
                | none => pure ()
    | none => pure ()
    if found.isNone && config.enableContextualDemodulation then
      for hEq : equalityIndex in [:equalityClause.size] do
        if found.isNone then
          match selectedOrientedEqualityAt? equalityClause equalityIndex with
          | some equality =>
              for hTarget : targetIndex in [:targetClause.size] do
                if found.isNone then
                  for position in literalSubterms targetClause[targetIndex] do
                    if found.isNone then
                      match contextualDemodulateLiteral? equalityClause targetClause equality
                          targetIndex position with
                      | some result => found := some result
                      | none => pure ()
          | none => pure ()
    return found

end Redundancy
end Automation
end YesMetaZFC
