import YesMetaZFC.Automation.CoreNormalForm.Semantics

/-!
# Core normal form anti-prenex payload

本模块只建立可复算的反前束 / mini-scoping 数据层：依赖摘要、局部重写 trace
和 `AntiPrenexPayload.check`。这里暂不声明 soundness，也不接入搜索器或 DAG 主线。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm

namespace SyntaxEq

mutual
  /-- Core normal form 项的布尔结构相等与 Lean 等式一致。 -/
  @[simp]
  theorem termEq_eq_true {left right : Term} :
      termEq left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [termEq, termEq_eq_true, formulaEq_eq_true, termListEq_eq_true, and_assoc]

  /-- Core normal form 公式的布尔结构相等与 Lean 等式一致。 -/
  @[simp]
  theorem formulaEq_eq_true {left right : Formula} :
      formulaEq left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [formulaEq, termEq_eq_true, formulaEq_eq_true, termListEq_eq_true, and_assoc]

  /-- Core normal form 项列表的布尔结构相等与 Lean 等式一致。 -/
  @[simp]
  theorem termListEq_eq_true {left right : List Term} :
      termListEq left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [termListEq, termEq_eq_true, termListEq_eq_true]
end

@[simp]
theorem atomEq_eq_true {left right : Atom} :
    atomEq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [atomEq, termEq_eq_true, termListEq_eq_true, and_assoc]

@[simp]
theorem literalEq_eq_true {left right : Literal} :
    literalEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [literalEq, atomEq_eq_true]

@[simp]
theorem nnfEq_eq_true {left right : Nnf} :
    nnfEq left right = true ↔ left = right := by
  induction left generalizing right with
  | trueE =>
      cases right <;> simp [nnfEq]
  | falseE =>
      cases right <;> simp [nnfEq]
  | lit left =>
      cases right <;> simp [nnfEq, literalEq_eq_true]
  | conj leftA leftB ihA ihB =>
      cases right <;> simp [nnfEq, ihA, ihB]
  | disj leftA leftB ihA ihB =>
      cases right <;> simp [nnfEq, ihA, ihB]
  | forallE leftSort leftBody ih =>
      cases right <;> simp [nnfEq, ih]
  | existsE leftSort leftBody ih =>
      cases right <;> simp [nnfEq, ih]

end SyntaxEq

namespace AntiPrenex

/-- 反前束阶段的执行预算。 -/
structure Config where
  maxSteps : Nat := 512
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 绑定变量深度支持集。约定为严格递增、无重复的自然数列表。 -/
abbrev Support := List Nat

namespace Support

/-- 合并两个有序无重复自然数列表。 -/
def merge : Support → Support → Support
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead == rightHead then
        leftHead :: merge leftTail rightTail
      else if leftHead < rightHead then
        leftHead :: merge leftTail (rightHead :: rightTail)
      else
        rightHead :: merge (leftHead :: leftTail) rightTail

/-- 穿过一个绑定器后，将子树支持集投影回外层深度。 -/
def exitBinder : Support → Support
  | [] => []
  | depth :: rest =>
      if depth == 0 then
        exitBinder rest
      else
        (depth - 1) :: exitBinder rest

/-- 支持集是否提到当前位置的最外层绑定器。 -/
def usesCurrentBinder (support : Support) : Bool :=
  support.any (fun depth => depth == 0)

/-- 支持集是否保持严格递增。 -/
def sortedStrict : Support → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first < second) && sortedStrict (second :: rest)

end Support

mutual
  /-- 核心项中的绑定变量深度支持集。 -/
  def termSupport : Term → Support
    | Term.bvar _ index => [index]
    | Term.fvar .. => []
    | Term.app _ args => termListSupport args
    | Term.apply fn arg => Support.merge (termSupport fn) (termSupport arg)
    | Term.bool _ => []
    | Term.notE body => termSupport body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        Support.merge (termSupport left) (termSupport right)
    | Term.quote formula => formulaSupport formula
    | Term.lam _ _ body => Support.exitBinder (termSupport body)
    | Term.ite _ condition thenTerm elseTerm =>
        Support.merge (formulaSupport condition)
          (Support.merge (termSupport thenTerm) (termSupport elseTerm))

  /-- 核心公式中的绑定变量深度支持集。 -/
  def formulaSupport : Formula → Support
    | Formula.trueE => []
    | Formula.falseE => []
    | Formula.atom _ args => termListSupport args
    | Formula.equal _ left right => Support.merge (termSupport left) (termSupport right)
    | Formula.boolTerm term => termSupport term
    | Formula.neg body => formulaSupport body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Support.merge (formulaSupport left) (formulaSupport right)
    | Formula.forallE _ body
    | Formula.existsE _ body =>
        Support.exitBinder (formulaSupport body)

  /-- 核心项列表中的绑定变量深度支持集。 -/
  def termListSupport : List Term → Support
    | [] => []
    | term :: rest => Support.merge (termSupport term) (termListSupport rest)
end

/-- 原子中的绑定变量深度支持集。 -/
def atomSupport : Atom → Support
  | Atom.predicate _ args => termListSupport args
  | Atom.equal _ left right => Support.merge (termSupport left) (termSupport right)
  | Atom.boolTerm term => termSupport term

/-- 字面量中的绑定变量深度支持集。 -/
def literalSupport (literal : Literal) : Support :=
  atomSupport literal.atom

/-- NNF 中的绑定变量深度支持集。 -/
def nnfSupport : Nnf → Support
  | Nnf.trueE => []
  | Nnf.falseE => []
  | Nnf.lit literal => literalSupport literal
  | Nnf.conj left right => Support.merge (nnfSupport left) (nnfSupport right)
  | Nnf.disj left right => Support.merge (nnfSupport left) (nnfSupport right)
  | Nnf.forallE _ body => Support.exitBinder (nnfSupport body)
  | Nnf.existsE _ body => Support.exitBinder (nnfSupport body)

/-- 可检查依赖摘要。 -/
structure Dependency where
  support : Support
  usesCurrent : Bool
  size : Nat
  quantifiers : Nat
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace Dependency

/-- 从 NNF 复算依赖摘要。 -/
def ofNnf (nnf : Nnf) : Dependency :=
  let support := nnfSupport nnf
  {
    support := support
    usesCurrent := Support.usesCurrentBinder support
    size := nnf.size
    quantifiers := nnf.quantifierCount
  }

/-- 逐字段比较依赖摘要。 -/
def eq (left right : Dependency) : Bool :=
  left.support == right.support &&
    left.usesCurrent == right.usesCurrent &&
      left.size == right.size &&
        left.quantifiers == right.quantifiers

/-- 依赖摘要的逐字段比较在自反情形下由四个基础 `BEq` 证明闭合。 -/
theorem eq_self (dependency : Dependency) : eq dependency dependency = true :=
  Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨beq_self_eq_true dependency.support,
          beq_self_eq_true dependency.usesCurrent⟩,
        beq_self_eq_true dependency.size⟩,
      beq_self_eq_true dependency.quantifiers⟩

/-- 摘要是否表示当前绑定器独立。 -/
def independent (dependency : Dependency) : Bool :=
  !dependency.usesCurrent

/--
检查摘要是否逐字段来自给定 NNF。

`ofNnf` 已同时构造 canonical support、当前位置依赖、大小与量词计数，因此完整字段比较
已经蕴含后两项一致性。这里不再重复执行 support 排序审计，避免 checked replay 再次
归约 `Support.merge` 的 well-founded 实现。
-/
def checkFor (dependency : Dependency) (nnf : Nnf) : Bool :=
  eq dependency (ofNnf nnf)

/-- 由 `ofNnf` 构造的 canonical 摘要总能通过完整字段检查。 -/
theorem checkFor_ofNnf (nnf : Nnf) : checkFor (ofNnf nnf) nnf = true :=
  eq_self (ofNnf nnf)

/-- 当前绑定器是否不支配该 NNF。 -/
def independentCurrentBinder (nnf : Nnf) : Bool :=
  !nnf.usesCurrentBinder

end Dependency

/-- trace 中用来定位局部重写位置的路径片段。 -/
inductive PathStep where
  | left
  | right
  | body
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 局部重写路径。 -/
abbrev Path := List PathStep

/-- 侧条件对应的局部分支。 -/
inductive Branch where
  | body
  | left
  | right
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 当前反前束 checker 支持的保守规则族。 -/
inductive Rule where
  | dropForall
  | dropExists
  | forallConjSplit
  | forallConjIndependentLeft
  | forallConjIndependentRight
  | existsDisjSplit
  | existsDisjIndependentLeft
  | existsDisjIndependentRight
  | forallDisjIndependentLeft
  | forallDisjIndependentRight
  | existsConjIndependentLeft
  | existsConjIndependentRight
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- trace 中记录的可计算侧条件。 -/
inductive SideCondition where
  | independentCurrentBinder (branch : Branch) (dependency : Dependency)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace SideCondition

/--
侧条件自身是否声明了一个独立分支。

语义检查只消费实际依赖位；support 的规范排序属于构造器审计，不进入 soundness 边界。
-/
def check : SideCondition → Bool
  | independentCurrentBinder _ dependency =>
      dependency.independent &&
        dependency.usesCurrent == Support.usesCurrentBinder dependency.support

/-- 侧条件的完整构造审计。 -/
def auditCheck (condition : SideCondition) : Bool :=
  condition.check &&
    match condition with
    | independentCurrentBinder _ dependency =>
        Support.sortedStrict dependency.support

end SideCondition

/-- 一步完整状态重写。`before`/`after` 是整棵当前 NNF，`path` 指向局部规则位置。 -/
structure Step where
  path : Path
  rule : Rule
  before : Nnf
  after : Nnf
  beforeDependency : Dependency
  afterDependency : Dependency
  sideCondition? : Option SideCondition := none
  deriving Repr, Lean.ToExpr

namespace Step

/-- 从重写前后状态构造带依赖摘要的 trace step。 -/
def ofRewrite
    (path : Path) (rule : Rule) (before after : Nnf)
    (sideCondition? : Option SideCondition := none) : Step :=
  {
    path := path
    rule := rule
    before := before
    after := after
    beforeDependency := Dependency.ofNnf before
    afterDependency := Dependency.ofNnf after
    sideCondition? := sideCondition?
  }

/-- 逐字段比较 trace step。 -/
def eq (left right : Step) : Bool :=
  decide (left.path = right.path) &&
    decide (left.rule = right.rule) &&
      SyntaxEq.nnfEq left.before right.before &&
        SyntaxEq.nnfEq left.after right.after &&
          decide (left.beforeDependency = right.beforeDependency) &&
            decide (left.afterDependency = right.afterDependency) &&
              decide (left.sideCondition? = right.sideCondition?)

/-- step 结构比较与 Lean 等式一致。 -/
@[simp]
theorem eq_eq_true {left right : Step} :
    eq left right = true ↔ left = right := by
  cases left
  cases right
  simp [eq, SyntaxEq.nnfEq_eq_true, and_assoc]

end Step

/-- 局部根节点重写结果。 -/
structure Rewrite where
  rule : Rule
  after : Nnf
  sideCondition? : Option SideCondition := none
  deriving Repr, Lean.ToExpr

/-- 构造“当前绑定器独立”的侧条件。 -/
def independentCondition (branch : Branch) (nnf : Nnf) : SideCondition :=
  SideCondition.independentCurrentBinder branch (Dependency.ofNnf nnf)

/-- 尝试在当前根节点执行一条保守反前束规则。 -/
def rewriteRoot? : Nnf → Option Rewrite
  | Nnf.forallE sort body =>
      if Dependency.independentCurrentBinder body then
        some {
          rule := Rule.dropForall
          after := body.dropCurrentBinder
          sideCondition? := some (independentCondition Branch.body body)
        }
      else
        match body with
        | Nnf.conj left right =>
            if Dependency.independentCurrentBinder left then
              some {
                rule := Rule.forallConjIndependentLeft
                after := Nnf.conj left.dropCurrentBinder (Nnf.forallE sort right)
                sideCondition? := some (independentCondition Branch.left left)
              }
            else if Dependency.independentCurrentBinder right then
              some {
                rule := Rule.forallConjIndependentRight
                after := Nnf.conj (Nnf.forallE sort left) right.dropCurrentBinder
                sideCondition? := some (independentCondition Branch.right right)
              }
            else
              some {
                rule := Rule.forallConjSplit
                after := Nnf.conj (Nnf.forallE sort left) (Nnf.forallE sort right)
              }
        | Nnf.disj left right =>
            if Dependency.independentCurrentBinder left then
              some {
                rule := Rule.forallDisjIndependentLeft
                after := Nnf.disj left.dropCurrentBinder (Nnf.forallE sort right)
                sideCondition? := some (independentCondition Branch.left left)
              }
            else if Dependency.independentCurrentBinder right then
              some {
                rule := Rule.forallDisjIndependentRight
                after := Nnf.disj (Nnf.forallE sort left) right.dropCurrentBinder
                sideCondition? := some (independentCondition Branch.right right)
              }
            else
              none
        | _ => none
  | Nnf.existsE sort body =>
      if Dependency.independentCurrentBinder body then
        some {
          rule := Rule.dropExists
          after := body.dropCurrentBinder
          sideCondition? := some (independentCondition Branch.body body)
        }
      else
        match body with
        | Nnf.disj left right =>
            if Dependency.independentCurrentBinder left then
              some {
                rule := Rule.existsDisjIndependentLeft
                after := Nnf.disj left.dropCurrentBinder (Nnf.existsE sort right)
                sideCondition? := some (independentCondition Branch.left left)
              }
            else if Dependency.independentCurrentBinder right then
              some {
                rule := Rule.existsDisjIndependentRight
                after := Nnf.disj (Nnf.existsE sort left) right.dropCurrentBinder
                sideCondition? := some (independentCondition Branch.right right)
              }
            else
              some {
                rule := Rule.existsDisjSplit
                after := Nnf.disj (Nnf.existsE sort left) (Nnf.existsE sort right)
              }
        | Nnf.conj left right =>
            if Dependency.independentCurrentBinder left then
              some {
                rule := Rule.existsConjIndependentLeft
                after := Nnf.conj left.dropCurrentBinder (Nnf.existsE sort right)
                sideCondition? := some (independentCondition Branch.left left)
              }
            else if Dependency.independentCurrentBinder right then
              some {
                rule := Rule.existsConjIndependentRight
                after := Nnf.conj (Nnf.existsE sort left) right.dropCurrentBinder
                sideCondition? := some (independentCondition Branch.right right)
              }
            else
              none
        | _ => none
  | _ => none

/-- 在当前 NNF 中按前序顺序寻找第一条可执行反前束重写。 -/
def rewriteOnceAt (path : Path) (current : Nnf) : Option Step :=
  match rewriteRoot? current with
  | some rewrite =>
      some (Step.ofRewrite path rewrite.rule current rewrite.after rewrite.sideCondition?)
  | none =>
      match current with
      | Nnf.conj left right =>
          match rewriteOnceAt (path ++ [PathStep.left]) left with
          | some child =>
              some (Step.ofRewrite child.path child.rule current
                (Nnf.conj child.after right) child.sideCondition?)
          | none =>
              match rewriteOnceAt (path ++ [PathStep.right]) right with
              | some child =>
                  some (Step.ofRewrite child.path child.rule current
                    (Nnf.conj left child.after) child.sideCondition?)
              | none => none
      | Nnf.disj left right =>
          match rewriteOnceAt (path ++ [PathStep.left]) left with
          | some child =>
              some (Step.ofRewrite child.path child.rule current
                (Nnf.disj child.after right) child.sideCondition?)
          | none =>
              match rewriteOnceAt (path ++ [PathStep.right]) right with
              | some child =>
                  some (Step.ofRewrite child.path child.rule current
                    (Nnf.disj left child.after) child.sideCondition?)
              | none => none
      | Nnf.forallE sort body =>
          match rewriteOnceAt (path ++ [PathStep.body]) body with
          | some child =>
              some (Step.ofRewrite child.path child.rule current
                (Nnf.forallE sort child.after) child.sideCondition?)
          | none => none
      | Nnf.existsE sort body =>
          match rewriteOnceAt (path ++ [PathStep.body]) body with
          | some child =>
              some (Step.ofRewrite child.path child.rule current
                (Nnf.existsE sort child.after) child.sideCondition?)
          | none => none
      | _ => none

/-- 在整棵 NNF 上执行一条确定性的反前束重写。 -/
def rewriteOnce? (current : Nnf) : Option Step :=
  rewriteOnceAt [] current

/-- `rewriteOnce?` 返回的 step 总是记录完整输入作为 `before`。 -/
theorem rewriteOnce?_before_eq {current : Nnf} {step : Step}
    (hStep : rewriteOnce? current = some step) :
    step.before = current := by
  unfold rewriteOnce? at hStep
  induction current generalizing step with
  | trueE | falseE | lit =>
      simp [rewriteOnceAt, rewriteRoot?] at hStep
  | conj left right ihLeft ihRight =>
      rw [rewriteOnceAt] at hStep
      simp only [rewriteRoot?] at hStep
      cases hLeft : rewriteOnceAt [PathStep.left] left with
      | some child =>
          simp [hLeft] at hStep
          subst step
          rfl
      | none =>
          simp [hLeft] at hStep
          cases hRight : rewriteOnceAt [PathStep.right] right with
          | some child =>
              simp [hRight] at hStep
              subst step
              rfl
          | none =>
              simp [hRight] at hStep
  | disj left right ihLeft ihRight =>
      rw [rewriteOnceAt] at hStep
      simp only [rewriteRoot?] at hStep
      cases hLeft : rewriteOnceAt [PathStep.left] left with
      | some child =>
          simp [hLeft] at hStep
          subst step
          rfl
      | none =>
          simp [hLeft] at hStep
          cases hRight : rewriteOnceAt [PathStep.right] right with
          | some child =>
              simp [hRight] at hStep
              subst step
              rfl
          | none =>
              simp [hRight] at hStep
  | forallE sort body ih =>
      rw [rewriteOnceAt] at hStep
      cases hRoot : rewriteRoot? (Nnf.forallE sort body) with
      | some rewrite =>
          simp [hRoot] at hStep
          subst step
          rfl
      | none =>
          simp [hRoot] at hStep
          cases hBody : rewriteOnceAt [PathStep.body] body with
          | some child =>
              simp [hBody] at hStep
              subst step
              rfl
          | none =>
              simp [hBody] at hStep
  | existsE sort body ih =>
      rw [rewriteOnceAt] at hStep
      cases hRoot : rewriteRoot? (Nnf.existsE sort body) with
      | some rewrite =>
          simp [hRoot] at hStep
          subst step
          rfl
      | none =>
          simp [hRoot] at hStep
          cases hBody : rewriteOnceAt [PathStep.body] body with
          | some child =>
              simp [hBody] at hStep
              subst step
              rfl
          | none =>
              simp [hBody] at hStep

namespace Step

/-- trace step 是否确实是当前 checker 的下一步。 -/
def check (step : Step) : Bool :=
  match rewriteOnce? step.before with
  | some expected => eq step expected
  | none => false

/-- 当前确定性重写器产生的 step 一定通过 kernel-facing checker。 -/
theorem check_of_rewriteOnce? {current : Nnf} {step : Step}
    (hStep : rewriteOnce? current = some step) :
    step.check = true := by
  have hBefore := rewriteOnce?_before_eq hStep
  subst current
  simp [check, hStep, eq]

/-- trace step 的非语义构造审计。 -/
def auditCheck (step : Step) : Bool :=
  step.check &&
    Dependency.checkFor step.beforeDependency step.before &&
      Dependency.checkFor step.afterDependency step.after &&
        match step.sideCondition? with
        | some condition => condition.auditCheck
        | none => true

end Step

/-- 反前束 trace。 -/
abbrev Trace := Array Step

namespace Trace

/-- 比较两个 trace。 -/
def eqList : List Step → List Step → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => left.eq right && eqList leftRest rightRest
  | _, _ => false

/-- 比较两个 trace。 -/
def eq (left right : Trace) : Bool :=
  eqList left.toList right.toList

/-- 顺序重放 trace。 -/
def replayList? (current : Nnf) : List Step → Option Nnf
  | [] => some current
  | step :: rest =>
      if SyntaxEq.nnfEq step.before current && step.check then
        replayList? step.after rest
      else
        none

/-- 顺序重放 trace。 -/
def replay? (source : Nnf) (trace : Trace) : Option Nnf :=
  replayList? source trace.toList

/-- trace 是否能从 source 重放到 result。 -/
def check (source result : Nnf) (trace : Trace) : Bool :=
  match replay? source trace with
  | some replayed => SyntaxEq.nnfEq replayed result
  | none => false

/-- trace 中所有 step 的完整构造审计。 -/
def auditCheck (trace : Trace) : Bool :=
  trace.all Step.auditCheck

/-- trace 中显式独立性侧条件数量。 -/
def sideConditionCount (trace : Trace) : Nat :=
  Id.run do
    let mut count := 0
    for step in trace do
      if step.sideCondition?.isSome then
        count := count + 1
    return count

end Trace

/-- 反前束算法的内部结果。 -/
structure Result where
  result : Nnf
  trace : Trace
  fuelExhausted : Bool
  deriving Repr, Lean.ToExpr

/-- 在固定步数内执行反前束重写。 -/
def normalizeLoop (remaining : Nat) (current : Nnf) (trace : Trace) : Result :=
  match remaining with
  | 0 =>
      {
        result := current
        trace := trace
        fuelExhausted := (rewriteOnce? current).isSome
      }
  | fuel + 1 =>
      match rewriteOnce? current with
      | some step => normalizeLoop fuel step.after (trace.push step)
      | none =>
          {
            result := current
            trace := trace
            fuelExhausted := false
          }

/-- 运行反前束纯算法。 -/
def normalize (config : Config) (source : Nnf) : Result :=
  normalizeLoop config.maxSteps source #[]

namespace Trace

private theorem replayList?_append (source : Nnf) (first second : List Step) :
    replayList? source (first ++ second) =
      match replayList? source first with
      | some current => replayList? current second
      | none => none := by
  induction first generalizing source with
  | nil =>
      rfl
  | cons step rest ih =>
      simp only [List.cons_append, replayList?]
      by_cases hStep : SyntaxEq.nnfEq step.before source && step.check
      · simp [hStep, ih]
      · simp [hStep]

private theorem replayList?_normalizeLoop
    (remaining : Nat) (source current : Nnf) (trace : Trace)
    (hReplay : replayList? source trace.toList = some current) :
    replayList? source (normalizeLoop remaining current trace).trace.toList =
      some (normalizeLoop remaining current trace).result := by
  induction remaining generalizing current trace with
  | zero =>
      simpa [normalizeLoop] using hReplay
  | succ remaining ih =>
      cases hStep : rewriteOnce? current with
      | none =>
          simpa [normalizeLoop, hStep] using hReplay
      | some step =>
          have hBefore := rewriteOnce?_before_eq hStep
          have hChecked := Step.check_of_rewriteOnce? hStep
          have hNext :
              replayList? source (trace.push step).toList = some step.after := by
            rw [Array.toList_push, replayList?_append, hReplay]
            simp [replayList?, hBefore, hChecked, SyntaxEq.nnfEq_eq_true]
          simpa [normalizeLoop, hStep] using
            ih step.after (trace.push step) hNext

/-- `normalize` 生成的显式 trace 可逐步回放到其结果。 -/
theorem check_normalize (config : Config) (source : Nnf) :
    check source (normalize config source).result (normalize config source).trace = true := by
  have hReplay := replayList?_normalizeLoop config.maxSteps source source #[] (by rfl)
  unfold check replay? normalize
  rw [hReplay]
  exact SyntaxEq.nnfEq_eq_true.mpr rfl

end Trace

/-- 逐字段比较公共 stats。 -/
def statsEq (left right : Certificate.Stats) : Bool :=
  left.steps == right.steps &&
    left.clauses == right.clauses &&
      left.literals == right.literals &&
        left.generated == right.generated &&
          left.retained == right.retained &&
            left.verified == right.verified &&
              left.residuals == right.residuals &&
                left.fuel == right.fuel

/-- 构造反前束阶段的计数摘要。 -/
def statsOf (config : Config) (source result : Nnf) (trace : Trace)
    (fuelExhausted : Bool) : Certificate.Stats :=
  {
    steps := trace.size
    generated := source.size
    retained := result.size
    verified := trace.sideConditionCount
    residuals := if fuelExhausted then 1 else 0
    fuel := config.maxSteps
  }

end AntiPrenex

/-- 反前束 / mini-scoping 的可检查 payload。 -/
structure AntiPrenexPayload where
  config : AntiPrenex.Config
  source : Nnf
  result : Nnf
  trace : AntiPrenex.Trace
  sourceDependency : AntiPrenex.Dependency
  resultDependency : AntiPrenex.Dependency
  sourceSize : Nat
  resultSize : Nat
  steps : Nat
  fuelExhausted : Bool
  stats : Certificate.Stats
  deriving Repr, Lean.ToExpr

namespace AntiPrenexPayload

/-- 从 source 运行纯算法并构造 payload。 -/
def build (config : AntiPrenex.Config) (source : Nnf) : AntiPrenexPayload :=
  let normalized := AntiPrenex.normalize config source
  {
    config := config
    source := source
    result := normalized.result
    trace := normalized.trace
    sourceDependency := AntiPrenex.Dependency.ofNnf source
    resultDependency := AntiPrenex.Dependency.ofNnf normalized.result
    sourceSize := source.size
    resultSize := normalized.result.size
    steps := normalized.trace.size
    fuelExhausted := normalized.fuelExhausted
    stats := AntiPrenex.statsOf config source normalized.result normalized.trace
      normalized.fuelExhausted
  }

/-- 检查反前束 payload 的 kernel-facing 语义数据。 -/
def check (payload : AntiPrenexPayload) : Bool :=
  AntiPrenex.Dependency.checkFor payload.sourceDependency payload.source &&
    AntiPrenex.Dependency.checkFor payload.resultDependency payload.result &&
      AntiPrenex.Trace.check payload.source payload.result payload.trace

/--
反前束 payload 的完整确定性构造审计。

canonical build、trace 选择、support 排序与计数复算不参与语义 soundness，只用于离线
确认搜索端仍由当前确定性构造器产生。
-/
def auditCheck (payload : AntiPrenexPayload) : Bool :=
  let expected := build payload.config payload.source
  check payload &&
    AntiPrenex.Trace.auditCheck payload.trace &&
      SyntaxEq.nnfEq payload.result expected.result &&
        AntiPrenex.Trace.eq payload.trace expected.trace &&
          AntiPrenex.Dependency.eq payload.sourceDependency expected.sourceDependency &&
            AntiPrenex.Dependency.eq payload.resultDependency expected.resultDependency &&
              payload.sourceSize == expected.sourceSize &&
                payload.resultSize == expected.resultSize &&
                  payload.steps == expected.steps &&
                    payload.fuelExhausted == expected.fuelExhausted &&
                      AntiPrenex.statsEq payload.stats expected.stats

/-- 纯构造器产生的 payload 由通用逐步 trace 定理闭合 checker。 -/
theorem check_build (config : AntiPrenex.Config) (source : Nnf) :
    check (build config source) = true := by
  unfold check build
  simp [AntiPrenex.Dependency.checkFor_ofNnf, AntiPrenex.Trace.check_normalize]

/-- 逐字段比较反前束 payload。 -/
def eq (left right : AntiPrenexPayload) : Bool :=
  left.config == right.config &&
    SyntaxEq.nnfEq left.source right.source &&
      SyntaxEq.nnfEq left.result right.result &&
        AntiPrenex.Trace.eq left.trace right.trace &&
          AntiPrenex.Dependency.eq left.sourceDependency right.sourceDependency &&
            AntiPrenex.Dependency.eq left.resultDependency right.resultDependency &&
              left.sourceSize == right.sourceSize &&
                left.resultSize == right.resultSize &&
                  left.steps == right.steps &&
                    left.fuelExhausted == right.fuelExhausted &&
                      AntiPrenex.statsEq left.stats right.stats

/-- 构造已通过 checker 的反前束 payload。 -/
def mk? (config : AntiPrenex.Config) (source : Nnf) :
    Option (Certificate.Checked AntiPrenexPayload AntiPrenexPayload.check) :=
  Certificate.Checked.mk? (check := AntiPrenexPayload.check) (build config source)

end AntiPrenexPayload

/-- 反前束 / mini-scoping 的总结果。 -/
structure AntiPrenexResult where
  payload : AntiPrenexPayload
  checked? : Option (Certificate.Checked AntiPrenexPayload AntiPrenexPayload.check)

namespace AntiPrenexResult

/-- 从 source 运行反前束，并尽量附带 checked payload。 -/
def build (config : AntiPrenex.Config) (source : Nnf) : AntiPrenexResult :=
  let payload := AntiPrenexPayload.build config source
  {
    payload := payload
    checked? := Certificate.Checked.mk? (check := AntiPrenexPayload.check) payload
  }

/-- 反前束结果中的规范化 NNF。 -/
def result (result : AntiPrenexResult) : Nnf :=
  result.payload.result

/-- 反前束结果中的 trace。 -/
def trace (result : AntiPrenexResult) : AntiPrenex.Trace :=
  result.payload.trace

/-- 反前束结果是否携带 checked payload。 -/
def isChecked (result : AntiPrenexResult) : Bool :=
  result.checked?.isSome

/-- 检查 result 的 payload 与 checked witness 是否一致。 -/
def check (result : AntiPrenexResult) : Bool :=
  AntiPrenexPayload.check result.payload &&
    match result.checked? with
    | some checked => AntiPrenexPayload.eq result.payload checked.payload
    | none => false

end AntiPrenexResult

/-- 默认配置下的反前束 / mini-scoping 入口。 -/
def miniScope (source : Nnf) : AntiPrenexResult :=
  AntiPrenexResult.build {} source

/-- 指定配置的反前束 / mini-scoping 入口。 -/
def miniScopeWith (config : AntiPrenex.Config) (source : Nnf) : AntiPrenexResult :=
  AntiPrenexResult.build config source

end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
