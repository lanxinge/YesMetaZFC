import YesMetaZFC.Automation.CoreNormalForm.DefinitionalCnf

/-!
# 搜索期 lazy fold/unfold 定义注册表

本模块把 checked definitional CNF 的定义谓词与 canonical search-clause slot 对齐。
注册表不改变初始字句问题，也不引入新的证明规则；它只决定搜索器何时把已经存在的
source slot 放入当前 saturation arena。

方向约定：

* 正定义文字 `d(args)` 触发 `directUnfoldSlots`，即自身定义中含 `¬d(args)` 的字句；
* 负定义文字 `¬d(args)` 触发 `directFoldSlots`，即自身定义中含 `d(args)` 的字句；
* 父定义中的谓词引用只进入 `occurrenceSlots`，不参与触发；
* definitional CNF 的最终 root 字句属于 `seedSlots`，搜索开始时立即开放。
-/

namespace YesMetaZFC
namespace Automation
namespace LazyDefinitionRegistry

abbrev SearchClause := CoreSyntax.Search.Clause
abbrev SearchLiteral := CoreSyntax.Search.Literal
abbrev Definition := CoreSyntax.NormalForm.DefinitionalCnf.Definition
abbrev CnfPayload := CoreSyntax.NormalForm.DefinitionalCnfPayload
abbrev Nnf := CoreSyntax.NormalForm.Nnf
abbrev CnfRef := CoreSyntax.NormalForm.DefinitionalCnf.Ref
abbrev CnfClauseSet := CoreSyntax.NormalForm.ClauseSet

private def pushNatUnique (values : Array Nat) (value : Nat) : Array Nat :=
  if values.contains value then values else values.push value

/-- definitional-CNF 源树中的二叉分支。 -/
inductive Branch where
  | left
  | right
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 一个定义节点从 CNF source 根出发的稳定结构路径。 -/
abbrev DefinitionPath := Array Branch

/--
搜索期定义开放策略。

空 `unfoldPaths` 保持默认行为，即所有定义都可按需开放。非空时，每条路径注册一个
需要展开的定义子树；抵达该子树所需的祖先路径也自动开放，未被连接的兄弟分支保持
关闭。
-/
structure UnfoldRegistration where
  path : DefinitionPath
  projection? : Option Branch := none
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

structure Policy where
  unfoldPaths : Array UnfoldRegistration := #[]
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Policy

/-- `candidate` 是否为 `path` 的结构前缀。 -/
def isPrefixOf (candidate path : DefinitionPath) : Bool := Id.run do
  if candidate.size > path.size then
    return false
  for index in [:candidate.size] do
    if candidate.getD index .left != path.getD index .left then
      return false
  return true

/-- 一条注册是否允许当前路径。投影节点的后代必须沿被选中的直接分支。 -/
def registrationEnables (registered : UnfoldRegistration)
    (path : DefinitionPath) : Bool :=
  if isPrefixOf path registered.path then
    true
  else if !isPrefixOf registered.path path then
    false
  else
    match registered.projection? with
    | none => true
    | some branch => path.getD registered.path.size branch == branch

/-- 一个定义路径是否位于注册子树中，或是抵达注册子树所需的祖先。 -/
def enables (policy : Policy) (path : DefinitionPath) : Bool :=
  policy.unfoldPaths.isEmpty ||
    policy.unfoldPaths.any fun registered => registrationEnables registered path

/-- 当前路径是否有一个只选取左/右直接展开分支的注册。 -/
def projection? (policy : Policy) (path : DefinitionPath) : Option Branch :=
  policy.unfoldPaths.findSome? fun registered =>
    if registered.path == path then registered.projection? else none

end Policy

/-- 一个直接定义链接在 canonical clause table 中的稳定位置。 -/
structure LinkSlot where
  slot : Nat
  branch? : Option Branch := none
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace LinkSlot

/-- 透明比较。 -/
def eq (left right : LinkSlot) : Bool :=
  left.slot == right.slot && left.branch? == right.branch?

def arrayEq (left right : Array LinkSlot) : Bool :=
  left.size == right.size &&
    (left.toList.zip right.toList).all fun pair => eq pair.1 pair.2

end LinkSlot

/-- 一个定义谓词对应的双向 lazy source slots。 -/
structure Entry where
  predicate : CoreSyntax.PredicateSymbol
  path : DefinitionPath := #[]
  directUnfoldSlots : Array LinkSlot := #[]
  directFoldSlots : Array LinkSlot := #[]
  occurrenceSlots : Array Nat := #[]
  deriving Repr, Inhabited, Lean.ToExpr

namespace Entry

/-- 注册表条目的透明结构相等。 -/
def eq (left right : Entry) : Bool :=
  left.predicate == right.predicate &&
    left.path == right.path &&
      LinkSlot.arrayEq left.directUnfoldSlots right.directUnfoldSlots &&
        LinkSlot.arrayEq left.directFoldSlots right.directFoldSlots &&
          left.occurrenceSlots == right.occurrenceSlots

/-- 注册表条目列表的透明结构相等。 -/
def listEq : List Entry → List Entry → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      eq left right && listEq leftRest rightRest
  | _, _ => false

/-- 注册表条目数组的透明结构相等。 -/
def arrayEq (left right : Array Entry) : Bool :=
  listEq left.toList right.toList

end Entry

/-- 搜索文字是否使用指定的定义谓词。 -/
def literalUsesPredicate (literal : SearchLiteral)
    (predicate : CoreSyntax.PredicateSymbol) : Bool :=
  match literal.predicate with
  | .predicate candidate => candidate == predicate
  | .definition id arity =>
      predicate.role == CoreSyntax.PredicateRole.definition &&
        predicate.id == id && predicate.arity == arity
  | _ => false

/-- 字句是否含有指定极性的定义谓词文字。 -/
def clauseUsesPredicate (clause : SearchClause)
    (predicate : CoreSyntax.PredicateSymbol) (positive : Bool) : Bool :=
  clause.any fun literal =>
    literal.positive == positive && literalUsesPredicate literal predicate

/-- 从定义条目汇总全部按需开放 slots。 -/
def collectLazySlots (entries : Array Entry) : Array Nat :=
  entries.foldl
    (fun slots entry =>
      entry.directFoldSlots.foldl (fun slots link => pushNatUnique slots link.slot) <|
        entry.directUnfoldSlots.foldl
          (fun slots link => pushNatUnique slots link.slot) slots)
    #[]

/-- canonical table 中不属于定义链接的 slots 必须从搜索开始就开放。 -/
def collectSeedSlots (clauseCount : Nat) (lazySlots : Array Nat) : Array Nat :=
  Id.run do
    let mut seedSlots := #[]
    for slot in [:clauseCount] do
      if !lazySlots.contains slot then
        seedSlots := seedSlots.push slot
    return seedSlots

/-- 为一段直接定义子句建立带分支标签的 slot。 -/
def directLinks (start : Nat) (clauses : CnfClauseSet)
    (branch? : Option Branch) : Array LinkSlot :=
  clauses.mapIdx fun index _ => {
    slot := start + index
    branch? := branch?
  }

/--
`buildCore` 的定义子句布局。

布局器复用同一 postorder 和同一 clause offset，避免从谓词 occurrence 猜 slot 顺序。
-/
structure LayoutState where
  nextDefinition : Nat := 0
  nextSlot : Nat := 0
  entries : Array Entry := #[]

abbrev LayoutM := StateM LayoutState

def collectLayoutEntries (definitions : Array Definition)
    (source : Nnf) : Array Entry :=
  let rec visit (path : DefinitionPath) :
      Nnf → LayoutM (Option CnfRef)
    | .trueE => pure (some (.truth true))
    | .falseE => pure (some (.truth false))
    | .lit literal => pure (some (.lit literal))
    | .forallE _ _ | .existsE _ _ => do
        modify fun state => { state with nextSlot := state.nextSlot + 1 }
        pure (some (.truth false))
    | .conj left right => do
        let some leftRef ← visit (path.push .left) left | pure none
        let some rightRef ← visit (path.push .right) right | pure none
        let state ← get
        let some definition := definitions[state.nextDefinition]? | pure none
        let defLit := definition.literal true
        let leftClauses :=
          CoreSyntax.NormalForm.DefinitionalCnf.clausesOfRefs
            [.lit defLit.negate, leftRef]
        let rightClauses :=
          CoreSyntax.NormalForm.DefinitionalCnf.clausesOfRefs
            [.lit defLit.negate, rightRef]
        let foldClauses :=
          CoreSyntax.NormalForm.DefinitionalCnf.clausesOfRefs
            [.lit defLit, leftRef.negate, rightRef.negate]
        let directUnfoldSlots :=
          directLinks state.nextSlot leftClauses (some .left) ++
            directLinks (state.nextSlot + leftClauses.size) rightClauses (some .right)
        let directFoldSlots :=
          directLinks
            (state.nextSlot + leftClauses.size + rightClauses.size) foldClauses none
        let nextSlot :=
          state.nextSlot + leftClauses.size + rightClauses.size + foldClauses.size
        modify fun current => {
          nextDefinition := current.nextDefinition + 1
          nextSlot := nextSlot
          entries := current.entries.push {
            predicate := definition.predicate
            path := path
            directUnfoldSlots := directUnfoldSlots
            directFoldSlots := directFoldSlots
          }
        }
        pure (some (.lit defLit))
    | .disj left right => do
        let some leftRef ← visit (path.push .left) left | pure none
        let some rightRef ← visit (path.push .right) right | pure none
        let state ← get
        let some definition := definitions[state.nextDefinition]? | pure none
        let defLit := definition.literal true
        let leftClauses :=
          CoreSyntax.NormalForm.DefinitionalCnf.clausesOfRefs
            [.lit defLit, leftRef.negate]
        let rightClauses :=
          CoreSyntax.NormalForm.DefinitionalCnf.clausesOfRefs
            [.lit defLit, rightRef.negate]
        let unfoldClauses :=
          CoreSyntax.NormalForm.DefinitionalCnf.clausesOfRefs
            [.lit defLit.negate, leftRef, rightRef]
        let directFoldSlots :=
          directLinks state.nextSlot leftClauses (some .left) ++
            directLinks (state.nextSlot + leftClauses.size) rightClauses (some .right)
        let directUnfoldSlots :=
          directLinks
            (state.nextSlot + leftClauses.size + rightClauses.size) unfoldClauses none
        let nextSlot :=
          state.nextSlot + leftClauses.size + rightClauses.size + unfoldClauses.size
        modify fun current => {
          nextDefinition := current.nextDefinition + 1
          nextSlot := nextSlot
          entries := current.entries.push {
            predicate := definition.predicate
            path := path
            directUnfoldSlots := directUnfoldSlots
            directFoldSlots := directFoldSlots
          }
        }
        pure (some (.lit defLit))
  (visit #[] source).run {} |>.2.entries

/-- 为每个 entry 补上只读的父定义 occurrence 元数据。 -/
def attachOccurrences (initialClauses : Array SearchClause) (entry : Entry) : Entry :=
  let directSlots :=
    entry.directUnfoldSlots.foldl (fun slots link => pushNatUnique slots link.slot) <|
      entry.directFoldSlots.foldl (fun slots link => pushNatUnique slots link.slot) #[]
  let occurrenceSlots := Id.run do
    let mut slots := #[]
    for h : slot in [:initialClauses.size] do
      if !directSlots.contains slot &&
          (clauseUsesPredicate initialClauses[slot] entry.predicate false ||
            clauseUsesPredicate initialClauses[slot] entry.predicate true) then
        slots := slots.push slot
    return slots
  { entry with occurrenceSlots := occurrenceSlots }

/-- 按策略关闭未注册定义路径，同时保留 predicate/path 元数据。 -/
def applyPolicy (policy : Policy) (entry : Entry) : Entry :=
  if !policy.enables entry.path then
    { entry with directUnfoldSlots := #[], directFoldSlots := #[] }
  else
    let filterLinks (links : Array LinkSlot) : Array LinkSlot :=
      match policy.projection? entry.path with
      | none => links
      | some branch =>
          links.filter fun link =>
            match link.branch? with
            | none => true
            | some candidate => candidate == branch
    { entry with
      directUnfoldSlots := filterLinks entry.directUnfoldSlots
      directFoldSlots := filterLinks entry.directFoldSlots }

/-- lazy definition registry 的完整可检查 payload。 -/
structure Payload where
  projectionSource : CoreSyntax.Formula
  cnf : CnfPayload
  initialClauses : Array SearchClause
  policy : Policy := {}
  seedSlots : Array Nat
  entries : Array Entry
  deriving Repr, Lean.ToExpr

namespace Payload

/-- 从 checked preprocessing 保留的数据确定性构造注册表。 -/
def build (projectionSource : CoreSyntax.Formula) (cnf : CnfPayload)
    (initialClauses : Array SearchClause) (policy : Policy := {}) : Payload :=
  let baseEntries :=
    collectLayoutEntries cnf.definitions cnf.source
      |>.map fun entry => attachOccurrences initialClauses entry
  let seedSlots :=
    collectSeedSlots initialClauses.size (collectLazySlots baseEntries)
  let entries := baseEntries.map (applyPolicy policy)
  {
    projectionSource := projectionSource
    cnf := cnf
    initialClauses := initialClauses
    policy := policy
    seedSlots := seedSlots
    entries := entries
  }

/-- 注册表 payload 的透明结构相等。 -/
def eq (left right : Payload) : Bool :=
  CoreSyntax.NormalForm.SyntaxEq.formulaEq
      left.projectionSource right.projectionSource &&
    CoreSyntax.NormalForm.DefinitionalCnfPayload.eq left.cnf right.cnf &&
      CoreSyntax.Search.clauseListEq
          left.initialClauses.toList right.initialClauses.toList &&
        left.policy == right.policy &&
          left.seedSlots == right.seedSlots &&
            Entry.arrayEq left.entries right.entries

/-- canonical search-clause table 是否正是该 CNF 的确定性一阶投影。 -/
def projectionAligned (payload : Payload) : Bool :=
  match
      (CoreSyntax.NormalForm.FirstOrderProjection.projectClauseSet {}
        payload.cnf.clauses)
        (CoreSyntax.NormalForm.FirstOrderProjection.initialState
          payload.projectionSource) with
  | some (clauses, _) =>
      CoreSyntax.Search.clauseListEq clauses.toList payload.initialClauses.toList
  | none => false

/-- slot 数组是否无重复且全部落在 canonical table 内。 -/
def slotsWellFormed (clauseCount : Nat) (slots : Array Nat) : Bool :=
  let unique := slots.foldl pushNatUnique #[]
  unique.size == slots.size && slots.all fun slot => slot < clauseCount

/-- 单个条目的 slots 是否精确命中对应极性的定义文字。 -/
def entryWellFormed (payload : Payload) (entry : Entry) : Bool :=
  let unfoldSlots := entry.directUnfoldSlots.map LinkSlot.slot
  let foldSlots := entry.directFoldSlots.map LinkSlot.slot
  entry.predicate.role == CoreSyntax.PredicateRole.definition &&
    slotsWellFormed payload.initialClauses.size unfoldSlots &&
    slotsWellFormed payload.initialClauses.size foldSlots &&
    slotsWellFormed payload.initialClauses.size entry.occurrenceSlots &&
    !unfoldSlots.any payload.seedSlots.contains &&
    !foldSlots.any payload.seedSlots.contains &&
    entry.directUnfoldSlots.all (fun link =>
      match payload.initialClauses[link.slot]? with
      | some clause => clauseUsesPredicate clause entry.predicate false
      | none => false) &&
    entry.directFoldSlots.all (fun link =>
      match payload.initialClauses[link.slot]? with
      | some clause => clauseUsesPredicate clause entry.predicate true
      | none => false) &&
    entry.occurrenceSlots.all fun slot =>
      match payload.initialClauses[slot]? with
      | some clause =>
          clauseUsesPredicate clause entry.predicate false ||
            clauseUsesPredicate clause entry.predicate true
      | none => false

/-- 注册表的局部 slot 不变量。 -/
def localCheck (payload : Payload) : Bool :=
  slotsWellFormed payload.initialClauses.size payload.seedSlots &&
    payload.entries.size == payload.cnf.definitions.size &&
      payload.entries.all (entryWellFormed payload)

/-- 注册表总 checker。 -/
def check (payload : Payload) : Bool :=
  CoreSyntax.NormalForm.DefinitionalCnfPayload.check payload.cnf &&
    payload.projectionAligned &&
      payload.localCheck &&
        eq payload
          (build payload.projectionSource payload.cnf payload.initialClauses
            payload.policy)

/-- 指定 search literal 对应的 lazy source slots。 -/
def slotsForLiteral (payload : Payload) (literal : SearchLiteral) : Array Nat :=
  Id.run do
    for entry in payload.entries do
      if literalUsesPredicate literal entry.predicate then
        return if literal.positive then
          entry.directUnfoldSlots.map LinkSlot.slot
        else
          entry.directFoldSlots.map LinkSlot.slot
    return #[]

/-- 除 root seed 外，注册表可能按需开放的全部 source slots。 -/
def lazySlots (payload : Payload) : Array Nat :=
  Id.run do
    let mut slots := #[]
    for slot in [:payload.initialClauses.size] do
      if !payload.seedSlots.contains slot then
        slots := slots.push slot
    return slots

end Payload

/-- 已通过可计算 checker 的 lazy definition registry。 -/
abbrev Checked := Certificate.Checked Payload Payload.check

/-- 构造并检查 lazy definition registry。 -/
def mk? (projectionSource : CoreSyntax.Formula) (cnf : CnfPayload)
    (initialClauses : Array SearchClause) (policy : Policy := {}) :
    Option Checked :=
  Certificate.Checked.mk? <|
    Payload.build projectionSource cnf initialClauses policy

end LazyDefinitionRegistry
end Automation
end YesMetaZFC
