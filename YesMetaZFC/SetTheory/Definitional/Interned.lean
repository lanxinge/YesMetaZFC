import YesMetaZFC.Automation.Data.Intern
import YesMetaZFC.SetTheory.Definitional.Language

/-!
# 带定义原子公式的 interned operational DAG

本层面向自动化热路径。数学定理仍使用依赖索引的 `Definitional.Formula`；这里把原子、
项和公式节点放入共享图，并以稳定 handle 表示。

冻结图可以通过带 fuel 的 `Graph.decodeFormula` 回到可信语法。`bind` 与 `rename` 在
`(FormulaId, binderLift)` 上 memoize，因此同一共享子公式只处理一次。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Interned

inductive AtomTag
inductive TermTag
inductive FormulaTag

abbrev AtomId := Automation.Data.Id AtomTag
abbrev TermId := Automation.Data.Id TermTag
abbrev FormulaId := Automation.Data.Id FormulaTag

/-!
## 稳定原子注册表

本层是可执行自动化运行时，因此符号和节点都位于 `Type`。数学核本身仍保持
universe-polymorphic。
-/

/-- 稳定原子编号注册表。已分配编号在增量扩展时保持不变。 -/
structure AtomRegistry (σ : AtomSignature) [BEq σ.Symbol]
    [Hashable σ.Symbol] where
  table : Automation.Data.InternTable AtomTag σ.Symbol :=
    Automation.Data.InternTable.empty

namespace AtomRegistry

variable {σ : AtomSignature} [BEq σ.Symbol] [Hashable σ.Symbol]

def empty : AtomRegistry σ :=
  {}

def size (registry : AtomRegistry σ) : Nat :=
  registry.table.size

def get? (registry : AtomRegistry σ) (id : AtomId) : Option σ.Symbol :=
  registry.table.get? id

def lookup? (registry : AtomRegistry σ) (symbol : σ.Symbol) : Option AtomId :=
  registry.table.lookup? symbol

/-- ST 生命周期内的增量原子注册表。 -/
structure Builder (ω : Type) (σ : AtomSignature) [BEq σ.Symbol]
    [Hashable σ.Symbol] where
  table : Automation.Data.InternTable.Builder ω AtomTag σ.Symbol

namespace Builder

variable {ω : Type} {σ : AtomSignature} [BEq σ.Symbol]
  [Hashable σ.Symbol]

def empty (capacity : Nat := 16) : ST ω (Builder ω σ) := do
  return {
    table := ← Automation.Data.InternTable.Builder.empty
      (σ := ω) (tag := AtomTag) (α := σ.Symbol) capacity
  }

def ofRegistry (registry : AtomRegistry σ) : ST ω (Builder ω σ) := do
  return {
    table := ← Automation.Data.InternTable.Builder.ofTable registry.table
  }

def intern (builder : Builder ω σ) (symbol : σ.Symbol) : ST ω AtomId :=
  builder.table.intern symbol

def freeze (builder : Builder ω σ) : ST ω (AtomRegistry σ) := do
  return { table := ← builder.table.freeze }

end Builder
end AtomRegistry

/-!
## Operational 节点
-/

/-- Operational DAG 中的变量项节点。 -/
inductive TermNode where
  | bound (index : Nat)
  | free (id : FreeVarId)
  deriving Repr, BEq, DecidableEq, Hashable

/-- Operational DAG 中不带依赖索引的公式节点。 -/
inductive FormulaNode where
  | falsum
  | truth
  | mem (left right : TermId)
  | atom (symbol : AtomId) (arguments : Array TermId)
  | neg (body : FormulaId)
  | conj (left right : FormulaId)
  | disj (left right : FormulaId)
  | imp (left right : FormulaId)
  | iff (left right : FormulaId)
  | forallE (body : FormulaId)
  | existsE (body : FormulaId)
  deriving Repr, BEq, DecidableEq, Hashable

/-- 冻结的共享公式图。 -/
structure Graph (σ : AtomSignature) [BEq σ.Symbol]
    [Hashable σ.Symbol] where
  atoms : AtomRegistry σ := AtomRegistry.empty
  terms : Automation.Data.InternTable TermTag TermNode :=
    Automation.Data.InternTable.empty
  formulas : Automation.Data.InternTable FormulaTag FormulaNode :=
    Automation.Data.InternTable.empty

namespace Graph

variable {σ : AtomSignature} [BEq σ.Symbol] [Hashable σ.Symbol]

def empty : Graph σ :=
  {}

def atomCount (graph : Graph σ) : Nat :=
  graph.atoms.size

def termCount (graph : Graph σ) : Nat :=
  graph.terms.size

def formulaCount (graph : Graph σ) : Nat :=
  graph.formulas.size

def termNode? (graph : Graph σ) (id : TermId) : Option TermNode :=
  graph.terms.get? id

def formulaNode? (graph : Graph σ) (id : FormulaId) : Option FormulaNode :=
  graph.formulas.get? id

/-- 把 operational 项节点恢复为指定深度的新核项。 -/
def decodeTerm (graph : Graph σ) (depth : Nat) (id : TermId) :
    Option (Term depth) := do
  match ← graph.termNode? id with
  | .bound index =>
      if hIndex : index < depth then
        return .bound ⟨index, hIndex⟩
      else
        none
  | .free freeId =>
      return .free freeId

private def decodeTermArray (graph : Graph σ) (depth : Nat)
    (ids : Array TermId) : Option (Array (Term depth)) :=
  ids.mapM (graph.decodeTerm depth)

/-- 带 fuel 解码公式；恶意循环或越界节点安全地返回 `none`。 -/
def decodeFormulaWithFuel (graph : Graph σ) :
    (fuel availableStage depth : Nat) → FormulaId →
      Option (Formula σ availableStage depth)
  | 0, _, _, _ => none
  | fuel + 1, availableStage, depth, id =>
      match graph.formulaNode? id with
      | none => none
      | some .falsum => some Formula.falsum
      | some .truth => some Formula.truth
      | some (.mem left right) => do
          return .mem
            (← graph.decodeTerm depth left)
            (← graph.decodeTerm depth right)
      | some (.atom symbolId argumentIds) => do
          let symbol ← graph.atoms.get? symbolId
          if hStage : σ.stage symbol < availableStage then
            let arguments ← graph.decodeTermArray depth argumentIds
            if hArity : arguments.size = σ.arity symbol then
              return .atom symbol hStage {
                terms := arguments
                size_eq := hArity
              }
            else
              none
          else
            none
      | some (.neg body) => do
          return .neg
            (← graph.decodeFormulaWithFuel fuel availableStage depth body)
      | some (.conj left right) => do
          return .conj
            (← graph.decodeFormulaWithFuel fuel availableStage depth left)
            (← graph.decodeFormulaWithFuel fuel availableStage depth right)
      | some (.disj left right) => do
          return .disj
            (← graph.decodeFormulaWithFuel fuel availableStage depth left)
            (← graph.decodeFormulaWithFuel fuel availableStage depth right)
      | some (.imp left right) => do
          return .imp
            (← graph.decodeFormulaWithFuel fuel availableStage depth left)
            (← graph.decodeFormulaWithFuel fuel availableStage depth right)
      | some (.iff left right) => do
          return .iff
            (← graph.decodeFormulaWithFuel fuel availableStage depth left)
            (← graph.decodeFormulaWithFuel fuel availableStage depth right)
      | some (.forallE body) => do
          return .forallE
            (← graph.decodeFormulaWithFuel fuel availableStage (depth + 1) body)
      | some (.existsE body) => do
          return .existsE
            (← graph.decodeFormulaWithFuel fuel availableStage (depth + 1) body)

/-- 使用图大小给出的保守 fuel 解码根公式。 -/
def decodeFormula (graph : Graph σ) (availableStage depth : Nat)
    (root : FormulaId) : Option (Formula σ availableStage depth) :=
  graph.decodeFormulaWithFuel (graph.formulaCount + 1)
    availableStage depth root

/-- 解码成功后的可检查可信边界。 -/
structure CheckedFormula (graph : Graph σ) (availableStage depth : Nat)
    (root : FormulaId) where
  formula : Formula σ availableStage depth
  decode_eq : graph.decodeFormula availableStage depth root = some formula

/-- 仅在整个根图能恢复为依赖索引公式时产生 checked payload。 -/
def checkFormula (graph : Graph σ) (availableStage depth : Nat)
    (root : FormulaId) :
    Option (CheckedFormula graph availableStage depth root) :=
  match hDecode : graph.decodeFormula availableStage depth root with
  | none => none
  | some formula => some {
      formula := formula
      decode_eq := hDecode
    }

end Graph

/-!
## 增量构造与共享保持变换
-/

/-- ST 生命周期内的共享公式图 builder。 -/
structure Builder (ω : Type) (σ : AtomSignature) [BEq σ.Symbol]
    [Hashable σ.Symbol] where
  atoms : AtomRegistry.Builder ω σ
  terms : Automation.Data.InternTable.Builder ω TermTag TermNode
  formulas : Automation.Data.InternTable.Builder ω FormulaTag FormulaNode

namespace Builder

variable {ω : Type} {σ : AtomSignature} [BEq σ.Symbol]
  [Hashable σ.Symbol]

def empty (capacity : Nat := 64) : ST ω (Builder ω σ) := do
  return {
    atoms := ← AtomRegistry.Builder.empty capacity
    terms := ← Automation.Data.InternTable.Builder.empty
      (σ := ω) (tag := TermTag) (α := TermNode) capacity
    formulas := ← Automation.Data.InternTable.Builder.empty
      (σ := ω) (tag := FormulaTag) (α := FormulaNode) capacity
  }

def ofGraph (graph : Graph σ) : ST ω (Builder ω σ) := do
  return {
    atoms := ← AtomRegistry.Builder.ofRegistry graph.atoms
    terms := ← Automation.Data.InternTable.Builder.ofTable graph.terms
    formulas := ← Automation.Data.InternTable.Builder.ofTable graph.formulas
  }

def freeze (builder : Builder ω σ) : ST ω (Graph σ) := do
  return {
    atoms := ← builder.atoms.freeze
    terms := ← builder.terms.freeze
    formulas := ← builder.formulas.freeze
  }

def internTerm (builder : Builder ω σ) {depth : Nat}
    (term : Term depth) : ST ω TermId :=
  builder.terms.intern <|
    match term with
    | .bound entry => .bound entry.val
    | .free id => .free id

def internFormula (builder : Builder ω σ) :
    {availableStage depth : Nat} →
      Formula σ availableStage depth → ST ω FormulaId
  | _, _, .falsum =>
      builder.formulas.intern .falsum
  | _, _, .truth =>
      builder.formulas.intern .truth
  | _, _, .mem left right => do
      let leftId ← builder.internTerm left
      let rightId ← builder.internTerm right
      builder.formulas.intern (.mem leftId rightId)
  | _, _, .atom symbol _ arguments => do
      let symbolId ← builder.atoms.intern symbol
      let argumentIds ← arguments.terms.mapM builder.internTerm
      builder.formulas.intern (.atom symbolId argumentIds)
  | _, _, .neg body => do
      let bodyId ← builder.internFormula body
      builder.formulas.intern (.neg bodyId)
  | _, _, .conj left right => do
      let leftId ← builder.internFormula left
      let rightId ← builder.internFormula right
      builder.formulas.intern (.conj leftId rightId)
  | _, _, .disj left right => do
      let leftId ← builder.internFormula left
      let rightId ← builder.internFormula right
      builder.formulas.intern (.disj leftId rightId)
  | _, _, .imp left right => do
      let leftId ← builder.internFormula left
      let rightId ← builder.internFormula right
      builder.formulas.intern (.imp leftId rightId)
  | _, _, .iff left right => do
      let leftId ← builder.internFormula left
      let rightId ← builder.internFormula right
      builder.formulas.intern (.iff leftId rightId)
  | _, _, .forallE body => do
      let bodyId ← builder.internFormula body
      builder.formulas.intern (.forallE bodyId)
  | _, _, .existsE body => do
      let bodyId ← builder.internFormula body
      builder.formulas.intern (.existsE bodyId)

private def weakenTermId (builder : Builder ω σ) (amount : Nat)
    (termId : TermId) : ST ω (Option TermId) := do
  match ← builder.terms.get? termId with
  | some (.bound index) =>
      return some (← builder.terms.intern (.bound (index + amount)))
  | some (.free _) =>
      return some termId
  | none =>
      return none

private def bindTermId (builder : Builder ω σ)
    (substitution : Array TermId) (binderLift : Nat)
    (termId : TermId) : ST ω (Option TermId) := do
  match ← builder.terms.get? termId with
  | some (.free _) =>
      return some termId
  | some (.bound index) =>
      if index < binderLift then
        return some termId
      else
        let sourceIndex := index - binderLift
        let some replacement := substitution[sourceIndex]?
          | return none
        builder.weakenTermId binderLift replacement
  | none =>
      return none

private def bindTermIds (builder : Builder ω σ)
    (substitution : Array TermId) (binderLift : Nat)
    (termIds : Array TermId) : ST ω (Option (Array TermId)) := do
  let mut result := Array.emptyWithCapacity termIds.size
  for termId in termIds do
    let some bound ← builder.bindTermId substitution binderLift termId
      | return none
    result := result.push bound
  return some result

private def bindFormulaWithFuel (builder : Builder ω σ)
    (memo : ST.Ref ω (Std.HashMap (FormulaId × Nat) FormulaId))
    (visited : ST.Ref ω Nat) (substitution : Array TermId) :
    Nat → Nat → FormulaId → ST ω (Option FormulaId)
  | 0, _, _ =>
      return none
  | fuel + 1, binderLift, formulaId => do
      let key := (formulaId, binderLift)
      if let some cached := (← memo.get).get? key then
        return some cached
      let some node ← builder.formulas.get? formulaId
        | return none
      visited.modify (· + 1)
      let result? ←
        match node with
        | .falsum => do
            pure (some (← builder.formulas.intern .falsum))
        | .truth => do
            pure (some (← builder.formulas.intern .truth))
        | .mem left right => do
            let some left' ← builder.bindTermId substitution binderLift left
              | return none
            let some right' ← builder.bindTermId substitution binderLift right
              | return none
            pure (some (← builder.formulas.intern (.mem left' right')))
        | .atom symbol arguments => do
            let some arguments' ←
                builder.bindTermIds substitution binderLift arguments
              | return none
            pure (some (← builder.formulas.intern (.atom symbol arguments')))
        | .neg body => do
            let some body' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift body
              | return none
            pure (some (← builder.formulas.intern (.neg body')))
        | .conj left right => do
            let some left' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift left
              | return none
            let some right' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift right
              | return none
            pure (some (← builder.formulas.intern (.conj left' right')))
        | .disj left right => do
            let some left' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift left
              | return none
            let some right' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift right
              | return none
            pure (some (← builder.formulas.intern (.disj left' right')))
        | .imp left right => do
            let some left' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift left
              | return none
            let some right' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift right
              | return none
            pure (some (← builder.formulas.intern (.imp left' right')))
        | .iff left right => do
            let some left' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift left
              | return none
            let some right' ← bindFormulaWithFuel builder memo visited substitution
                fuel binderLift right
              | return none
            pure (some (← builder.formulas.intern (.iff left' right')))
        | .forallE body => do
            let some body' ← bindFormulaWithFuel builder memo visited substitution
                fuel (binderLift + 1) body
              | return none
            pure (some (← builder.formulas.intern (.forallE body')))
        | .existsE body => do
            let some body' ← bindFormulaWithFuel builder memo visited substitution
                fuel (binderLift + 1) body
              | return none
            pure (some (← builder.formulas.intern (.existsE body')))
      if let some result := result? then
        memo.modify fun entries => entries.insert key result
      return result?

/-- 单次 memoized bind 的根和实际处理过的 `(formula, binderLift)` 数量。 -/
structure BindResult where
  root : FormulaId
  visitedNodes : Nat
  deriving Repr

def bindFormula (builder : Builder ω σ) (fuel : Nat) (root : FormulaId)
    (substitution : Array TermId) : ST ω (Option BindResult) := do
  let memo ← ST.mkRef {}
  let visited ← ST.mkRef 0
  let some result ←
      bindFormulaWithFuel builder memo visited substitution fuel 0 root
    | return none
  return some {
    root := result
    visitedNodes := ← visited.get
  }

end Builder

namespace Graph

variable {σ : AtomSignature} [BEq σ.Symbol] [Hashable σ.Symbol]

/-- 从一个可信新核公式建立共享 operational DAG。 -/
def ofFormula {availableStage depth : Nat}
    (formula : Formula σ availableStage depth) : Graph σ × FormulaId :=
  runST fun ω => do
    let builder ← Builder.empty (ω := ω)
    let root ← builder.internFormula formula
    return (← builder.freeze, root)

/-- 共享图变换结果；`visitedNodes` 用于审计 memoization 是否命中。 -/
structure BindResult (σ : AtomSignature) [BEq σ.Symbol]
    [Hashable σ.Symbol] where
  graph : Graph σ
  root : FormulaId
  visitedNodes : Nat

/-- 在共享图上执行 memoized substitution，并保留访问统计。 -/
def bindWithStats {sourceDepth targetDepth : Nat} (graph : Graph σ)
    (root : FormulaId) (substitution : Fin sourceDepth → Term targetDepth) :
    Option (BindResult σ) :=
  runST fun ω => do
    let builder ← Builder.ofGraph (ω := ω) graph
    let substitutionIds ← (Array.ofFn substitution).mapM builder.internTerm
    let some result ←
        builder.bindFormula (graph.formulaCount + 1) root substitutionIds
      | return none
    return some {
      graph := ← builder.freeze
      root := result.root
      visitedNodes := result.visitedNodes
    }

/-- 在共享图上执行 memoized substitution，并返回扩展后的冻结图。 -/
def bind {sourceDepth targetDepth : Nat} (graph : Graph σ)
    (root : FormulaId) (substitution : Fin sourceDepth → Term targetDepth) :
    Option (Graph σ × FormulaId) := do
  let result ← graph.bindWithStats root substitution
  return (result.graph, result.root)

/-- `rename` 是 operational `bind` 的纯 bound-variable 特例。 -/
def rename {sourceDepth targetDepth : Nat} (graph : Graph σ)
    (root : FormulaId) (indexMap : Fin sourceDepth → Fin targetDepth) :
    Option (Graph σ × FormulaId) :=
  graph.bind root (.bound ∘ indexMap)

end Graph

end Interned
end Definitional
end SetTheory
end YesMetaZFC
