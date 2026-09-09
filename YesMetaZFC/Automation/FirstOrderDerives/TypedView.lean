import Lean
import YesMetaZFC.Logic.FirstOrder.Derivation.Structural
import YesMetaZFC.Logic.Syntax

/-!
# 一阶自动化的内在类型公式视图

本模块只观察新语法核已经保证良构的 `Term`、`Arguments` 与 `Formula`。反射键保留
符号和类型化变量的 Lean 表达式身份，不再维护 raw 变量编号、作用域深度、延迟
`openAt`/`closeFreeAt` 变换或 admissibility 检查证书。

定义包装只在当前根节点按需展开；替换与重命名由语法核自身的显式快路径负责。
-/

namespace YesMetaZFC
namespace Automation
namespace FirstOrderDerives
namespace TypedView

open Lean Meta

initialize registerTraceClass `YesMetaZFC.proveAuto.firstOrderDerives

universe u v w

/-- 沿公式等式运输推导。 -/
theorem derives_cast_formula
    {σ : Logic.Signature.{u, v, w}}
    {T : Logic.FirstOrder.Theory σ}
    {free : Logic.FirstOrder.SortContext σ}
    {Γ : Logic.FirstOrder.Context σ free}
    {φ ψ : Logic.FirstOrder.OpenFormula σ free}
    (hFormula : φ = ψ) (proof : Logic.FirstOrder.Derives T Γ φ) :
    Logic.FirstOrder.Derives T Γ ψ := by
  cases hFormula
  exact proof

structure Config where
  signature : Expr
  free : Expr
  universeLevels : List Level

mutual
  inductive TermKey where
    | bvar (entry : Expr)
    | fvar (sort entry : Expr)
    | app (function : Expr) (arguments : ArgumentsKey)
    | opaque (raw : Expr)

  inductive ArgumentsKey where
    | nil
    | cons (head : TermKey) (tail : ArgumentsKey)
    | opaque (raw : Expr)
end

inductive FormulaKey where
  | falsum
  | truth
  | rel (relation : Expr) (arguments : ArgumentsKey)
  | equal (left right : TermKey)
  | neg (body : FormulaKey)
  | conj (left right : FormulaKey)
  | disj (left right : FormulaKey)
  | imp (left right : FormulaKey)
  | iff (left right : FormulaKey)
  | forallE (sort : Expr) (body : FormulaKey)
  | existsE (sort : Expr) (body : FormulaKey)
  | opaque (raw : Expr)

structure FormulaNode where
  raw : Expr
  key : FormulaKey

structure TermNode where
  raw : Expr
  key : TermKey

structure CompiledFormula where
  source : Expr
  node : FormulaNode
  alignment : Expr

structure ObjectVariable where
  sort : Expr
  entry : Expr

inductive FormulaShell where
  | falsum
  | truth
  | neg (body : FormulaNode)
  | conj (left right : FormulaNode)
  | disj (left right : FormulaNode)
  | imp (left right : FormulaNode)
  | iff (left right : FormulaNode)
  | forallE (sort : Expr) (body : FormulaNode)
  | existsE (sort : Expr) (body : FormulaNode)
  | equal (left right : TermNode)
  | atom

/-- 原子字段只做可约透明度下的定义等价比较。 -/
def atomic_eq (left right : Expr) : MetaM Bool := do
  if Expr.equal left right then
    return true
  withoutModifyingState do
    withTransparency .reducible <| isDefEq left right

private def delta_head? (expression : Expr) : MetaM (Option Expr) := do
  match expression.getAppFn with
  | .const declaration levels =>
      let info ← getConstInfo declaration
      let some value := info.value?
        | return none
      return some <|
        (value.instantiateLevelParams info.levelParams levels).beta
          expression.getAppArgs
  | _ =>
      return none

/-- 只展开到当前构造子，不主动正规化整棵 AST。 -/
private partial def expose_head (expression : Expr) (fuel : Nat := 64) :
    MetaM Expr := do
  let expression ← instantiateMVars expression
  if fuel == 0 then
    return expression
  -- 先约化 recursor 的实际参数，再展开包装，避免把类型化替换打散成 Eq.rec。
  let reduced ← withTransparency .default <| whnf expression
  unless Expr.equal reduced expression do
    return ← expose_head reduced (fuel - 1)
  if let some unfolded ← delta_head? expression then
    unless Expr.equal unfolded expression do
      return ← expose_head unfolded (fuel - 1)
  return expression

private def defeq_alignment? (left right : Expr) : MetaM (Option Expr) := do
  if Expr.equal left right then
    return some (← mkEqRefl left)
  let savedState ← saveState
  let aligned ←
    try
      withTransparency .default <| isDefEq left right
    catch _ =>
      pure false
  savedState.restore
  if aligned then
    return some (← mkEqRefl left)
  return none

mutual
  private partial def compile_term
      (expression : Expr) (fuel : Nat := 128) : MetaM TermNode := do
    let source ← instantiateMVars expression
    if fuel == 0 then
      return { raw := source, key := .opaque source }
    let expression ← expose_head source fuel
    if expression.isAppOfArity ``Logic.FirstOrder.Term.bvar 5 then
      return { raw := source, key := .bvar expression.getAppArgs[4]! }
    if expression.isAppOfArity ``Logic.FirstOrder.Term.fvar 5 then
      let arguments := expression.getAppArgs
      return {
        raw := source
        key := .fvar arguments[3]! arguments[4]!
      }
    if expression.isAppOfArity ``Logic.FirstOrder.Term.app 5 then
      let arguments := expression.getAppArgs
      let compiledArguments ← compile_arguments arguments[4]! (fuel - 1)
      return {
        raw := source
        key := .app arguments[3]! compiledArguments.2
      }
    return { raw := source, key := .opaque expression }

  private partial def compile_arguments
      (expression : Expr) (fuel : Nat := 128) : MetaM (Expr × ArgumentsKey) := do
    let source ← instantiateMVars expression
    if fuel == 0 then
      return (source, .opaque source)
    let expression ← expose_head source fuel
    if expression.isAppOfArity ``Logic.FirstOrder.Arguments.nil 3 then
      return (expression, .nil)
    if expression.isAppOfArity ``Logic.FirstOrder.Arguments.cons 7 then
      let arguments := expression.getAppArgs
      let head ← compile_term arguments[5]! (fuel - 1)
      let tail ← compile_arguments arguments[6]! (fuel - 1)
      return (source, .cons head.key tail.2)
    return (expression, .opaque expression)
end

private partial def compile_formula_node
    (expression : Expr) (fuel : Nat := 256) : MetaM FormulaNode := do
  let source ← instantiateMVars expression
  if fuel == 0 then
    return { raw := source, key := .opaque source }
  let expression ← expose_head source fuel
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.falsum 3 then
    return { raw := expression, key := .falsum }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.truth 3 then
    return { raw := expression, key := .truth }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.rel 5 then
    let arguments := expression.getAppArgs
    let compiledArguments ← compile_arguments arguments[4]! (fuel - 1)
    -- 原子保留已有类型参数与项；反射键只观察结构，不强制展开 numeral 的递归实现。
    return { raw := expression, key := .rel arguments[3]! compiledArguments.2 }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.equal 6 then
    let arguments := expression.getAppArgs
    let left ← compile_term arguments[4]! (fuel - 1)
    let right ← compile_term arguments[5]! (fuel - 1)
    return { raw := expression, key := .equal left.key right.key }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.neg 4 then
    let body ← compile_formula_node expression.getAppArgs[3]! (fuel - 1)
    let raw := mkAppN expression.getAppFn (expression.getAppArgs.set! 3 body.raw)
    return { raw, key := .neg body.key }
  for constructor in
      [``Logic.FirstOrder.Formula.conj,
        ``Logic.FirstOrder.Formula.disj,
        ``Logic.FirstOrder.Formula.imp,
        ``Logic.FirstOrder.Formula.iff] do
    if expression.isAppOfArity constructor 5 then
      let arguments := expression.getAppArgs
      let left ← compile_formula_node arguments[3]! (fuel - 1)
      let right ← compile_formula_node arguments[4]! (fuel - 1)
      let raw := mkAppN expression.getAppFn ((arguments.set! 3 left.raw).set! 4 right.raw)
      let key :=
        if constructor == ``Logic.FirstOrder.Formula.conj then
          FormulaKey.conj left.key right.key
        else if constructor == ``Logic.FirstOrder.Formula.disj then
          FormulaKey.disj left.key right.key
        else if constructor == ``Logic.FirstOrder.Formula.imp then
          FormulaKey.imp left.key right.key
        else
          FormulaKey.iff left.key right.key
      return { raw, key }
  for constructor in
      [``Logic.FirstOrder.Formula.forallE,
        ``Logic.FirstOrder.Formula.existsE] do
    if expression.isAppOfArity constructor 5 then
      let arguments := expression.getAppArgs
      let body ← compile_formula_node arguments[4]! (fuel - 1)
      let raw := mkAppN expression.getAppFn (arguments.set! 4 body.raw)
      let key :=
        if constructor == ``Logic.FirstOrder.Formula.forallE then
          FormulaKey.forallE arguments[3]! body.key
        else
          FormulaKey.existsE arguments[3]! body.key
      return { raw, key }
  return { raw := expression, key := .opaque expression }

def compile_formula (_config : Config) (formula : Expr) : MetaM CompiledFormula := do
  let source ← instantiateMVars formula
  let node ← compile_formula_node source
  let some alignment ← defeq_alignment? source node.raw
    | throwError
        "intrinsic formula view could not align {source} with {node.raw}"
  return { source, node, alignment }

def cast_derives (alignment proof : Expr) : MetaM Expr :=
  mkAppM ``derives_cast_formula #[alignment, proof]

def FormulaNode.alignment_with?
    (_config : Config) (left right : FormulaNode) : MetaM (Option Expr) :=
  defeq_alignment? left.raw right.raw

def TermNode.alignment_with?
    (_config : Config) (left right : TermNode) : MetaM (Option Expr) :=
  defeq_alignment? left.raw right.raw

def FormulaNode.shell (node : FormulaNode) : FormulaShell :=
  match node.key with
  | .falsum =>
      .falsum
  | .truth =>
      .truth
  | .neg body =>
      .neg { raw := node.raw.getAppArgs[3]!, key := body }
  | .conj left right =>
      .conj
        { raw := node.raw.getAppArgs[3]!, key := left }
        { raw := node.raw.getAppArgs[4]!, key := right }
  | .disj left right =>
      .disj
        { raw := node.raw.getAppArgs[3]!, key := left }
        { raw := node.raw.getAppArgs[4]!, key := right }
  | .imp left right =>
      .imp
        { raw := node.raw.getAppArgs[3]!, key := left }
        { raw := node.raw.getAppArgs[4]!, key := right }
  | .iff left right =>
      .iff
        { raw := node.raw.getAppArgs[3]!, key := left }
        { raw := node.raw.getAppArgs[4]!, key := right }
  | .forallE sort body =>
      .forallE sort { raw := node.raw.getAppArgs[4]!, key := body }
  | .existsE sort body =>
      .existsE sort { raw := node.raw.getAppArgs[4]!, key := body }
  | .equal left right =>
      .equal
        { raw := node.raw.getAppArgs[4]!, key := left }
        { raw := node.raw.getAppArgs[5]!, key := right }
  | .rel .. | .opaque .. =>
      .atom

/-- 若等式两端定义相等，返回自反式到目标等式的运输证明。 -/
def FormulaNode.equality_reflexive_alignment?
    (config : Config) (node : FormulaNode) :
    MetaM (Option (Expr × Expr)) := do
  let .equal left right := node.shell
    | return none
  unless (← left.alignment_with? config right).isSome do
    return none
  let reflexive ←
    mkAppM ``Logic.FirstOrder.Formula.equal #[left.raw, left.raw]
  let some alignment ← defeq_alignment? reflexive node.raw
    | return none
  return some (left.raw, alignment)

def FormulaNode.neg (_config : Config) (body : FormulaNode) :
    MetaM FormulaNode := do
  let raw ← mkAppM ``Logic.FirstOrder.Formula.neg #[body.raw]
  compile_formula_node raw

/-- 以类型正确的项实例化最外层 binder。 -/
def FormulaNode.instantiate_top
    (_config : Config) (replacement : Expr) (body : FormulaNode) :
    MetaM CompiledFormula := do
  let source ←
    mkAppM ``Logic.FirstOrder.Formula.instantiateTop
      #[replacement, body.raw]
  let source ← instantiateMVars source
  let node ← compile_formula_node source
  let some alignment ← defeq_alignment? source node.raw
    | throwError
        "intrinsic instantiated formula could not align {source} with {node.raw}"
  return { source, node, alignment }

private def Config.sort_type (config : Config) : MetaM Expr := do
  let freeType ← whnf (← inferType config.free)
  unless freeType.isAppOfArity ``List 1 do
    throwError "intrinsic free context has unexpected type {freeType}"
  return freeType.getAppArgs[0]!

private def Config.empty_bound (config : Config) : MetaM Expr := do
  let sortType ← config.sort_type
  let level ← getLevel sortType
  return mkApp (mkConst ``List.nil [level]) sortType

/-- 在当前开放公式的 free 上下文中重建该变量项。 -/
def ObjectVariable.term (config : Config) (objectVariable : ObjectVariable) :
    MetaM Expr := do
  let emptyBound ← config.empty_bound
  return mkAppN
    (mkConst ``Logic.FirstOrder.Term.fvar config.universeLevels)
    #[config.signature, emptyBound, config.free,
      objectVariable.sort, objectVariable.entry]

mutual
  private partial def TermKey.collect_variables
      (variables : Array ObjectVariable) :
      TermKey → MetaM (Array ObjectVariable)
    | .bvar .. | .opaque .. =>
        return variables
    | .fvar sort entry => do
        for candidate in variables do
          if (← atomic_eq candidate.sort sort) &&
              (← atomic_eq candidate.entry entry) then
            return variables
        return variables.push { sort, entry }
    | .app _ arguments =>
        arguments.collect_variables variables

  private partial def ArgumentsKey.collect_variables
      (variables : Array ObjectVariable) :
      ArgumentsKey → MetaM (Array ObjectVariable)
    | .nil | .opaque .. =>
        return variables
    | .cons head tail => do
        let variables ← head.collect_variables variables
        tail.collect_variables variables
end

private partial def FormulaKey.collect_variables
    (variables : Array ObjectVariable) :
    FormulaKey → MetaM (Array ObjectVariable)
  | .falsum | .truth | .opaque .. =>
      return variables
  | .rel _ arguments =>
      arguments.collect_variables variables
  | .equal left right => do
      let variables ← left.collect_variables variables
      right.collect_variables variables
  | .neg body
  | .forallE _ body
  | .existsE _ body =>
      body.collect_variables variables
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right => do
      let variables ← left.collect_variables variables
      right.collect_variables variables

def FormulaNode.collect_variables
    (_config : Config) (node : FormulaNode) :
    MetaM (Array ObjectVariable) :=
  node.key.collect_variables #[]

end TypedView
end FirstOrderDerives
end Automation
end YesMetaZFC
