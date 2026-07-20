import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.HOReplayQuotation
import YesMetaZFC.Logic.HigherOrder

/-!
# 单基础域宿主简单高阶重化

本模块只负责固定 `Type 0` 的宿主简单类型、项、公式快照和 Lean 元层重化。
函数应用按柯里化结构逐层保存为 `apply`，lambda 原样保存为 `lam`；搜索、checked
payload 与语义回放仍复用现有 `CoreSyntax`、`Logic.HigherOrder` 和 HODAG 主线。

宿主对象域可以位于任意 `Type u`。当前前端只接受由同一基础域生成的非依赖简单
函数类型；依赖函数、异质基础域和命题值函数会给出明确拒绝诊断。
-/

namespace YesMetaZFC
namespace Automation
namespace HostHigherOrder

universe u x

open CoreSyntax

/-- 由单一宿主对象域自由生成的简单类型。 -/
inductive SimpleType where
  | object
  | arrow (domain codomain : SimpleType)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

namespace SimpleType

/-- 简单类型在任意 universe 宿主对象域上的直接解释。 -/
@[reducible] def denote (α : Type u) : SimpleType → Type u
  | .object => α
  | .arrow domain codomain => denote α domain → denote α codomain

/-- 宿主简单类型进入公共 core sort。 -/
def toCore : SimpleType → CoreSort
  | .object => .object
  | .arrow domain codomain => .arrow domain.toCore codomain.toCore

/-- core sort 回到宿主简单类型；非宿主 sort 只走不可达的 object fallback。 -/
def ofCore : CoreSort → SimpleType
  | .arrow domain codomain => .arrow (ofCore domain) (ofCore codomain)
  | _ => .object

@[simp]
theorem ofCore_toCore (sort : SimpleType) :
    ofCore sort.toCore = sort := by
  induction sort with
  | object =>
      rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp [toCore, ofCore, ihDomain, ihCodomain]

/-- 宿主简单类型进入原生 HO 基础 sort `Unit` 的自由箭头闭包。 -/
def toHigherOrder : SimpleType → Logic.HigherOrder.SimpleType Unit
  | .object => .base ()
  | .arrow domain codomain =>
      .arrow domain.toHigherOrder codomain.toHigherOrder

/-- 是否真正含有函数层。 -/
def isHigherOrder : SimpleType → Bool
  | .object => false
  | .arrow _ _ => true

/-- 到 core sort 的投影不合并不同宿主简单类型。 -/
theorem toCore_injective : Function.Injective toCore := by
  intro left
  induction left with
  | object =>
      intro right h
      cases right with
      | object =>
          rfl
      | arrow _ _ =>
          simp [toCore] at h
  | arrow leftDomain leftCodomain ihDomain ihCodomain =>
      intro right h
      cases right with
      | object =>
          simp [toCore] at h
      | arrow rightDomain rightCodomain =>
          simp only [toCore, CoreSort.arrow.injEq] at h
          have hDomain := ihDomain h.1
          have hCodomain := ihCodomain h.2
          cases hDomain
          cases hCodomain
          rfl

end SimpleType

/-- 每个宿主函数值都以其完整柯里化类型作为零元符号进入快照。 -/
structure FunctionSymbol where
  id : Nat
  sort : SimpleType
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

/-- 宿主谓词保留全部简单类型参数。 -/
structure PredicateSymbol where
  id : Nat
  domain : List SimpleType
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

/-- 单基础域宿主高阶项。 -/
inductive Term where
  | bvar (sort : SimpleType) (index : Nat)
  | symbol (value : FunctionSymbol)
  | apply (function argument : Term)
  | lam (domain codomain : SimpleType) (body : Term)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, Lean.ToExpr

/-- 单基础域宿主高阶公式。 -/
inductive Formula where
  | atom (symbol : PredicateSymbol) (arguments : List Term)
  | equal (sort : SimpleType) (left right : Term)
  | falsum
  | truth
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | imp (left right : Formula)
  | iff (left right : Formula)
  | forallE (sort : SimpleType) (body : Formula)
  | existsE (sort : SimpleType) (body : Formula)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, Lean.ToExpr

/-- 一份纯 `Type 0` 的宿主高阶问题快照。 -/
structure Problem where
  premises : List Formula
  target : Formula
  deriving Repr, Inhabited, Lean.ToExpr

namespace Term

/-- 按最近绑定变量优先的上下文推断项类型。 -/
def inferSortWith (context : List SimpleType) : Term → Option SimpleType
  | .bvar sort index =>
      if context[index]? = some sort then some sort else none
  | .symbol value => some value.sort
  | .apply function argument => do
      let functionSort ← function.inferSortWith context
      let argumentSort ← argument.inferSortWith context
      match functionSort with
      | .object => none
      | .arrow domain codomain =>
          if argumentSort = domain then some codomain else none
  | .lam domain codomain body => do
      let bodySort ← body.inferSortWith (domain :: context)
      if bodySort = codomain then
        some (.arrow domain codomain)
      else
        none

/-- 逐项推断参数列表的简单类型。 -/
def inferSortListWith (context : List SimpleType) :
    List Term → Option (List SimpleType)
  | [] => some []
  | head :: tail => do
      let headSort ← head.inferSortWith context
      let tailSorts ← inferSortListWith context tail
      return headSort :: tailSorts

/-- 空绑定上下文中的闭项类型。 -/
def inferSort? (term : Term) : Option SimpleType :=
  term.inferSortWith []

/-- 宿主项进入公共 FOOL/lambda core。 -/
def toCore : Term → CoreSyntax.Term
  | .bvar sort index => .bvar sort.toCore index
  | .symbol value =>
      .app {
        id := value.id
        arity := 0
        role := .parameter
        inputSorts := []
        outputSort := value.sort.toCore
      } []
  | .apply function argument =>
      .apply function.toCore argument.toCore
  | .lam domain codomain body =>
      .lam domain.toCore codomain.toCore body.toCore

end Term

namespace Formula

/-- 在给定绑定上下文中检查公式 scope、简单类型与谓词参数。 -/
def checkWith (context : List SimpleType) : Formula → Bool
  | .atom symbol arguments =>
      Term.inferSortListWith context arguments = some symbol.domain
  | .equal sort left right =>
      left.inferSortWith context = some sort &&
        right.inferSortWith context = some sort
  | .falsum | .truth => true
  | .neg body => body.checkWith context
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      left.checkWith context && right.checkWith context
  | .forallE sort body
  | .existsE sort body =>
      body.checkWith (sort :: context)

/-- 闭公式 checker。 -/
def check (formula : Formula) : Bool :=
  formula.checkWith []

/-- 公式是否含有函数类型、`apply` 或 `lam`。 -/
partial def hasHigherOrder : Formula → Bool
  | .atom symbol arguments =>
      symbol.domain.any SimpleType.isHigherOrder ||
        arguments.any termHasHigherOrder
  | .equal sort left right =>
      sort.isHigherOrder || termHasHigherOrder left ||
        termHasHigherOrder right
  | .falsum | .truth => false
  | .neg body => body.hasHigherOrder
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      left.hasHigherOrder || right.hasHigherOrder
  | .forallE sort body
  | .existsE sort body =>
      sort.isHigherOrder || body.hasHigherOrder
where
  termHasHigherOrder : Term → Bool
    | .bvar sort _ => sort.isHigherOrder
    | .symbol symbol => symbol.sort.isHigherOrder
    | .apply _ _ | .lam _ _ _ => true

/-- 宿主谓词符号进入公共 core。 -/
def predicateToCore (symbol : PredicateSymbol) : CoreSyntax.PredicateSymbol := {
  id := symbol.id
  arity := symbol.domain.length
  role := .relation
  inputSorts := symbol.domain.map SimpleType.toCore
}

/-- 宿主高阶公式进入公共 FOOL/lambda core。 -/
def toCore : Formula → CoreSyntax.Formula
  | .atom symbol arguments =>
      .atom (predicateToCore symbol) (arguments.map Term.toCore)
  | .equal sort left right =>
      .equal sort.toCore left.toCore right.toCore
  | .falsum => .falseE
  | .truth => .trueE
  | .neg body => .neg body.toCore
  | .conj left right => .conj left.toCore right.toCore
  | .disj left right => .disj left.toCore right.toCore
  | .imp left right => .imp left.toCore right.toCore
  | .iff left right => .iffE left.toCore right.toCore
  | .forallE sort body => .forallE sort.toCore body.toCore
  | .existsE sort body => .existsE sort.toCore body.toCore

end Formula

namespace Problem

/-- 整问题的纯语法 checker。 -/
def check (problem : Problem) : Bool :=
  problem.premises.all Formula.check && problem.target.check

/-- 整问题是否真的需要 HO provider。 -/
def hasHigherOrder (problem : Problem) : Bool :=
  problem.premises.any Formula.hasHigherOrder ||
    problem.target.hasHigherOrder

/-- 整问题进入公共 core source 语法。 -/
def toCorePremises (problem : Problem) : List CoreSyntax.Formula :=
  problem.premises.map Formula.toCore

/-- 整问题目标进入公共 core source 语法。 -/
def toCoreTarget (problem : Problem) : CoreSyntax.Formula :=
  problem.target.toCore

end Problem

/-! ## 到原生 HO checker 语法的直接投影 -/

/-- 宿主快照使用的固定原生 HO 签名。 -/
def higherOrderSignature : Logic.HigherOrder.Signature where
  BaseSort := Unit
  FuncSymbol := FunctionSymbol
  RelSymbol := PredicateSymbol
  funcDomain := fun _ => []
  funcCodomain := fun symbol => symbol.sort.toHigherOrder
  isFunctionExtensionalityWitness := fun _ => false
  relDomain := fun symbol =>
    symbol.domain.map SimpleType.toHigherOrder

instance higherOrderSignatureBaseSortDecidableEq :
    DecidableEq higherOrderSignature.BaseSort :=
  inferInstanceAs (DecidableEq Unit)

namespace Term

/-- 宿主项直接进入现有 `Logic.HigherOrder.Term`。 -/
def toHigherOrder : Term → Logic.HigherOrder.Term higherOrderSignature
  | .bvar sort index =>
      .var (.bvar sort.toHigherOrder index)
  | .symbol value => .app value []
  | .apply function argument =>
      .apply function.toHigherOrder argument.toHigherOrder
  | .lam domain codomain body =>
      .lam domain.toHigherOrder codomain.toHigherOrder body.toHigherOrder

end Term

namespace Formula

/-- 宿主公式直接进入现有 `Logic.HigherOrder.Formula`。 -/
def toHigherOrder : Formula → Logic.HigherOrder.Formula higherOrderSignature
  | .atom symbol arguments =>
      .rel symbol (arguments.map Term.toHigherOrder)
  | .equal sort left right =>
      .equal sort.toHigherOrder left.toHigherOrder right.toHigherOrder
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toHigherOrder
  | .conj left right => .conj left.toHigherOrder right.toHigherOrder
  | .disj left right => .disj left.toHigherOrder right.toHigherOrder
  | .imp left right => .imp left.toHigherOrder right.toHigherOrder
  | .iff left right => .iff left.toHigherOrder right.toHigherOrder
  | .forallE sort body =>
      .forallE sort.toHigherOrder body.toHigherOrder
  | .existsE sort body =>
      .existsE sort.toHigherOrder body.toHigherOrder

end Formula

/-! ## 任意 universe 的宿主解释与可实现 core 模型 -/

/-- core sort 在单一宿主基础域上的真实简单类型解释。 -/
@[reducible] def CoreDenote (α : Type u) : CoreSort → Type u
  | .object => α
  | .bool | .prop => ULift.{u} Prop
  | .named _ => ULift.{u} Unit
  | .arrow domain codomain =>
      CoreDenote α domain → CoreDenote α codomain

/-- 每个 core sort 的 canonical 默认值。 -/
def coreDefault (default : α) : (sort : CoreSort) → CoreDenote α sort
  | .object => default
  | .bool | .prop => ⟨False⟩
  | .named _ => ⟨()⟩
  | .arrow _ codomain => fun _ => coreDefault default codomain

mutual
  /-- 宿主简单类型值进入对应 core sort 的真实解释。 -/
  def simpleToCore {α : Type u} : (sort : SimpleType) →
      SimpleType.denote α sort → CoreDenote α sort.toCore
    | .object, value => value
    | .arrow domain codomain, value =>
        fun argument =>
          simpleToCore codomain
            (value (coreToSimple domain argument))

  /-- core 中来自宿主简单类型的值回到原 Lean 类型。 -/
  def coreToSimple {α : Type u} : (sort : SimpleType) →
      CoreDenote α sort.toCore → SimpleType.denote α sort
    | .object, value => value
    | .arrow domain codomain, value =>
        fun argument =>
          coreToSimple codomain
            (value (simpleToCore domain argument))
end

mutual
  @[simp]
  theorem coreToSimple_simpleToCore {α : Type u} (sort : SimpleType)
      (value : SimpleType.denote α sort) :
      coreToSimple sort (simpleToCore sort value) = value := by
    cases sort with
    | object =>
        rfl
    | arrow domain codomain =>
        simp only [simpleToCore, coreToSimple]
        funext argument
        rw [coreToSimple_simpleToCore domain,
          coreToSimple_simpleToCore codomain]

  @[simp]
theorem simpleToCore_coreToSimple {α : Type u} (sort : SimpleType)
      (value : CoreDenote α sort.toCore) :
      simpleToCore sort (coreToSimple sort value) = value := by
    cases sort with
    | object =>
        rfl
    | arrow domain codomain =>
        simp only [simpleToCore, coreToSimple]
        funext argument
        rw [simpleToCore_coreToSimple domain,
          simpleToCore_coreToSimple codomain]
end

/-- 每个简单类型上的编码都是单射。 -/
theorem simpleToCore_injective {α : Type u} (sort : SimpleType) :
    Function.Injective (simpleToCore (α := α) sort) := by
  intro left right h
  have hDecoded := congrArg (coreToSimple sort) h
  simpa using hDecoded

/-- 把不同简单类型的宿主值打包进 preprocessing 使用的单 carrier。 -/
structure Value (α : Type u) where
  sort : CoreSort
  value : CoreDenote α sort

namespace Value

/-- 按目标 sort 读取打包值；错 sort 只用于不可达的 total fallback。 -/
def read (default : α) (sort : CoreSort) (value : Value α) :
    CoreDenote α sort :=
  if h : value.sort = sort then
    h ▸ value.value
  else
    coreDefault default sort

@[simp]
theorem read_mk (default : α) (sort : CoreSort) (value : CoreDenote α sort) :
    read default sort ⟨sort, value⟩ = value := by
  simp [read]

/-- 把任意打包值 total 地收紧到指定 sort。 -/
def coerce (default : α) (sort : CoreSort) (value : Value α) : Value α :=
  ⟨sort, value.read default sort⟩

@[simp]
theorem coerce_sort (default : α) (sort : CoreSort) (value : Value α) :
    (value.coerce default sort).sort = sort :=
  rfl

theorem coerce_eq_self (default : α) (sort : CoreSort) (value : Value α)
    (hSort : value.sort = sort) :
    value.coerce default sort = value := by
  rcases value with ⟨actualSort, value⟩
  simp only at hSort
  subst actualSort
  simp [coerce, read]

/-- 单 carrier 上的 typed application。 -/
def apply (default : α) (function argument : Value α) : Value α :=
  match function with
  | ⟨.arrow domain codomain, value⟩ =>
      ⟨codomain, value (argument.read default domain)⟩
  | _ => ⟨.object, default⟩

/-- 单 carrier 上只观察声明 domain 的 typed lambda。 -/
def lambda (default : α) (domain codomain : CoreSort)
    (body : Value α → Value α) : Value α :=
  ⟨.arrow domain codomain, fun argument =>
    (body ⟨domain, argument⟩).read default codomain⟩

/-- typed lambda 对 typed argument 满足 β；该引理只消费模型合同中的两项 sort 前提。 -/
theorem apply_lambda (default : α) (domain codomain : CoreSort)
    (body : Value α → Value α) (argument : Value α)
    (hArgument : argument.sort = domain)
    (hBody : ∀ value, value.sort = domain → (body value).sort = codomain) :
    apply default (lambda default domain codomain body) argument =
      body argument := by
  rcases argument with ⟨argumentSort, argument⟩
  simp only at hArgument
  subst argumentSort
  simp only [lambda, apply, read_mk]
  exact coerce_eq_self default codomain _ <| hBody ⟨domain, argument⟩ rfl

/-- 同 sort 的底层值相等时，对应 packed 值相等。 -/
theorem eq_of_value_eq {sort : CoreSort} {left right : CoreDenote α sort}
    (h : left = right) :
    (⟨sort, left⟩ : Value α) = ⟨sort, right⟩ := by
  cases h
  rfl

/-- 已知 tag 后，packed equality 与底层 typed equality 等价。 -/
theorem eq_iff_read_eq (default : α) (sort : CoreSort)
    (left right : Value α) (hLeft : left.sort = sort)
    (hRight : right.sort = sort) :
    left = right ↔ left.read default sort = right.read default sort := by
  rcases left with ⟨leftSort, left⟩
  rcases right with ⟨rightSort, right⟩
  simp only at hLeft hRight
  subst leftSort
  subst rightSort
  simp [read]

end Value

/-- 宿主直接解释使用的异质简单类型值。 -/
structure SimpleValue (α : Type u) where
  sort : SimpleType
  value : SimpleType.denote α sort

namespace SimpleValue

/-- 每个宿主简单类型的默认值。 -/
def default (base : α) : (sort : SimpleType) → SimpleType.denote α sort
  | .object => base
  | .arrow _ codomain => fun _ => default base codomain

/-- 按声明 simple type 读取宿主值。 -/
def read (base : α) (sort : SimpleType) (value : SimpleValue α) :
    SimpleType.denote α sort :=
  if h : value.sort = sort then
    h ▸ value.value
  else
    default base sort

@[simp]
theorem read_mk (base : α) (sort : SimpleType)
    (value : SimpleType.denote α sort) :
    read base sort ⟨sort, value⟩ = value := by
  simp [read]

/-- 把宿主值收紧到声明 simple type。 -/
def coerce (base : α) (sort : SimpleType) (value : SimpleValue α) :
    SimpleValue α :=
  ⟨sort, value.read base sort⟩

theorem coerce_eq_self (base : α) (sort : SimpleType) (value : SimpleValue α)
    (hSort : value.sort = sort) :
    value.coerce base sort = value := by
  rcases value with ⟨actualSort, value⟩
  simp only at hSort
  subst actualSort
  simp [coerce, read]

/-- 宿主简单类型 application。 -/
def apply (base : α) (function argument : SimpleValue α) : SimpleValue α :=
  match function with
  | ⟨.arrow domain codomain, value⟩ =>
      ⟨codomain, value (argument.read base domain)⟩
  | _ => ⟨.object, base⟩

/-- 宿主简单类型 lambda。 -/
def lambda (base : α) (domain codomain : SimpleType)
    (body : SimpleValue α → SimpleValue α) : SimpleValue α :=
  ⟨.arrow domain codomain, fun argument =>
    (body ⟨domain, argument⟩).read base codomain⟩

/-- 宿主值进入 core 单 carrier。 -/
def toCore (value : SimpleValue α) : Value α :=
  ⟨value.sort.toCore, simpleToCore value.sort value.value⟩

/-- core 值按给定宿主 simple type 解包。 -/
def ofCore (base : α) (sort : SimpleType) (value : Value α) :
    SimpleValue α :=
  ⟨sort, coreToSimple sort (value.read base sort.toCore)⟩

@[simp]
theorem ofCore_toCore (base : α) (value : SimpleValue α) :
    ofCore base value.sort value.toCore = value := by
  rcases value with ⟨sort, value⟩
  simp [ofCore, toCore]

theorem default_toCore (base : α) (sort : SimpleType) :
    simpleToCore sort (default base sort) = coreDefault base sort.toCore := by
  induction sort with
  | object =>
      rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [default, simpleToCore]
      funext argument
      exact ihCodomain

theorem read_toCore (base : α) (sort : SimpleType) (value : SimpleValue α) :
    simpleToCore sort (value.read base sort) =
      value.toCore.read base sort.toCore := by
  rcases value with ⟨actualSort, value⟩
  by_cases hSort : actualSort = sort
  · subst actualSort
    simp [read, toCore, Value.read]
  · have hCoreSort : actualSort.toCore ≠ sort.toCore := fun h =>
      hSort (SimpleType.toCore_injective h)
    simp [read, toCore, Value.read, hSort, hCoreSort, default_toCore]

theorem coerce_toCore (base : α) (sort : SimpleType) (value : SimpleValue α) :
    (value.coerce base sort).toCore =
      value.toCore.coerce base sort.toCore := by
  apply Value.eq_of_value_eq
  exact read_toCore base sort value

theorem apply_toCore (base : α) (domain codomain : SimpleType)
    (function argument : SimpleValue α)
    (hFunction : function.sort = .arrow domain codomain)
    (hArgument : argument.sort = domain) :
    (apply base function argument).toCore =
      Value.apply base function.toCore argument.toCore := by
  rcases function with ⟨functionSort, function⟩
  rcases argument with ⟨argumentSort, argument⟩
  simp only at hFunction hArgument
  subst functionSort
  subst argumentSort
  simp [apply, toCore, Value.apply, read, Value.read, SimpleType.toCore,
    simpleToCore]

theorem lambda_toCore (base : α) (domain codomain : SimpleType)
    (coreBody : Value α → Value α)
    (simpleBody : SimpleValue α → SimpleValue α)
    (hBody :
      ∀ argument : CoreDenote α domain.toCore,
        coreBody ⟨domain.toCore, argument⟩ =
          (simpleBody ⟨domain, coreToSimple domain argument⟩).toCore) :
    Value.lambda base domain.toCore codomain.toCore coreBody =
      (lambda base domain codomain simpleBody).toCore := by
  apply Value.eq_of_value_eq
  funext argument
  change
    (coreBody ⟨domain.toCore, argument⟩).read base codomain.toCore =
      simpleToCore codomain
        ((simpleBody ⟨domain, coreToSimple domain argument⟩).read base codomain)
  rw [hBody argument]
  exact (read_toCore base codomain _).symm

end SimpleValue

/-- 宿主函数与谓词符号的 proof-relevant 解释表。 -/
structure Interpretation (α : Type u) where
  default : α
  function : Nat → SimpleValue α
  predicate : Nat → List (SimpleValue α) → Prop

namespace Term

/-- 最近 binder 优先的宿主 packed 环境。 -/
def pushBound (bound : Nat → SimpleValue α)
    (value : SimpleValue α) : Nat → SimpleValue α
  | 0 => value
  | index + 1 => bound index

/-- 宿主 packed 环境按 checker 上下文保持 binder sort。 -/
def BoundWellSorted (context : List SimpleType)
    (bound : Nat → SimpleValue α) : Prop :=
  ∀ index sort, context[index]? = some sort → (bound index).sort = sort

/-- typed 值压栈后继续保持扩展的 checker 上下文。 -/
theorem boundWellSorted_push {context : List SimpleType}
    {bound : Nat → SimpleValue α} (hBound : BoundWellSorted context bound)
    (sort : SimpleType) (value : SimpleValue α) (hValue : value.sort = sort) :
    BoundWellSorted (sort :: context) (pushBound bound value) := by
  intro index target hLookup
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hLookup
      subst target
      exact hValue
  | succ index =>
      exact hBound index target <| by
        simpa using hLookup

/-- 宿主项直接解释到 packed 简单类型值。 -/
def eval (interpretation : Interpretation α)
    (bound : Nat → SimpleValue α) : Term → SimpleValue α
  | .bvar sort index =>
      (bound index).coerce interpretation.default sort
  | .symbol value =>
      (interpretation.function value.id).coerce
        interpretation.default value.sort
  | .apply function argument =>
      SimpleValue.apply interpretation.default
        (function.eval interpretation bound)
        (argument.eval interpretation bound)
  | .lam domain codomain body =>
      SimpleValue.lambda interpretation.default domain codomain fun value =>
        body.eval interpretation (pushBound bound value)

/-- checker 成功的宿主项解释携带其声明 sort tag。 -/
theorem eval_sort_of_inferSortWith
    (interpretation : Interpretation α) (bound : Nat → SimpleValue α)
    (context : List SimpleType) (term : Term) (sort : SimpleType)
    (hCheck : term.inferSortWith context = some sort) :
    (term.eval interpretation bound).sort = sort := by
  induction term generalizing context sort bound with
  | bvar annotated index =>
      unfold Term.inferSortWith at hCheck
      split at hCheck
      next hLookup =>
        simp only [Option.some.injEq] at hCheck
        subst sort
        rfl
      next =>
        simp at hCheck
  | symbol value =>
      unfold Term.inferSortWith at hCheck
      simp only [Option.some.injEq] at hCheck
      subst sort
      rfl
  | apply function argument ihFunction ihArgument =>
      unfold Term.inferSortWith at hCheck
      cases hFunction : function.inferSortWith context with
      | none =>
          simp [hFunction] at hCheck
      | some functionSort =>
          cases hArgument : argument.inferSortWith context with
          | none =>
              simp [hFunction, hArgument] at hCheck
          | some argumentSort =>
              cases functionSort with
              | object =>
                  simp [hFunction, hArgument] at hCheck
              | arrow domain codomain =>
                  by_cases hDomain : argumentSort = domain
                  · simp [hFunction, hArgument, hDomain] at hCheck
                    subst argumentSort
                    subst sort
                    have hFunctionTag :=
                      ihFunction bound context (.arrow domain codomain) hFunction
                    cases hEval : function.eval interpretation bound with
                    | mk actualSort functionValue =>
                        simp only [hEval] at hFunctionTag
                        subst actualSort
                        simp [Term.eval, hEval, SimpleValue.apply]
                  · simp [hFunction, hArgument, hDomain] at hCheck
  | lam domain codomain body ih =>
      unfold Term.inferSortWith at hCheck
      cases hBody : body.inferSortWith (domain :: context) with
      | none =>
          simp [hBody] at hCheck
      | some bodySort =>
          by_cases hCodomain : bodySort = codomain
          · simp [hBody, hCodomain] at hCheck
            subst bodySort
            subst sort
            rfl
          · simp [hBody, hCodomain] at hCheck

end Term

namespace Formula

/-- 宿主高阶公式的直接 Lean 解释。 -/
def eval (interpretation : Interpretation α) (bound : Nat → SimpleValue α) :
    Formula → Prop
  | .atom symbol arguments =>
      interpretation.predicate symbol.id
        (arguments.map fun term => term.eval interpretation bound)
  | .equal sort left right =>
      (left.eval interpretation bound).read interpretation.default sort =
        (right.eval interpretation bound).read interpretation.default sort
  | .falsum => False
  | .truth => True
  | .neg body => ¬ body.eval interpretation bound
  | .conj left right =>
      left.eval interpretation bound ∧ right.eval interpretation bound
  | .disj left right =>
      left.eval interpretation bound ∨ right.eval interpretation bound
  | .imp left right =>
      left.eval interpretation bound → right.eval interpretation bound
  | .iff left right =>
      left.eval interpretation bound ↔ right.eval interpretation bound
  | .forallE sort body =>
      ∀ value : SimpleType.denote α sort,
        body.eval interpretation
          (Term.pushBound bound ⟨sort, value⟩)
  | .existsE sort body =>
      ∃ value : SimpleType.denote α sort,
        body.eval interpretation
          (Term.pushBound bound ⟨sort, value⟩)

end Formula

namespace Interpretation

open CoreSyntax.NormalForm
open CoreSyntax.NormalForm.Semantics

/-- core 参数列表按宿主谓词声明的 simple type 逐项解包。 -/
def decodeArguments (interpretation : Interpretation α) :
    List SimpleType → List (Value α) → List (SimpleValue α)
  | [], _ => []
  | sort :: sorts, value :: values =>
      SimpleValue.ofCore interpretation.default sort value ::
        decodeArguments interpretation sorts values
  | sort :: sorts, [] =>
      ⟨sort, SimpleValue.default interpretation.default sort⟩ ::
        decodeArguments interpretation sorts []

/-- sort tags 对齐时，core 编码后的宿主参数可逐项无损解码。 -/
theorem decodeArguments_toCore (interpretation : Interpretation α) :
    ∀ (sorts : List SimpleType) (values : List (SimpleValue α)),
      values.map SimpleValue.sort = sorts →
        decodeArguments interpretation sorts (values.map SimpleValue.toCore) =
          values
  | [], [], _ => rfl
  | [], _ :: _, hSorts => by
      simp at hSorts
  | _ :: _, [], hSorts => by
      simp at hSorts
  | sort :: sorts, value :: values, hSorts => by
      simp only [List.map_cons, List.cons.injEq] at hSorts
      cases hSorts.1
      change
        SimpleValue.ofCore interpretation.default value.sort value.toCore ::
            decodeArguments interpretation sorts
              (values.map SimpleValue.toCore) =
          value :: values
      rw [SimpleValue.ofCore_toCore]
      rw [decodeArguments_toCore interpretation sorts values hSorts.2]

/-- 宿主解释给出 preprocessing 所需的真正 typed core 模型。 -/
noncomputable def coreModel (interpretation : Interpretation α) : Semantics.Model.{u} := {
  Carrier := Value α
  default := ⟨.object, interpretation.default⟩
  sortInterp := fun sort value => value.sort = sort
  sortNonempty := fun sort => ⟨⟨sort, coreDefault interpretation.default sort⟩, rfl⟩
  functionInterp := fun symbol _ =>
    (interpretation.function symbol.id).toCore.coerce
      interpretation.default symbol.outputSort
  predicateInterp := fun symbol arguments =>
    interpretation.predicate symbol.id <|
      decodeArguments interpretation
        (symbol.inputSorts.map SimpleType.ofCore) arguments
  applyInterp := Value.apply interpretation.default
  boolValue := fun value => ⟨.bool, ⟨value = true⟩⟩
  notValue := fun value =>
    ⟨.bool, ⟨¬ (value.read interpretation.default .bool).down⟩⟩
  andValue := fun left right =>
    ⟨.bool, ⟨(left.read interpretation.default .bool).down ∧
      (right.read interpretation.default .bool).down⟩⟩
  orValue := fun left right =>
    ⟨.bool, ⟨(left.read interpretation.default .bool).down ∨
      (right.read interpretation.default .bool).down⟩⟩
  impValue := fun left right =>
    ⟨.bool, ⟨(left.read interpretation.default .bool).down →
      (right.read interpretation.default .bool).down⟩⟩
  iffValue := fun left right =>
    ⟨.bool, ⟨(left.read interpretation.default .bool).down ↔
      (right.read interpretation.default .bool).down⟩⟩
  quoteValue := fun proposition => ⟨.bool, ⟨proposition⟩⟩
  lambdaValue := Value.lambda interpretation.default
  iteValue := fun condition thenValue elseValue =>
    @ite (Value α) condition (Classical.propDecidable condition)
      thenValue elseValue
  boolHolds := fun value => (value.read interpretation.default .bool).down
}

/-- canonical packed bound 环境。 -/
def coreEnv (interpretation : Interpretation α)
    (bound : Nat → SimpleValue α) :
    Semantics.Env interpretation.coreModel where
  boundVal := fun index => (bound index).toCore
  freeVal := fun sort _ => ⟨sort, coreDefault interpretation.default sort⟩

@[simp]
theorem coreEnv_push (interpretation : Interpretation α)
    (bound : Nat → SimpleValue α) (value : SimpleValue α) :
    (interpretation.coreEnv bound).push value.toCore =
      interpretation.coreEnv (Term.pushBound bound value) := by
  unfold coreEnv Semantics.Env.push
  congr
  funext index
  cases index <;> rfl

/-- canonical free assignment 保持全部 sort。 -/
theorem coreEnv_respectsFree (interpretation : Interpretation α)
    (bound : Nat → SimpleValue α) :
    Semantics.Env.RespectsFree (interpretation.coreEnv bound) := by
  intro sort id
  rfl

/-- Σ 简单类型模型满足 typed FOOL/lambda 合同。 -/
noncomputable def coreContract (interpretation : Interpretation α) :
    Semantics.FoolLambdaContract interpretation.coreModel where
  function_sort := by
    intro symbol arguments
    rfl
  apply_sort := by
    intro domain codomain functionValue argumentValue hFunction hArgument
    rcases functionValue with ⟨functionSort, function⟩
    simp only [coreModel] at hFunction
    subst functionSort
    rfl
  bool_sort := by
    intro value
    rfl
  not_sort := by
    intro value hValue
    rfl
  and_sort := by
    intro left right hLeft hRight
    rfl
  or_sort := by
    intro left right hLeft hRight
    rfl
  imp_sort := by
    intro left right hLeft hRight
    rfl
  iff_sort := by
    intro left right hLeft hRight
    rfl
  quote_sort := by
    intro proposition
    rfl
  lambda_sort := by
    intro domain codomain body hBody
    rfl
  lambda_congr := by
    intro domain codomain left right hPointwise
    apply Value.eq_of_value_eq
    funext value
    have h := hPointwise ⟨domain, value⟩ rfl
    exact congrArg (Value.read interpretation.default codomain) h
  ite_sort := by
    intro sort condition thenValue elseValue hThen hElse
    change thenValue.sort = sort at hThen
    change elseValue.sort = sort at hElse
    by_cases hCondition : condition
    · simpa [coreModel, hCondition] using hThen
    · simpa [coreModel, hCondition] using hElse
  bool_holds := by
    intro value
    simp [coreModel, Value.read]
  bool_extensionality := by
    intro left right hLeft hRight
    constructor
    · intro h
      cases h
      exact Iff.rfl
    · intro h
      rcases left with ⟨leftSort, left⟩
      rcases right with ⟨rightSort, right⟩
      simp only [coreModel] at hLeft hRight
      subst leftSort
      subst rightSort
      rcases left with ⟨left⟩
      rcases right with ⟨right⟩
      exact Value.eq_of_value_eq <| congrArg ULift.up (propext h)
  quote_eq_iff := by
    intro left right
    constructor
    · intro h
      have hRead :=
        congrArg (Value.read interpretation.default .bool) h
      simpa [coreModel] using hRead
    · intro h
      exact Value.eq_of_value_eq <| congrArg ULift.up (propext h)
  quote_holds := by
    intro proposition
    simp [coreModel]
  not_holds := by
    intro value
    rfl
  and_holds := by
    intro left right
    rfl
  or_holds := by
    intro left right
    rfl
  imp_holds := by
    intro left right
    rfl
  iff_holds := by
    intro left right
    rfl
  ite_value := by
    intro condition thenValue elseValue
    rfl
  beta := by
    intro domain codomain body argument hBody hArgument
    rcases argument with ⟨argumentSort, argument⟩
    simp only [coreModel] at hArgument
    subst argumentSort
    simpa [coreModel] using
      Value.apply_lambda interpretation.default domain codomain body
        (⟨domain, argument⟩ : Value α) rfl
        (fun value hValue => hBody value hValue)
  eta := by
    intro domain codomain functionValue hFunction
    rcases functionValue with ⟨functionSort, function⟩
    simp only [coreModel] at hFunction
    subst functionSort
    apply Value.eq_of_value_eq
    funext argument
    simp [coreModel, Value.apply, Value.read]
  function_extensionality := by
    intro domain codomain left right hLeft hRight
    constructor
    · intro h
      cases h
      intro value hValue
      rfl
    · intro h
      rcases left with ⟨leftSort, left⟩
      rcases right with ⟨rightSort, right⟩
      simp only [coreModel] at hLeft hRight
      subst leftSort
      subst rightSort
      apply Value.eq_of_value_eq
      funext argument
      have hAt := h ⟨domain, argument⟩ rfl
      have hRead :=
        congrArg (Value.read interpretation.default codomain) hAt
      simpa [coreModel, Value.apply] using hRead

/-- checker 与环境共同保证时，宿主项解释与 core 投影逐项一致。 -/
theorem termCore (interpretation : Interpretation α)
      (bound : Nat → SimpleValue α) (context : List SimpleType)
      (hBound : Term.BoundWellSorted context bound) :
      ∀ (term : Term) (sort : SimpleType),
        term.inferSortWith context = some sort →
          Semantics.Term.eval (interpretation.coreEnv bound) term.toCore =
            (term.eval interpretation bound).toCore
    | .bvar annotated index, sort, hCheck => by
        simp only [Term.inferSortWith] at hCheck
        split at hCheck
        next hLookup =>
          simp only [Option.some.injEq] at hCheck
          subst sort
          simp only [Term.toCore, Semantics.Term.eval, Term.eval]
          rw [SimpleValue.coerce_eq_self interpretation.default annotated
            (bound index) (hBound index annotated hLookup)]
          rfl
        next =>
          simp at hCheck
    | .symbol symbol, sort, hCheck => by
        simp only [Term.inferSortWith, Option.some.injEq] at hCheck
        subst sort
        simp only [Term.toCore, Semantics.Term.eval, Term.eval, coreModel]
        exact
          (SimpleValue.coerce_toCore interpretation.default symbol.sort
            (interpretation.function symbol.id)).symm
    | .apply function argument, sort, hCheck => by
        simp only [Term.inferSortWith] at hCheck
        cases hFunction : function.inferSortWith context with
        | none =>
            simp [hFunction] at hCheck
        | some functionSort =>
            cases hArgument : argument.inferSortWith context with
            | none =>
                simp [hFunction, hArgument] at hCheck
            | some argumentSort =>
                cases functionSort with
                | object =>
                    simp [hFunction, hArgument] at hCheck
                | arrow domain codomain =>
                    by_cases hDomain : argumentSort = domain
                    · simp [hFunction, hArgument, hDomain] at hCheck
                      subst argumentSort
                      subst sort
                      have hFunctionTag :=
                        Term.eval_sort_of_inferSortWith interpretation bound context
                          function (.arrow domain codomain) hFunction
                      have hArgumentTag :=
                        Term.eval_sort_of_inferSortWith interpretation bound context
                          argument domain hArgument
                      simp only [Term.toCore, Semantics.Term.eval, Term.eval,
                        coreModel]
                      have hCoreFunction :=
                        termCore interpretation bound context hBound function
                          (.arrow domain codomain) hFunction
                      have hCoreArgument :=
                        termCore interpretation bound context hBound argument
                          domain hArgument
                      calc
                        Value.apply interpretation.default
                            (Semantics.Term.eval
                              (interpretation.coreEnv bound) function.toCore)
                            (Semantics.Term.eval
                              (interpretation.coreEnv bound) argument.toCore) =
                            Value.apply interpretation.default
                              (function.eval interpretation bound).toCore
                              (Semantics.Term.eval
                                (interpretation.coreEnv bound) argument.toCore) := by
                              rw [hCoreFunction]
                        _ =
                            Value.apply interpretation.default
                              (function.eval interpretation bound).toCore
                              (argument.eval interpretation bound).toCore := by
                              rw [hCoreArgument]
                        _ =
                            (SimpleValue.apply interpretation.default
                              (function.eval interpretation bound)
                              (argument.eval interpretation bound)).toCore :=
                              (SimpleValue.apply_toCore interpretation.default
                                domain codomain
                                (function.eval interpretation bound)
                                (argument.eval interpretation bound)
                                hFunctionTag hArgumentTag).symm
                    · simp [hFunction, hArgument, hDomain] at hCheck
    | .lam domain codomain body, sort, hCheck => by
        simp only [Term.inferSortWith] at hCheck
        cases hBody : body.inferSortWith (domain :: context) with
        | none =>
            simp [hBody] at hCheck
        | some bodySort =>
            by_cases hCodomain : bodySort = codomain
            · simp [hBody, hCodomain] at hCheck
              subst bodySort
              subst sort
              simp only [Term.toCore, Semantics.Term.eval, Term.eval, coreModel]
              apply SimpleValue.lambda_toCore
              intro argument
              let hostArgument : SimpleValue α :=
                ⟨domain, coreToSimple domain argument⟩
              have hArgumentCore :
                  hostArgument.toCore =
                    (⟨domain.toCore, argument⟩ : Value α) := by
                apply Value.eq_of_value_eq
                exact simpleToCore_coreToSimple domain argument
              calc
                Semantics.Term.eval
                    ((interpretation.coreEnv bound).push
                      ⟨domain.toCore, argument⟩) body.toCore =
                    Semantics.Term.eval
                      ((interpretation.coreEnv bound).push hostArgument.toCore)
                      body.toCore := by rw [hArgumentCore]
                _ =
                    Semantics.Term.eval
                      (interpretation.coreEnv
                        (Term.pushBound bound hostArgument)) body.toCore := by
                    rw [coreEnv_push]
                _ =
                    (body.eval interpretation
                      (Term.pushBound bound hostArgument)).toCore :=
                    termCore interpretation
                      (Term.pushBound bound hostArgument) (domain :: context)
                      (Term.boundWellSorted_push hBound domain hostArgument rfl)
                      body codomain hBody
            · simp [hBody, hCodomain] at hCheck

/-- 参数列表的 core 解释逐项交换。 -/
theorem termListCore (interpretation : Interpretation α)
    (bound : Nat → SimpleValue α) (context : List SimpleType)
    (hBound : Term.BoundWellSorted context bound) :
    ∀ (terms : List Term) (sorts : List SimpleType),
      Term.inferSortListWith context terms = some sorts →
        (terms.map Term.toCore).map
            (Semantics.Term.eval (interpretation.coreEnv bound)) =
          (terms.map (Term.eval interpretation bound)).map SimpleValue.toCore
  | [], sorts, hCheck => by
      simp only [Term.inferSortListWith, Option.some.injEq] at hCheck
      subst sorts
      rfl
  | head :: tail, sorts, hCheck => by
      simp only [Term.inferSortListWith] at hCheck
      cases hHead : head.inferSortWith context with
      | none =>
          simp [hHead] at hCheck
      | some headSort =>
          cases hTail : Term.inferSortListWith context tail with
          | none =>
              simp [hHead, hTail] at hCheck
          | some tailSorts =>
              simp [hHead, hTail] at hCheck
              subst sorts
              simp only [List.map_cons]
              rw [termCore interpretation bound context hBound head headSort hHead]
              rw [termListCore interpretation bound context hBound tail tailSorts hTail]
              rfl

/-- checker 推断出的参数 sort 与直接宿主解释的 packed tags 一致。 -/
theorem termListEvalSorts (interpretation : Interpretation α)
    (bound : Nat → SimpleValue α) (context : List SimpleType) :
    ∀ (terms : List Term) (sorts : List SimpleType),
      Term.inferSortListWith context terms = some sorts →
        (terms.map (Term.eval interpretation bound)).map SimpleValue.sort = sorts
  | [], sorts, hCheck => by
      simp only [Term.inferSortListWith, Option.some.injEq] at hCheck
      subst sorts
      rfl
  | head :: tail, sorts, hCheck => by
      simp only [Term.inferSortListWith] at hCheck
      cases hHead : head.inferSortWith context with
      | none =>
          simp [hHead] at hCheck
      | some headSort =>
          cases hTail : Term.inferSortListWith context tail with
          | none =>
              simp [hHead, hTail] at hCheck
          | some tailSorts =>
              simp [hHead, hTail] at hCheck
              subst sorts
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨
                Term.eval_sort_of_inferSortWith interpretation bound context
                  head headSort hHead,
                termListEvalSorts interpretation bound context tail tailSorts hTail⟩

/-- 宿主公式解释与其 core 投影在同一 typed binder 上下文中一致。 -/
theorem formulaCore (interpretation : Interpretation α)
    (bound : Nat → SimpleValue α) (context : List SimpleType)
    (hBound : Term.BoundWellSorted context bound) (formula : Formula)
    (hCheck : formula.checkWith context = true) :
    Semantics.Formula.Satisfies
        (interpretation.coreEnv bound) formula.toCore ↔
      formula.eval interpretation bound := by
  induction formula generalizing context bound with
  | atom symbol arguments =>
      have hSorts :
          Term.inferSortListWith context arguments = some symbol.domain := by
        simpa [Formula.checkWith] using hCheck
      simp only [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval, coreModel,
        Formula.predicateToCore]
      have hDomains :
          (symbol.domain.map SimpleType.toCore).map SimpleType.ofCore =
            symbol.domain := by
        simp [List.map_map, Function.comp_def]
      have hCoreTerms :
          (arguments.map Term.toCore).map
              (Semantics.Term.eval (interpretation.coreEnv bound)) =
            (arguments.map (Term.eval interpretation bound)).map
              SimpleValue.toCore :=
        termListCore interpretation bound context hBound
          arguments symbol.domain hSorts
      have hDecoded :
          interpretation.decodeArguments symbol.domain
              ((arguments.map Term.toCore).map
                (Semantics.Term.eval (interpretation.coreEnv bound))) =
            arguments.map (Term.eval interpretation bound) := by
        calc
          _ =
              interpretation.decodeArguments symbol.domain
                ((arguments.map (Term.eval interpretation bound)).map
                  SimpleValue.toCore) :=
            congrArg (interpretation.decodeArguments symbol.domain) hCoreTerms
          _ = _ :=
            decodeArguments_toCore interpretation symbol.domain
              (arguments.map (Term.eval interpretation bound))
              (termListEvalSorts interpretation bound context
                arguments symbol.domain hSorts)
      have hDecodedSource :
          interpretation.decodeArguments
              ((symbol.domain.map SimpleType.toCore).map SimpleType.ofCore)
              ((arguments.map Term.toCore).map
                (Semantics.Term.eval (interpretation.coreEnv bound))) =
            arguments.map (Term.eval interpretation bound) := by
        calc
          _ =
              interpretation.decodeArguments symbol.domain
                ((arguments.map Term.toCore).map
                  (Semantics.Term.eval (interpretation.coreEnv bound))) :=
            congrArg
              (fun sorts =>
                interpretation.decodeArguments sorts
                  ((arguments.map Term.toCore).map
                    (Semantics.Term.eval (interpretation.coreEnv bound))))
              hDomains
          _ = _ := hDecoded
      exact hDecodedSource ▸ Iff.rfl
  | equal sort left right =>
      have hChecks :
          left.inferSortWith context = some sort ∧
            right.inferSortWith context = some sort := by
        simpa [Formula.checkWith, Bool.and_eq_true_iff] using hCheck
      have hLeftCore :=
        termCore interpretation bound context hBound left sort hChecks.1
      have hRightCore :=
        termCore interpretation bound context hBound right sort hChecks.2
      have hLeftTag :=
        Term.eval_sort_of_inferSortWith interpretation bound context
          left sort hChecks.1
      have hRightTag :=
        Term.eval_sort_of_inferSortWith interpretation bound context
          right sort hChecks.2
      have hLeftCoreTag :
          (left.eval interpretation bound).toCore.sort = sort.toCore := by
        change (left.eval interpretation bound).sort.toCore = sort.toCore
        exact congrArg SimpleType.toCore hLeftTag
      have hRightCoreTag :
          (right.eval interpretation bound).toCore.sort = sort.toCore := by
        change (right.eval interpretation bound).sort.toCore = sort.toCore
        exact congrArg SimpleType.toCore hRightTag
      simp only [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval]
      rw [hLeftCore, hRightCore]
      refine (Value.eq_iff_read_eq interpretation.default sort.toCore _ _
        hLeftCoreTag hRightCoreTag).trans ?_
      rw [← SimpleValue.read_toCore interpretation.default sort
        (left.eval interpretation bound)]
      rw [← SimpleValue.read_toCore interpretation.default sort
        (right.eval interpretation bound)]
      constructor
      · intro h
        exact simpleToCore_injective sort h
      · intro h
        exact congrArg (simpleToCore sort) h
  | falsum =>
      simp [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval]
  | truth =>
      simp [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval]
  | neg body ih =>
      simpa [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval] using
          not_congr (ih bound context hBound hCheck)
  | conj left right ihLeft ihRight =>
      have hFields : left.checkWith context ∧ right.checkWith context := by
        simpa [Formula.checkWith, Bool.and_eq_true_iff] using hCheck
      simpa [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval] using
          and_congr
            (ihLeft bound context hBound hFields.1)
            (ihRight bound context hBound hFields.2)
  | disj left right ihLeft ihRight =>
      have hFields : left.checkWith context ∧ right.checkWith context := by
        simpa [Formula.checkWith, Bool.and_eq_true_iff] using hCheck
      simpa [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval] using
          or_congr
            (ihLeft bound context hBound hFields.1)
            (ihRight bound context hBound hFields.2)
  | imp left right ihLeft ihRight =>
      have hFields : left.checkWith context ∧ right.checkWith context := by
        simpa [Formula.checkWith, Bool.and_eq_true_iff] using hCheck
      simpa [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval] using
          imp_congr
            (ihLeft bound context hBound hFields.1)
            (ihRight bound context hBound hFields.2)
  | iff left right ihLeft ihRight =>
      have hFields : left.checkWith context ∧ right.checkWith context := by
        simpa [Formula.checkWith, Bool.and_eq_true_iff] using hCheck
      simpa [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval] using
          iff_congr
            (ihLeft bound context hBound hFields.1)
            (ihRight bound context hBound hFields.2)
  | forallE sort body ih =>
      simp only [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval, coreModel]
      constructor
      · intro h value
        let hostValue : SimpleValue α := ⟨sort, value⟩
        have hBodyCore := h hostValue.toCore rfl
        have hEnv :
            (interpretation.coreEnv bound).push hostValue.toCore =
              interpretation.coreEnv (Term.pushBound bound hostValue) :=
          coreEnv_push interpretation bound hostValue
        have hBodyCore' :
            Semantics.Formula.Satisfies
              (interpretation.coreEnv
                (Term.pushBound bound hostValue)) body.toCore :=
          Eq.mp
            (congrArg
              (fun env => Semantics.Formula.Satisfies env body.toCore) hEnv)
            hBodyCore
        exact
          (ih (Term.pushBound bound hostValue) (sort :: context)
            (Term.boundWellSorted_push hBound sort hostValue rfl) hCheck).mp
            hBodyCore'
      · intro h value hValue
        rcases value with ⟨valueSort, value⟩
        change valueSort = sort.toCore at hValue
        subst valueSort
        let hostValue : SimpleValue α :=
          ⟨sort, coreToSimple sort value⟩
        have hValueCore :
            hostValue.toCore = (⟨sort.toCore, value⟩ : Value α) := by
          apply Value.eq_of_value_eq
          exact simpleToCore_coreToSimple sort value
        have hBodyCore :=
          (ih (Term.pushBound bound hostValue) (sort :: context)
            (Term.boundWellSorted_push hBound sort hostValue rfl) hCheck).mpr
            (h (coreToSimple sort value))
        have hEnv :
            (interpretation.coreEnv bound).push hostValue.toCore =
              interpretation.coreEnv (Term.pushBound bound hostValue) :=
          coreEnv_push interpretation bound hostValue
        have hBodyCore' :
            Semantics.Formula.Satisfies
              ((interpretation.coreEnv bound).push hostValue.toCore)
              body.toCore :=
          Eq.mpr
            (congrArg
              (fun env => Semantics.Formula.Satisfies env body.toCore) hEnv)
            hBodyCore
        have hEnvValue :
            (interpretation.coreEnv bound).push hostValue.toCore =
              (interpretation.coreEnv bound).push
                (⟨sort.toCore, value⟩ : Value α) :=
          congrArg (interpretation.coreEnv bound).push hValueCore
        exact Eq.mp
          (congrArg
            (fun env => Semantics.Formula.Satisfies env body.toCore) hEnvValue)
          hBodyCore'
  | existsE sort body ih =>
      simp only [Formula.toCore, Semantics.Formula.Satisfies,
        Semantics.Formula.eval, Formula.eval, coreModel]
      constructor
      · rintro ⟨value, hValue, hBodyCore⟩
        rcases value with ⟨valueSort, value⟩
        change valueSort = sort.toCore at hValue
        subst valueSort
        let hostValue : SimpleValue α :=
          ⟨sort, coreToSimple sort value⟩
        have hValueCore :
            hostValue.toCore = (⟨sort.toCore, value⟩ : Value α) := by
          apply Value.eq_of_value_eq
          exact simpleToCore_coreToSimple sort value
        have hEnv :
            (interpretation.coreEnv bound).push hostValue.toCore =
              interpretation.coreEnv (Term.pushBound bound hostValue) :=
          coreEnv_push interpretation bound hostValue
        have hEnvValue :
            (interpretation.coreEnv bound).push
                (⟨sort.toCore, value⟩ : Value α) =
              (interpretation.coreEnv bound).push hostValue.toCore :=
          congrArg (interpretation.coreEnv bound).push hValueCore.symm
        have hBodyHostCore :
            Semantics.Formula.Satisfies
              ((interpretation.coreEnv bound).push hostValue.toCore)
              body.toCore :=
          Eq.mp
            (congrArg
              (fun env => Semantics.Formula.Satisfies env body.toCore)
              hEnvValue)
            hBodyCore
        have hBodyCore' :
            Semantics.Formula.Satisfies
              (interpretation.coreEnv
                (Term.pushBound bound hostValue)) body.toCore :=
          Eq.mp
            (congrArg
              (fun env => Semantics.Formula.Satisfies env body.toCore) hEnv)
            hBodyHostCore
        exact ⟨coreToSimple sort value,
          (ih (Term.pushBound bound hostValue) (sort :: context)
            (Term.boundWellSorted_push hBound sort hostValue rfl) hCheck).mp
            hBodyCore'⟩
      · rintro ⟨value, hBody⟩
        let hostValue : SimpleValue α := ⟨sort, value⟩
        refine ⟨hostValue.toCore, rfl, ?_⟩
        have hEnv :
            (interpretation.coreEnv bound).push hostValue.toCore =
              interpretation.coreEnv (Term.pushBound bound hostValue) :=
          coreEnv_push interpretation bound hostValue
        have hBodyCore :
            Semantics.Formula.Satisfies
              (interpretation.coreEnv
                (Term.pushBound bound hostValue)) body.toCore :=
          (ih (Term.pushBound bound hostValue) (sort :: context)
            (Term.boundWellSorted_push hBound sort hostValue rfl) hCheck).mpr
            hBody
        exact Eq.mpr
          (congrArg
            (fun env => Semantics.Formula.Satisfies env body.toCore) hEnv)
          hBodyCore

end Interpretation

/-! ## Proof-carrying checked 宿主输入与原生 HO provider -/

/-- 元层重化后钉回原 Lean 命题的 proof-carrying 高阶输入。 -/
structure CheckedInput (goal : Prop) where
  Domain : Type u
  interpretation : Interpretation Domain
  facts : HostProp.Facts
  premises : List Formula
  target : Formula
  problemChecked : Problem.check { premises := premises, target := target } = true
  premisesAligned :
    premises.map
        (Formula.eval interpretation fun _ =>
          ⟨.object, interpretation.default⟩) =
      facts.propositions
  targetAligned :
    Formula.eval interpretation
        (fun _ => ⟨.object, interpretation.default⟩) target =
      goal

namespace CheckedInput

/-- 闭公式使用的 canonical 宿主 binder 环境。 -/
def bound {goal : Prop} (input : CheckedInput.{u} goal) :
    Nat → SimpleValue input.Domain :=
  fun _ => ⟨.object, input.interpretation.default⟩

/-- 空 checker 上下文不要求 canonical 环境提供任何可达 binder。 -/
theorem boundWellSorted {goal : Prop} (input : CheckedInput.{u} goal) :
    Term.BoundWellSorted [] input.bound := by
  intro index sort hLookup
  simp at hLookup

/-- 对齐后的每个高阶前提都有原 Lean proof。 -/
theorem premiseHolds {goal : Prop} (input : CheckedInput.{u} goal)
    {formula : Formula} (hFormula : formula ∈ input.premises) :
    Formula.eval input.interpretation input.bound formula := by
  apply input.facts.holds
  rw [← input.premisesAligned]
  exact List.mem_map.mpr ⟨formula, hFormula, rfl⟩

/-- 对齐后的高阶目标解释可以回到原 Lean 目标。 -/
theorem goalOfTarget {goal : Prop} (input : CheckedInput.{u} goal)
    (hTarget : Formula.eval input.interpretation input.bound input.target) :
    goal := by
  rw [← input.targetAligned]
  exact hTarget

/-- 纯宿主高阶快照进入整问题 preprocessing source。 -/
def sourceProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.Problem := {
  premises := premises.map Formula.toCore
  target := target.toCore
}

/-- checked 宿主输入对应的唯一 core source problem。 -/
def sourceProblem {goal : Prop} (input : CheckedInput.{u} goal) :
    SourcePreprocessing.Problem :=
  sourceProblemOfSyntax input.premises input.target

/-- source problem 的闭合前提与目标都通过宿主简单类型 checker。 -/
theorem problemChecks {goal : Prop} (input : CheckedInput.{u} goal) :
    input.premises.all Formula.check = true ∧ input.target.check = true := by
  simpa [Problem.check] using input.problemChecked

/-- 原 Lean 目标为假时，proof-carrying 前提构造 canonical core refutation 模型。 -/
theorem sourceSatisfiedOfNotGoal {goal : Prop}
    (input : CheckedInput.{u} goal) (hGoal : ¬ goal) :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      (input.interpretation.coreEnv input.bound)
      input.sourceProblem.refutationSource := by
  unfold sourceProblem sourceProblemOfSyntax
  unfold SourcePreprocessing.Problem.refutationSource
  apply HostProp.CheckedInput.coreSatisfiesConjunctionList
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTarget
  · rcases List.mem_map.mp hPremise with ⟨source, hSource, rfl⟩
    have hSourceCheck : source.check = true :=
      (List.all_eq_true.mp input.problemChecks.1) source hSource
    exact
      (input.interpretation.formulaCore input.bound []
        input.boundWellSorted source hSourceCheck).mpr
        (input.premiseHolds hSource)
  · subst formula
    have hCoreTarget :
        ¬ CoreSyntax.NormalForm.Semantics.Formula.Satisfies
          (input.interpretation.coreEnv input.bound)
          input.target.toCore := by
      intro hTargetCore
      apply hGoal
      apply input.goalOfTarget
      exact
        (input.interpretation.formulaCore input.bound []
          input.boundWellSorted input.target input.problemChecks.2).mp
          hTargetCore
    simpa [CoreSyntax.NormalForm.Semantics.Formula.Satisfies,
      CoreSyntax.NormalForm.Semantics.Formula.eval] using hCoreTarget

/-- checked preprocessing 与最小 HO-DAG replay artifact 直接闭合宿主目标。 -/
theorem soundOfReplayArtifact {goal : Prop} (input : CheckedInput.{u} goal)
    (result : SourcePreprocessing.CheckedResult input.sourceProblem)
    (artifact : HORefutationProvider.CheckedReplayArtifact result.clauses) :
    goal := by
  apply Classical.byContradiction
  intro hGoal
  let base := input.interpretation.coreEnv input.bound
  rcases result.modelExtension input.interpretation.coreModel base with
    ⟨extension⟩
  have hSource :
      CoreSyntax.NormalForm.Semantics.Formula.Satisfies
        base result.checked.payload.source :=
    result.sourceSatisfied_of_refutation (input.sourceSatisfiedOfNotGoal hGoal)
  exact artifact.refutesCoreModel
    extension.target
    (extension.contract input.interpretation.coreContract)
    (extension.functionSort input.interpretation.coreContract)
    (extension.rebase base)
    (by
      intro targetEnv hFree hBound
      simpa [SourcePreprocessing.CheckedResult.clauses] using
        extension.clausesSatisfiedTarget
          input.interpretation.coreContract
          (input.interpretation.coreEnv_respectsFree input.bound) hSource
          targetEnv hFree hBound)

/-- 完整搜索 artifact 统一投影到最小 semantic replay。 -/
theorem soundOfArtifact {goal : Prop} (input : CheckedInput.{u} goal)
    (result : SourcePreprocessing.CheckedResult input.sourceProblem)
    (artifact : HORefutationProvider.CheckedArtifact result.clauses) :
    goal :=
  input.soundOfReplayArtifact result artifact.replay

/-- 独立纯语法 source 与 checked 输入对齐时，最小 HO replay 仍闭合原目标。 -/
theorem soundOfReplayArtifactFromProblem {goal : Prop}
    (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (hSource : sourceProblem = input.sourceProblem)
    (result : SourcePreprocessing.CheckedResult sourceProblem)
    (artifact : HORefutationProvider.CheckedReplayArtifact result.clauses) :
    goal := by
  subst sourceProblem
  exact input.soundOfReplayArtifact result artifact

/-- 独立纯语法 source 与 checked 输入对齐时，HO artifact 仍闭合原目标。 -/
theorem soundOfArtifactFromProblem {goal : Prop}
    (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (hSource : sourceProblem = input.sourceProblem)
    (result : SourcePreprocessing.CheckedResult sourceProblem)
    (artifact : HORefutationProvider.CheckedArtifact result.clauses) :
    goal := by
  subst sourceProblem
  exact input.soundOfArtifact result artifact

/-- 元层搜索只引用纯数据 preprocessing 与最小 HO replay artifact。 -/
def goalAttemptFromReplay {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (hSource : sourceProblem = input.sourceProblem)
    (result : SourcePreprocessing.CheckedResult sourceProblem)
    (artifact : HORefutationProvider.CheckedReplayArtifact result.clauses)
    (label : String := "native host higher-order") :
    ProveAutoRequest.GoalAttempt goal := {
  closed := true
  summary := label
  sound := by
    intro _
    exact input.soundOfReplayArtifactFromProblem
      sourceProblem hSource result artifact
}

/-- 默认 HO provider 的 proof-carrying replay 稳定入口。 -/
@[reducible] def defaultGoalAttemptFromReplay
    {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (hSource : sourceProblem = input.sourceProblem)
    (result : SourcePreprocessing.CheckedResult sourceProblem)
    (artifact : HORefutationProvider.CheckedReplayArtifact result.clauses) :
    ProveAutoRequest.GoalAttempt goal :=
  input.goalAttemptFromReplay sourceProblem hSource result artifact

/-- 纯语法 HO source 的 proof-free 闭合状态。 -/
def runClosed (sourceProblem : SourcePreprocessing.Problem)
    (settings : SourcePreprocessing.Settings := {})
    (config : SourcePreprocessing.HOAvatarConfig := {}) : Bool :=
  match SourcePreprocessing.runChecked sourceProblem settings with
  | .error _ => false
  | .ok result =>
      if hNative :
          HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
            result.clauses = true then
        match HORefutationProvider.run result.clauses hNative config with
        | .error _ => false
        | .ok _ => true
      else
        false

/-- 纯语法 HO source 的结构化运行摘要。 -/
def runSummary (sourceProblem : SourcePreprocessing.Problem)
    (settings : SourcePreprocessing.Settings := {})
    (config : SourcePreprocessing.HOAvatarConfig := {})
    (label : String := "native host higher-order") : String :=
  match SourcePreprocessing.runChecked sourceProblem settings with
  | .error diagnostic => diagnostic.label
  | .ok result =>
      if hNative :
          HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
            result.clauses = true then
        match HORefutationProvider.run result.clauses hNative config with
        | .error diagnostic => diagnostic.label
        | .ok _ => label
      else
        "native host higher-order preprocessing left the checked apply/lam fragment"

/-- proof-free closed 标记为真时，对应 checked HO artifact 闭合原宿主目标。 -/
theorem soundOfRunClosed {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (hSource : sourceProblem = input.sourceProblem)
    (settings : SourcePreprocessing.Settings := {})
    (config : SourcePreprocessing.HOAvatarConfig := {})
    (hClosed : runClosed sourceProblem settings config = true) :
    goal := by
  unfold runClosed at hClosed
  cases hResult : SourcePreprocessing.runChecked sourceProblem settings with
  | error diagnostic =>
      simp [hResult] at hClosed
  | ok result =>
      by_cases hNative :
          HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
            result.clauses = true
      · simp only [hResult, hNative, ↓reduceDIte] at hClosed
        cases hArtifact :
            HORefutationProvider.run result.clauses hNative config with
        | error diagnostic =>
            simp [hArtifact] at hClosed
        | ok artifact =>
            exact input.soundOfArtifactFromProblem
              sourceProblem hSource result artifact
      · simp [hResult, hNative] at hClosed

/-- 宿主高阶输入运行 checked preprocessing 与原生 HO-AVATAR/HODAG。 -/
def goalAttemptFromProblem {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (hSource : sourceProblem = input.sourceProblem)
    (settings : SourcePreprocessing.Settings := {})
    (config : SourcePreprocessing.HOAvatarConfig := {})
    (label : String := "native host higher-order") :
    ProveAutoRequest.GoalAttempt goal := {
  closed := runClosed sourceProblem settings config
  summary := runSummary sourceProblem settings config label
  sound := input.soundOfRunClosed sourceProblem hSource settings config
}

/-- checked 输入使用自身 source 快照运行原生 HO provider。 -/
def goalAttempt {goal : Prop} (input : CheckedInput.{u} goal)
    (settings : SourcePreprocessing.Settings := {})
    (config : SourcePreprocessing.HOAvatarConfig := {})
    (label : String := "native host higher-order") :
    ProveAutoRequest.GoalAttempt goal :=
  input.goalAttemptFromProblem input.sourceProblem rfl settings config label

/-- 元层 provider 使用默认 checked HO 配置的稳定入口。 -/
@[reducible] def defaultGoalAttemptFromProblem {goal : Prop}
    (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (hSource : sourceProblem = input.sourceProblem) :
    ProveAutoRequest.GoalAttempt goal :=
  input.goalAttemptFromProblem sourceProblem hSource

end CheckedInput

/-! ## Lean 元层重化 -/

open Lean Meta

initialize registerTraceClass `YesMetaZFC.proveAuto.hostHigherOrder

/-- 一个固定语法函数符号及其宿主 Lean 解释。 -/
structure FunctionBinding where
  symbol : FunctionSymbol
  expression : Expr
  deriving Inhabited

/-- 一个固定语法谓词符号及其宿主 Lean 解释。 -/
structure PredicateBinding where
  symbol : PredicateSymbol
  expression : Expr
  deriving Inhabited

/-- 下一层 checked bridge 消费的元层重化结果。 -/
structure ReifiedProblem where
  domain : Expr
  problem : Problem
  functions : Array FunctionBinding
  predicates : Array PredicateBinding

private structure BoundEntry where
  fvar : FVarId
  sort : SimpleType
  deriving Inhabited

private structure NativeReifyState where
  domain : Expr
  functions : Array FunctionBinding := #[]
  predicates : Array PredicateBinding := #[]
  bound : Array BoundEntry := #[]

private abbrev NativeReifyM := StateRefT NativeReifyState MetaM

private def withSimpleBinder {β : Type}
    (binderName : Name) (binderType : Expr) (sort : SimpleType)
    (action : Expr → NativeReifyM β) : NativeReifyM β := do
  let state ← get
  let (result, nextState) ←
    withLocalDeclD binderName binderType fun binder =>
      (action binder).run {
        state with
        bound := state.bound.push {
          fvar := binder.fvarId!
          sort := sort
        }
      }
  set { nextState with bound := state.bound }
  return result

private def rememberBaseDomain (candidate : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  let candidate ← instantiateMVars candidate
  match ← whnf (← inferType candidate) with
  | .sort _ => pure ()
  | type =>
      throwError
        "native host higher-order base domain is not a type: {type}"
  match ← get with
  | none =>
      set (some candidate)
  | some domain =>
      unless ← withTransparency .reducible <| isDefEq domain candidate do
        throwError
          "native host higher-order reification found heterogeneous base domains \
          {domain} and {candidate}"

private partial def discoverSimpleTypeBase (candidate : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  let candidate ← instantiateMVars candidate
  let reduced ← whnf candidate
  match reduced with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        throwError
          "native host higher-order proof arguments are not simple term domains"
      if body.hasLooseBVar 0 then
        throwError
          "native host higher-order dependent function types are unsupported: \
          {candidate}"
      discoverSimpleTypeBase domain
      discoverSimpleTypeBase body
  | .sort .zero =>
      throwError
        "native host higher-order proposition-valued functions are unsupported"
  | .sort _ =>
      throwError
        "native host higher-order type universes are not simple term domains"
  | _ =>
      rememberBaseDomain candidate

private partial def discoverFormulaDomain (expression : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isAppOfArity ``Not 1 then
    return ← discoverFormulaDomain expression.getAppArgs[0]!
  if expression.isAppOfArity ``And 2 ||
      expression.isAppOfArity ``Or 2 ||
      expression.isAppOfArity ``Iff 2 then
    for argument in expression.getAppArgs do
      discoverFormulaDomain argument
    return
  if expression.isAppOfArity ``Eq 3 then
    discoverSimpleTypeBase expression.getAppArgs[0]!
    return
  if expression.isAppOfArity ``Exists 2 then
    let domain := expression.getAppArgs[0]!
    discoverSimpleTypeBase domain
    let predicate ← whnf expression.getAppArgs[1]!
    match predicate with
    | .lam _ _ body _ =>
        discoverFormulaDomain body
    | _ =>
        return
    return
  match expression with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError
            "native host higher-order dependent proposition binders are unsupported"
        discoverFormulaDomain domain
        discoverFormulaDomain body
      else
        discoverSimpleTypeBase domain
        discoverFormulaDomain body
  | .letE _ _ value body _ =>
      discoverFormulaDomain (body.instantiate1 value)
  | _ =>
      return

private def discoverSharedDomain? (expressions : Array Expr) :
    MetaM (Option Expr) := do
  let (_, domain?) ← (expressions.forM discoverFormulaDomain).run none
  return domain?

private partial def reifySimpleType (candidate : Expr) :
    NativeReifyM SimpleType := do
  let candidate ← instantiateMVars candidate
  let base := (← get).domain
  if ← withTransparency .reducible <| isDefEq candidate base then
    return .object
  let reduced ← whnf candidate
  match reduced with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        throwError
          "native host higher-order proof arguments are not simple term domains"
      if body.hasLooseBVar 0 then
        throwError
          "native host higher-order dependent function types are unsupported: \
          {candidate}"
      return .arrow (← reifySimpleType domain) (← reifySimpleType body)
  | .sort .zero =>
      throwError
        "native host higher-order proposition-valued functions are unsupported"
  | _ =>
      throwError
        "native host higher-order type is outside the shared simple domain: \
        {candidate}"

private def reifySimpleType? (candidate : Expr) :
    NativeReifyM (Option SimpleType) := do
  try
    return some (← reifySimpleType candidate)
  catch _ =>
    return none

private def capturesSimpleBound (expression : Expr) : NativeReifyM Bool := do
  let state ← get
  let (_, freeVariables) ← expression.collectFVars.run {}
  return state.bound.any fun entry =>
    freeVariables.fvarIds.contains entry.fvar

private def currentContext : NativeReifyM (List SimpleType) := do
  return (← get).bound.toList.reverse.map BoundEntry.sort

private def internFunction (expression : Expr) (sort : SimpleType) :
    NativeReifyM FunctionSymbol := do
  let state ← get
  if let some index := state.functions.findIdx? fun binding =>
      binding.symbol.sort == sort && binding.expression == expression then
    return state.functions[index]!.symbol
  let symbol : FunctionSymbol := {
    id := state.functions.size
    sort := sort
  }
  set {
    state with
    functions := state.functions.push { symbol, expression }
  }
  return symbol

private def internPredicate (expression : Expr) (domain : List SimpleType) :
    NativeReifyM PredicateSymbol := do
  let state ← get
  if let some index := state.predicates.findIdx? fun binding =>
      binding.symbol.domain == domain && binding.expression == expression then
    return state.predicates[index]!.symbol
  let symbol : PredicateSymbol := {
    id := state.predicates.size
    domain := domain
  }
  set {
    state with
    predicates := state.predicates.push { symbol, expression }
  }
  return symbol

private def splitSimpleSuffix (expression : Expr) :
    NativeReifyM (Expr × Array Expr) := do
  let arguments := expression.getAppArgs
  let mut split := arguments.size
  while split > 0 do
    let argumentType ← instantiateMVars (← inferType arguments[split - 1]!)
    if (← reifySimpleType? argumentType).isSome then
      split := split - 1
    else
      break
  let mut head := expression.getAppFn
  for index in [0 : split] do
    head := mkApp head arguments[index]!
  return (head, arguments.extract split arguments.size)

private def ensureTermSort (term : Term) (expected : SimpleType) :
    NativeReifyM Unit := do
  let context ← currentContext
  unless term.inferSortWith context = some expected do
    throwError
      "internal native host higher-order term lost simple type alignment"

private partial def reifyTerm (expression : Expr) : NativeReifyM Term := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  let expected ← reifySimpleType (← inferType expression)
  match expression with
  | .bvar _ =>
      throwError
        "unexpected loose binder during native host higher-order reification"
  | .fvar fvar =>
      let state ← get
      if let some position := state.bound.findIdx? fun entry =>
          entry.fvar == fvar then
        let entry := state.bound[position]!
        unless entry.sort = expected do
          throwError
            "native host higher-order bound variable changed simple type"
        return .bvar entry.sort (state.bound.size - position - 1)
      if ← capturesSimpleBound expression then
        throwError
          "native host higher-order symbol captures a simple bound variable"
      return .symbol (← internFunction expression expected)
  | .lam name binderDomain body _ =>
      let .arrow expectedDomain expectedCodomain := expected
        | throwError
            "native host higher-order lambda does not have a function type"
      let actualDomain ← reifySimpleType binderDomain
      unless actualDomain = expectedDomain do
        throwError
          "native host higher-order lambda binder changed simple type"
      let term ← withSimpleBinder name binderDomain actualDomain fun binder =>
        do
          let term ← reifyTerm (body.instantiate1 binder)
          ensureTermSort term expectedCodomain
          return term
      return .lam actualDomain expectedCodomain term
  | .letE _ _ value body _ =>
      reifyTerm (body.instantiate1 value)
  | _ =>
      let (head, arguments) ← splitSimpleSuffix expression
      if arguments.isEmpty then
        if ← capturesSimpleBound expression then
          throwError
            "native host higher-order symbol captures a simple bound variable"
        return .symbol (← internFunction expression expected)
      let mut term ← reifyTerm head
      for argument in arguments do
        term := .apply term (← reifyTerm argument)
      ensureTermSort term expected
      return term

private partial def reifyFormula (expression : Expr) :
    NativeReifyM Formula := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isConstOf ``False then
    return .falsum
  if expression.isConstOf ``True then
    return .truth
  if expression.isAppOfArity ``Not 1 then
    return .neg (← reifyFormula expression.getAppArgs[0]!)
  if expression.isAppOfArity ``And 2 then
    return .conj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Or 2 then
    return .disj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Iff 2 then
    return .iff
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Eq 3 then
    let sort ← reifySimpleType expression.getAppArgs[0]!
    return .equal sort
      (← reifyTerm expression.getAppArgs[1]!)
      (← reifyTerm expression.getAppArgs[2]!)
  if expression.isAppOfArity ``Exists 2 then
    let domain := expression.getAppArgs[0]!
    let sort ← reifySimpleType domain
    let predicate := expression.getAppArgs[1]!
    let reduced ← whnf predicate
    let body ←
      match reduced with
      | .lam name binderDomain body _ => do
          let binderSort ← reifySimpleType binderDomain
          unless binderSort = sort do
            throwError
              "native host higher-order existential binder changed simple type"
          withSimpleBinder name binderDomain sort fun binder =>
            reifyFormula (body.instantiate1 binder)
      | _ =>
          withSimpleBinder `witness domain sort fun binder =>
            reifyFormula (mkApp predicate binder)
    return .existsE sort body
  match expression with
  | .forallE name domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError
            "native host higher-order dependent proposition binders are unsupported"
        return .imp (← reifyFormula domain) (← reifyFormula body)
      let sort ← reifySimpleType domain
      return .forallE sort <|
        ← withSimpleBinder name domain sort fun binder =>
          reifyFormula (body.instantiate1 binder)
  | .letE _ _ value body _ =>
      reifyFormula (body.instantiate1 value)
  | _ =>
      unless ← isProp expression do
        throwError
          "native host higher-order formula expected a proposition"
      let (head, arguments) ← splitSimpleSuffix expression
      if ← capturesSimpleBound head then
        throwError
          "native host higher-order predicate captures a simple bound variable"
      let mut terms := #[]
      let mut domain := #[]
      for argument in arguments do
        let sort ← reifySimpleType (← inferType argument)
        terms := terms.push (← reifyTerm argument)
        domain := domain.push sort
      let symbol ← internPredicate head domain.toList
      return .atom symbol terms.toList

private def reifyProblemFromTypes
    (goal : Expr) (premiseTypes : Array Expr) :
    MetaM ReifiedProblem := do
  let expressions := premiseTypes.push goal
  let some domain ← discoverSharedDomain? expressions
    | throwError
        "native host higher-order reification found no shared simple object domain"
  let ((premises, target), state) ←
    (do
      let premises ← premiseTypes.toList.mapM reifyFormula
      let target ← reifyFormula goal
      return (premises, target)).run { domain := domain }
  let problem : Problem := { premises, target }
  unless problem.check do
    throwError
      "internal native host higher-order snapshot failed its simple type checker"
  trace[YesMetaZFC.proveAuto.hostHigherOrder]
    "domain={domain}; functions={state.functions.size}; \
    predicates={state.predicates.size}; premises={premises.length}; \
    higherOrder={problem.hasHigherOrder}"
  return {
    domain := domain
    problem := problem
    functions := state.functions
    predicates := state.predicates
  }

/--
把当前宿主目标与 proof 类型重化为固定 `Type 0` 快照。

此函数只建立语法与宿主符号表；下一层 checked bridge 负责构造模型解释和 soundness。
-/
def reifyProblem (goal : Expr) (proofs : Array Expr) :
    MetaM ReifiedProblem := do
  let premiseTypes ← proofs.mapM fun proof => do
    instantiateMVars (← inferType proof)
  reifyProblemFromTypes goal premiseTypes

/-- 保留明确拒绝消息的元层重化结果。 -/
def reifyProblemResult (goal : Expr) (proofs : Array Expr) :
    MetaM (Except MessageData ReifiedProblem) := do
  try
    return .ok (← reifyProblem goal proofs)
  catch error =>
    return .error error.toMessageData

/-- provider 探测使用的安静入口；拒绝原因写入专用 trace。 -/
def reifyProblem? (goal : Expr) (proofs : Array Expr) :
    MetaM (Option ReifiedProblem) := do
  match ← reifyProblemResult goal proofs with
  | .ok problem => return some problem
  | .error message =>
      trace[YesMetaZFC.proveAuto.hostHigherOrder]
        "reification rejected request: {message}"
      return none

private def domainLevel (domain : Expr) : MetaM Level := do
  match ← whnf (← inferType domain) with
  | .sort (.succ level) =>
      return level
  | type =>
      throwError "native host higher-order domain is not a type: {type}"

private def objectDefault? (domain : Expr) : MetaM (Option Expr) := do
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let localType ← instantiateMVars localDecl.type
    if ← withTransparency .reducible <| isDefEq localType domain then
      return some localDecl.toExpr
  let level ← domainLevel domain
  let sortLevel := Level.succ level
  let nonemptyType := mkApp (mkConst ``Nonempty [sortLevel]) domain
  try
    let nonempty ← synthInstance nonemptyType
    return some <|
      mkApp2 (mkConst ``Classical.choice [sortLevel]) domain nonempty
  catch _ =>
    return none

private def simpleValueExpr (domain : Expr) (level : Level)
    (sort : SimpleType) (value : Expr) : Expr :=
  mkAppN (mkConst ``SimpleValue.mk [level])
    #[domain, toExpr sort, value]

private def functionTableExpr (domain default : Expr)
    (bindings : Array FunctionBinding) : MetaM Expr := do
  let level ← domainLevel domain
  let simpleValueType := mkApp (mkConst ``SimpleValue [level]) domain
  let fallback := simpleValueExpr domain level .object default
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol => do
    let mut body := fallback
    let mut index := bindings.size
    while index > 0 do
      index := index - 1
      let some binding := bindings[index]?
        | throwError "internal native higher-order function table escaped bounds"
      let branch :=
        simpleValueExpr domain level binding.symbol.sort binding.expression
      let condition ← mkEq symbol (mkNatLit index)
      let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
      body := mkApp5 (mkConst ``ite [Level.succ level])
        simpleValueType condition decidable branch body
    mkLambdaFVars #[symbol] body

private partial def applyPredicateFromList (domain default : Expr)
    (resultType fallback head : Expr) (sorts : List SimpleType)
    (arguments : Expr) (values : Array Expr := #[]) : MetaM Expr := do
  match sorts with
  | [] =>
      let result := mkAppN head values
      let actualType ← instantiateMVars (← inferType result)
      unless ← withTransparency .reducible <| isDefEq actualType resultType do
        throwError
          "native host higher-order predicate {head} does not return Prop"
      return result
  | sort :: tailSorts =>
      let level ← domainLevel domain
      let simpleValueType := mkApp (mkConst ``SimpleValue [level]) domain
      let listType := mkApp (mkConst ``List [level]) simpleValueType
      let .sort resultUniverse ← whnf (← inferType resultType)
        | throwError "native host higher-order predicate result is not a type"
      let motive ←
        withLocalDeclD `items listType fun items =>
          mkLambdaFVars #[items] resultType
      let consBranch ←
        withLocalDeclD `value simpleValueType fun value =>
          withLocalDeclD `tail listType fun tail => do
            let decoded :=
              mkAppN (mkConst ``SimpleValue.read [level])
                #[domain, default, toExpr sort, value]
            let body ← applyPredicateFromList domain default
              resultType fallback head tailSorts tail (values.push decoded)
            mkLambdaFVars #[value, tail] body
      return mkAppN
        (mkConst ``List.casesOn [resultUniverse, level])
        #[simpleValueType, motive, arguments, fallback, consBranch]

private def predicateTableExpr (domain default : Expr)
    (bindings : Array PredicateBinding) : MetaM Expr := do
  let level ← domainLevel domain
  let simpleValueType := mkApp (mkConst ``SimpleValue [level]) domain
  let listType := mkApp (mkConst ``List [level]) simpleValueType
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol =>
    withLocalDeclD `arguments listType fun arguments => do
      let mut body := mkConst ``False
      let mut index := bindings.size
      while index > 0 do
        index := index - 1
        let some binding := bindings[index]?
          | throwError "internal native higher-order predicate table escaped bounds"
        let branch ← applyPredicateFromList domain default
          (mkSort Level.zero) (mkConst ``False)
          binding.expression binding.symbol.domain arguments
        let condition ← mkEq symbol (mkNatLit index)
        let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
        body := mkApp5 (mkConst ``ite [Level.succ Level.zero])
          (mkSort Level.zero) condition decidable branch body
      mkLambdaFVars #[symbol, arguments] body

private def defaultBoundExpr (domain default : Expr) : MetaM Expr := do
  let level ← domainLevel domain
  let fallback := simpleValueExpr domain level .object default
  withLocalDeclD `index (mkConst ``Nat) fun index =>
    mkLambdaFVars #[index] fallback

private structure CheckedInputExpr where
  expression : Expr
  sourceProblem : SourcePreprocessing.Problem

private def checkedInputExpr?
    (goal : Expr) (proofs premiseTypes : Array Expr) :
    MetaM (Option CheckedInputExpr) := do
  trace[YesMetaZFC.proveAuto.hostHigherOrder]
    "start checked native request: proofs={proofs.size}"
  let reified? ←
    try
      pure <| some (← reifyProblemFromTypes goal premiseTypes)
    catch error =>
      trace[YesMetaZFC.proveAuto.hostHigherOrder]
        "reification rejected request: {error.toMessageData}"
      pure none
  let some reified := reified?
    | return none
  unless reified.problem.hasHigherOrder do
    trace[YesMetaZFC.proveAuto.hostHigherOrder]
      "snapshot is first-order; leaving it to HostFirstOrder"
    return none
  let some default ← objectDefault? reified.domain
    | trace[YesMetaZFC.proveAuto.hostHigherOrder]
        "native domain has no local value or Nonempty instance: {reified.domain}"
      return none
  let level ← domainLevel reified.domain
  let functionTable ←
    functionTableExpr reified.domain default reified.functions
  let predicateTable ←
    predicateTableExpr reified.domain default reified.predicates
  let interpretation :=
    mkAppN (mkConst ``Interpretation.mk [level])
      #[reified.domain, default, functionTable, predicateTable]
  let facts ← HostProp.proofFactsExprWithTypes proofs premiseTypes
  let premiseList ←
    mkListLit (mkConst ``Formula) (reified.problem.premises.map toExpr)
  let targetFormula := toExpr reified.problem.target
  let problemExpr := toExpr reified.problem
  let problemCheck ← mkAppM ``Problem.check #[problemExpr]
  let problemChecked ← mkEqRefl (toExpr true)
  unless ← withTransparency .all <|
      isDefEq (← inferType problemChecked)
        (← mkEq problemCheck (toExpr true)) do
    throwError
      "internal HostHigherOrder syntax snapshot is not definitionally checked"
  let bound ← defaultBoundExpr reified.domain default
  let evalFunction :=
    mkApp3 (mkConst ``Formula.eval [level])
      reified.domain interpretation bound
  let premiseEvals ← mkAppM ``List.map #[evalFunction, premiseList]
  let factPropositions ← mkAppM ``HostProp.Facts.propositions #[facts]
  let targetEval :=
    mkApp4 (mkConst ``Formula.eval [level])
      reified.domain interpretation bound targetFormula
  let premisesAligned ← mkEqRefl premiseEvals
  unless ← withTransparency .all <|
      isDefEq (← inferType premisesAligned)
        (← mkEq premiseEvals factPropositions) do
    throwError
      "internal HostHigherOrder premise alignment is not definitional"
  let targetAligned ← mkEqRefl targetEval
  unless ← withTransparency .all <|
      isDefEq (← inferType targetAligned) (← mkEq targetEval goal) do
    throwError
      "internal HostHigherOrder target alignment is not definitional:\n\
      eval={indentExpr targetEval}\ngoal={indentExpr goal}"
  trace[YesMetaZFC.proveAuto.hostHigherOrder]
    "built checked input: functions={reified.functions.size}; \
    predicates={reified.predicates.size}; premises={reified.problem.premises.length}"
  return some {
    expression := mkAppN (mkConst ``CheckedInput.mk [level])
      #[goal, reified.domain, interpretation, facts, premiseList, targetFormula,
        problemChecked, premisesAligned, targetAligned]
    sourceProblem :=
      CheckedInput.sourceProblemOfSyntax
        reified.problem.premises reified.problem.target
  }

private def buildAttempt? (request : ProveAutoRequest.PreparedContextRequest) :
    MetaM (Option Expr) := do
  unless ← isProp request.goal do
    return none
  let proofs := request.facts
  let premiseTypes := request.terminal.factPropositions
  let some reified ← checkedInputExpr? request.goal proofs premiseTypes
    | return none
  let input := reified.expression
  let premiseList ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.premises #[input])
  let targetFormula ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.target #[input])
  let sourceProblem ←
    mkAppM ``CheckedInput.sourceProblemOfSyntax #[premiseList, targetFormula]
  let expectedSource ← mkAppM ``CheckedInput.sourceProblem #[input]
  unless ← isDefEq sourceProblem expectedSource do
    throwError "internal HostHigherOrder source snapshot lost syntax alignment"
  let hSource ← mkEqRefl sourceProblem
  let attempt ←
    match SourcePreprocessing.runChecked reified.sourceProblem with
    | Except.error error =>
        pure <| KernelReplay.failureAttemptExpr request.goal error.label
    | Except.ok result =>
        if hNative :
            HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
              result.clauses = true then
          match HORefutationProvider.run result.clauses hNative with
          | Except.error error =>
              pure <| KernelReplay.failureAttemptExpr request.goal error.label
          | Except.ok artifact => do
              let settingsExpr :=
                toExpr ({} : SourcePreprocessing.Settings)
              let payloadExpr ←
                KernelReplay.preprocessingPayloadExpr
                  (toExpr result.checked.payload.source)
                  (toExpr result.checked.payload.normalized) settingsExpr
                  result.checked.payload.normalizationTrace
                  result.checked.payload.initialNnf
              let payloadCheck ←
                mkAppM
                  ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check
                  #[payloadExpr]
              let hPayload ←
                KernelReplay.boolTrueProof
                  "higher-order preprocessing payload" payloadCheck
              let checkedExpr ←
                mkAppM ``Certificate.Checked.mk #[payloadExpr, hPayload]
              let payloadSource ←
                mkAppM
                  ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.source
                  #[payloadExpr]
              let refutationSource ←
                mkAppM ``SourcePreprocessing.Problem.refutationSource
                  #[sourceProblem]
              let hResultSource ←
                KernelReplay.equalityProof
                  "higher-order preprocessing source"
                  payloadSource refutationSource
              let antiPrenex ←
                mkAppM
                  ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.antiPrenex
                  #[payloadExpr]
              let antiPrenexResult ←
                mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.result
                  #[antiPrenex]
              let freeCheck ←
                mkAppM
                  ``CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
                  #[antiPrenexResult]
              let hFree ←
                KernelReplay.boolTrueProof
                  "higher-order preprocessing free closure" freeCheck
              let resultExpr ←
                mkAppM ``SourcePreprocessing.CheckedResult.mk
                  #[checkedExpr, hResultSource, hFree]
              let clausesExpr ←
                mkAppM ``SourcePreprocessing.CheckedResult.clauses
                  #[resultExpr]
              let nativeCheck ←
                mkAppM
                  ``HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
                  #[clausesExpr]
              let hNativeExpr ←
                KernelReplay.boolTrueProof
                  "higher-order native clause projection" nativeCheck
              let expectedCoreProblemExpr ←
                mkAppM
                  ``HOSearchMaterialization.CoreProjectionSoundness.coreProblem
                  #[clausesExpr]
              let coreProblem :=
                HOSearchMaterialization.CoreProjectionSoundness.coreProblem
                  result.clauses
              let coreProblemExpr := toExpr coreProblem
              let dagExpr :=
                HOSearchMaterialization.ReplayQuotation.dagExprWithProblem
                  coreProblemExpr artifact.checked.checked.dag
              let dagCheck ← mkAppM ``HODAGCertificate.DAG.check #[dagExpr]
              let hDagCheck ←
                KernelReplay.boolTrueProof
                  "higher-order DAG checker" dagCheck
              let checkedDag ←
                mkAppM ``HODAGCertificate.CheckedDAG.mk
                  #[dagExpr, hDagCheck]
              let checkedDagExpr ←
                mkAppM ``HODAGCertificate.CheckedDAG.dag #[checkedDag]
              let selectorRegistryCheck ←
                mkAppM
                  ``HODAGCertificate.DAG.avatarSelectorRegistryChecked
                  #[dagExpr]
              let hSelectorRegistry ←
                KernelReplay.boolTrueProof
                  "higher-order selector registry" selectorRegistryCheck
              let checkedAvatar ←
                mkAppM ``HODAGCertificate.CheckedAvatarDAG.mk
                  #[checkedDag, hSelectorRegistry]
              let witnessRegistryExpr ←
                mkAppM ``HOExtensionalWitnessRegistry.Registry.ofDAG
                  #[checkedDagExpr]
              let witnessRegistryCheck ←
                mkAppM ``HOExtensionalWitnessRegistry.Registry.check
                  #[checkedDagExpr, witnessRegistryExpr]
              let hWitnessRegistry ←
                KernelReplay.boolTrueProof
                  "higher-order extensional witness registry"
                  witnessRegistryCheck
              let hWitnessExtracted ← mkEqRefl witnessRegistryExpr
              let checkedWitnessRegistry ←
                mkAppM ``HOExtensionalWitnessRegistry.CheckedRegistry.mk
                  #[witnessRegistryExpr, hWitnessExtracted, hWitnessRegistry]
              let checkedProblem ←
                mkAppM ``HODAGCertificate.DAG.problem #[checkedDagExpr]
              let hCheckedProblem ←
                KernelReplay.equalityProof
                  "higher-order DAG problem alignment"
                  checkedProblem coreProblemExpr
              let hCoreProblem ←
                KernelReplay.equalityProof
                  "higher-order core problem quotation"
                  coreProblemExpr expectedCoreProblemExpr
              let hProblemEq ←
                mkAppM ``Eq.trans #[hCheckedProblem, hCoreProblem]
              let initialClauses ←
                mkAppM ``HODAGCertificate.Problem.initialClauses
                  #[coreProblemExpr]
              let initialClauseCheck ←
                mkAppOptM ``HODAGCertificate.Clause.check
                  #[some (mkConst ``HOSearchMaterialization.SearchSignature),
                    none]
              let initialClauseCount ←
                mkAppM ``Array.size #[initialClauses]
              let initialChecks ←
                mkAppM ``Array.all
                  #[initialClauses, initialClauseCheck, toExpr 0,
                    initialClauseCount]
              let hInitialChecks ←
                KernelReplay.boolTrueProof
                  "higher-order initial clause checks" initialChecks
              let hExpectedInitialChecks ←
                mkAppM ``HORefutationProvider.initialChecks_of_problem_eq
                  #[hCoreProblem, hInitialChecks]
              let supportedCheck ←
                mkAppM ``HODAGCertificate.DAG.avatarSoundnessSupported
                  #[dagExpr]
              let hSupported ←
                KernelReplay.boolTrueProof
                  "higher-order AVATAR soundness capability" supportedCheck
              let replayArtifact ←
                mkAppM ``HORefutationProvider.CheckedReplayArtifact.mk
                  #[checkedAvatar, checkedWitnessRegistry, hProblemEq,
                    hNativeExpr, hExpectedInitialChecks, hSupported]
              mkAppM ``CheckedInput.defaultGoalAttemptFromReplay
                #[input, sourceProblem, hSource, resultExpr, replayArtifact]
        else
          pure <| KernelReplay.failureAttemptExpr request.goal
            "native host higher-order preprocessing left the checked apply/lam fragment"
  let attempt ← instantiateMVars attempt
  let (_, freeVariables) ← attempt.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in freeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal HostHigherOrder request leaked a temporary free variable: \
        {freeVariable.name}"
  return some attempt

/-- 原生简单高阶宿主公式优先于单排序 FO 与命题骨架进入 checked provider。 -/
def contextProvider : ProveAutoRequest.ContextProvider where
  priority := 150
  requirement := .hostObjectSyntax
  build? := buildAttempt?

register_prove_auto_context_provider contextProvider

end HostHigherOrder
end Automation
end YesMetaZFC
