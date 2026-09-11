import YesMetaZFC.Logic.Syntax
import YesMetaZFC.Model.Values

/-!
# 内在排序的一阶 Tarski 语义

模型的载体直接由对象语言排序索引，环境也直接解释类型化变量。因此：

* 项求值的结果排序由返回类型保证；
* 函数与关系只接受签名指定的异质参数列；
* 量词只遍历对应排序的宿主类型；
* 不再需要 `sortInterp`、参数排序证明或项求值良构定理。

这与内在语法核保持同一原则：不能由核心类型构造出的非法对象，不进入后续证明
义务。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x y

/-- 多排序 Tarski 结构；每个排序直接解释为一个宿主类型。 -/
structure Structure (σ : Signature.{u, v, w}) where
  Carrier : σ.SortSymbol → Type (max u x)
  nonempty : ∀ sort, Nonempty (Carrier sort)
  funcInterp : (function : σ.FuncSymbol) →
    Values Carrier (σ.funcDomain function) → Carrier (σ.funcCodomain function)
  relInterp : (relation : σ.RelSymbol) →
    Values Carrier (σ.relDomain relation) → Prop

/-- 对一个排序上下文中的全部变量赋值。 -/
abbrev Assignment {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) (context : SortContext σ) :=
  {sort : σ.SortSymbol} → Variable context sort → M.Carrier sort

namespace Assignment

/-- 空上下文的唯一赋值。 -/
def empty {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} : Assignment M [] :=
  fun entry => nomatch entry

/-- 在上下文头部加入一个值。 -/
def push {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {context : SortContext σ} {sort : σ.SortSymbol}
    (value : M.Carrier sort) (assignment : Assignment M context) :
    Assignment M (sort :: context) :=
  fun entry =>
    match entry with
    | .here => value
    | .there previous => assignment previous

@[simp] theorem push_here {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {context : SortContext σ} {sort : σ.SortSymbol}
    (value : M.Carrier sort) (assignment : Assignment M context) :
    push value assignment (.here : Variable (sort :: context) sort) = value :=
  rfl

@[simp] theorem push_there {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {context : SortContext σ} {introduced sort : σ.SortSymbol}
    (value : M.Carrier introduced) (assignment : Assignment M context)
    (entry : Variable context sort) :
    push value assignment (.there entry) = assignment entry :=
  rfl

end Assignment

/-- 分别解释 bound 与 free 上下文的类型化环境。 -/
structure Env {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ)
    (bound free : SortContext σ) where
  boundVal : Assignment M bound
  freeVal : Assignment M free

namespace Env

/-- 环境由 bound/free 两个赋值分量逐点外延确定。 -/
@[ext (iff := false)] theorem ext {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {left right : Env M bound free}
    (hBound : ∀ {sort} (entry : Variable bound sort),
      left.boundVal entry = right.boundVal entry)
    (hFree : ∀ {sort} (entry : Variable free sort),
      left.freeVal entry = right.freeVal entry) : left = right := by
  rw [Env.mk.injEq]
  constructor
  · funext sort entry
    exact hBound entry
  · funext sort entry
    exact hFree entry

/-- 空 bound/free 上下文的唯一环境。 -/
def empty {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} : Env M [] [] where
  boundVal := Assignment.empty
  freeVal := Assignment.empty

/-- 在 bound 上下文头部压入一个值。 -/
def pushBound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier sort) :
    Env M (sort :: bound) free where
  boundVal := Assignment.push value env.boundVal
  freeVal := env.freeVal

@[simp] theorem pushBound_bound_here {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier sort) :
    (env.pushBound value).boundVal
      (.here : Variable (sort :: bound) sort) = value :=
  rfl

@[simp] theorem pushBound_bound_there {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (entry : Variable bound sort) :
    (env.pushBound value).boundVal (.there entry) = env.boundVal entry :=
  rfl

@[simp] theorem pushBound_free {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (entry : Variable free sort) :
    (env.pushBound value).freeVal entry = env.freeVal entry :=
  rfl

end Env

mutual

/-- 内在排序项的解释；返回类型就是该项的语义排序。 -/
def Term.eval {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free) :
    {sort : σ.SortSymbol} → Term σ bound free sort → M.Carrier sort
  | _, .bvar entry => env.boundVal entry
  | _, .fvar entry => env.freeVal entry
  | _, .app function arguments =>
      M.funcInterp function (Arguments.eval env arguments)

/-- 异质参数列的逐项解释。 -/
def Arguments.eval {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free) :
    {sorts : List σ.SortSymbol} →
      Arguments σ bound free sorts → Values M.Carrier sorts
  | _, .nil => .nil
  | _, .cons term rest =>
      .cons (Term.eval env term) (Arguments.eval env rest)

end

namespace Formula

/-- 内在排序公式的满足关系。 -/
def satisfies {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free) :
    Formula σ bound free → Prop
  | .falsum => False
  | .truth => True
  | .rel relation arguments =>
      M.relInterp relation (Arguments.eval env arguments)
  | .equal left right => Term.eval env left = Term.eval env right
  | .neg body => ¬ satisfies env body
  | .conj left right => satisfies env left ∧ satisfies env right
  | .disj left right => satisfies env left ∨ satisfies env right
  | .imp left right => satisfies env left → satisfies env right
  | .iff left right => satisfies env left ↔ satisfies env right
  | .forallE _ body =>
      ∀ value, satisfies (env.pushBound value) body
  | .existsE _ body =>
      ∃ value, satisfies (env.pushBound value) body

/-- 有限合取的满足关系等价于逐个满足列表中的公式。 -/
theorem satisfies_conjunctionList_iff {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free)
    (formulas : List (Formula σ bound free)) :
    satisfies env (conjunctionList formulas) ↔
      ∀ formula ∈ formulas, satisfies env formula := by
  induction formulas with
  | nil =>
      simp [conjunctionList, satisfies]
  | cons formula rest ih =>
      cases rest with
      | nil =>
          simp [conjunctionList]
      | cons next tail =>
          simp [conjunctionList, satisfies, ih]

/-- 有限析取的满足关系等价于至少满足列表中的一个公式。 -/
theorem satisfies_disjunctionList_iff {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free)
    (formulas : List (Formula σ bound free)) :
    satisfies env (disjunctionList formulas) ↔
      ∃ formula ∈ formulas, satisfies env formula := by
  induction formulas with
  | nil =>
      simp [disjunctionList, satisfies]
  | cons formula rest ih =>
      cases rest with
      | nil =>
          simp [disjunctionList]
      | cons next tail =>
          simp [disjunctionList, satisfies, ih]

end Formula
end FirstOrder
end Logic
end YesMetaZFC
