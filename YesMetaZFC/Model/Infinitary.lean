import YesMetaZFC.Model.FirstOrder.Semantics

/-!
# `L_{κ,κ}` 风格无穷一阶逻辑

无穷连接词和量词块使用小索引族；项、参数列和环境仍保持内在排序。自由变量与
bound 变量都由类型化上下文给出，不再依赖自然数编号或语义排序证明。
-/

namespace YesMetaZFC
namespace Logic
namespace Infinitary

universe u v w i x

structure Kappa where
  Small : Type i → Prop

namespace Kappa

def unrestricted : Kappa.{i} where
  Small := fun _ => True

end Kappa

/-- 按排序分族的变量上下文。 -/
abbrev Context (σ : Signature.{u, v, w}) := σ.SortSymbol → Type i

abbrev BoundContext := Context
abbrev FreeContext := Context

namespace Context

def empty {σ : Signature.{u, v, w}} : Context σ := fun _ => Empty

/-- 由一个带排序的小索引族扩展上下文。 -/
def extend {σ : Signature.{u, v, w}} (Γ : Context σ)
    {I : Type i} (sortOf : I → σ.SortSymbol) : Context σ :=
  fun sort => Sum (Γ sort) {index : I // sortOf index = sort}

end Context

namespace BoundContext

abbrev empty := @Context.empty
abbrev extend := @Context.extend

end BoundContext

mutual

/-- 内在排序的无穷逻辑项。 -/
inductive Term (σ : Signature.{u, v, w})
    (bound free : Context.{u, v, w, i} σ) :
    σ.SortSymbol → Type (max u v w i) where
  | bvar {sort : σ.SortSymbol} : bound sort → Term σ bound free sort
  | fvar {sort : σ.SortSymbol} : free sort → Term σ bound free sort
  | app (function : σ.FuncSymbol) :
      Arguments σ bound free (σ.funcDomain function) →
        Term σ bound free (σ.funcCodomain function)

/-- 由参数排序列表索引的异质参数列。 -/
inductive Arguments (σ : Signature.{u, v, w})
    (bound free : Context.{u, v, w, i} σ) :
    List σ.SortSymbol → Type (max u v w i) where
  | nil : Arguments σ bound free []
  | cons {sort : σ.SortSymbol} {sorts : List σ.SortSymbol} :
      Term σ bound free sort → Arguments σ bound free sorts →
        Arguments σ bound free (sort :: sorts)

end

/-- `L_{κ,κ}` 公式。 -/
inductive Formula (κ : Kappa.{i}) (σ : Signature.{u, v, w}) :
    Context.{u, v, w, i} σ → Context.{u, v, w, i} σ →
      Type (max u v w (i + 1)) where
  | falsum {bound free} : Formula κ σ bound free
  | truth {bound free} : Formula κ σ bound free
  | rel {bound free} (relation : σ.RelSymbol) :
      Arguments σ bound free (σ.relDomain relation) → Formula κ σ bound free
  | equal {bound free} {sort : σ.SortSymbol} :
      Term σ bound free sort → Term σ bound free sort → Formula κ σ bound free
  | neg {bound free} : Formula κ σ bound free → Formula κ σ bound free
  | conj {bound free} :
      Formula κ σ bound free → Formula κ σ bound free → Formula κ σ bound free
  | disj {bound free} :
      Formula κ σ bound free → Formula κ σ bound free → Formula κ σ bound free
  | imp {bound free} :
      Formula κ σ bound free → Formula κ σ bound free → Formula κ σ bound free
  | iff {bound free} :
      Formula κ σ bound free → Formula κ σ bound free → Formula κ σ bound free
  | iConj {bound free} {I : Type i} :
      κ.Small I → (I → Formula κ σ bound free) → Formula κ σ bound free
  | iDisj {bound free} {I : Type i} :
      κ.Small I → (I → Formula κ σ bound free) → Formula κ σ bound free
  | forallBlock {bound free} {I : Type i} :
      κ.Small I → (sortOf : I → σ.SortSymbol) →
        Formula κ σ (Context.extend bound sortOf) free →
          Formula κ σ bound free
  | existsBlock {bound free} {I : Type i} :
      κ.Small I → (sortOf : I → σ.SortSymbol) →
        Formula κ σ (Context.extend bound sortOf) free →
          Formula κ σ bound free

/-- 类型化无穷逻辑环境。 -/
structure Env {σ : Signature.{u, v, w}}
    (M : FirstOrder.Structure.{u, v, w, x} σ)
    (bound free : Context.{u, v, w, i} σ) where
  boundVal : ∀ {sort}, bound sort → M.Carrier sort
  freeVal : ∀ {sort}, free sort → M.Carrier sort

namespace Env

/-- 把一个带排序的小索引族压入 bound 环境。 -/
def pushBlock {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {bound free : Context.{u, v, w, i} σ}
    (env : Env M bound free) {I : Type i}
    (sortOf : I → σ.SortSymbol)
    (values : (index : I) → M.Carrier (sortOf index)) :
    Env M (Context.extend bound sortOf) free where
  boundVal := by
    intro sort entry
    cases entry with
    | inl previous => exact env.boundVal previous
    | inr tagged =>
        rcases tagged with ⟨index, rfl⟩
        exact values index
  freeVal := env.freeVal

end Env

mutual

def Term.eval {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {bound free : Context.{u, v, w, i} σ} (env : Env M bound free) :
    {sort : σ.SortSymbol} → Term σ bound free sort → M.Carrier sort
  | _, .bvar entry => env.boundVal entry
  | _, .fvar entry => env.freeVal entry
  | _, .app function arguments =>
      M.funcInterp function (Arguments.eval env arguments)

def Arguments.eval {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {bound free : Context.{u, v, w, i} σ} (env : Env M bound free) :
    {sorts : List σ.SortSymbol} → Arguments σ bound free sorts →
      FirstOrder.Values M.Carrier sorts
  | _, .nil => .nil
  | _, .cons term rest =>
      .cons (Term.eval env term) (Arguments.eval env rest)

end

namespace Formula

/-- `L_{κ,κ}` 的类型化 Tarski 满足关系。 -/
def satisfies {κ : Kappa.{i}} {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {bound free : Context.{u, v, w, i} σ} (env : Env M bound free) :
    Formula κ σ bound free → Prop
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
  | .iConj _ family => ∀ index, satisfies env (family index)
  | .iDisj _ family => ∃ index, satisfies env (family index)
  | .forallBlock _ sortOf body =>
      ∀ values, satisfies (env.pushBlock sortOf values) body
  | .existsBlock _ sortOf body =>
      ∃ values, satisfies (env.pushBlock sortOf values) body

end Formula
end Infinitary
end Logic
end YesMetaZFC
