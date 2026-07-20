import YesMetaZFC.Logic.Semantics

/-!
# `L_{κ,κ}` 风格无穷一阶逻辑

这一层采用上下文索引的 locally nameless 变体：自由变量仍用稳定编号，bound 变量
由局部 context 给出。这样 `< κ` 长量词块不需要把任意索引族编码成 `Nat`，也不会引入
捕获避免替换的额外负担。
-/

namespace YesMetaZFC
namespace Logic
namespace Infinitary

universe u v w i x

/-- `κ` 在 Lean 里作为“小索引族”谓词抽象出现；具体基数事实可在上层实例化。 -/
structure Kappa where
  Small : Type i → Prop

namespace Kappa

/-- 不限制索引大小的调试/语义档位。真正的 `L_{κ,κ}` 应替换成具体 smallness。 -/
def unrestricted : Kappa.{i} where
  Small := fun _ => True

end Kappa

abbrev FreeVarId := FirstOrder.FreeVarId

/-- 每个 sort 对应一族局部 bound 变量。 -/
abbrev BoundContext (σ : Signature.{u, v, w}) := σ.SortSymbol → Type i

namespace BoundContext

def empty {σ : Signature.{u, v, w}} : BoundContext σ :=
  fun _ => Empty

/-- 按一个小索引族扩展 bound context；每个索引携带自己的 sort。 -/
def extend {σ : Signature.{u, v, w}} (Γ : BoundContext σ)
    {I : Type i} (sortOf : I → σ.SortSymbol) : BoundContext σ :=
  fun sort => Sum (Γ sort) {idx : I // sortOf idx = sort}

end BoundContext

/-- 无穷逻辑项：bound 变量来自局部 context，free 变量来自稳定编号。 -/
inductive Term (σ : Signature.{u, v, w}) (Γ : BoundContext.{u, v, w, i} σ) where
  | bvar : (sort : σ.SortSymbol) → Γ sort → Term σ Γ
  | fvar : σ.SortSymbol → FreeVarId → Term σ Γ
  | app : σ.FuncSymbol → List (Term σ Γ) → Term σ Γ

/-- `L_{κ,κ}` 公式。无穷合取/析取和量词块都显式携带 `κ.Small` 证据。 -/
inductive Formula (κ : Kappa.{i}) (σ : Signature.{u, v, w}) :
    BoundContext.{u, v, w, i} σ → Type (max u v w (i + 1)) where
  | falsum {Γ : BoundContext σ} : Formula κ σ Γ
  | truth {Γ : BoundContext σ} : Formula κ σ Γ
  | rel {Γ : BoundContext σ} :
      σ.RelSymbol → List (Term σ Γ) → Formula κ σ Γ
  | equal {Γ : BoundContext σ} :
      Term σ Γ → Term σ Γ → Formula κ σ Γ
  | neg {Γ : BoundContext σ} :
      Formula κ σ Γ → Formula κ σ Γ
  | conj {Γ : BoundContext σ} :
      Formula κ σ Γ → Formula κ σ Γ → Formula κ σ Γ
  | disj {Γ : BoundContext σ} :
      Formula κ σ Γ → Formula κ σ Γ → Formula κ σ Γ
  | imp {Γ : BoundContext σ} :
      Formula κ σ Γ → Formula κ σ Γ → Formula κ σ Γ
  | iff {Γ : BoundContext σ} :
      Formula κ σ Γ → Formula κ σ Γ → Formula κ σ Γ
  | iConj {Γ : BoundContext σ} {I : Type i} :
      κ.Small I → (I → Formula κ σ Γ) → Formula κ σ Γ
  | iDisj {Γ : BoundContext σ} {I : Type i} :
      κ.Small I → (I → Formula κ σ Γ) → Formula κ σ Γ
  | forallBlock {Γ : BoundContext σ} {I : Type i} :
      κ.Small I → (sortOf : I → σ.SortSymbol) →
        Formula κ σ (BoundContext.extend Γ sortOf) → Formula κ σ Γ
  | existsBlock {Γ : BoundContext σ} {I : Type i} :
      κ.Small I → (sortOf : I → σ.SortSymbol) →
        Formula κ σ (BoundContext.extend Γ sortOf) → Formula κ σ Γ

/-- 上下文索引语义环境。 -/
structure Env {σ : Signature.{u, v, w}}
    (M : FirstOrder.Structure.{u, v, w, x} σ)
    (Γ : BoundContext.{u, v, w, i} σ) where
  boundVal : ∀ sort, Γ sort → M.Domain
  freeVal : σ.SortSymbol → FreeVarId → M.Domain
  boundSort : ∀ sort var, M.sortInterp sort (boundVal sort var)
  freeSort : ∀ sort id, M.sortInterp sort (freeVal sort id)

namespace Env

/-- 把一个 `< κ` 量词块压入环境。 -/
def pushBlock {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {Γ : BoundContext.{u, v, w, i} σ} (env : Env M Γ)
    {I : Type i} (sortOf : I → σ.SortSymbol)
    (values : I → M.Domain)
    (hValues : ∀ idx, M.sortInterp (sortOf idx) (values idx)) :
    Env M (BoundContext.extend Γ sortOf) where
  boundVal := by
    intro sort var
    cases var with
    | inl old => exact env.boundVal sort old
    | inr tagged => exact values tagged.1
  freeVal := env.freeVal
  boundSort := by
    intro sort var
    cases var with
    | inl old => exact env.boundSort sort old
    | inr tagged =>
        rcases tagged with ⟨idx, hSort⟩
        simpa [hSort] using hValues idx
  freeSort := env.freeSort

end Env

namespace Term

def eval {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {Γ : BoundContext.{u, v, w, i} σ} (env : Env M Γ) :
    Term σ Γ → M.Domain
  | bvar sort var => env.boundVal sort var
  | fvar sort id => env.freeVal sort id
  | app f args => M.funcInterp f (args.map (eval env))

end Term

namespace Formula

/-- `L_{κ,κ}` Tarski 满足关系。smallness 证据只限制语法形成，不影响语义递归。 -/
def satisfies {κ : Kappa.{i}} {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {Γ : BoundContext.{u, v, w, i} σ} (env : Env M Γ) :
    Formula κ σ Γ → Prop
  | falsum => False
  | truth => True
  | rel r args => M.relInterp r (args.map (Term.eval env))
  | equal left right => Term.eval env left = Term.eval env right
  | neg φ => ¬ satisfies env φ
  | conj φ ψ => satisfies env φ ∧ satisfies env ψ
  | disj φ ψ => satisfies env φ ∨ satisfies env ψ
  | imp φ ψ => satisfies env φ → satisfies env ψ
  | iff φ ψ => satisfies env φ ↔ satisfies env ψ
  | iConj _ family => ∀ idx, satisfies env (family idx)
  | iDisj _ family => ∃ idx, satisfies env (family idx)
  | forallBlock _ sortOf body =>
      ∀ values, ∀ hValues : ∀ idx, M.sortInterp (sortOf idx) (values idx),
        satisfies (env.pushBlock sortOf values hValues) body
  | existsBlock _ sortOf body =>
      ∃ values, ∃ hValues : ∀ idx, M.sortInterp (sortOf idx) (values idx),
        satisfies (env.pushBlock sortOf values hValues) body

end Formula

end Infinitary
end Logic
end YesMetaZFC
