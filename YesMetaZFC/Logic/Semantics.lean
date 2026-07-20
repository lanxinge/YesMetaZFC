import YesMetaZFC.Logic.Syntax

/-!
# Tarski 语义

当前语义采用单域模型加 sort 谓词。这样能保留多 sorted 语法，同时避免 dependent
carrier 在 replay 定理里制造大量 cast。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

/-- 参数值逐项满足对应 sort。 -/
def ArgsSatisfy {S : Type u} {α : Type x}
    (sortInterp : S → α → Prop) : List α → List S → Prop
  | [], [] => True
  | value :: values, sort :: sorts =>
      sortInterp sort value ∧ ArgsSatisfy sortInterp values sorts
  | _, _ => False

/-- 单域多 sorted Tarski 结构。 -/
structure Structure (σ : Signature.{u, v, w}) where
  Domain : Type x
  nonempty : Nonempty Domain
  sortInterp : σ.SortSymbol → Domain → Prop
  sortNonempty : ∀ sort, ∃ value, sortInterp sort value
  funcInterp : σ.FuncSymbol → List Domain → Domain
  funcSort :
    ∀ (f : σ.FuncSymbol) (args : List Domain),
      ArgsSatisfy sortInterp args (σ.funcDomain f) →
        sortInterp (σ.funcCodomain f) (funcInterp f args)
  relInterp : σ.RelSymbol → List Domain → Prop

namespace Structure

/-- 空 arity 的常量解释。 -/
def constInterp {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ)
    (f : σ.FuncSymbol) (h : σ.funcDomain f = []) : M.Domain :=
  by
    have _ := h
    exact M.funcInterp f []

end Structure

/-- 变量赋值。bound 变量和 free 变量都按 sort 编号。 -/
structure Env {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ) where
  boundVal : σ.SortSymbol → Nat → M.Domain
  freeVal : σ.SortSymbol → FreeVarId → M.Domain
  boundSort : ∀ sort idx, M.sortInterp sort (boundVal sort idx)
  freeSort : ∀ sort id, M.sortInterp sort (freeVal sort id)

namespace Env

/-- 在同 sort 的 bound stack 顶部压入一个值。 -/
def pushBound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (env : Env M)
    (sort : σ.SortSymbol) (value : M.Domain)
    (hValue : M.sortInterp sort value) : Env M where
  boundVal := fun target idx =>
    if target = sort then
      match idx with
      | 0 => value
      | Nat.succ prev => env.boundVal target prev
    else
      env.boundVal target idx
  freeVal := env.freeVal
  boundSort := by
    intro target idx
    by_cases h : target = sort
    · subst h
      cases idx with
      | zero =>
          simpa using hValue
      | succ prev =>
          simpa using env.boundSort target prev
    · simpa [h] using env.boundSort target idx
  freeSort := env.freeSort

end Env

namespace Term

/-- 项解释。sort 正确性由 `eval_sort_of_wellSorted` 连接到签名 arity。 -/
def eval {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) : Term σ → M.Domain
  | var (.bvar sort idx) => env.boundVal sort idx
  | var (.fvar sort id) => env.freeVal sort id
  | app f args => M.funcInterp f (args.map (eval env))

end Term

namespace Formula

/-- 公式满足关系。量词只遍历对应 sort 谓词下的对象。 -/
def satisfies {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (env : Env M) :
    Formula σ → Prop
  | falsum => False
  | truth => True
  | rel r args => M.relInterp r (args.map (Term.eval env))
  | equal left right => Term.eval env left = Term.eval env right
  | neg φ => ¬ satisfies env φ
  | conj φ ψ => satisfies env φ ∧ satisfies env ψ
  | disj φ ψ => satisfies env φ ∨ satisfies env ψ
  | imp φ ψ => satisfies env φ → satisfies env ψ
  | iff φ ψ => satisfies env φ ↔ satisfies env ψ
  | forallE sort body =>
      ∀ value, ∀ hValue : M.sortInterp sort value,
        satisfies (env.pushBound sort value hValue) body
  | existsE sort body =>
      ∃ value, ∃ hValue : M.sortInterp sort value,
        satisfies (env.pushBound sort value hValue) body

/-- 有限合取的满足关系等价于逐个满足列表中的公式。 -/
theorem satisfies_conjunctionList_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (env : Env M) (formulas : List (Formula σ)) :
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

end Formula

/- well-sorted 项解释和参数列表 sort 满足性一起归纳。 -/
mutual
  /-- well-sorted 项的解释落在对应 sort 里。 -/
  theorem Term.eval_sort_of_wellSorted {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} {env : Env M}
      {term : Term σ} {sort : σ.SortSymbol}
      (hTerm : TermWellSorted term sort) :
      M.sortInterp sort (Term.eval env term) := by
    cases hTerm with
    | bvar sort idx =>
        simpa [Term.eval] using env.boundSort sort idx
    | fvar sort id =>
        simpa [Term.eval] using env.freeSort sort id
    | app f hArgs =>
        simpa [Term.eval] using
          M.funcSort f _ (args_satisfy_of_wellSorted (env := env) hArgs)

  theorem args_satisfy_of_wellSorted {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} {env : Env M}
      {args : List (Term σ)} {sorts : List σ.SortSymbol}
      (hArgs : ArgsWellSorted args sorts) :
      ArgsSatisfy M.sortInterp (args.map (Term.eval env)) sorts := by
    cases hArgs with
    | nil =>
        simp [ArgsSatisfy]
    | cons hTerm hRest =>
        simp [ArgsSatisfy, Term.eval_sort_of_wellSorted hTerm,
          args_satisfy_of_wellSorted hRest]
end

end FirstOrder
end Logic
end YesMetaZFC
