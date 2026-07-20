import YesMetaZFC.Logic.Signature

/-!
# Sorted locally nameless 语法

这是新语义核的原始语法层。自由变量用稳定编号，约束变量用 de Bruijn index；
index 按 sort 分别计数，因此量词只会移动同 sort 的 bound stack。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

abbrev FreeVarId := Nat

/-- LN 变量：bound 变量带 sort 与 de Bruijn index，free 变量带 sort 与稳定编号。 -/
inductive Var (σ : Signature.{u, v, w}) where
  | bvar : σ.SortSymbol → Nat → Var σ
  | fvar : σ.SortSymbol → FreeVarId → Var σ

namespace Var

def sort {σ : Signature.{u, v, w}} : Var σ → σ.SortSymbol
  | bvar s _ => s
  | fvar s _ => s

end Var

/-- 一阶项。函数应用暂不把 arity 做进构造子，而交给 well-sorted 关系检查。 -/
inductive Term (σ : Signature.{u, v, w}) where
  | var : Var σ → Term σ
  | app : σ.FuncSymbol → List (Term σ) → Term σ

/-- 一阶公式。等词保留在核心内，后续 ATP/DAG 可以直接 replay 等词规则。 -/
inductive Formula (σ : Signature.{u, v, w}) where
  | falsum : Formula σ
  | truth : Formula σ
  | rel : σ.RelSymbol → List (Term σ) → Formula σ
  | equal : Term σ → Term σ → Formula σ
  | neg : Formula σ → Formula σ
  | conj : Formula σ → Formula σ → Formula σ
  | disj : Formula σ → Formula σ → Formula σ
  | imp : Formula σ → Formula σ → Formula σ
  | iff : Formula σ → Formula σ → Formula σ
  | forallE : σ.SortSymbol → Formula σ → Formula σ
  | existsE : σ.SortSymbol → Formula σ → Formula σ

/-- 一个 scope 记录每个 sort 当前可用的 bound 深度。 -/
abbrev Scope (σ : Signature.{u, v, w}) := σ.SortSymbol → Nat

namespace Scope

def empty {σ : Signature.{u, v, w}} : Scope σ :=
  fun _ => 0

def push {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (ctx : Scope σ) (s : σ.SortSymbol) : Scope σ :=
  fun t => if t = s then ctx t + 1 else ctx t

end Scope

/- 项和参数列表的 sort 正确性互相递归定义。 -/
mutual
  inductive TermWellSorted {σ : Signature.{u, v, w}} :
      Term σ → σ.SortSymbol → Prop where
    | bvar (s : σ.SortSymbol) (idx : Nat) :
        TermWellSorted (.var (.bvar s idx)) s
    | fvar (s : σ.SortSymbol) (id : FreeVarId) :
        TermWellSorted (.var (.fvar s id)) s
    | app (f : σ.FuncSymbol) {args : List (Term σ)}
        (hArgs : ArgsWellSorted args (σ.funcDomain f)) :
        TermWellSorted (.app f args) (σ.funcCodomain f)

  /-- 参数列表逐项匹配 arity sort。 -/
  inductive ArgsWellSorted {σ : Signature.{u, v, w}} :
      List (Term σ) → List σ.SortSymbol → Prop where
    | nil : ArgsWellSorted [] []
    | cons {term : Term σ} {terms : List (Term σ)}
        {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
        (hTerm : TermWellSorted term sort)
        (hRest : ArgsWellSorted terms sorts) :
        ArgsWellSorted (term :: terms) (sort :: sorts)
end

/-- 公式的 sort 正确性。 -/
inductive FormulaWellFormed {σ : Signature.{u, v, w}} : Formula σ → Prop where
  | falsum : FormulaWellFormed .falsum
  | truth : FormulaWellFormed .truth
  | rel (r : σ.RelSymbol) {args : List (Term σ)}
      (hArgs : ArgsWellSorted args (σ.relDomain r)) :
      FormulaWellFormed (.rel r args)
  | equal {left right : Term σ} {s : σ.SortSymbol}
      (hLeft : TermWellSorted left s)
      (hRight : TermWellSorted right s) :
      FormulaWellFormed (.equal left right)
  | neg {φ : Formula σ} (h : FormulaWellFormed φ) :
      FormulaWellFormed (.neg φ)
  | conj {φ ψ : Formula σ}
      (hφ : FormulaWellFormed φ) (hψ : FormulaWellFormed ψ) :
      FormulaWellFormed (.conj φ ψ)
  | disj {φ ψ : Formula σ}
      (hφ : FormulaWellFormed φ) (hψ : FormulaWellFormed ψ) :
      FormulaWellFormed (.disj φ ψ)
  | imp {φ ψ : Formula σ}
      (hφ : FormulaWellFormed φ) (hψ : FormulaWellFormed ψ) :
      FormulaWellFormed (.imp φ ψ)
  | iff {φ ψ : Formula σ}
      (hφ : FormulaWellFormed φ) (hψ : FormulaWellFormed ψ) :
      FormulaWellFormed (.iff φ ψ)
  | forallE (s : σ.SortSymbol) {body : Formula σ}
      (hBody : FormulaWellFormed body) :
      FormulaWellFormed (.forallE s body)
  | existsE (s : σ.SortSymbol) {body : Formula σ}
      (hBody : FormulaWellFormed body) :
      FormulaWellFormed (.existsE s body)

/-- 项的 scope 正确性；free 变量不受 bound scope 限制。 -/
inductive TermScoped {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] :
    Scope σ → Term σ → Prop where
  | bvar {ctx : Scope σ} {s : σ.SortSymbol} {idx : Nat} (hIdx : idx < ctx s) :
      TermScoped ctx (.var (.bvar s idx))
  | fvar {ctx : Scope σ} (s : σ.SortSymbol) (id : FreeVarId) :
      TermScoped ctx (.var (.fvar s id))
  | app {ctx : Scope σ} (f : σ.FuncSymbol) (args : List (Term σ))
      (hArgs : ∀ term, term ∈ args → TermScoped ctx term) :
      TermScoped ctx (.app f args)

/-- 公式的 scope 正确性。量词只扩展同 sort 的 bound stack。 -/
inductive FormulaScoped {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] :
    Scope σ → Formula σ → Prop where
  | falsum {ctx : Scope σ} : FormulaScoped ctx .falsum
  | truth {ctx : Scope σ} : FormulaScoped ctx .truth
  | rel {ctx : Scope σ} (r : σ.RelSymbol) (args : List (Term σ))
      (hArgs : ∀ term, term ∈ args → TermScoped ctx term) :
      FormulaScoped ctx (.rel r args)
  | equal {ctx : Scope σ} {left right : Term σ}
      (hLeft : TermScoped ctx left) (hRight : TermScoped ctx right) :
      FormulaScoped ctx (.equal left right)
  | neg {ctx : Scope σ} {φ : Formula σ} (h : FormulaScoped ctx φ) :
      FormulaScoped ctx (.neg φ)
  | conj {ctx : Scope σ} {φ ψ : Formula σ}
      (hφ : FormulaScoped ctx φ) (hψ : FormulaScoped ctx ψ) :
      FormulaScoped ctx (.conj φ ψ)
  | disj {ctx : Scope σ} {φ ψ : Formula σ}
      (hφ : FormulaScoped ctx φ) (hψ : FormulaScoped ctx ψ) :
      FormulaScoped ctx (.disj φ ψ)
  | imp {ctx : Scope σ} {φ ψ : Formula σ}
      (hφ : FormulaScoped ctx φ) (hψ : FormulaScoped ctx ψ) :
      FormulaScoped ctx (.imp φ ψ)
  | iff {ctx : Scope σ} {φ ψ : Formula σ}
      (hφ : FormulaScoped ctx φ) (hψ : FormulaScoped ctx ψ) :
      FormulaScoped ctx (.iff φ ψ)
  | forallE {ctx : Scope σ} (s : σ.SortSymbol) {body : Formula σ}
      (hBody : FormulaScoped (Scope.push ctx s) body) :
      FormulaScoped ctx (.forallE s body)
  | existsE {ctx : Scope σ} (s : σ.SortSymbol) {body : Formula σ}
      (hBody : FormulaScoped (Scope.push ctx s) body) :
      FormulaScoped ctx (.existsE s body)

def FormulaClosed {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (φ : Formula σ) : Prop :=
  FormulaScoped Scope.empty φ

namespace Term

/-- 在指定 sort 的第 `depth` 个 binder 处打开项。replacement 通常要求 locally closed。 -/
def openAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (depth : Nat) (replacement : Term σ) :
    Term σ → Term σ
  | var (.bvar s idx) =>
      if s = target then
        if idx = depth then
          replacement
        else if depth < idx then
          var (.bvar s (idx - 1))
        else
          var (.bvar s idx)
      else
        var (.bvar s idx)
  | var (.fvar s id) => var (.fvar s id)
  | app f args => app f (args.map (openAt target depth replacement))

/-- 关闭一个 free 变量，形成指定 sort 的 bound 变量。 -/
def closeFreeAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) :
    Term σ → Term σ
  | var (.bvar s idx) =>
      if s = target ∧ depth ≤ idx then
        var (.bvar s (idx + 1))
      else
        var (.bvar s idx)
  | var (.fvar s id') =>
      if s = target ∧ id' = id then
        var (.bvar s depth)
      else
        var (.fvar s id')
  | app f args => app f (args.map (closeFreeAt target id depth))

end Term

namespace Formula

/-- 右结合有限合取；空列表解释为真，单元素列表保持原公式。 -/
def conjunctionList {σ : Signature.{u, v, w}} :
    List (Formula σ) → Formula σ
  | [] => truth
  | [formula] => formula
  | formula :: rest => conj formula (conjunctionList rest)

private def nextDepth {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (target binder : σ.SortSymbol) (depth : Nat) : Nat :=
  if binder = target then depth + 1 else depth

/-- 打开公式中的指定 sort binder。 -/
def openAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (depth : Nat) (replacement : Term σ) :
    Formula σ → Formula σ
  | falsum => falsum
  | truth => truth
  | rel r args => rel r (args.map (Term.openAt target depth replacement))
  | equal left right =>
      equal (Term.openAt target depth replacement left)
        (Term.openAt target depth replacement right)
  | neg φ => neg (openAt target depth replacement φ)
  | conj φ ψ => conj (openAt target depth replacement φ) (openAt target depth replacement ψ)
  | disj φ ψ => disj (openAt target depth replacement φ) (openAt target depth replacement ψ)
  | imp φ ψ => imp (openAt target depth replacement φ) (openAt target depth replacement ψ)
  | iff φ ψ => iff (openAt target depth replacement φ) (openAt target depth replacement ψ)
  | forallE s body => forallE s (openAt target (nextDepth target s depth) replacement body)
  | existsE s body => existsE s (openAt target (nextDepth target s depth) replacement body)

/-- 关闭公式中的 free 变量。 -/
def closeFreeAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) :
    Formula σ → Formula σ
  | falsum => falsum
  | truth => truth
  | rel r args => rel r (args.map (Term.closeFreeAt target id depth))
  | equal left right =>
      equal (Term.closeFreeAt target id depth left)
        (Term.closeFreeAt target id depth right)
  | neg φ => neg (closeFreeAt target id depth φ)
  | conj φ ψ => conj (closeFreeAt target id depth φ) (closeFreeAt target id depth ψ)
  | disj φ ψ => disj (closeFreeAt target id depth φ) (closeFreeAt target id depth ψ)
  | imp φ ψ => imp (closeFreeAt target id depth φ) (closeFreeAt target id depth ψ)
  | iff φ ψ => iff (closeFreeAt target id depth φ) (closeFreeAt target id depth ψ)
  | forallE s body => forallE s (closeFreeAt target id (nextDepth target s depth) body)
  | existsE s body => existsE s (closeFreeAt target id (nextDepth target s depth) body)

end Formula

end FirstOrder
end Logic
end YesMetaZFC
