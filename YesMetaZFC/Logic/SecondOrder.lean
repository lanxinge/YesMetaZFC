import YesMetaZFC.Logic.Infinitary

/-!
# 二阶逻辑语义

默认自动化面向 Henkin 语义：二阶关系变量只在显式给出的 admissible relation
domain 中量化。Full second-order semantics 也进入系统，但只作为语义能力，不承诺
自动化搜索或证书生成。
-/

namespace YesMetaZFC
namespace Logic
namespace SecondOrder

universe u v w i x y

abbrev RelVarId := Nat
abbrev BoundContext := Infinitary.BoundContext
abbrev Term := Infinitary.Term
abbrev One : Type i := ULift.{i, 0} Unit

def oneSort {σ : Signature.{u, v, w}} (sort : σ.SortSymbol) : One.{i} → σ.SortSymbol :=
  fun _ => sort

/-- 二阶关系变量 context，按参数 sort 列表分族。 -/
abbrev RelContext (σ : Signature.{u, v, w}) := List σ.SortSymbol → Type i

namespace RelContext

def empty {σ : Signature.{u, v, w}} : RelContext σ :=
  fun _ => Empty

def extend {σ : Signature.{u, v, w}} (Δ : RelContext σ)
    (domains : List σ.SortSymbol) : RelContext σ :=
  fun query => Sum (Δ query) (PLift (query = domains))

end RelContext

/-- 二阶公式：一阶对象变量 context 与二阶关系变量 context 分开管理。 -/
inductive Formula (σ : Signature.{u, v, w}) :
    BoundContext.{u, v, w, i} σ → RelContext.{u, v, w, i} σ →
      Type (max u v w (i + 1)) where
  | falsum {Γ : BoundContext σ} {Δ : RelContext σ} : Formula σ Γ Δ
  | truth {Γ : BoundContext σ} {Δ : RelContext σ} : Formula σ Γ Δ
  | rel {Γ : BoundContext σ} {Δ : RelContext σ} :
      σ.RelSymbol → List (Term σ Γ) → Formula σ Γ Δ
  | equal {Γ : BoundContext σ} {Δ : RelContext σ} :
      Term σ Γ → Term σ Γ → Formula σ Γ Δ
  | relBound :
      (domains : List σ.SortSymbol) → Δ domains → List (Term σ Γ) → Formula σ Γ Δ
  | relFree :
      (domains : List σ.SortSymbol) → RelVarId → List (Term σ Γ) → Formula σ Γ Δ
  | neg : Formula σ Γ Δ → Formula σ Γ Δ
  | conj : Formula σ Γ Δ → Formula σ Γ Δ → Formula σ Γ Δ
  | disj : Formula σ Γ Δ → Formula σ Γ Δ → Formula σ Γ Δ
  | imp : Formula σ Γ Δ → Formula σ Γ Δ → Formula σ Γ Δ
  | iff : Formula σ Γ Δ → Formula σ Γ Δ → Formula σ Γ Δ
  | forallObj :
      (sort : σ.SortSymbol) →
        Formula σ (Infinitary.BoundContext.extend Γ (oneSort sort)) Δ →
          Formula σ Γ Δ
  | existsObj :
      (sort : σ.SortSymbol) →
        Formula σ (Infinitary.BoundContext.extend Γ (oneSort sort)) Δ →
          Formula σ Γ Δ
  | forallRel :
      (domains : List σ.SortSymbol) →
        Formula σ Γ (RelContext.extend Δ domains) → Formula σ Γ Δ
  | existsRel :
      (domains : List σ.SortSymbol) →
        Formula σ Γ (RelContext.extend Δ domains) → Formula σ Γ Δ

namespace Henkin

/-- Henkin 二阶结构：每个关系 arity/sort 列表有一个 admissible relation domain。 -/
structure Structure (σ : Signature.{u, v, w}) where
  base : FirstOrder.Structure.{u, v, w, x} σ
  relDomain : List σ.SortSymbol → Type y
  relInterp : ∀ domains, relDomain domains → List base.Domain → Prop

/-- Henkin 语义环境。 -/
structure Env {σ : Signature.{u, v, w}} (H : Structure.{u, v, w, x, y} σ)
    (Γ : BoundContext.{u, v, w, i} σ) (Δ : RelContext.{u, v, w, i} σ) where
  firstOrder : Infinitary.Env H.base Γ
  boundRel : ∀ domains, Δ domains → H.relDomain domains
  freeRel : ∀ domains, RelVarId → H.relDomain domains

namespace Env

def pushObj {σ : Signature.{u, v, w}} {H : Structure.{u, v, w, x, y} σ}
    {Γ : BoundContext.{u, v, w, i} σ} {Δ : RelContext.{u, v, w, i} σ}
    (env : Env H Γ Δ) (sort : σ.SortSymbol) (value : H.base.Domain)
    (hValue : H.base.sortInterp sort value) :
    Env H (Infinitary.BoundContext.extend Γ (oneSort sort)) Δ where
  firstOrder :=
    env.firstOrder.pushBlock (oneSort sort)
      (fun _ => value) (fun _ => hValue)
  boundRel := env.boundRel
  freeRel := env.freeRel

def pushRel {σ : Signature.{u, v, w}} {H : Structure.{u, v, w, x, y} σ}
    {Γ : BoundContext.{u, v, w, i} σ} {Δ : RelContext.{u, v, w, i} σ}
    (env : Env H Γ Δ) (domains : List σ.SortSymbol)
    (rel : H.relDomain domains) :
    Env H Γ (RelContext.extend Δ domains) where
  firstOrder := env.firstOrder
  boundRel := by
    intro query var
    cases var with
    | inl old => exact env.boundRel query old
    | inr hEq =>
        cases hEq with
        | up hEq =>
            cases hEq
            exact rel
  freeRel := env.freeRel

end Env

namespace Formula

/-- Henkin 二阶满足关系；这是默认可接自动化证书的二阶语义。 -/
def satisfies {σ : Signature.{u, v, w}} {H : Structure.{u, v, w, x, y} σ}
    {Γ : BoundContext.{u, v, w, i} σ} {Δ : RelContext.{u, v, w, i} σ}
    (env : Env H Γ Δ) : _root_.YesMetaZFC.Logic.SecondOrder.Formula σ Γ Δ → Prop
  | .falsum => False
  | .truth => True
  | .rel r args => H.base.relInterp r (args.map (Infinitary.Term.eval env.firstOrder))
  | .equal left right =>
      Infinitary.Term.eval env.firstOrder left = Infinitary.Term.eval env.firstOrder right
  | .relBound domains rel args =>
      H.relInterp domains (env.boundRel domains rel)
        (args.map (Infinitary.Term.eval env.firstOrder))
  | .relFree domains rel args =>
      H.relInterp domains (env.freeRel domains rel)
        (args.map (Infinitary.Term.eval env.firstOrder))
  | .neg φ => ¬ satisfies env φ
  | .conj φ ψ => satisfies env φ ∧ satisfies env ψ
  | .disj φ ψ => satisfies env φ ∨ satisfies env ψ
  | .imp φ ψ => satisfies env φ → satisfies env ψ
  | .iff φ ψ => satisfies env φ ↔ satisfies env ψ
  | .forallObj sort body =>
      ∀ value, ∀ hValue : H.base.sortInterp sort value,
        satisfies (env.pushObj sort value hValue) body
  | .existsObj sort body =>
      ∃ value, ∃ hValue : H.base.sortInterp sort value,
        satisfies (env.pushObj sort value hValue) body
  | .forallRel domains body =>
      ∀ rel : H.relDomain domains, satisfies (env.pushRel domains rel) body
  | .existsRel domains body =>
      ∃ rel : H.relDomain domains, satisfies (env.pushRel domains rel) body

end Formula

end Henkin

namespace Full

/-- Full 二阶语义中的关系变量解释为所有谓词；不作为默认自动化搜索空间。 -/
abbrev Relation {σ : Signature.{u, v, w}}
    (M : FirstOrder.Structure.{u, v, w, x} σ)
    (_domains : List σ.SortSymbol) :=
  List M.Domain → Prop

structure Env {σ : Signature.{u, v, w}} (M : FirstOrder.Structure.{u, v, w, x} σ)
    (Γ : BoundContext.{u, v, w, i} σ) (Δ : RelContext.{u, v, w, i} σ) where
  firstOrder : Infinitary.Env M Γ
  boundRel : ∀ domains, Δ domains → Relation M domains
  freeRel : ∀ domains, RelVarId → Relation M domains

namespace Env

def pushObj {σ : Signature.{u, v, w}} {M : FirstOrder.Structure.{u, v, w, x} σ}
    {Γ : BoundContext.{u, v, w, i} σ} {Δ : RelContext.{u, v, w, i} σ}
    (env : Env M Γ Δ) (sort : σ.SortSymbol) (value : M.Domain)
    (hValue : M.sortInterp sort value) :
    Env M (Infinitary.BoundContext.extend Γ (oneSort sort)) Δ where
  firstOrder :=
    env.firstOrder.pushBlock (oneSort sort)
      (fun _ => value) (fun _ => hValue)
  boundRel := env.boundRel
  freeRel := env.freeRel

def pushRel {σ : Signature.{u, v, w}} {M : FirstOrder.Structure.{u, v, w, x} σ}
    {Γ : BoundContext.{u, v, w, i} σ} {Δ : RelContext.{u, v, w, i} σ}
    (env : Env M Γ Δ) (domains : List σ.SortSymbol)
    (rel : Relation M domains) :
    Env M Γ (RelContext.extend Δ domains) where
  firstOrder := env.firstOrder
  boundRel := by
    intro query var
    cases var with
    | inl old => exact env.boundRel query old
    | inr hEq =>
        cases hEq with
        | up hEq =>
            cases hEq
            exact rel
  freeRel := env.freeRel

end Env

namespace Formula

/-- Full 二阶满足关系：二阶量词遍历所有谓词。 -/
def satisfies {σ : Signature.{u, v, w}} {M : FirstOrder.Structure.{u, v, w, x} σ}
    {Γ : BoundContext.{u, v, w, i} σ} {Δ : RelContext.{u, v, w, i} σ}
    (env : Env M Γ Δ) : _root_.YesMetaZFC.Logic.SecondOrder.Formula σ Γ Δ → Prop
  | .falsum => False
  | .truth => True
  | .rel r args => M.relInterp r (args.map (Infinitary.Term.eval env.firstOrder))
  | .equal left right =>
      Infinitary.Term.eval env.firstOrder left = Infinitary.Term.eval env.firstOrder right
  | .relBound domains rel args =>
      env.boundRel domains rel (args.map (Infinitary.Term.eval env.firstOrder))
  | .relFree domains rel args =>
      env.freeRel domains rel (args.map (Infinitary.Term.eval env.firstOrder))
  | .neg φ => ¬ satisfies env φ
  | .conj φ ψ => satisfies env φ ∧ satisfies env ψ
  | .disj φ ψ => satisfies env φ ∨ satisfies env ψ
  | .imp φ ψ => satisfies env φ → satisfies env ψ
  | .iff φ ψ => satisfies env φ ↔ satisfies env ψ
  | .forallObj sort body =>
      ∀ value, ∀ hValue : M.sortInterp sort value,
        satisfies (env.pushObj sort value hValue) body
  | .existsObj sort body =>
      ∃ value, ∃ hValue : M.sortInterp sort value,
        satisfies (env.pushObj sort value hValue) body
  | .forallRel domains body =>
      ∀ rel : Relation M domains, satisfies (env.pushRel domains rel) body
  | .existsRel domains body =>
      ∃ rel : Relation M domains, satisfies (env.pushRel domains rel) body

end Formula

end Full

/-- 二阶语义模式。Henkin 是自动化默认档位；Full 只保证语义解释存在。 -/
inductive SemanticsMode where
  | henkin
  | full
  deriving DecidableEq, Repr

namespace SemanticsMode

def automationSupported : SemanticsMode → Bool
  | .henkin => true
  | .full => false

end SemanticsMode

end SecondOrder
end Logic
end YesMetaZFC
