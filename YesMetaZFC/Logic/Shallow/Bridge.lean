import YesMetaZFC.Logic.Fragment
import YesMetaZFC.Logic.Theory

/-!
# 浅嵌入机械桥接

桥接层不做搜索，也不猜证明。它只把已经识别出来的浅层语义对象包装成
proof-carrying view：每个 view 同时携带深嵌入对象和语义保持定理。
后续 tactic / elaborator 可以自动生成这些 view，但可信内核只消费本文件的构造子。
-/

namespace YesMetaZFC
namespace Logic
namespace Shallow
namespace FirstOrder

universe u v w x

open _root_.YesMetaZFC.Logic.FirstOrder

/-- 浅嵌入桥接规格。Full 二阶不应作为默认自动化目标。 -/
structure BridgeSpec (σ : Signature.{u, v, w}) where
  fragment : Fragment := Fragment.firstOrderEq
  support : AutomationSupport := Fragment.automationSupport fragment

namespace BridgeSpec

/-- 默认一阶等词桥接规格。 -/
def firstOrderEq (σ : Signature.{u, v, w}) : BridgeSpec σ where
  fragment := Fragment.firstOrderEq
  support := Fragment.automationSupport Fragment.firstOrderEq

/-- 默认二阶桥接规格使用 Henkin 语义，只承诺部分自动化。 -/
def secondOrderHenkin (σ : Signature.{u, v, w}) : BridgeSpec σ where
  fragment := Fragment.defaultSecondOrder
  support := Fragment.automationSupport Fragment.defaultSecondOrder

/-- Full second-order 只作为语义桥接档位，不进入默认自动化搜索承诺。 -/
def secondOrderFullSemanticOnly (σ : Signature.{u, v, w}) : BridgeSpec σ where
  fragment := Fragment.secondOrderFull
  support := Fragment.automationSupport Fragment.secondOrderFull

end BridgeSpec

/-- 浅层项 view：`value` 是浅语义，`deep` 是深嵌入项，`sound` 连接两者。 -/
structure TermView {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) (sort : σ.SortSymbol) where
  deep : Term σ
  wellSorted : TermWellSorted deep sort
  value : Env M → M.Domain
  sound : ∀ env, value env = Term.eval env deep

namespace TermView

theorem value_sort {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {sort : σ.SortSymbol} (view : TermView M sort) (env : Env M) :
    M.sortInterp sort (view.value env) := by
  rw [view.sound env]
  exact Term.eval_sort_of_wellSorted (env := env) view.wellSorted

/-- bound 变量桥接。 -/
def bvar {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ)
    (sort : σ.SortSymbol) (idx : Nat) : TermView M sort where
  deep := Term.var (.bvar sort idx)
  wellSorted := TermWellSorted.bvar sort idx
  value := fun env => env.boundVal sort idx
  sound := by
    intro env
    simp [Term.eval]

/-- free 变量桥接。 -/
def fvar {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ)
    (sort : σ.SortSymbol) (id : FreeVarId) : TermView M sort where
  deep := Term.var (.fvar sort id)
  wellSorted := TermWellSorted.fvar sort id
  value := fun env => env.freeVal sort id
  sound := by
    intro env
    simp [Term.eval]

end TermView

/-- 参数列表 view，按 signature 中的 sort 列表逐项桥接。 -/
structure ArgsView {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) (sorts : List σ.SortSymbol) where
  deep : List (Term σ)
  wellSorted : ArgsWellSorted deep sorts
  values : Env M → List M.Domain
  sound : ∀ env, values env = deep.map (Term.eval env)

namespace ArgsView

def nil {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ) :
    ArgsView M [] where
  deep := []
  wellSorted := ArgsWellSorted.nil
  values := fun _ => []
  sound := by
    intro env
    rfl

def cons {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (head : TermView M sort) (tail : ArgsView M sorts) :
    ArgsView M (sort :: sorts) where
  deep := head.deep :: tail.deep
  wellSorted := ArgsWellSorted.cons head.wellSorted tail.wellSorted
  values := fun env => head.value env :: tail.values env
  sound := by
    intro env
    simp [head.sound env, tail.sound env]

end ArgsView

namespace TermView

/-- 函数应用桥接。 -/
def app {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (f : σ.FuncSymbol) (args : ArgsView M (σ.funcDomain f)) :
    TermView M (σ.funcCodomain f) where
  deep := Term.app f args.deep
  wellSorted := TermWellSorted.app f args.wellSorted
  value := fun env => M.funcInterp f (args.values env)
  sound := by
    intro env
    simp [Term.eval, args.sound env]

end TermView

/-- 浅层公式 view：`prop` 是浅命题语义，`deep` 是深嵌入公式。 -/
structure FormulaView {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (M : Structure.{u, v, w, x} σ) where
  deep : Formula σ
  wellFormed : FormulaWellFormed deep
  prop : Env M → Prop
  sound : ∀ env, prop env ↔ Formula.satisfies env deep

namespace FormulaView

def falsum {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (M : Structure.{u, v, w, x} σ) : FormulaView M where
  deep := Formula.falsum
  wellFormed := FormulaWellFormed.falsum
  prop := fun _ => False
  sound := by
    intro env
    rfl

def truth {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (M : Structure.{u, v, w, x} σ) : FormulaView M where
  deep := Formula.truth
  wellFormed := FormulaWellFormed.truth
  prop := fun _ => True
  sound := by
    intro env
    rfl

def rel {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ}
    (r : σ.RelSymbol) (args : ArgsView M (σ.relDomain r)) :
    FormulaView M where
  deep := Formula.rel r args.deep
  wellFormed := FormulaWellFormed.rel r args.wellSorted
  prop := fun env => M.relInterp r (args.values env)
  sound := by
    intro env
    simp [Formula.satisfies, args.sound env]

def equal {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {sort : σ.SortSymbol}
    (left right : TermView M sort) : FormulaView M where
  deep := Formula.equal left.deep right.deep
  wellFormed := FormulaWellFormed.equal left.wellSorted right.wellSorted
  prop := fun env => left.value env = right.value env
  sound := by
    intro env
    simp [Formula.satisfies, left.sound env, right.sound env]

def neg {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (view : FormulaView M) :
    FormulaView M where
  deep := Formula.neg view.deep
  wellFormed := FormulaWellFormed.neg view.wellFormed
  prop := fun env => ¬ view.prop env
  sound := by
    intro env
    simpa [Formula.satisfies] using not_congr (view.sound env)

def conj {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (left right : FormulaView M) :
    FormulaView M where
  deep := Formula.conj left.deep right.deep
  wellFormed := FormulaWellFormed.conj left.wellFormed right.wellFormed
  prop := fun env => left.prop env ∧ right.prop env
  sound := by
    intro env
    exact and_congr (left.sound env) (right.sound env)

def disj {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (left right : FormulaView M) :
    FormulaView M where
  deep := Formula.disj left.deep right.deep
  wellFormed := FormulaWellFormed.disj left.wellFormed right.wellFormed
  prop := fun env => left.prop env ∨ right.prop env
  sound := by
    intro env
    exact or_congr (left.sound env) (right.sound env)

def imp {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (left right : FormulaView M) :
    FormulaView M where
  deep := Formula.imp left.deep right.deep
  wellFormed := FormulaWellFormed.imp left.wellFormed right.wellFormed
  prop := fun env => left.prop env → right.prop env
  sound := by
    intro env
    exact imp_congr (left.sound env) (right.sound env)

def iff {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (left right : FormulaView M) :
    FormulaView M where
  deep := Formula.iff left.deep right.deep
  wellFormed := FormulaWellFormed.iff left.wellFormed right.wellFormed
  prop := fun env => left.prop env ↔ right.prop env
  sound := by
    intro env
    exact iff_congr (left.sound env) (right.sound env)

def forallE {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (sort : σ.SortSymbol)
    (body : FormulaView M) : FormulaView M where
  deep := Formula.forallE sort body.deep
  wellFormed := FormulaWellFormed.forallE sort body.wellFormed
  prop := fun env =>
    ∀ value, ∀ hValue : M.sortInterp sort value,
      body.prop (env.pushBound sort value hValue)
  sound := by
    intro env
    simp [Formula.satisfies, body.sound]

def existsE {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (sort : σ.SortSymbol)
    (body : FormulaView M) : FormulaView M where
  deep := Formula.existsE sort body.deep
  wellFormed := FormulaWellFormed.existsE sort body.wellFormed
  prop := fun env =>
    ∃ value, ∃ hValue : M.sortInterp sort value,
      body.prop (env.pushBound sort value hValue)
  sound := by
    intro env
    simp [Formula.satisfies, body.sound]

end FormulaView

/-- 一个已经桥接完成的公式，可作为自动化入口的可信 payload。 -/
structure BridgeResult {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (M : Structure.{u, v, w, x} σ) where
  spec : BridgeSpec σ
  formula : FormulaView M

namespace BridgeResult

def deep {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (result : BridgeResult M) : Formula σ :=
  result.formula.deep

def prop {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (result : BridgeResult M) : Env M → Prop :=
  result.formula.prop

theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (result : BridgeResult M) :
    ∀ env, result.prop env ↔ Formula.satisfies env result.deep :=
  result.formula.sound

end BridgeResult

end FirstOrder
end Shallow
end Logic
end YesMetaZFC
