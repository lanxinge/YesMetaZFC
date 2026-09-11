import YesMetaZFC.Logic.Fragment
import YesMetaZFC.Model.FirstOrder.Theory

/-!
# 内在类型语法的浅嵌入桥接

每个 view 只携带深嵌入对象、浅语义和二者的等价性。排序、元数与作用域由深对象的
类型索引保证，不再重复存放良构证书。
-/

namespace YesMetaZFC
namespace Logic
namespace Shallow
namespace FirstOrder

universe u v w x

open _root_.YesMetaZFC.Logic.FirstOrder

/-- 浅嵌入桥接规格。Full 二阶不作为默认自动化目标。 -/
structure BridgeSpec (σ : Signature.{u, v, w}) where
  fragment : Fragment := Fragment.firstOrderEq
  support : AutomationSupport := Fragment.automationSupport fragment

namespace BridgeSpec

def firstOrderEq (σ : Signature.{u, v, w}) : BridgeSpec σ where
  fragment := Fragment.firstOrderEq
  support := Fragment.automationSupport Fragment.firstOrderEq

def secondOrderHenkin (σ : Signature.{u, v, w}) : BridgeSpec σ where
  fragment := Fragment.defaultSecondOrder
  support := Fragment.automationSupport Fragment.defaultSecondOrder

def secondOrderFullSemanticOnly
    (σ : Signature.{u, v, w}) : BridgeSpec σ where
  fragment := Fragment.secondOrderFull
  support := Fragment.automationSupport Fragment.secondOrderFull

end BridgeSpec

/-- 类型化项的浅语义 view。 -/
structure TermView {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ)
    (bound free : SortContext σ) (sort : σ.SortSymbol) where
  deep : Term σ bound free sort
  value : Env M bound free → M.Carrier sort
  sound : ∀ env, value env = deep.eval env

namespace TermView

def bvar {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (entry : Variable bound sort) : TermView M bound free sort where
  deep := .bvar entry
  value := fun env => env.boundVal entry
  sound := fun _ => rfl

def fvar {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (entry : Variable free sort) : TermView M bound free sort where
  deep := .fvar entry
  value := fun env => env.freeVal entry
  sound := fun _ => rfl

end TermView

/-- 类型化异质参数列的浅语义 view。 -/
structure ArgsView {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ)
    (bound free : SortContext σ) (sorts : List σ.SortSymbol) where
  deep : Arguments σ bound free sorts
  values : Env M bound free → Values M.Carrier sorts
  sound : ∀ env, values env = deep.eval env

namespace ArgsView

def nil {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} : ArgsView M bound free [] where
  deep := .nil
  values := fun _ => .nil
  sound := fun _ => rfl

def cons {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (head : TermView M bound free sort)
    (tail : ArgsView M bound free sorts) :
    ArgsView M bound free (sort :: sorts) where
  deep := .cons head.deep tail.deep
  values := fun env => .cons (head.value env) (tail.values env)
  sound := by
    intro env
    rw [head.sound env, tail.sound env]
    rfl

end ArgsView

namespace TermView

def app {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (function : σ.FuncSymbol)
    (arguments : ArgsView M bound free (σ.funcDomain function)) :
    TermView M bound free (σ.funcCodomain function) where
  deep := .app function arguments.deep
  value := fun env => M.funcInterp function (arguments.values env)
  sound := by
    intro env
    rw [arguments.sound env]
    rfl

end TermView

/-- 类型化公式的浅命题 view。 -/
structure FormulaView {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ)
    (bound free : SortContext σ) where
  deep : Formula σ bound free
  prop : Env M bound free → Prop
  sound : ∀ env, prop env ↔ Formula.satisfies env deep

namespace FormulaView

def falsum {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} : FormulaView M bound free where
  deep := .falsum
  prop := fun _ => False
  sound := fun _ => Iff.rfl

def truth {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} : FormulaView M bound free where
  deep := .truth
  prop := fun _ => True
  sound := fun _ => Iff.rfl

def rel {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (relation : σ.RelSymbol)
    (arguments : ArgsView M bound free (σ.relDomain relation)) :
    FormulaView M bound free where
  deep := .rel relation arguments.deep
  prop := fun env => M.relInterp relation (arguments.values env)
  sound := by
    intro env
    rw [arguments.sound env]
    rfl

def equal {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (left right : TermView M bound free sort) :
    FormulaView M bound free where
  deep := .equal left.deep right.deep
  prop := fun env => left.value env = right.value env
  sound := by
    intro env
    rw [left.sound env, right.sound env]
    rfl

def neg {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (body : FormulaView M bound free) :
    FormulaView M bound free where
  deep := .neg body.deep
  prop := fun env => ¬ body.prop env
  sound := fun env => not_congr (body.sound env)

def conj {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (left right : FormulaView M bound free) : FormulaView M bound free where
  deep := .conj left.deep right.deep
  prop := fun env => left.prop env ∧ right.prop env
  sound := fun env => and_congr (left.sound env) (right.sound env)

def disj {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (left right : FormulaView M bound free) : FormulaView M bound free where
  deep := .disj left.deep right.deep
  prop := fun env => left.prop env ∨ right.prop env
  sound := fun env => or_congr (left.sound env) (right.sound env)

def imp {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (left right : FormulaView M bound free) : FormulaView M bound free where
  deep := .imp left.deep right.deep
  prop := fun env => left.prop env → right.prop env
  sound := fun env => imp_congr (left.sound env) (right.sound env)

def iff {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (left right : FormulaView M bound free) : FormulaView M bound free where
  deep := .iff left.deep right.deep
  prop := fun env => left.prop env ↔ right.prop env
  sound := fun env => iff_congr (left.sound env) (right.sound env)

def forallE {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (body : FormulaView M (sort :: bound) free) :
    FormulaView M bound free where
  deep := .forallE sort body.deep
  prop := fun env => ∀ value, body.prop (env.pushBound value)
  sound := by
    intro env
    exact forall_congr' (fun value => body.sound (env.pushBound value))

def existsE {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (body : FormulaView M (sort :: bound) free) :
    FormulaView M bound free where
  deep := .existsE sort body.deep
  prop := fun env => ∃ value, body.prop (env.pushBound value)
  sound := by
    intro env
    constructor
    · rintro ⟨value, hBody⟩
      exact ⟨value, (body.sound (env.pushBound value)).mp hBody⟩
    · rintro ⟨value, hBody⟩
      exact ⟨value, (body.sound (env.pushBound value)).mpr hBody⟩

end FormulaView

/-- 自动化入口的可信一阶浅桥 payload。 -/
structure BridgeResult {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) (free : SortContext σ := []) where
  spec : BridgeSpec σ
  formula : FormulaView M [] free

namespace BridgeResult

def deep {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (result : BridgeResult M free) : OpenFormula σ free :=
  result.formula.deep

def prop {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (result : BridgeResult M free) : Env M [] free → Prop :=
  result.formula.prop

theorem sound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (result : BridgeResult M free) :
    ∀ env, result.prop env ↔ Formula.satisfies env result.deep :=
  result.formula.sound

end BridgeResult
end FirstOrder
end Shallow
end Logic
end YesMetaZFC
