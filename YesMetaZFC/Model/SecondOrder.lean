import YesMetaZFC.Model.Infinitary

/-!
# 内在类型的二阶逻辑语义

对象变量和关系变量都由类型化上下文管理。关系应用直接携带与关系参数排序一致的
异质参数列；因此自由关系变量不再使用自然数编号，Henkin 与 full 语义也不再承担
参数排序、变量良构或索引越界证明。
-/

namespace YesMetaZFC
namespace Logic
namespace SecondOrder

universe u v w i x y

abbrev ObjContext := Infinitary.Context

/-- 二阶关系变量上下文，按参数排序列表分族。 -/
abbrev RelContext (σ : Signature.{u, v, w}) := List σ.SortSymbol → Type i

namespace RelContext

def empty {σ : Signature.{u, v, w}} : RelContext.{u, v, w, i} σ :=
  fun _ => ULift.{i, 0} Empty

/-- 在指定参数排序处加入一个新的关系变量。 -/
def extend {σ : Signature.{u, v, w}}
    (context : RelContext.{u, v, w, i} σ)
    (domains : List σ.SortSymbol) : RelContext.{u, v, w, i} σ :=
  fun query => Sum (context query) (PLift (query = domains))

end RelContext

abbrev One : Type i := ULift.{i, 0} Unit

def oneSort {σ : Signature.{u, v, w}}
    (sort : σ.SortSymbol) : One.{i} → σ.SortSymbol :=
  fun _ => sort

/--
内在类型的二阶公式。四个上下文依次管理对象 bound/free 变量与关系 bound/free
变量；所有应用节点都在构造时保证参数排序正确。
-/
inductive Formula (σ : Signature.{u, v, w}) :
    ObjContext.{u, v, w, i} σ → ObjContext.{u, v, w, i} σ →
    RelContext.{u, v, w, i} σ → RelContext.{u, v, w, i} σ →
      Type (max u v w (i + 1)) where
  | falsum {objBound objFree relBound relFree} :
      Formula σ objBound objFree relBound relFree
  | truth {objBound objFree relBound relFree} :
      Formula σ objBound objFree relBound relFree
  | rel {objBound objFree relBound relFree} (relation : σ.RelSymbol) :
      Infinitary.Arguments σ objBound objFree (σ.relDomain relation) →
        Formula σ objBound objFree relBound relFree
  | equal {objBound objFree relBound relFree} {sort : σ.SortSymbol} :
      Infinitary.Term σ objBound objFree sort →
      Infinitary.Term σ objBound objFree sort →
        Formula σ objBound objFree relBound relFree
  | relBound {objBound objFree relBound relFree}
      {domains : List σ.SortSymbol} :
      relBound domains → Infinitary.Arguments σ objBound objFree domains →
        Formula σ objBound objFree relBound relFree
  | relFree {objBound objFree relBound relFree}
      {domains : List σ.SortSymbol} :
      relFree domains → Infinitary.Arguments σ objBound objFree domains →
        Formula σ objBound objFree relBound relFree
  | neg {objBound objFree relBound relFree} :
      Formula σ objBound objFree relBound relFree →
        Formula σ objBound objFree relBound relFree
  | conj {objBound objFree relBound relFree} :
      Formula σ objBound objFree relBound relFree →
      Formula σ objBound objFree relBound relFree →
        Formula σ objBound objFree relBound relFree
  | disj {objBound objFree relBound relFree} :
      Formula σ objBound objFree relBound relFree →
      Formula σ objBound objFree relBound relFree →
        Formula σ objBound objFree relBound relFree
  | imp {objBound objFree relBound relFree} :
      Formula σ objBound objFree relBound relFree →
      Formula σ objBound objFree relBound relFree →
        Formula σ objBound objFree relBound relFree
  | iff {objBound objFree relBound relFree} :
      Formula σ objBound objFree relBound relFree →
      Formula σ objBound objFree relBound relFree →
        Formula σ objBound objFree relBound relFree
  | forallObj {objBound objFree relBound relFree}
      (sort : σ.SortSymbol) :
      Formula σ (Infinitary.Context.extend objBound (oneSort sort)) objFree
        relBound relFree → Formula σ objBound objFree relBound relFree
  | existsObj {objBound objFree relBound relFree}
      (sort : σ.SortSymbol) :
      Formula σ (Infinitary.Context.extend objBound (oneSort sort)) objFree
        relBound relFree → Formula σ objBound objFree relBound relFree
  | forallRel {objBound objFree relBound relFree}
      (domains : List σ.SortSymbol) :
      Formula σ objBound objFree (RelContext.extend relBound domains) relFree →
        Formula σ objBound objFree relBound relFree
  | existsRel {objBound objFree relBound relFree}
      (domains : List σ.SortSymbol) :
      Formula σ objBound objFree (RelContext.extend relBound domains) relFree →
        Formula σ objBound objFree relBound relFree

namespace Henkin

-- 各字段（或其签名别名）保留独立宇宙；结构类型的 max 不是冗余参数。
set_option linter.checkUnivs false in
/-- Henkin 二阶结构：每种关系类型有一个显式的可量化关系域。 -/
structure Structure (σ : Signature.{u, v, w}) where
  base : FirstOrder.Structure.{u, v, w, x} σ
  relDomain : List σ.SortSymbol → Type y
  relInterp : ∀ domains, relDomain domains →
    FirstOrder.Values base.Carrier domains → Prop

/-- Henkin 环境同时解释对象变量和关系变量。 -/
structure Env {σ : Signature.{u, v, w}}
    (H : Structure.{u, v, w, x, y} σ)
    (objBound objFree : ObjContext.{u, v, w, i} σ)
    (relBound relFree : RelContext.{u, v, w, i} σ) where
  firstOrder : Infinitary.Env H.base objBound objFree
  boundRel : ∀ {domains}, relBound domains → H.relDomain domains
  freeRel : ∀ {domains}, relFree domains → H.relDomain domains

namespace Env

def pushObj {σ : Signature.{u, v, w}}
    {H : Structure.{u, v, w, x, y} σ}
    {objBound objFree : ObjContext.{u, v, w, i} σ}
    {relBound relFree : RelContext.{u, v, w, i} σ}
    (env : Env H objBound objFree relBound relFree)
    (sort : σ.SortSymbol) (value : H.base.Carrier sort) :
    Env H (Infinitary.Context.extend objBound (oneSort sort)) objFree
      relBound relFree where
  firstOrder := env.firstOrder.pushBlock (oneSort sort) (fun _ => value)
  boundRel := env.boundRel
  freeRel := env.freeRel

def pushRel {σ : Signature.{u, v, w}}
    {H : Structure.{u, v, w, x, y} σ}
    {objBound objFree : ObjContext.{u, v, w, i} σ}
    {relBound relFree : RelContext.{u, v, w, i} σ}
    (env : Env H objBound objFree relBound relFree)
    (domains : List σ.SortSymbol) (relation : H.relDomain domains) :
    Env H objBound objFree (RelContext.extend relBound domains) relFree where
  firstOrder := env.firstOrder
  boundRel := by
    intro query entry
    cases entry with
    | inl previous => exact env.boundRel previous
    | inr tagged =>
        cases tagged with
        | up equality =>
            cases equality
            exact relation
  freeRel := env.freeRel

end Env

namespace Formula

/-- Henkin 二阶满足关系；这是默认可接自动化证书的语义。 -/
def satisfies {σ : Signature.{u, v, w}}
    {H : Structure.{u, v, w, x, y} σ}
    {objBound objFree : ObjContext.{u, v, w, i} σ}
    {relBound relFree : RelContext.{u, v, w, i} σ}
    (env : Env H objBound objFree relBound relFree) :
    _root_.YesMetaZFC.Logic.SecondOrder.Formula σ
      objBound objFree relBound relFree → Prop
  | .falsum => False
  | .truth => True
  | .rel relation arguments =>
      H.base.relInterp relation (Infinitary.Arguments.eval env.firstOrder arguments)
  | .equal left right =>
      Infinitary.Term.eval env.firstOrder left =
        Infinitary.Term.eval env.firstOrder right
  | .relBound relation arguments =>
      H.relInterp _ (env.boundRel relation)
        (Infinitary.Arguments.eval env.firstOrder arguments)
  | .relFree relation arguments =>
      H.relInterp _ (env.freeRel relation)
        (Infinitary.Arguments.eval env.firstOrder arguments)
  | .neg body => ¬ satisfies env body
  | .conj left right => satisfies env left ∧ satisfies env right
  | .disj left right => satisfies env left ∨ satisfies env right
  | .imp left right => satisfies env left → satisfies env right
  | .iff left right => satisfies env left ↔ satisfies env right
  | .forallObj sort body =>
      ∀ value : H.base.Carrier sort, satisfies (env.pushObj sort value) body
  | .existsObj sort body =>
      ∃ value : H.base.Carrier sort, satisfies (env.pushObj sort value) body
  | .forallRel domains body =>
      ∀ relation : H.relDomain domains,
        satisfies (env.pushRel domains relation) body
  | .existsRel domains body =>
      ∃ relation : H.relDomain domains,
        satisfies (env.pushRel domains relation) body

end Formula
end Henkin

namespace Full

/-- Full 二阶语义中的关系变量解释为全部类型正确的谓词。 -/
abbrev Relation {σ : Signature.{u, v, w}}
    (M : FirstOrder.Structure.{u, v, w, x} σ)
    (domains : List σ.SortSymbol) :=
  FirstOrder.Values M.Carrier domains → Prop

structure Env {σ : Signature.{u, v, w}}
    (M : FirstOrder.Structure.{u, v, w, x} σ)
    (objBound objFree : ObjContext.{u, v, w, i} σ)
    (relBound relFree : RelContext.{u, v, w, i} σ) where
  firstOrder : Infinitary.Env M objBound objFree
  boundRel : ∀ {domains}, relBound domains → Relation M domains
  freeRel : ∀ {domains}, relFree domains → Relation M domains

namespace Env

def pushObj {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {objBound objFree : ObjContext.{u, v, w, i} σ}
    {relBound relFree : RelContext.{u, v, w, i} σ}
    (env : Env M objBound objFree relBound relFree)
    (sort : σ.SortSymbol) (value : M.Carrier sort) :
    Env M (Infinitary.Context.extend objBound (oneSort sort)) objFree
      relBound relFree where
  firstOrder := env.firstOrder.pushBlock (oneSort sort) (fun _ => value)
  boundRel := env.boundRel
  freeRel := env.freeRel

def pushRel {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {objBound objFree : ObjContext.{u, v, w, i} σ}
    {relBound relFree : RelContext.{u, v, w, i} σ}
    (env : Env M objBound objFree relBound relFree)
    (domains : List σ.SortSymbol) (relation : Relation M domains) :
    Env M objBound objFree (RelContext.extend relBound domains) relFree where
  firstOrder := env.firstOrder
  boundRel := by
    intro query entry
    cases entry with
    | inl previous => exact env.boundRel previous
    | inr tagged =>
        cases tagged with
        | up equality =>
            cases equality
            exact relation
  freeRel := env.freeRel

end Env

namespace Formula

/-- Full 二阶满足关系：二阶量词遍历全部类型正确的谓词。 -/
def satisfies {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {objBound objFree : ObjContext.{u, v, w, i} σ}
    {relBound relFree : RelContext.{u, v, w, i} σ}
    (env : Env M objBound objFree relBound relFree) :
    _root_.YesMetaZFC.Logic.SecondOrder.Formula σ
      objBound objFree relBound relFree → Prop
  | .falsum => False
  | .truth => True
  | .rel relation arguments =>
      M.relInterp relation (Infinitary.Arguments.eval env.firstOrder arguments)
  | .equal left right =>
      Infinitary.Term.eval env.firstOrder left =
        Infinitary.Term.eval env.firstOrder right
  | .relBound relation arguments =>
      env.boundRel relation (Infinitary.Arguments.eval env.firstOrder arguments)
  | .relFree relation arguments =>
      env.freeRel relation (Infinitary.Arguments.eval env.firstOrder arguments)
  | .neg body => ¬ satisfies env body
  | .conj left right => satisfies env left ∧ satisfies env right
  | .disj left right => satisfies env left ∨ satisfies env right
  | .imp left right => satisfies env left → satisfies env right
  | .iff left right => satisfies env left ↔ satisfies env right
  | .forallObj sort body =>
      ∀ value : M.Carrier sort, satisfies (env.pushObj sort value) body
  | .existsObj sort body =>
      ∃ value : M.Carrier sort, satisfies (env.pushObj sort value) body
  | .forallRel domains body =>
      ∀ relation : Relation M domains,
        satisfies (env.pushRel domains relation) body
  | .existsRel domains body =>
      ∃ relation : Relation M domains,
        satisfies (env.pushRel domains relation) body

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
