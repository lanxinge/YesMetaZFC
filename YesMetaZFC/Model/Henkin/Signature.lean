import YesMetaZFC.Logic.FirstOrder.FunctionMap

/-!
# Henkin 常量签名

每个排序加入一列按 `Nat` 编号的零元函数。它们只用于完备性构造中的见证，不进入
原始理论；原签名的函数与关系通过 `base` 分支保留。由于见证常量是签名构造子，
选择新见证不再需要扫描公式中的自由变量编号。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

inductive HenkinFunc (σ : Signature.{u, v, w}) where
  | base : σ.FuncSymbol → HenkinFunc σ
  | witness : σ.SortSymbol → Nat → HenkinFunc σ

/-- 签名投影参与隐式参数类型的比较，需在隐式透明度下展开。 -/
@[implicit_reducible]
def henkinSignature (σ : Signature.{u, v, w}) : Signature where
  SortSymbol := σ.SortSymbol
  FuncSymbol := HenkinFunc σ
  RelSymbol := σ.RelSymbol
  funcDomain
    | .base function => σ.funcDomain function
    | .witness _ _ => []
  funcCodomain
    | .base function => σ.funcCodomain function
    | .witness sort _ => sort
  relDomain := σ.relDomain

namespace HenkinSignature

variable {σ : Signature.{u, v, w}}

/-- Henkin 常量扩张后的签名。 -/
abbrev HSignature (σ : Signature.{u, v, w}) := henkinSignature σ

mutual

/-- 将原签名项提升到 Henkin 签名。 -/
def liftTerm {bound free : SortContext σ} :
    {sort : σ.SortSymbol} → Term σ bound free sort →
      Term (henkinSignature σ) bound free sort
  | _, .bvar entry => .bvar entry
  | _, .fvar entry => .fvar entry
  | _, .app function arguments =>
      .app (HenkinFunc.base function) (liftArguments arguments)

/-- 将原签名参数列提升到 Henkin 签名。 -/
def liftArguments {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} → Arguments σ bound free sorts →
      Arguments (henkinSignature σ) bound free sorts
  | _, .nil => .nil
  | _, .cons head tail =>
      .cons (liftTerm head) (liftArguments tail)

/-- 将原签名公式提升到 Henkin 签名。 -/
def liftFormula {bound free : SortContext σ} :
    Formula σ bound free → Formula (henkinSignature σ) bound free
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments => .rel relation (liftArguments arguments)
  | .equal left right => .equal (liftTerm left) (liftTerm right)
  | .neg body => .neg (liftFormula body)
  | .conj left right => .conj (liftFormula left) (liftFormula right)
  | .disj left right => .disj (liftFormula left) (liftFormula right)
  | .imp left right => .imp (liftFormula left) (liftFormula right)
  | .iff left right => .iff (liftFormula left) (liftFormula right)
  | .forallE sort body => .forallE sort (liftFormula body)
  | .existsE sort body => .existsE sort (liftFormula body)

end

@[simp] theorem liftTerm_bvar {bound free : SortContext σ}
    {sort : σ.SortSymbol} (entry : Variable bound sort) :
    liftTerm (.bvar entry : Term σ bound free sort) = .bvar entry :=
  by cases entry <;> rfl

@[simp] theorem liftTerm_fvar {bound free : SortContext σ}
    {sort : σ.SortSymbol} (entry : Variable free sort) :
    liftTerm (.fvar entry : Term σ bound free sort) = .fvar entry :=
  by cases entry <;> rfl

@[simp] theorem liftTerm_app {bound free : SortContext σ}
    (function : σ.FuncSymbol)
    (arguments : Arguments σ bound free (σ.funcDomain function)) :
    liftTerm (.app function arguments) =
      Term.app (HenkinFunc.base function) (liftArguments arguments) :=
  rfl

@[simp] theorem liftArguments_nil {bound free : SortContext σ} :
    liftArguments (.nil : Arguments σ bound free []) = .nil :=
  rfl

@[simp] theorem liftArguments_cons {bound free : SortContext σ}
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (head : Term σ bound free sort)
    (tail : Arguments σ bound free sorts) :
    liftArguments (.cons head tail) =
      .cons (liftTerm head) (liftArguments tail) :=
  rfl

@[simp] theorem liftFormula_falsum {bound free : SortContext σ} :
    liftFormula (.falsum : Formula σ bound free) =
      (.falsum : Formula (henkinSignature σ) bound free) :=
  by simp [liftFormula]

@[simp] theorem liftFormula_truth {bound free : SortContext σ} :
    liftFormula (.truth : Formula σ bound free) =
      (.truth : Formula (henkinSignature σ) bound free) :=
  by simp [liftFormula]

@[simp] theorem liftFormula_rel {bound free : SortContext σ}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation)) :
    liftFormula (.rel relation arguments) =
      Formula.rel (σ := henkinSignature σ) relation
        (liftArguments arguments) :=
  rfl

@[simp] theorem liftFormula_equal {bound free : SortContext σ}
    {sort : σ.SortSymbol} (left right : Term σ bound free sort) :
    liftFormula (.equal left right) =
      Formula.equal (σ := henkinSignature σ)
        (liftTerm left) (liftTerm right) :=
  rfl

@[simp] theorem liftFormula_neg {bound free : SortContext σ}
    (body : Formula σ bound free) :
    liftFormula (.neg body) = .neg (liftFormula body) :=
  rfl

@[simp] theorem liftFormula_conj {bound free : SortContext σ}
    (left right : Formula σ bound free) :
    liftFormula (.conj left right) =
      .conj (liftFormula left) (liftFormula right) :=
  rfl

@[simp] theorem liftFormula_disj {bound free : SortContext σ}
    (left right : Formula σ bound free) :
    liftFormula (.disj left right) =
      .disj (liftFormula left) (liftFormula right) :=
  rfl

@[simp] theorem liftFormula_imp {bound free : SortContext σ}
    (left right : Formula σ bound free) :
    liftFormula (.imp left right) =
      .imp (liftFormula left) (liftFormula right) :=
  rfl

@[simp] theorem liftFormula_iff {bound free : SortContext σ}
    (left right : Formula σ bound free) :
    liftFormula (.iff left right) =
      .iff (liftFormula left) (liftFormula right) :=
  rfl

@[simp] theorem liftFormula_forallE {bound free : SortContext σ}
    (sort : σ.SortSymbol) (body : Formula σ (sort :: bound) free) :
    liftFormula (.forallE sort body) =
      .forallE sort (liftFormula body) :=
  rfl

@[simp] theorem liftFormula_existsE {bound free : SortContext σ}
    (sort : σ.SortSymbol) (body : Formula σ (sort :: bound) free) :
    liftFormula (.existsE sort body) =
      .existsE sort (liftFormula body) :=
  rfl

end HenkinSignature

end FirstOrder
end Logic
end YesMetaZFC
