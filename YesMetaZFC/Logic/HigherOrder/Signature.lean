/-!
# 简单类型高阶签名

高阶自动化不修改已经稳定的一阶签名，而是在基础 sort 上自由生成箭头 sort。
函数与关系符号可以直接声明高阶参数，因此证书层无需先做 lambda lifting。
-/

namespace YesMetaZFC
namespace Logic
namespace HigherOrder

universe u v w

/-- 由基础 sort 自由生成的简单类型。 -/
inductive SimpleType (Base : Type u) where
  | base (symbol : Base)
  | arrow (domain codomain : SimpleType Base)
  deriving Repr, DecidableEq

namespace SimpleType

/-- 多元函数类型的右结合编码。 -/
def arrowFrom {Base : Type u} :
    List (SimpleType Base) → SimpleType Base → SimpleType Base
  | [], result => result
  | argument :: rest, result => .arrow argument (arrowFrom rest result)

/-- 若当前 sort 是箭头类型，则返回定义域和值域。 -/
def arrow? {Base : Type u} :
    SimpleType Base → Option (SimpleType Base × SimpleType Base)
  | .arrow domain codomain => some (domain, codomain)
  | .base _ => none

end SimpleType

/-- 简单类型高阶签名。符号本身仍由外部稳定编号或对象类型提供。 -/
structure Signature where
  BaseSort : Type u
  FuncSymbol : Type v
  RelSymbol : Type w
  funcDomain : FuncSymbol → List (SimpleType BaseSort)
  funcCodomain : FuncSymbol → SimpleType BaseSort
  /-- 是否为函数外延负规则保留的显式差异见证符号。 -/
  isFunctionExtensionalityWitness : FuncSymbol → Bool
  relDomain : RelSymbol → List (SimpleType BaseSort)

namespace Signature

/-- 函数字符的未柯里化元数。 -/
def funcArity (σ : Signature) (symbol : σ.FuncSymbol) : Nat :=
  (σ.funcDomain symbol).length

/-- 关系字符的元数。 -/
def relArity (σ : Signature) (symbol : σ.RelSymbol) : Nat :=
  (σ.relDomain symbol).length

/-- 把函数符号视为可继续被 `apply` 消费的柯里化类型。 -/
def funcSort (σ : Signature) (symbol : σ.FuncSymbol) : SimpleType σ.BaseSort :=
  SimpleType.arrowFrom (σ.funcDomain symbol) (σ.funcCodomain symbol)

end Signature

end HigherOrder
end Logic
end YesMetaZFC
