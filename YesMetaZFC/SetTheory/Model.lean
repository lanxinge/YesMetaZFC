import YesMetaZFC.Automation.HostNormalization.RuleRegistry
import YesMetaZFC.SetTheory.Binding

/-!
# 集合论语法共享的模型底座

本模块只定义对象域、隶属关系、变量环境和外延性合同，不依赖新旧任一公式 AST。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

/-- 集合论结构：非空对象域加一个二元隶属关系。 -/
structure Structure where
  Domain : Type u
  nonempty : Nonempty Domain
  mem : Domain → Domain → Prop

/-- bound/free 变量环境。 -/
structure Env (ℳ : Structure.{u}) (depth : Nat) where
  bound : Fin depth → ℳ.Domain
  free : FreeVarId → ℳ.Domain

namespace Env

/-- 在 de Bruijn 栈顶压入一个新对象。 -/
def push {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (value : ℳ.Domain) : Env ℳ (depth + 1) where
  bound := Fin.cases value env.bound
  free := env.free

/-- 沿 bound-variable 嵌入重索引环境。 -/
def reindex {ℳ : Structure.{u}} {sourceDepth targetDepth : Nat}
    (env : Env ℳ targetDepth)
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    Env ℳ sourceDepth where
  bound := env.bound ∘ indexMap
  free := env.free

/-- 压栈后，提升的索引嵌入与环境重索引交换。 -/
@[prove_auto_norm index]
theorem reindex_push_lift {ℳ : Structure.{u}}
    {sourceDepth targetDepth : Nat}
    (env : Env ℳ targetDepth) (value : ℳ.Domain)
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    (env.push value).reindex (BoundEmbedding.lift indexMap) =
      (env.reindex indexMap).push value := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry <;> rfl
  · rfl

/-- 两次压栈后按 `Fin.succ` 拉回，保留较早压入的对象。 -/
@[prove_auto_norm index]
theorem reindex_push_succ {ℳ : Structure.{u}}
    {depth : Nat} (env : Env ℳ depth)
    (older newer : ℳ.Domain) :
    ((env.push older).push newer).reindex Fin.succ =
      env.push older :=
  rfl

/-- 一元模式主变量下插入 binder 后，拉回环境只保留最新模式对象。 -/
@[prove_auto_norm index]
theorem reindex_push_unaryUnderOne {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (ordinal value : ℳ.Domain) :
    ((env.push ordinal).push value).reindex
        (BoundEmbedding.unaryUnderOne
          (parameterCount := parameterCount)) =
      env.push value := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun parameter => ?_) entry <;> rfl
  · rfl

/-- 一元模式穿过两个局部 binder 后，拉回环境保留模式对象与参数。 -/
@[prove_auto_norm index]
theorem reindex_push_unaryUnderTwo {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (source subset value : ℳ.Domain) :
    (((env.push source).push subset).push value).reindex
        (BoundEmbedding.unaryUnderTwo
          (parameterCount := parameterCount)) =
      env.push value := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun parameter => ?_) entry <;> rfl
  · rfl

/-- 二元模式穿过一个局部 binder 后，拉回环境保留输入、输出与参数。 -/
@[prove_auto_norm index]
theorem reindex_push_binaryUnderOne {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (source input output : ℳ.Domain) :
    ((((env.push source).push input).push output).reindex
        (BoundEmbedding.binaryUnderOne
          (parameterCount := parameterCount))) =
      (env.push input).push output := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry
    · rfl
    · refine Fin.cases ?_ (fun parameter => ?_) previous <;> rfl
  · rfl

/-- 二元模式穿过两个局部 binder 后，拉回环境保留输入、输出与参数。 -/
@[prove_auto_norm index]
theorem reindex_push_binaryUnderTwo {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (source collection input output : ℳ.Domain) :
    (((((env.push source).push collection).push input).push output).reindex
        (BoundEmbedding.binaryUnderTwo
          (parameterCount := parameterCount))) =
      (env.push input).push output := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry
    · rfl
    · refine Fin.cases ?_ (fun parameter => ?_) previous <;> rfl
  · rfl

end Env

/-- 隶属结构的外延性合同。 -/
structure Extensional (ℳ : Structure.{u}) : Prop where
  eq_of_same_members :
    ∀ left right : ℳ.Domain,
      (∀ value, ℳ.mem value left ↔ ℳ.mem value right) →
        left = right

end SetTheory
end YesMetaZFC
