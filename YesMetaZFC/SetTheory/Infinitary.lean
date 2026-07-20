import YesMetaZFC.Logic.Infinitary
import YesMetaZFC.SetTheory.Definitional.Project

/-!
# 纯集合论的 `L_{κ,κ}` 扩展

有限一阶语言继续固定在 `Type 0`。本模块只让无穷连接词和量词块的索引族进入
universe-polymorphic 层；定义原子沿有限嵌入保持为原子，不在这里展开定义体。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Infinitary

universe i u

abbrev Kappa := Logic.Infinitary.Kappa

/-- 无穷语言项；依然没有函数符号。 -/
inductive Term (Γ : Type i) where
  | bound : Γ → Term Γ
  | free : FreeVarId → Term Γ

namespace Term

def rename {Γ Δ : Type i} (indexMap : Γ → Δ) : Term Γ → Term Δ
  | .bound entry => .bound (indexMap entry)
  | .free id => .free id

def weaken {Γ : Type i} (term : Term Γ) : Term (Sum Γ Unit) :=
  term.rename Sum.inl

def newest {Γ : Type i} : Term (Sum Γ Unit) :=
  .bound (.inr ())

end Term

/--
纯集合论 `L_{κ,κ}` 公式。

有限量词单独保留，保证有限公式无需额外证明 `Unit` 是 `κ`-small。
-/
inductive Formula (κ : Kappa.{i}) : Type i → Type (i + 1) where
  | falsum {Γ : Type i} : Formula κ Γ
  | truth {Γ : Type i} : Formula κ Γ
  | mem {Γ : Type i} : Term Γ → Term Γ → Formula κ Γ
  | atom {Γ : Type i} (symbol : Definitional.Project.CoreAtom) :
      (Fin (Definitional.Project.coreSignature.arity symbol) → Term Γ) →
        Formula κ Γ
  | neg {Γ : Type i} : Formula κ Γ → Formula κ Γ
  | conj {Γ : Type i} : Formula κ Γ → Formula κ Γ → Formula κ Γ
  | disj {Γ : Type i} : Formula κ Γ → Formula κ Γ → Formula κ Γ
  | imp {Γ : Type i} : Formula κ Γ → Formula κ Γ → Formula κ Γ
  | iff {Γ : Type i} : Formula κ Γ → Formula κ Γ → Formula κ Γ
  | forallE {Γ : Type i} : Formula κ (Sum Γ Unit) → Formula κ Γ
  | existsE {Γ : Type i} : Formula κ (Sum Γ Unit) → Formula κ Γ
  | iConj {Γ I : Type i} :
      κ.Small I → (I → Formula κ Γ) → Formula κ Γ
  | iDisj {Γ I : Type i} :
      κ.Small I → (I → Formula κ Γ) → Formula κ Γ
  | forallBlock {Γ I : Type i} :
      κ.Small I → Formula κ (Sum Γ I) → Formula κ Γ
  | existsBlock {Γ I : Type i} :
      κ.Small I → Formula κ (Sum Γ I) → Formula κ Γ

namespace Formula

private def sumMap {Γ Δ I : Type i} (indexMap : Γ → Δ) :
    Sum Γ I → Sum Δ I
  | .inl entry => .inl (indexMap entry)
  | .inr index => .inr index

private def sumMapUnit {Γ Δ : Type i} (indexMap : Γ → Δ) :
    Sum Γ Unit → Sum Δ Unit
  | .inl entry => .inl (indexMap entry)
  | .inr marker => .inr marker

def rename {κ : Kappa.{i}} {Γ Δ : Type i}
    (indexMap : Γ → Δ) : Formula κ Γ → Formula κ Δ
  | .falsum => .falsum
  | .truth => .truth
  | .mem left right => .mem (left.rename indexMap) (right.rename indexMap)
  | .atom symbol arguments =>
      .atom symbol fun entry => (arguments entry).rename indexMap
  | .neg formula => .neg (rename indexMap formula)
  | .conj left right => .conj (rename indexMap left) (rename indexMap right)
  | .disj left right => .disj (rename indexMap left) (rename indexMap right)
  | .imp left right => .imp (rename indexMap left) (rename indexMap right)
  | .iff left right => .iff (rename indexMap left) (rename indexMap right)
  | .forallE body => .forallE (rename (sumMapUnit indexMap) body)
  | .existsE body => .existsE (rename (sumMapUnit indexMap) body)
  | .iConj hSmall family => .iConj hSmall fun index => rename indexMap (family index)
  | .iDisj hSmall family => .iDisj hSmall fun index => rename indexMap (family index)
  | .forallBlock hSmall body => .forallBlock hSmall (rename (sumMap indexMap) body)
  | .existsBlock hSmall body => .existsBlock hSmall (rename (sumMap indexMap) body)

private def pairArguments {Γ : Type i} (left right : Term Γ) :
    Fin 2 → Term Γ :=
  Fin.cases left <| Fin.cases right Fin.elim0

/-- 无穷层中的原生外延等同原子。 -/
def extensionalEq {κ : Kappa.{i}} {Γ : Type i}
    (left right : Term Γ) : Formula κ Γ :=
  .atom .extensionalEq (pairArguments left right)

/-- 无穷层中的原生子集原子。 -/
def subset {κ : Kappa.{i}} {Γ : Type i}
    (left right : Term Γ) : Formula κ Γ :=
  .atom .subset (pairArguments left right)

end Formula

/-- 无穷语言环境。 -/
structure Env (ℳ : SetTheory.Structure.{u}) (Γ : Type i) where
  bound : Γ → ℳ.Domain
  free : FreeVarId → ℳ.Domain

namespace Env

def push {ℳ : SetTheory.Structure.{u}} {Γ I : Type i}
    (env : Env ℳ Γ) (values : I → ℳ.Domain) : Env ℳ (Sum Γ I) where
  bound
    | .inl entry => env.bound entry
    | .inr index => values index
  free := env.free

def pushOne {ℳ : SetTheory.Structure.{u}} {Γ : Type i}
    (env : Env ℳ Γ) (value : ℳ.Domain) : Env ℳ (Sum Γ Unit) where
  bound
    | .inl entry => env.bound entry
    | .inr _ => value
  free := env.free

end Env

namespace Term

def eval {ℳ : SetTheory.Structure.{u}} {Γ : Type i}
    (env : Env ℳ Γ) : Term Γ → ℳ.Domain
  | .bound entry => env.bound entry
  | .free id => env.free id

end Term

namespace Formula

/-- 纯集合论 `L_{κ,κ}` 的 Tarski 语义。 -/
def satisfies {κ : Kappa.{i}} {ℳ : SetTheory.Structure.{u}}
    {Γ : Type i} (env : Env ℳ Γ) : Formula κ Γ → Prop
  | .falsum => False
  | .truth => True
  | .mem left right => ℳ.mem (left.eval env) (right.eval env)
  | .atom symbol arguments =>
      Definitional.Project.Semantics.interpretation.atom symbol
        (fun entry => (arguments entry).eval env) env.free
  | .neg formula => ¬ satisfies env formula
  | .conj left right => satisfies env left ∧ satisfies env right
  | .disj left right => satisfies env left ∨ satisfies env right
  | .imp left right => satisfies env left → satisfies env right
  | .iff left right => satisfies env left ↔ satisfies env right
  | .forallE body =>
      ∀ value, satisfies (env.pushOne value) body
  | .existsE body =>
      ∃ value, satisfies (env.pushOne value) body
  | .iConj _ family => ∀ index, satisfies env (family index)
  | .iDisj _ family => ∃ index, satisfies env (family index)
  | .forallBlock _ body =>
      ∀ values, satisfies (env.push values) body
  | .existsBlock _ body =>
      ∃ values, satisfies (env.push values) body

end Formula

namespace FinitaryEmbedding

private def finSuccToSum {depth : Nat} :
    ULift.{i, 0} (Fin (depth + 1)) → Sum (ULift.{i, 0} (Fin depth)) Unit
  | ⟨entry⟩ => Fin.cases (.inr ()) (fun previous => .inl ⟨previous⟩) entry

def term {depth : Nat} :
    Definitional.Project.Term depth → Term (ULift.{i, 0} (Fin depth))
  | .bound entry => .bound ⟨entry⟩
  | .free id => .free id

def formula {κ : Kappa.{i}} {depth : Nat} :
    Definitional.Project.Formula 1 depth →
      Formula κ (ULift.{i, 0} (Fin depth))
  | .falsum => .falsum
  | .truth => .truth
  | .mem left right => .mem (term left) (term right)
  | .atom symbol _ arguments =>
      .atom symbol fun entry => term (arguments entry)
  | .neg source => .neg (formula source)
  | .conj left right => .conj (formula left) (formula right)
  | .disj left right => .disj (formula left) (formula right)
  | .imp left right => .imp (formula left) (formula right)
  | .iff left right => .iff (formula left) (formula right)
  | .forallE body =>
      .forallE ((formula body).rename finSuccToSum)
  | .existsE body =>
      .existsE ((formula body).rename finSuccToSum)

end FinitaryEmbedding

end Infinitary
end SetTheory
end YesMetaZFC
