import YesMetaZFC.SetTheory.Definitional.Project

/-!
# 项目原子核的公式层级与模式

模式公式继续使用 intrinsically scoped 的 bound 参数。项目原子已经是 proof-carrying 的
语法叶节点，因此 `CoreAtom.extensionalEq` 和 `CoreAtom.subset` 可以直接作为 `Delta0`
原子使用，不需要重新打开定义体。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

namespace Formula

/-- 项目集合论 `Delta0` 公式的 proof-carrying 分类。 -/
inductive IsDelta0 : {depth : Nat} → Formula 1 depth → Prop where
  | falsum {depth : Nat} : IsDelta0 (.falsum : Formula 1 depth)
  | truth {depth : Nat} : IsDelta0 (.truth : Formula 1 depth)
  | mem {depth : Nat} (left right : Term depth) :
      IsDelta0 (.mem left right)
  | atom {depth : Nat} (symbol : CoreAtom)
      (hStage : coreSignature.stage symbol < 1)
      (arguments : TermVector (coreSignature.arity symbol) depth) :
      IsDelta0 (.atom symbol hStage arguments)
  | neg {depth : Nat} {formula : Formula 1 depth} :
      IsDelta0 formula → IsDelta0 (.neg formula)
  | conj {depth : Nat} {left right : Formula 1 depth} :
      IsDelta0 left → IsDelta0 right → IsDelta0 (.conj left right)
  | disj {depth : Nat} {left right : Formula 1 depth} :
      IsDelta0 left → IsDelta0 right → IsDelta0 (.disj left right)
  | imp {depth : Nat} {left right : Formula 1 depth} :
      IsDelta0 left → IsDelta0 right → IsDelta0 (.imp left right)
  | iff {depth : Nat} {left right : Formula 1 depth} :
      IsDelta0 left → IsDelta0 right → IsDelta0 (.iff left right)
  | forallMem {depth : Nat} (set : Term depth)
      {body : Formula 1 (depth + 1)} :
      IsDelta0 body → IsDelta0 (forallMem set body)
  | existsMem {depth : Nat} (set : Term depth)
      {body : Formula 1 (depth + 1)} :
      IsDelta0 body → IsDelta0 (existsMem set body)

end Formula

/-- 一元项目公式模式；index `0` 是元素，后续 index 是参数。 -/
structure UnarySchema (parameterCount : Nat) where
  body : Formula 1 (parameterCount + 1)
  freeClosed : body.FreeClosed

/-- 带 `Delta0` 证据的一元项目公式模式。 -/
structure Delta0UnarySchema (parameterCount : Nat)
    extends UnarySchema parameterCount where
  delta0 : body.IsDelta0

/-- 二元项目公式模式；index `0` 是输出，index `1` 是输入，后续 index 是参数。 -/
structure BinarySchema (parameterCount : Nat) where
  body : Formula 1 (parameterCount + 2)
  freeClosed : body.FreeClosed

/-- 带 `Delta0` 证据的二元项目公式模式。 -/
structure Delta0BinarySchema (parameterCount : Nat)
    extends BinarySchema parameterCount where
  delta0 : body.IsDelta0

namespace UnarySchema

/-- 一元 schema 在参数环境下表示的纸面类。 -/
def denote {ℳ : Structure.{u}} {parameterCount : Nat}
    (schema : UnarySchema parameterCount)
    (env : Env ℳ parameterCount) (value : ℳ.Domain) : Prop :=
  Formula.satisfies (env.push value) schema.body

end UnarySchema

namespace BinarySchema

/-- 二元 schema 在参数环境下表示的纸面二元类关系。 -/
def denote {ℳ : Structure.{u}} {parameterCount : Nat}
    (schema : BinarySchema parameterCount)
    (env : Env ℳ parameterCount)
    (input output : ℳ.Domain) : Prop :=
  Formula.satisfies ((env.push input).push output) schema.body

end BinarySchema

end Project
end Definitional
end SetTheory
end YesMetaZFC
