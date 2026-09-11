import YesMetaZFC.SetTheory.Definitional.Project.Syntax

/-!
# 项目公式层级与 schema 的纯语法层

本模块只记录 `Delta0` 分类和一元、二元 schema 数据，不赋予它们模型解释。
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
  freeClosed : body.FreeClosed := by simp -implicitDefEqProofs [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]

/-- 带 `Delta0` 证据的一元项目公式模式。 -/
structure Delta0UnarySchema (parameterCount : Nat)
    extends UnarySchema parameterCount where
  delta0 : body.IsDelta0

/-- 二元项目公式模式；index `0` 是输出，index `1` 是输入，后续 index 是参数。 -/
structure BinarySchema (parameterCount : Nat) where
  body : Formula 1 (parameterCount + 2)
  freeClosed : body.FreeClosed := by simp -implicitDefEqProofs [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]

/-- 带 `Delta0` 证据的二元项目公式模式。 -/
structure Delta0BinarySchema (parameterCount : Nat)
    extends BinarySchema parameterCount where
  delta0 : body.IsDelta0

attribute [simp] UnarySchema.freeClosed BinarySchema.freeClosed

end Project
end Definitional
end SetTheory
end YesMetaZFC
