import YesMetaZFC.SetTheory.Axioms.KP

/-! # 含完整成员归纳模式的 KP

仓库的 KP 保持原有集合正则公理。KPi 显式加入全部实际公式的成员归纳，
用于可容许递归及非标准模型；这是一层理论扩张，不把外部良基性作为模型条件。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project

namespace Axioms.Schema

def mi_core_m {n} (φ : UnarySchema n) : Formula 1 n :=
  .imp (.forallE (.imp (Formula.forallMem .newest (φ.body.rename BoundEmbedding.unaryUnderOne)) φ.body))
    (.forallE φ.body)

def mi_axiom {n} (φ : UnarySchema n) : Sentence :=
  Sentence.forallClosure (mi_core_m φ) (by
    simp -implicitDefEqProofs [mi_core_m, Definitional.Formula.FreeClosed])

end Axioms.Schema

namespace KPi
inductive Axiom : Definitional.Project.Theory where
  | kp {s : Sentence} : KP s → Axiom s
  | induction {n} (φ : UnarySchema n) : Axiom (Axioms.Schema.mi_axiom φ)
end KPi

abbrev KPi : Definitional.Project.Theory := KPi.Axiom

end YesMetaZFC.SetTheory
