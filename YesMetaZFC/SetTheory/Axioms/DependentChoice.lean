import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Kuratowski

/-! # 依赖选择的原句子与 ZF＋DC

关系、初值和整条序列均为模型内部集合；长度取模型自己的 ω。
公理保留指定初值，便于直接构造稠密集中的下降链。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project

def dc_chain_m (𝒞 : OrderedPairConvention) {d} (ω X R a g : Term d) : Formula 1 d :=
  .conj (Formula.isFunctionFromTo 𝒞 g ω X) (.conj
    (.forallE (.imp (.forallE (.neg (.mem .newest (.bound 1))))
      (Formula.orderedPairMem 𝒞 .newest a.weaken g.weaken)))
    (.forallE (.forallE (.forallE (.forallE (.imp (Formula.isSuccessor (.bound 2) (.bound 3))
      (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) g.weaken.weaken.weaken.weaken)
        (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest g.weaken.weaken.weaken.weaken)
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken.weaken.weaken)))))))))
derive_free_closed dc_chain_m

def dc_m (𝒞 : OrderedPairConvention) {d} (ω : Term d) : Formula 1 d :=
  .forallE (.forallE (.forallE (.imp (.mem .newest (.bound 2))
    (.imp (.forallE (.imp (.mem .newest (.bound 3)) (.existsE (.conj
      (.mem .newest (.bound 4)) (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))))))
      (.existsE (dc_chain_m 𝒞 ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest))))))
derive_free_closed dc_m

def Axioms.dc_axiom : Sentence := Sentence.ofFormula
  (.forallE (.imp (Formula.isOmega .newest) (dc_m kpair_convention_l .newest)))
  (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])

namespace ZFDC
inductive Axiom : Theory where
  | zf {s : Sentence} : ZF s → Axiom s
  | dc : Axiom Axioms.dc_axiom
end ZFDC

abbrev ZFDC : Theory := ZFDC.Axiom

end YesMetaZFC.SetTheory
