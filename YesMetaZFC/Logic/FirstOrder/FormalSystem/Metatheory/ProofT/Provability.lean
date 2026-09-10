import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier

/-! # 普通可证明性与第一可导性条件

沿用完整 AST quotation 和既有证明图。D1 从标准证明码的正表示获得，
不要求对象模型的自然数域标准，也不假定理论一致或可靠。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.Delta1ProofPresentation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
variable {Traw Thilbert : SetTheory}

/-- 使用当前证明图的普通可证明性句子。 -/
def provable (P : Delta1ProofPresentation Traw Thilbert)
    (formula : SetSentence) : SetSentence :=
  P.graph.provability (IntrinsicQuotation.quote formula)

/-- 对象一致性句子：不存在矛盾的证明码。 -/
def consistency (P : Delta1ProofPresentation Traw Thilbert) : SetSentence :=
  ¬ₘ P.provable Formula.falsum

theorem provable_sigma1 (P : Delta1ProofPresentation Traw Thilbert)
    (formula : SetSentence) : Formula.IsSigma1 set_levy_bound (P.provable formula) :=
  P.graph.provability_sigma1 _

theorem consistency_pi1 (P : Delta1ProofPresentation Traw Thilbert) :
    Formula.IsPi1 set_levy_bound P.consistency :=
  P.graph.neg_provability_pi1 _

/-- D1：每个普通推导都能在表示理论内证明自己的可证明性。 -/
theorem necessitation (P : Delta1ProofPresentation Traw Thilbert)
    {formula : SetSentence} (hDerives : Derives Thilbert [] formula) :
    Derives Traw [] (P.provable formula) := by
  obtain ⟨code, hCode⟩ := P.realize hDerives
  unfold provable Delta0ProofGraph.provability
  apply Derives.exists_intro (numₘ(code))
  rw [FormulaTemplate.apply_two_instantiateTop_bvar]
  exact hCode

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.Delta1ProofPresentation
