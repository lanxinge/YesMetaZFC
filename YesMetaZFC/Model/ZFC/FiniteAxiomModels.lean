import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteAxiomBasis

/-! # 有限公理基与原理论的模型等价

使用原基的普通推导完备性和内核可靠性；无需额外的模型存在性或强完备性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.FiniteAxiomBasis
open Nonlogical.BasicSetTheory
set_option autoImplicit false
universe x

theorem models_iff {T : SetTheory} (basis : FiniteAxiomBasis T)
    (ℳ : Structure.{0,0,0,x} signature) :
    Theory.Models ℳ basis.theory ↔ Theory.Models ℳ T := by
  constructor
  · intro hBasis sentence hSentence
    exact (basis.complete hSentence).sound hBasis Env.empty (by intro formula h; cases h)
  · intro hTheory sentence hSentence
    exact hTheory sentence (basis.sound sentence hSentence)

/-- 模型验证沿原公理基的组合结构进行，不计算巨大闭公式列表。 -/
theorem singleton_models {ℳ : Structure.{0,0,0,x} signature} {φ : SetSentence}
    (hφ : φ.satisfies (Env.empty : Env ℳ [] [])) :
    Theory.Models ℳ (singleton φ).theory := by
  intro ψ hψ
  have hEqual : ψ = φ := List.mem_singleton.mp hψ
  exact hEqual.symm ▸ hφ

theorem union_models {T U : SetTheory} {left : FiniteAxiomBasis T} {right : FiniteAxiomBasis U}
    {ℳ : Structure.{0,0,0,x} signature}
    (hLeft : Theory.Models ℳ left.theory) (hRight : Theory.Models ℳ right.theory) :
    Theory.Models ℳ (union left right).theory := by
  intro φ hφ
  rcases List.mem_append.mp hφ with h | h
  · exact hLeft φ h
  · exact hRight φ h

theorem insert_models {T : SetTheory} {basis : FiniteAxiomBasis T} {φ : SetSentence}
    {ℳ : Structure.{0,0,0,x} signature}
    (hφ : φ.satisfies (Env.empty : Env ℳ [] [])) (hBasis : Theory.Models ℳ basis.theory) :
    Theory.Models ℳ (insert φ basis).theory :=
  union_models (singleton_models hφ) hBasis

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.FiniteAxiomBasis
