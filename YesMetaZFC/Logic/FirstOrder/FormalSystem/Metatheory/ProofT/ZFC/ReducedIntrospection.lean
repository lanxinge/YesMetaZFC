import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalVerificationReflection

/-! # 当前普通可证明性的第三可导性条件 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
open Nonlogical.BasicSetTheory
set_option autoImplicit false

/-- D3：原验证矩阵的任意内部轨迹反射给出无附加反射假设的自省。 -/
theorem introspection (φ : SetSentence) :
    Derives intrinsic_zfc_theory [] (.imp (provable φ) (provable (provable φ))) := by
  apply introspection_of_verification_reflection φ
  intro 𝒩 h𝒩 input hi ht
  obtain ⟨named, hn, hg⟩ := PureSourceNumeralSyntax.total h𝒩 hi
  exact ⟨named, hn, hg, InternalNumeralReflection.verification_reflection h𝒩 φ hi hn hg ht⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
