import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.NaturalProofPresentation

/-! # 模型内部自然数上的完整证明表示

在原完整证明图上要求输入证明码属于 ω；检查器、普通推导的可靠性与完备性以及
全部标准码的正负表示沿用已验证构造。ω 可以含有外部非标准自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedNaturalProofPresentation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x

noncomputable def presentation :
    Delta1ProofPresentation intrinsic_zfc_theory intrinsic_zfc_theory :=
  _root_.YesMetaZFC.Automation.NaturalProofPresentation.presentation
    ReducedProofPresentation.presentation (fun number =>
      Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_infinity
        (infinity_finite_numeral_mem_omega number))

/-- 任意接受的对象证明码都属于模型内部 ω。 -/
theorem natural_of_satisfied {𝒩 : Structure.{0,0,0,x} signature}
    {bound free : SetContext} (env : Env 𝒩 bound free)
    (code conclusion : SetTerm bound free)
    (h : (presentation.graph.condition code conclusion).satisfies env) :
    (code ∈ₘ ωₘ).satisfies env :=
  _root_.YesMetaZFC.Automation.NaturalProofPresentation.natural_of_satisfied
    ReducedProofPresentation.presentation.graph env code conclusion h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedNaturalProofPresentation
