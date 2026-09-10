import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalTraceReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofReflection

/-! # 有限轨迹装配与原验证矩阵的精确连接

这里保留原检查器正文及其全部局部行条件。本模块处理给定的有限骨架；
任意内部轨迹的反射见 InternalProofTraceReflection，矩阵连接见 InternalVerificationReflection。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def verificationRoot (φ : SetSentence) : SetOpenTerm [.set] :=
  IntrinsicQuotation.node 1 [(.fvar .here), (IntrinsicQuotation.quote φ : SetOpenTerm []).weakenFree SetSort.set]

theorem verificationMatrix_trace (φ : SetSentence) :
    ReducedProvability.verificationMatrix φ =
      ObjectTrace.condition (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition)
        ωₘ (verificationRoot φ) := by
  unfold ReducedProvability.verificationMatrix
  rw [ReducedProofPresentation.graph_condition, ObjectProofTree.template_apply]
  unfold Formula.openBoundTop
  rw [ObjectProofTree.condition_substituteMapped]
  change ObjectProofTree.condition ReducedProofPresentation.rowTest.condition (.fvar .here)
    (Term.openBoundTop (σ := signature) SetSort.set ((IntrinsicQuotation.quote φ : SetOpenTerm []).weakenBound SetSort.set)) = _
  rw [Term.openBoundTop_weakenBound]
  rfl

/-- 各行检查的内部证明可装配成原 verificationMatrix 的内部证明。 -/
theorem finite_verification (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] [.set]) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (φ : SetSentence) (rows : List (SetOpenTerm [.set])) (hRoot : verificationRoot φ ∈ rows)
    (hRows : ∀ row ∈ rows, TermEvaluates env values row)
    (hSteps : ∀ row ∈ rows, ProvableCode 𝒩 (formula 𝒩 values
      (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition row (ObjectFiniteSet.term rows)))) :
    ProvableCode 𝒩 (formula 𝒩 values (ReducedProvability.verificationMatrix φ)) := by
  rw [verificationMatrix_trace]
  exact checked_trace_values h𝒩 env values hv _ rows hRoot hRows hSteps

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
