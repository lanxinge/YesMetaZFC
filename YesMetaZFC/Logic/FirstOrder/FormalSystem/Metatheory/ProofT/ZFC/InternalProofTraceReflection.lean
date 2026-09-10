import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalCheckedRanking
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalProofRowReflection

/-! # 原证明树任意内部轨迹的正反射

消去外部有限骨架、逐条连边证明及局部查询反射输入。
归纳覆盖全部内部自然数证明码，包括外部非标准的编码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation
open PureSourceTraceComposition ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem proof_trace_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition) root) :
    CheckedProv 𝒩 ObjectProofTree.rules ReducedProofPresentation.rowTest.condition root :=
  checked_valid_positive h𝒩 ObjectProofTree.rules ReducedProofPresentation.rowTest.condition
    (InternalProofQueryReflection.currentRow h𝒩) (PureSourceLocalTests.currentRow h𝒩)
    ObjectCheckedReflection.proofPlan ObjectCheckedReflection.proof_valid hr hg

theorem proof_trace_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {root : SetOpenTerm free} (hr : TermEvaluates env values root)
    (ht : (ObjectCheckedTrace.condition ObjectProofTree.rules ReducedProofPresentation.rowTest.condition root).satisfies env) :
    ProvableCode 𝒩 (formula 𝒩 values
      (ObjectCheckedTrace.condition ObjectProofTree.rules ReducedProofPresentation.rowTest.condition root)) :=
  (checked_term_transfer h𝒩 env values hv _ _ root hr).mpr
    (proof_trace_positive h𝒩 hr.1 ((checked_satisfies _ _ _ _).mp ht))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
open Nonlogical.BasicSetTheory PureFinalArithmetic InternalNumeralReflection
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem proofTrace (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free : SetContext} {root : SetTerm bound free} (hr : Evaluates 𝒩 root) :
    Positive 𝒩 (ObjectCheckedTrace.condition ObjectProofTree.rules ReducedProofPresentation.rowTest.condition root) := by
  intro target env values hv bs fs hb hf ht
  simp only [ObjectCheckedTrace.condition, ObjectTrace.condition_substituteMapped] at ht ⊢
  exact proof_trace_values h𝒩 env values hv (hr env values hv bs fs hb hf) ht

theorem proof_trace_positive_derives :
    Derives intrinsic_zfc_theory [] (ObjectPositiveReflection.onNaturals ReducedProofPresentation.presentation.graph
      (ObjectCheckedTrace.condition ObjectProofTree.rules ReducedProofPresentation.rowTest.condition (.fvar .here))) :=
  positive_derives _ (fun _ h𝒩 => proofTrace h𝒩 (fvar _))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
