import YesMetaZFC.Automation.ObjectTransformRanking
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornRanking

/-! # 原四种语法变换的内部正反射

先完成查表阶段，再按输入码同时处理项、参数列和公式。
模式、深度、参数表及输入输出均可非标准，递归量词仍使用原提升规则。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation PureSourceTraceComposition ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem transform_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectSyntaxTransform.rules) root) :
    HornProv 𝒩 ObjectSyntaxTransform.rules root :=
  horn_valid_positive h𝒩 _ _ ObjectHornRanking.transform_valid hr hg

theorem transform_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (root : SetOpenTerm free) (hr : TermEvaluates env values root)
    (hg : (ObjectHorn.condition ObjectSyntaxTransform.rules root).satisfies env) :
    ProvableCode 𝒩 (formula 𝒩 values (ObjectHorn.condition ObjectSyntaxTransform.rules root)) :=
  (horn_term_transfer h𝒩 env values hv ObjectSyntaxTransform.rules root hr).mpr
    (transform_positive h𝒩 hr.1 ((horn_satisfies env ObjectSyntaxTransform.rules root).mp hg))

theorem transform_positive_derives : Derives intrinsic_zfc_theory []
    (ObjectHornReflection.onNaturals ReducedProofPresentation.presentation.graph ObjectSyntaxTransform.rules) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  change (ObjectHornReflection.onNaturals ReducedProofPresentation.presentation.graph ObjectSyntaxTransform.rules).satisfies (Env.empty : Env 𝒩 [] [])
  unfold ObjectHornReflection.onNaturals
  rw [forallNatural_satisfies]
  intro root hr
  rw [implication_satisfies, horn_satisfies, hornAt_satisfies]
  exact transform_positive h𝒩 hr

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
