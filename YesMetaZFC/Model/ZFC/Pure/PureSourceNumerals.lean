import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosser
import YesMetaZFC.Automation.NaturalProofPresentation

/-! # 任意原模型与其规范重扩张的基础数码对应

这里只使用原公理已经给出的全域定义，逐值比较空集和后继，再对外部有限 numeral
作归纳。未假定任意原模型的算术函数或递归谓词在所有参数上等于规范扩张。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumerals
open Nonlogical.BasicSetTheory PureFinalArithmetic
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
attribute [local irreducible] ReducedNaturalProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

noncomputable abbrev canonical (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :=
  (PureCompletedStage.expansion (PureZFCModels.reduct_models h𝒩)).model

/-- 原空集定义约束任意源模型中的空集常量。 -/
theorem empty_spec (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    ∀ element, ¬ mem 𝒩 element (z 𝒩) := by
  have hProof : Derives intrinsic_zfc_theory [] (empty_set_spec (∅ₘ : SetTerm [] [])) :=
    Derives.theory_weaken intrinsic_zfc_arithmetic_support.toArithmeticSupport.contains_empty_set
      empty_set_term_spec_derives
  have h := hProof.semantically_entails 𝒩 h𝒩
  simp only [Formula.TrueIn, empty_set_spec, membership_specification, empty_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies, not_true_eq_false] at h
  change (∀ element, mem 𝒩 element (z 𝒩) ↔ False) at h
  exact fun element hMember => (h element).mp hMember

/-- 后继成员规格由原规范后继推导取得，无额外模型约束。 -/
theorem successor_spec (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (input element : 𝒩.Carrier .set) :
    mem 𝒩 element (suc 𝒩 input) ↔ mem 𝒩 element input ∨ element = input := by
  have hProof := Derives.theory_weaken
    intrinsic_zfc_arithmetic_support.toArithmeticSupport.contains_successor
    (successor_term_membership_iff (Γ := [])
      (.fvar .here : SetOpenTerm [.set,.set]) (.fvar (.there .here)))
  have h := hProof.sound h𝒩 (templateEnv (.cons input (.cons element .nil)))
    (by intro formula hMember; cases hMember)
  change (mem 𝒩 element (suc 𝒩 input) ↔ element = input ∨ mem 𝒩 element input) at h
  exact h.trans or_comm

theorem empty_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    z 𝒩 = z (canonical h𝒩) :=
  (PureFinalBasic.empty_value (PureZFCModels.reduct_models h𝒩) (z 𝒩)).mpr (empty_spec h𝒩)

theorem successor_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (input : 𝒩.Carrier .set) : suc 𝒩 input = suc (canonical h𝒩) input := by
  apply PureModel.extensionality (PureZFCModels.reduct_models h𝒩)
  intro element
  exact (successor_spec h𝒩 input element).trans
    (PureFinalBasic.successor_value (PureZFCModels.reduct_models h𝒩) input element).symm

/-- 任意标准 numeral 的值在约化再规范扩张后保持。 -/
theorem numeral_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (number : Nat) :
    (numₘ(number) : SetTerm [] []).eval (Env.empty : Env 𝒩 [] []) =
      (numₘ(number) : SetTerm [] []).eval (Env.empty : Env (canonical h𝒩) [] []) := by
  induction number with
  | zero => exact empty_agrees h𝒩
  | succ number ih =>
    change suc 𝒩 ((numₘ(number) : SetTerm [] []).eval Env.empty) =
      suc (canonical h𝒩) ((numₘ(number) : SetTerm [] []).eval Env.empty)
    rw [successor_agrees h𝒩, ih]

/-- 任意当前 quotation 的值对应归约到标准 numeral；不展开巨大数值。 -/
theorem quotation_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence) :
    (IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] []) =
      (IntrinsicQuotation.quote formula).eval (Env.empty : Env (canonical h𝒩) [] []) := by
  have hCode := IntrinsicQuotation.quote_evaluate intrinsic_zfc_certificate_core formula
  exact (hCode.semantically_entails 𝒩 h𝒩).trans
    ((numeral_agrees h𝒩 (IntrinsicQuotation.value formula)).trans
      (hCode.semantically_entails (canonical h𝒩)
        (PureZFCModels.models (PureZFCModels.reduct_models h𝒩))).symm)

/-- 全部标准证明码上的正负表示足以给出该实例在两模型中的真值一致。 -/
theorem proof_numeral_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (number : Nat) (formula : SetSentence) :
    (ReducedNaturalProofPresentation.presentation.code number formula).TrueIn 𝒩 ↔
      (ReducedNaturalProofPresentation.presentation.code number formula).TrueIn (canonical h𝒩) :=
  _root_.YesMetaZFC.Automation.NaturalProofPresentation.models_agree
    ReducedNaturalProofPresentation.presentation h𝒩
    (PureZFCModels.models (PureZFCModels.reduct_models h𝒩)) number formula

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumerals
