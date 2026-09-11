import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRoundOneSpecifications
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalBasic
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalArithmetic

/-! # 无穷、归纳核与最小归纳集的原公理

归纳性始终是模型内部的集合性质，不加入外部标准性假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalInfinity
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer PureFinalBasic
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem inductive_value (hℳ : Theory.Models ℳ theory) (source : Carrier ℳ) :
    (E hℳ).relation .isInductiveSet (.cons source .nil) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsInductive source :=
  ((PureCompletedStage.realizes hℳ).relation .isInductiveSet (.cons source .nil)).symm.trans
    (PureStageSemantics.inductive_correct hℳ source)

theorem core_semantics (𝒩 : Structure.{0,0,0,x} S) (source candidate : 𝒩.Carrier s) :
    (inductive_core_spec (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons candidate (.cons source .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, Mem 𝒩 element candidate ↔ Mem 𝒩 element source ∧
        ∀ inductiveSet, 𝒩.relInterp .isInductiveSet (.cons inductiveSet .nil) →
          Mem 𝒩 element inductiveSet := by
  simp only [inductive_core_spec, membership_specification, inductive_core_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem inductive_core (hℳ : Theory.Models ℳ theory) :
    inductive_core_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro candidate source
  intro _
  apply ((PureCompletedStage.realizes hℳ).function .inductiveCore (.cons source .nil) candidate).symm.trans
  apply (PureRelationSetOperations.inductiveCore_correct hℳ candidate source).trans
  apply Iff.trans ?_ (core_semantics (E hℳ).model source candidate).symm
  apply forall_congr'
  intro element
  apply iff_congr Iff.rfl
  apply and_congr Iff.rfl
  apply forall_congr'
  intro inductiveSet
  exact imp_congr (inductive_value hℳ inductiveSet).symm Iff.rfl

theorem omega (hℳ : Theory.Models ℳ theory) :
    omega_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro candidate
  have hCore := ((PureCompletedStage.realizes hℳ).function .inductiveCore (.cons candidate .nil)
    (F hℳ .inductiveCore (.cons candidate .nil))).mpr rfl
  change candidate = F hℳ .omega .nil ↔
    (E hℳ).relation .isInductiveSet (.cons candidate .nil) ∧
      F hℳ .inductiveCore (.cons candidate .nil) = candidate
  exact ((PureCompletedStage.realizes hℳ).function .omega .nil candidate).symm.trans
    ((PureRoundOneSpecifications.omega_core_spec hℳ candidate _ hCore).trans
      (and_congr (inductive_value hℳ candidate).symm Iff.rfl))

theorem infinity_semantics (𝒩 : Structure.{0,0,0,x} S) :
    infinity_axiom.satisfies (Env.empty : Env 𝒩 [] []) ↔
      ∃ source, Mem 𝒩 (𝒩.funcInterp .emptySet .nil) source ∧
        ∀ input, Mem 𝒩 input source →
          Mem 𝒩 (𝒩.funcInterp .successor (.cons input .nil)) source := by
  simp only [infinity_axiom, infinity_condition, Formula.satisfies_existsFreeTop,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem infinity (hℳ : Theory.Models ℳ theory) :
    infinity_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (infinity_semantics (E hℳ).model).mpr
  refine ⟨PureNaturalInduction.omega hℳ, ?_, ?_⟩
  · change membership ℳ (PureFinalArithmetic.z (E hℳ).model) (PureNaturalInduction.omega hℳ)
    rw [PureFinalArithmetic.zero_final]
    exact PureArithmeticSpecifications.zero_mem hℳ
  · intro input hInput
    change membership ℳ (PureFinalArithmetic.suc (E hℳ).model input) (PureNaturalInduction.omega hℳ)
    rw [PureFinalArithmetic.succ_final]
    exact PureArithmeticSpecifications.succ_mem hℳ hInput

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalInfinity
