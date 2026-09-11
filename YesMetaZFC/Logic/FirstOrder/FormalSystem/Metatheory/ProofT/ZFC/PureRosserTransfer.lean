import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedRosser
import YesMetaZFC.Model.ZFC.Pure.PureModel
import YesMetaZFC.Model.Interpretation.SemanticTransfer
import YesMetaZFC.Model.Interpretation.RelationalExpansion

/-! # 裸 ZFC Rosser 回传的精确合同

仅有支撑公理的模型解释不足以回传不可证性。本接口另外要求源模型的裸 ZFC 约化，
以及指定 Rosser 句子的真值对应。它不要求全语言往返等价；具体解释和句子对应仍须
由后续定义消去证明提供，本模块不声明合同已经存在。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosserTransfer
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation
set_option autoImplicit false

structure Contract (target : Sentence ℒ) where
  expands : SemanticTransfer.Expands intrinsic_zfc_theory PureModel.theory
  reduction : SemanticTransfer.Reduction intrinsic_zfc_theory PureModel.theory
  agrees : reduction.Agrees ReducedRosser.sentence target

/-- 实际总函数图及全部支撑公理模型证明足以填充扩张这一侧。 -/
theorem expands_of_interpretation (I : RelationalTranslation.Interpretation signature ℒ)
    (hFunctional : ∀ ℳ : Structure.{0, 0, 0, 0} ℒ, Theory.Models ℳ PureModel.theory →
      RelationalTranslation.Functional I ℳ)
    (hModels : ∀ (ℳ : Structure.{0, 0, 0, 0} ℒ) (hℳ : Theory.Models ℳ PureModel.theory),
      Theory.Models (RelationalTranslation.expansion (hFunctional ℳ hℳ)).model intrinsic_zfc_theory) :
    SemanticTransfer.Expands intrinsic_zfc_theory PureModel.theory :=
  fun ℳ hℳ => ⟨(RelationalTranslation.expansion (hFunctional ℳ hℳ)).model, hModels ℳ hℳ⟩

/-- 合同填满后，终局前提精确是裸 ZFC 的一致性。 -/
theorem independent {target : Sentence ℒ} (contract : Contract target)
    (sourceSchedule : Completeness.Henkin.Schedule signature)
    (targetSchedule : Completeness.Henkin.Schedule ℒ)
    (hConsistent : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    (¬ Derives PureModel.theory [] target) ∧ (¬ Derives PureModel.theory [] (.neg target)) :=
  SemanticTransfer.independent sourceSchedule targetSchedule contract.expands contract.reduction
    contract.agrees ReducedRosser.independent hConsistent

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosserTransfer
