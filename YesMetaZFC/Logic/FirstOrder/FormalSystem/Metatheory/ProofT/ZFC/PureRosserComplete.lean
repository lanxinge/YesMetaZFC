import YesMetaZFC.Model.ZFC.Pure.PureSourceLocalTests

/-! # 当前纯 Rosser 句子的裸 ZFC 独立性

实际局部检查和内部自然数证明图的对应填满最后的 Agreement 前提。
这里的闭句仍是当前源 quotation 所构造 Rosser 句子的实际纯翻译。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosser
open Nonlogical.BasicSetTheory
set_option autoImplicit false

/-- 当前证明图的对应在任意原模型上成立。 -/
theorem agreement : Agreement := by
  apply PureNaturalRosserAgreement.agreement_of_natural_proofs
  intro 𝒩 h𝒩
  exact ⟨PureSourceLocalTests.proof_agreement h𝒩 _, PureSourceLocalTests.proof_agreement h𝒩 _⟩

/-- 只假定裸 ZFC 一致性；句子及其否定都不可推导。 -/
theorem independent
    (hConsistent : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    (¬ Derives PureModel.theory [] sentence) ∧ (¬ Derives PureModel.theory [] (.neg sentence)) :=
  independent_of_agreement agreement hConsistent

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosser
