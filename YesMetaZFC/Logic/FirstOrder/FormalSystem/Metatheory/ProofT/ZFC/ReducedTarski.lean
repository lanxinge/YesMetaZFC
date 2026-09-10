import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Tarski
import YesMetaZFC.Automation.ObjectTarskiFixedPoint
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedRosser

/-! # 原支撑理论上的塔斯基真不可定义定理

任意候选一元公式均有实际反例句。句法版仅假定原理论一致；语义版覆盖
任意原理论模型及全部宿主闭句，不将模型内部语法或自然数假定为外部标准。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedTarski
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe x

/-- 用当前 quotation 将候选一元公式应用于闭句的编码。 -/
def predicate_m (P : FormulaTemplate.Unary) (φ : SetSentence) : SetSentence :=
  P (IntrinsicQuotation.quote φ)

def liarSentence_m (P : FormulaTemplate.Unary) : SetSentence :=
  ObjectTarski.liarSentence_m intrinsic_zfc_core.code_domain P

theorem liar_fixed_point_m (P : FormulaTemplate.Unary) :
    Derives intrinsic_zfc_theory []
      (liarSentence_m P ↔ₘ ¬ₘ predicate_m P (liarSentence_m P)) :=
  ObjectTarski.liar_fixed_point_m ReducedRosser.diagonalSupport P

/-- 每个候选真谓词都有一个在原理论中可反驳的真值等价式。 -/
theorem liar_refutes_m (P : FormulaTemplate.Unary) :
    Derives intrinsic_zfc_theory []
      (¬ₘ (predicate_m P (liarSentence_m P) ↔ₘ liarSentence_m P)) :=
  Tarski.liar_refutes_m (liar_fixed_point_m P)

theorem biconditional_unprovable_m (P : FormulaTemplate.Unary)
    (hT : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    ¬ Derives intrinsic_zfc_theory []
      (predicate_m P (liarSentence_m P) ↔ₘ liarSentence_m P) :=
  Tarski.biconditional_unprovable_m (liar_fixed_point_m P) hT

/-- 一致的原支撑理论中，没有满足全部可证真值等价式的一元公式。 -/
theorem undefinable_syntax_m
    (hT : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    ¬ ∃ P : FormulaTemplate.Unary, Tarski.TruthSchema_m intrinsic_zfc_theory (predicate_m P) := by
  rintro ⟨P, h⟩
  exact Tarski.not_truth_schema_m (liar_fixed_point_m P) hT h

/-- 任意原模型中，没有在全部闭句上正确的无参数真谓词。 -/
theorem undefinable_semantics_m {ℳ : Structure.{0,0,0,x} signature}
    (hℳ : Theory.Models ℳ intrinsic_zfc_theory) :
    ¬ ∃ P : FormulaTemplate.Unary, Tarski.DefinesTruth_m ℳ (predicate_m P) := by
  rintro ⟨P, h⟩
  exact Tarski.not_defines_truth_m hℳ (liar_fixed_point_m P) h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedTarski
