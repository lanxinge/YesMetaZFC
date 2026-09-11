import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.Project
import YesMetaZFC.SetTheory.Axioms.ZFC

/-!
# ZFC 的内在证明内核

ZFC 公理直接以 Project 闭句的内在 FormalSystem 像进入目标理论；证明编码所需的
算术、有限序列和结构语法支撑则来自公共内在证明核。两者只在理论边界处做一次并，
不经过已退役的旧对象编码或原始回放支撑层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open QuineEncoding

set_option autoImplicit false

/-- Project ZFC 公理在内在 FormalSystem 闭句中的直接像。 -/
def intrinsic_zfc_axiom_theory : SetTheory :=
  fun formula =>
    ∃ sentence,
      _root_.YesMetaZFC.SetTheory.ZFC sentence ∧
        formula = project_sentence sentence

/-- ZFC 公理像与公共内在证明支撑组成的唯一 raw 目标理论。 -/
def intrinsic_zfc_theory : SetTheory :=
  Theory.union intrinsic_zfc_axiom_theory intrinsic_proof_theory

derive_theory_subset intrinsic_zfc_axiom_theory ⊆ intrinsic_zfc_theory

derive_theory_subset intrinsic_proof_theory ⊆ intrinsic_zfc_theory

derive_theory_subset intrinsic_syntax_carrier_theory ⊆ intrinsic_zfc_theory

derive_theory_subset expression_encoding_theory ⊆ intrinsic_zfc_theory

derive_theory_subset formal_language_encoding_theory ⊆ intrinsic_zfc_theory

derive_theory_subset natural_addition_bound_theory ⊆ intrinsic_zfc_theory

derive_theory_subset godel_pairing_core_theory ⊆ intrinsic_zfc_theory

derive_theory_subset power_set_operator_theory ⊆ intrinsic_zfc_theory => intrinsic_zfc_contains_power

/-- 任意 Project ZFC 公理的内在像都是新目标理论公理。 -/
theorem intrinsic_zfc_axiom_mem
    {sentence : _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence}
    (hSentence : _root_.YesMetaZFC.SetTheory.ZFC sentence) :
    intrinsic_zfc_theory (project_sentence sentence) :=
  Or.inl ⟨sentence, hSentence, rfl⟩

/-- ZFC 目标理论上的有限算术求值支撑。 -/
theorem intrinsic_zfc_arithmetic_support :
    ArithmeticEvaluationSupport intrinsic_zfc_theory :=
  intrinsic_proof_arithmetic_support.theory_weaken
    intrinsic_proof_theory_subset_intrinsic_zfc_theory

/-- ZFC 目标理论上的证明行承载支撑。 -/
theorem intrinsic_zfc_row_support :
    IntrinsicProofRowSupport intrinsic_zfc_theory :=
  intrinsic_proof_row_support_unified.theory_weaken
    intrinsic_proof_theory_subset_intrinsic_zfc_theory

/-- ZFC 目标理论上的直接结构码支撑。 -/
theorem intrinsic_zfc_structural_sequence_support :
    StructuralSequenceCodeSupport intrinsic_zfc_theory :=
  intrinsic_proof_structural_sequence_support.theory_weaken
    intrinsic_proof_theory_subset_intrinsic_zfc_theory

/-- ZFC 目标理论上的有限证书核心。 -/
theorem intrinsic_zfc_certificate_core :
    CertificateCore intrinsic_zfc_theory where
  toFiniteCore :=
    ArithmeticSupport.finite_core
      intrinsic_zfc_arithmetic_support.toArithmeticSupport
  pair_value := fun left right =>
    finite_numeral_godel_pair_value
      intrinsic_zfc_arithmetic_support left right

/-- ZFC 新证明链消费的完整内在支撑。 -/
theorem intrinsic_zfc_proof_support :
    IntrinsicProofSupport intrinsic_zfc_theory :=
  IntrinsicProofSupport.ofCoreAndRows
    intrinsic_zfc_certificate_core intrinsic_zfc_row_support

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
