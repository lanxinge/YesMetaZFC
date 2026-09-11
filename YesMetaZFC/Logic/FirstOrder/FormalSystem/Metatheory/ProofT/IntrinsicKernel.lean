import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuralSequenceCodeConstruction

/-!
# ProofT 内在证明内核装配

本模块把有限算术求值与证明行承载放入同一个对象理论，并直接装配
`CertificateCore`、序列反演和证明行支撑。下游只消费这一份统一合同，不再分别
维护配数计算、有限序列空间与公式码非空性的桥接实例。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 新内在证明内核的统一对象理论。 -/
def intrinsic_proof_theory : SetTheory :=
  Theory.union intrinsic_arithmetic_evaluation_theory
    intrinsic_proof_row_theory

derive_theory_subset intrinsic_arithmetic_evaluation_theory ⊆ intrinsic_proof_theory

derive_theory_subset intrinsic_proof_row_theory ⊆ intrinsic_proof_theory

/-- 统一理论上的有限算术求值支撑。 -/
theorem intrinsic_proof_arithmetic_support :
    ArithmeticEvaluationSupport intrinsic_proof_theory :=
  intrinsic_arithmetic_evaluation_support.theory_weaken
    intrinsic_arithmetic_evaluation_theory_subset_intrinsic_proof_theory

/-- 统一理论上的证明行承载支撑。 -/
theorem intrinsic_proof_row_support_unified :
    IntrinsicProofRowSupport intrinsic_proof_theory :=
  intrinsic_proof_row_support.theory_weaken
    intrinsic_proof_row_theory_subset_intrinsic_proof_theory

derive_theory_subset intrinsic_syntax_carrier_theory ⊆ intrinsic_proof_theory

derive_theory_subset expression_encoding_theory ⊆ intrinsic_proof_theory

derive_theory_subset formal_language_encoding_theory ⊆ intrinsic_proof_theory

derive_theory_subset natural_addition_bound_theory ⊆ intrinsic_proof_theory

/-- 统一内在理论上的直接结构码支撑。 -/
theorem intrinsic_proof_structural_sequence_support :
    StructuralSequenceCodeSupport intrinsic_proof_theory where
  toFiniteSequenceSpaceSupport :=
    intrinsic_proof_row_support_unified.toFiniteSequenceSpaceSupport
  contains_infinity := intrinsic_proof_arithmetic_support.contains_infinity
  contains_godel_pairing_core :=
    intrinsic_proof_arithmetic_support.contains_godel_pairing_core
  contains_natural_addition_bound :=
    natural_addition_bound_theory_subset_intrinsic_proof_theory

derive_theory_subset godel_pairing_core_theory ⊆ intrinsic_proof_theory

/-- 配数计算和有限 numeral 反演组成统一证书核心。 -/
theorem intrinsic_certificate_core :
    CertificateCore intrinsic_proof_theory where
  toFiniteCore :=
    ArithmeticSupport.finite_core
      intrinsic_proof_arithmetic_support.toArithmeticSupport
  pair_value := fun left right =>
    finite_numeral_godel_pair_value
      intrinsic_proof_arithmetic_support left right

/-- 新内在证明链的完整统一支撑。 -/
theorem intrinsic_proof_support :
    IntrinsicProofSupport intrinsic_proof_theory :=
  IntrinsicProofSupport.ofCoreAndRows
    intrinsic_certificate_core intrinsic_proof_row_support_unified

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
