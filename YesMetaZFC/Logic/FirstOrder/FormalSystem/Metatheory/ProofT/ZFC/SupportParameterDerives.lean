import YesMetaZFC.Automation.ObjectTermDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportParameters
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel

/-! # 十一类参数支撑公理入口的具体正负表示

表示原 indexed 参数证书的合法性，输入码为原始树码。
公理结论的构造、全称闭合与传输包连接是后续独立阶段。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SupportParameter
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation SupportParameters
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def condition {bound free : SetContext} (kind : Kind) (input : SetTerm bound free) : SetFormula bound free :=
  ObjectTermSyntax.parameterCondition (numₘ(kind.arity)) input

theorem condition_delta0 {bound free : SetContext} (kind : Kind) (input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition kind input) := ObjectTermSyntax.parameter_delta0 _ _

/-- 实际原公理分支的成功直接给出数值树码上的普通推导。 -/
theorem positive (kind : Kind) (input : Tree) (h : actual kind input = true) :
    Derives intrinsic_zfc_theory [] (condition kind (numₘ(treeValue input) : Code)) := by
  rw [actual_eq_decode] at h
  obtain ⟨parameters, hParameters⟩ := Option.isSome_iff_exists.mp h
  exact ObjectTermSyntax.parameter_positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity kind.arity input parameters hParameters

theorem negative (kind : Kind) (input : Tree) (h : actual kind input = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition kind (numₘ(treeValue input) : Code)) := by
  rw [actual_eq_decode] at h
  exact ObjectTermSyntax.parameter_negative intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport kind.arity input
    (Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp h))

theorem positive_at_tree (kind : Kind) (input : Tree) (h : actual kind input = true) :
    Derives intrinsic_zfc_theory [] (condition kind (IntrinsicQuotation.tree input)) := by
  rw [actual_eq_decode] at h
  obtain ⟨parameters, hParameters⟩ := Option.isSome_iff_exists.mp h
  exact ObjectTermSyntax.parameter_positive_at_tree intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport intrinsic_zfc_contains_power
    intrinsic_zfc_arithmetic_support.contains_infinity kind.arity input parameters hParameters

theorem negative_at_tree (kind : Kind) (input : Tree) (h : actual kind input = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition kind (IntrinsicQuotation.tree input)) := by
  rw [actual_eq_decode] at h
  exact ObjectTermSyntax.parameter_negative_at_tree intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport kind.arity input
    (Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp h))

/-- 任意自由上下文和类型正确的实际项，不增加自由变量数量或项深度上限。 -/
theorem encoded_positive (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    Derives intrinsic_zfc_theory [] (condition kind (IntrinsicQuotation.tree (SyntaxParameters.encode parameters))) :=
  positive_at_tree kind _ (by rw [actual_eq_decode, SyntaxParameters.decode_encode]; rfl)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SupportParameter
