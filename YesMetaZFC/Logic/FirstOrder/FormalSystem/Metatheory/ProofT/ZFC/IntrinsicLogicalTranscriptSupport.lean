import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open QuineEncoding
open StructuredCertificateCondition
open IntrinsicLogicalCertificate
open IntrinsicCheckedLine
open IntrinsicCheckedSequence
open IntrinsicFirstOrderLogicalLine
open IntrinsicVerifier

open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 实际 quotation 的载体成员事实一次性提升到目标上下文。 -/
theorem intrinsic_zfc_quote_formula_mem
    {σ : Signature} [QuotationNumbering σ] {bound free : SortContext σ}
    {Γ : Context signature []} (formula : Formula σ bound free) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      (quote formula : SetOpenTerm []) ∈ₘ syntax_formula_code_set_term :=
  FirstOrder.Derives.context_weaken (by simp)
    (FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      (intrinsic_syntax_carrier_quote_formula_mem formula))

/-- 实际 quotation 的深度识别，不再按每条逻辑公理重建构造树。 -/
theorem intrinsic_zfc_quote_formula_code_at
    {σ : Signature} [QuotationNumbering σ] {bound free : SortContext σ}
    {Γ : Context signature []} (formula : Formula σ bound free) :
    Γ ⊢ₘ[intrinsic_zfc_theory] formula_code_atₘ(numₘ(bound.length), quote formula) :=
  FirstOrder.Derives.context_weaken (by simp)
    (FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      (quote_formula_code_at formula))

/-- quotation 的内部自然数界随任意源公式直接取得。 -/
theorem intrinsic_zfc_quote_formula_mem_omega
    {σ : Signature} [QuotationNumbering σ] {bound free : SortContext σ}
    {Γ : Context signature []} (formula : Formula σ bound free) :
    Γ ⊢ₘ[intrinsic_zfc_theory] (quote formula : SetOpenTerm []) ∈ₘ ωₘ :=
  FirstOrder.Derives.context_weaken (by simp)
    (FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      (formula_code_at_code_mem_of_derives _ _ (quote_formula_code_at formula)))

/-- quotation 的内部自然数界随任意源项直接取得。 -/
theorem intrinsic_zfc_quote_term_mem_omega
    {σ : Signature} [QuotationNumbering σ] {bound free : SortContext σ}
    {sort : σ.SortSymbol} {Γ : Context signature []} (term : Term σ bound free sort) :
    Γ ⊢ₘ[intrinsic_zfc_theory] (quote_term term : SetOpenTerm []) ∈ₘ ωₘ :=
  FirstOrder.Derives.context_weaken (by simp)
    (FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      (term_code_at_code_mem_of_derives _ _ (quote_term_code_at term)))

/-- 逻辑证书的公共外壳保持内部自然数码域。 -/
theorem intrinsic_zfc_logical_certificate_mem_omega
    {free : SetContext} {Γ : Context signature free}
    (certificate : SetOpenTerm free)
    (hCertificate : Γ ⊢ₘ[intrinsic_zfc_theory] certificate ∈ₘ ωₘ) :
    Γ ⊢ₘ[intrinsic_zfc_theory] logical_certificate_code certificate ∈ₘ ωₘ :=
  godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory _ _
    (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0) hCertificate

theorem intrinsic_zfc_certificate_payload_bound_of_at
    {free : SetContext} {Γ : Context signature free}
    (certificates certificate : SetOpenTerm free)
    (index : Nat)
    (hCertificateBound : Γ ⊢ₘ[intrinsic_zfc_theory] certificate ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ logical_certificate_code certificate) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      certificate_payload_bound certificates (numₘ(index)) certificate := by
  unfold certificate_payload_bound
  have hZero : Γ ⊢ₘ[intrinsic_zfc_theory]
      (numₘ(0) : SetOpenTerm free) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hNodeEq : Γ ⊢ₘ[intrinsic_zfc_theory]
      godel_pairₘ(numₘ(0), certificate) ≐ₘ
        certificates ·ₘ numₘ(index) := by
    simpa [logical_certificate_code] using
      Metatheory.Derives.equality_symm hLogicalCertificate
  have hNodeEqS : Γ ⊢ₘ[intrinsic_zfc_theory]
      Sₘ(godel_pairₘ(numₘ(0), certificate)) ≐ₘ
        Sₘ(certificates ·ₘ numₘ(index)) :=
    successor_term_congr_of_equality
      (godel_pairₘ(numₘ(0), certificate))
      (certificates ·ₘ numₘ(index)) hNodeEq
  have hCoordinateAxiom : Γ ⊢ₘ[intrinsic_zfc_theory]
      ((numₘ(0) ∈ₘ (ωₘ : SetOpenTerm free)) ∧ₘ
        (certificate ∈ₘ ωₘ)) ⟶ₘ
      ((numₘ(0) ∈ₘ Sₘ(godel_pairₘ(numₘ(0), certificate))) ∧ₘ
        (certificate ∈ₘ Sₘ(godel_pairₘ(numₘ(0), certificate)))) :=
    FirstOrder.Derives.theory_weaken
      natural_addition_bound_theory_subset_intrinsic_zfc_theory
      (natural_godel_pairing_coordinate_bound_instance_derives
        (Γ := Γ) (numₘ(0)) certificate)
  have hPayloadNode : Γ ⊢ₘ[intrinsic_zfc_theory]
      certificate ∈ₘ Sₘ(godel_pairₘ(numₘ(0), certificate)) :=
    FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.imp_elim hCoordinateAxiom
        (FirstOrder.Derives.conj_intro hZero hCertificateBound)
  exact FirstOrder.Derives.iff_elim_left
    (membership_right_iff_of_equality
      certificate
      (Sₘ(godel_pairₘ(numₘ(0), certificate)))
      (Sₘ(certificates ·ₘ numₘ(index))) hNodeEqS)
    hPayloadNode

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
