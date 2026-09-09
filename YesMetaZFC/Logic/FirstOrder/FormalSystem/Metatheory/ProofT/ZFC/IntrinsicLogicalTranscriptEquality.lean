import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# ZFC 内在逻辑 transcript

等式替换的公式码、分支证书和逐行条件。公式的良构性与载体成员直接复用实际
quotation 的通用正确性；证书字段消费源项与源公式的内部自然数界。
行条件保留真实替换结果、证书上界及两个坐标等式。
-/

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

structure EqualitySubstitutionRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  left : Term σ [] free sort
  right : Term σ [] free sort
  body : Formula σ [sort] free

def equality_substitution_row_left_result
    {σ : Signature} {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : Formula σ [] free :=
  Formula.instantiateTop row.left row.body

def equality_substitution_row_right_result
    {σ : Signature} {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : Formula σ [] free :=
  Formula.instantiateTop row.right row.body

def equality_substitution_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : SetOpenTerm [] :=
  intrinsic_equality_substitution_axiom_code_term
    (quote_term row.left : SetOpenTerm [])
    (quote_term row.right : SetOpenTerm [])
    (quote (equality_substitution_row_left_result row) : SetOpenTerm [])
    (quote (equality_substitution_row_right_result row) : SetOpenTerm [])

def equality_substitution_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : SetOpenTerm [] :=
  equality_substitution_certificate_code_term
    (quote_term row.left : SetOpenTerm [])
    (quote_term row.right : SetOpenTerm [])
    (quote row.body : SetOpenTerm [])
    (quote (equality_substitution_row_left_result row) : SetOpenTerm [])
    (quote (equality_substitution_row_right_result row) : SetOpenTerm [])

def equality_substitution_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (equality_substitution_row_branch_code row)

theorem intrinsic_zfc_equality_substitution_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_substitution_row_formula_code row ∈ₘ
        syntax_formula_code_set_term := by
  exact intrinsic_zfc_quote_formula_mem
    (.imp (.equal row.left row.right)
      (.imp (equality_substitution_row_left_result row)
        (equality_substitution_row_right_result row)))

theorem intrinsic_zfc_equality_substitution_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_substitution_row_branch_code row ∈ₘ ωₘ := by
  apply godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
  · exact intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 10
  · apply godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
    · exact intrinsic_zfc_quote_term_mem_omega row.left
    · apply godel_pairing_mem_omega_of_extends
        godel_pairing_core_theory_subset_intrinsic_zfc_theory
      · exact intrinsic_zfc_quote_term_mem_omega row.right
      · apply godel_pairing_mem_omega_of_extends
          godel_pairing_core_theory_subset_intrinsic_zfc_theory
        · exact intrinsic_zfc_quote_formula_mem_omega row.body
        · apply godel_pairing_mem_omega_of_extends
            godel_pairing_core_theory_subset_intrinsic_zfc_theory
          · exact intrinsic_zfc_quote_formula_mem_omega (equality_substitution_row_left_result row)
          · exact intrinsic_zfc_quote_formula_mem_omega (equality_substitution_row_right_result row)

theorem intrinsic_zfc_equality_substitution_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code (equality_substitution_row_branch_code row) ∈ₘ ωₘ := by
  exact intrinsic_zfc_logical_certificate_mem_omega _
    (intrinsic_zfc_equality_substitution_branch_certificate_member row)

theorem intrinsic_zfc_equality_substitution_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (row : EqualitySubstitutionRow σ sort free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      equality_substitution_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code (equality_substitution_row_branch_code row))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ equality_substitution_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at certificates
    (equality_substitution_row_branch_code row) index hBranchBound hLogicalCertificate
  have hLine := quote_equality_substitution_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates row.left row.right row.body index hPayloadBound
    hLogicalCertificate
    (by simpa [equality_substitution_row_formula_code,
      equality_substitution_row_left_result,
      equality_substitution_row_right_result] using hCurrent)
  have hFormulaAt := intrinsic_zfc_quote_formula_code_at (Γ := Γ)
    (.imp (.equal row.left row.right)
      (.imp (equality_substitution_row_left_result row)
        (equality_substitution_row_right_result row)))
  simpa only [row_instance] using FirstOrder.Derives.conj_intro
    (formula_condition_of_equality checked_verifier _ _
      (Metatheory.Derives.equality_symm hCurrent) hFormulaAt) hLine

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
