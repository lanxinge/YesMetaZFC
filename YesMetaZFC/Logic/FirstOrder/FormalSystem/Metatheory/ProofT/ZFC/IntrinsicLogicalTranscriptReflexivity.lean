import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# ZFC 内在等式自反 transcript

这里直接以 typed Quine term 构造等式自反行，不经过旧 token 或具名变量层。
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

structure EqualityReflexivityRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  term : Term σ [] free sort

def equality_reflexivity_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) : SetOpenTerm [] :=
  equality_reflexivity_axiom_code_term
    (quote_term row.term : SetOpenTerm [])

def equality_reflexivity_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) : SetOpenTerm [] :=
  equality_reflexivity_certificate_code_term
    (quote_term row.term : SetOpenTerm [])

def equality_reflexivity_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (equality_reflexivity_row_branch_code row)

theorem intrinsic_zfc_equality_reflexivity_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_reflexivity_row_formula_code row ∈ₘ
        syntax_formula_code_set_term := by
  exact intrinsic_zfc_quote_formula_mem
    (.equal row.term row.term)

theorem intrinsic_zfc_equality_reflexivity_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_reflexivity_row_branch_code row ∈ₘ ωₘ := by
  apply godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
  · exact intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 11
  · exact intrinsic_zfc_quote_term_mem_omega row.term

theorem intrinsic_zfc_equality_reflexivity_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code (equality_reflexivity_row_branch_code row) ∈ₘ ωₘ := by
  exact intrinsic_zfc_logical_certificate_mem_omega _
    (intrinsic_zfc_equality_reflexivity_branch_certificate_member row)

theorem intrinsic_zfc_equality_reflexivity_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (row : EqualityReflexivityRow σ sort free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      equality_reflexivity_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code (equality_reflexivity_row_branch_code row))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ equality_reflexivity_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at certificates
    (equality_reflexivity_row_branch_code row) index hBranchBound hLogicalCertificate
  have hLine := quote_equality_reflexivity_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates row.term index hPayloadBound hLogicalCertificate
    (by simpa [equality_reflexivity_row_formula_code] using hCurrent)
  have hFormulaAt := intrinsic_zfc_quote_formula_code_at (Γ := Γ)
    (.equal row.term row.term)
  simpa only [row_instance] using FirstOrder.Derives.conj_intro
    (formula_condition_of_equality checked_verifier _ _
      (Metatheory.Derives.equality_symm hCurrent) hFormulaAt) hLine

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
