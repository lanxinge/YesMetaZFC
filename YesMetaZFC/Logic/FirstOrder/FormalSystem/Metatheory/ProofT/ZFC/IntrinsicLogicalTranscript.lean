import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptEquality
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptReflexivity

/-!
# ZFC 内在逻辑 transcript

五类逻辑证明行的统一 transcript：特化、全称分配、空泛全称、等式替换和等式自反。
各类行提供实际公式码、证书码和逐行条件，公共行列表接口负责两列的取值与装配。
具体规则的语法、作用域和证书条件均由各自的行正确性接口保证。
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


inductive LogicalTranscriptRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  | specialization (row : SpecializationRow σ sort free)
  | forall_distribution (row : ForallDistributionRow σ sort free)
  | vacuous_forall (row : VacuousForallRow σ sort free)
  | equality_substitution (row : EqualitySubstitutionRow σ sort free)
  | equality_reflexivity (row : EqualityReflexivityRow σ sort free)

def logical_transcript_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) : SetOpenTerm [] :=
  match row with
  | .specialization row => specialization_row_formula_code row
  | .forall_distribution row => forall_distribution_row_formula_code row
  | .vacuous_forall row => vacuous_forall_row_formula_code row
  | .equality_substitution row => equality_substitution_row_formula_code row
  | .equality_reflexivity row => equality_reflexivity_row_formula_code row

def logical_transcript_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) : SetOpenTerm [] :=
  match row with
  | .specialization row =>
      specialization_certificate_code_term
        (quote row.body : SetOpenTerm [])
        (quote_term row.replacement : SetOpenTerm [])
        (quote (Formula.instantiateTop row.replacement row.body) : SetOpenTerm [])
  | .forall_distribution row =>
      forall_distribution_certificate_code_term
        (quote row.antecedent : SetOpenTerm [])
        (quote row.consequent : SetOpenTerm [])
  | .vacuous_forall row => vacuous_forall_row_branch_code row
  | .equality_substitution row => equality_substitution_row_branch_code row
  | .equality_reflexivity row => equality_reflexivity_row_branch_code row

def logical_transcript_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (logical_transcript_row_branch_code row)

theorem intrinsic_zfc_logical_transcript_row_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_transcript_row_formula_code row ∈ₘ
        syntax_formula_code_set_term := by
  cases row with
  | specialization row =>
      simpa [logical_transcript_row_formula_code] using!
        intrinsic_zfc_specialization_formula_code_member
          row.body row.replacement
  | forall_distribution row =>
      simpa [logical_transcript_row_formula_code] using!
        intrinsic_zfc_forall_distribution_formula_code_member
          row.antecedent row.consequent
  | vacuous_forall row =>
      simpa [logical_transcript_row_formula_code,
        vacuous_forall_row_formula_code] using
        intrinsic_zfc_vacuous_forall_formula_code_member row.body
  | equality_substitution row =>
      simpa [logical_transcript_row_formula_code] using
        intrinsic_zfc_equality_substitution_formula_code_member row
  | equality_reflexivity row =>
      simpa [logical_transcript_row_formula_code] using
        intrinsic_zfc_equality_reflexivity_formula_code_member row

theorem intrinsic_zfc_logical_transcript_row_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_transcript_row_certificate_code row ∈ₘ ωₘ := by
  cases row with
  | specialization row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_specialization_certificate_member
          row.body row.replacement
  | forall_distribution row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_forall_distribution_certificate_member
          row.antecedent row.consequent
  | vacuous_forall row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code,
        vacuous_forall_row_branch_code] using
        intrinsic_zfc_vacuous_forall_certificate_member row.body
  | equality_substitution row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_substitution_certificate_member row
  | equality_reflexivity row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_reflexivity_certificate_member row

theorem intrinsic_zfc_logical_transcript_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (row : LogicalTranscriptRow σ sort free)
    (sequence certificates : SetOpenTerm [])
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      logical_transcript_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_transcript_row_certificate_code row)
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        logical_transcript_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  cases row with
  | specialization row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_specialization_row_instance
          sequence certificates row.body row.replacement index
          hBranchBound hLogicalCertificate hCurrent
  | forall_distribution row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_forall_distribution_row_instance
          sequence certificates row.antecedent row.consequent index
          hBranchBound hLogicalCertificate hCurrent
  | vacuous_forall row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_vacuous_forall_row_instance
          sequence certificates row index
          hBranchBound hLogicalCertificate hCurrent
  | equality_substitution row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_substitution_row_instance
          sequence certificates row index
          hBranchBound hLogicalCertificate hCurrent
  | equality_reflexivity row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_reflexivity_row_instance
          sequence certificates row index
          hBranchBound hLogicalCertificate hCurrent

theorem intrinsic_zfc_logical_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (LogicalTranscriptRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map logical_transcript_row_formula_code))
        (standard_sequence (rows.map logical_transcript_row_certificate_code)) := by
  apply intro_of_mapped_rows intrinsic_zfc_row_support checked_verifier rows
    logical_transcript_row_formula_code logical_transcript_row_certificate_code hNonempty
    (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega rows.length)
  · intro row _
    exact intrinsic_zfc_logical_transcript_row_formula_code_member row
  · intro row _
    exact intrinsic_zfc_logical_transcript_row_certificate_member row
  · intro index hIndex hCurrent hLogicalCertificate
    let row := rows[index]
    have hBranchBound :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          logical_transcript_row_branch_code row ∈ₘ ωₘ := by
      cases row with
      | specialization row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_specialization_branch_certificate_member
              row.body row.replacement
      | forall_distribution row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_forall_distribution_branch_certificate_member
              row.antecedent row.consequent
      | vacuous_forall row =>
          simpa [logical_transcript_row_branch_code,
            vacuous_forall_row_branch_code] using
            intrinsic_zfc_vacuous_forall_branch_certificate_member row.body
      | equality_substitution row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_equality_substitution_branch_certificate_member row
      | equality_reflexivity row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_equality_reflexivity_branch_certificate_member row
    exact intrinsic_zfc_logical_transcript_row_instance
      row _ _ index hBranchBound hLogicalCertificate hCurrent

theorem intrinsic_zfc_vacuous_forall_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (VacuousForallRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map vacuous_forall_row_formula_code))
        (standard_sequence (rows.map vacuous_forall_row_certificate_code)) := by
  let logicalRows : List (LogicalTranscriptRow σ sort free) :=
    rows.map LogicalTranscriptRow.vacuous_forall
  have hLogicalNonempty : logicalRows ≠ [] := by
    simpa [logicalRows] using hNonempty
  simpa [logicalRows, Function.comp_def] using!
    intrinsic_zfc_logical_transcript_condition logicalRows hLogicalNonempty

theorem intrinsic_zfc_equality_substitution_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (rows : List (EqualitySubstitutionRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map equality_substitution_row_formula_code))
        (standard_sequence (rows.map equality_substitution_row_certificate_code)) := by
  let logicalRows : List (LogicalTranscriptRow σ sort free) :=
    rows.map LogicalTranscriptRow.equality_substitution
  have hLogicalNonempty : logicalRows ≠ [] := by
    simpa [logicalRows] using hNonempty
  simpa [logicalRows, Function.comp_def] using!
    intrinsic_zfc_logical_transcript_condition logicalRows hLogicalNonempty

theorem intrinsic_zfc_equality_reflexivity_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (rows : List (EqualityReflexivityRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map equality_reflexivity_row_formula_code))
        (standard_sequence (rows.map equality_reflexivity_row_certificate_code)) := by
  let logicalRows : List (LogicalTranscriptRow σ sort free) :=
    rows.map LogicalTranscriptRow.equality_reflexivity
  have hLogicalNonempty : logicalRows ≠ [] := by
    simpa [logicalRows] using hNonempty
  simpa [logicalRows, Function.comp_def] using!
    intrinsic_zfc_logical_transcript_condition logicalRows hLogicalNonempty

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
