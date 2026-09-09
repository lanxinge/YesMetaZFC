import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# ZFC 内在逻辑 transcript

特化、全称分配及空泛全称的公式码、证书码与逐行条件。公式码优先复用实际 quotation
的通用正确性；空泛全称显式保留正文深度提升。两列序列通过公共行列表装配，
单行特化直接作为特化 transcript 的单元素实例。
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

structure SpecializationRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  body : Formula σ [sort] free
  replacement : Term σ [] free sort

def specialization_row_result
    {σ : Signature} {sort : σ.SortSymbol} {free : SortContext σ}
    (row : SpecializationRow σ sort free) : Formula σ [] free :=
  Formula.instantiateTop row.replacement row.body

def specialization_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : SpecializationRow σ sort free) : SetOpenTerm [] :=
  specialization_axiom_code_term
    (quote row.body : SetOpenTerm [])
    (quote (specialization_row_result row) : SetOpenTerm [])

def specialization_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : SpecializationRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code
    (specialization_certificate_code_term
      (quote row.body : SetOpenTerm [])
      (quote_term row.replacement : SetOpenTerm [])
      (quote (specialization_row_result row) : SetOpenTerm []))

theorem intrinsic_zfc_specialization_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      specialization_axiom_code_term
        (quote body : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement body) : SetOpenTerm []) ∈ₘ
      syntax_formula_code_set_term := by
  exact intrinsic_zfc_quote_formula_mem
    (.imp (.forallE sort body) (Formula.instantiateTop replacement body))

theorem intrinsic_zfc_specialization_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      specialization_certificate_code_term
        (quote body : SetOpenTerm [])
        (quote_term replacement : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement body) : SetOpenTerm []) ∈ₘ
      ωₘ := by
  apply godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
  · exact intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 7
  · apply godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
    · exact intrinsic_zfc_quote_formula_mem_omega body
    · apply godel_pairing_mem_omega_of_extends
        godel_pairing_core_theory_subset_intrinsic_zfc_theory
      · exact intrinsic_zfc_quote_term_mem_omega replacement
      · exact intrinsic_zfc_quote_formula_mem_omega (Formula.instantiateTop replacement body)

theorem intrinsic_zfc_specialization_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code
        (specialization_certificate_code_term
          (quote body : SetOpenTerm [])
          (quote_term replacement : SetOpenTerm [])
          (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])) ∈ₘ
      ωₘ := by
  exact intrinsic_zfc_logical_certificate_mem_omega _
    (intrinsic_zfc_specialization_branch_certificate_member body replacement)

theorem intrinsic_zfc_specialization_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      specialization_certificate_code_term
        (quote body : SetOpenTerm [])
        (quote_term replacement : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement body) : SetOpenTerm []) ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (specialization_certificate_code_term
            (quote body : SetOpenTerm [])
            (quote_term replacement : SetOpenTerm [])
            (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        specialization_axiom_code_term
          (quote body : SetOpenTerm [])
          (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at
    certificates
    (specialization_certificate_code_term
      (quote body : SetOpenTerm [])
      (quote_term replacement : SetOpenTerm [])
      (quote (Formula.instantiateTop replacement body) : SetOpenTerm []))
    index hBranchBound hLogicalCertificate
  have hLine := quote_specialization_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates body replacement index
    hPayloadBound hLogicalCertificate hCurrent
  have hFormulaAt := intrinsic_zfc_quote_formula_code_at (Γ := Γ)
    (.imp (.forallE sort body) (Formula.instantiateTop replacement body))
  simpa only [row_instance] using FirstOrder.Derives.conj_intro
    (formula_condition_of_equality checked_verifier _ _
      (Metatheory.Derives.equality_symm hCurrent) hFormulaAt) hLine

theorem intrinsic_zfc_specialization_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (SpecializationRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map specialization_row_formula_code))
        (standard_sequence (rows.map specialization_row_certificate_code)) := by
  apply intro_of_mapped_rows intrinsic_zfc_row_support checked_verifier rows
    specialization_row_formula_code specialization_row_certificate_code hNonempty
    (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega rows.length)
  · intro row _
    exact intrinsic_zfc_specialization_formula_code_member row.body row.replacement
  · intro row _
    exact intrinsic_zfc_specialization_certificate_member row.body row.replacement
  · intro index hIndex hCurrent hCertificate
    let row := rows[index]
    exact intrinsic_zfc_specialization_row_instance _ _ row.body row.replacement index
      (intrinsic_zfc_specialization_branch_certificate_member row.body row.replacement)
      hCertificate hCurrent

theorem intrinsic_zfc_singleton_specialization_sequence_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence
          [specialization_axiom_code_term
            (quote body : SetOpenTerm [])
            (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])])
        (standard_sequence
          [logical_certificate_code
            (specialization_certificate_code_term
              (quote body : SetOpenTerm [])
              (quote_term replacement : SetOpenTerm [])
              (quote (Formula.instantiateTop replacement body) : SetOpenTerm []))]) := by
  simpa [specialization_row_formula_code, specialization_row_certificate_code,
    specialization_row_result] using
    intrinsic_zfc_specialization_transcript_condition
      [SpecializationRow.mk body replacement] (by simp)

structure ForallDistributionRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  antecedent : Formula σ [sort] free
  consequent : Formula σ [sort] free

def forall_distribution_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : ForallDistributionRow σ sort free) : SetOpenTerm [] :=
  quantifier_distribution_axiom_code_term
    (quote row.antecedent : SetOpenTerm [])
    (quote row.consequent : SetOpenTerm [])

def forall_distribution_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : ForallDistributionRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code
    (forall_distribution_certificate_code_term
      (quote row.antecedent : SetOpenTerm [])
      (quote row.consequent : SetOpenTerm []))

theorem intrinsic_zfc_forall_distribution_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (antecedent consequent : Formula σ [sort] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      quantifier_distribution_axiom_code_term
        (quote antecedent : SetOpenTerm [])
        (quote consequent : SetOpenTerm []) ∈ₘ
      syntax_formula_code_set_term := by
  exact intrinsic_zfc_quote_formula_mem
    (.imp (.forallE sort (.imp antecedent consequent))
      (.imp (.forallE sort antecedent) (.forallE sort consequent)))

theorem intrinsic_zfc_forall_distribution_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (antecedent consequent : Formula σ [sort] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      forall_distribution_certificate_code_term
        (quote antecedent : SetOpenTerm [])
        (quote consequent : SetOpenTerm []) ∈ₘ ωₘ := by
  apply godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
  · exact intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 8
  · apply godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
    · exact intrinsic_zfc_quote_formula_mem_omega antecedent
    · exact intrinsic_zfc_quote_formula_mem_omega consequent

theorem intrinsic_zfc_forall_distribution_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (antecedent consequent : Formula σ [sort] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code
        (forall_distribution_certificate_code_term
          (quote antecedent : SetOpenTerm [])
          (quote consequent : SetOpenTerm [])) ∈ₘ ωₘ := by
  exact intrinsic_zfc_logical_certificate_mem_omega _
    (intrinsic_zfc_forall_distribution_branch_certificate_member antecedent consequent)

theorem intrinsic_zfc_forall_distribution_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (antecedent consequent : Formula σ [sort] free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      forall_distribution_certificate_code_term
        (quote antecedent : SetOpenTerm [])
        (quote consequent : SetOpenTerm []) ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (forall_distribution_certificate_code_term
            (quote antecedent : SetOpenTerm [])
            (quote consequent : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        quantifier_distribution_axiom_code_term
          (quote antecedent : SetOpenTerm [])
          (quote consequent : SetOpenTerm [])) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at
    certificates
    (forall_distribution_certificate_code_term
      (quote antecedent : SetOpenTerm [])
      (quote consequent : SetOpenTerm []))
    index hBranchBound hLogicalCertificate
  have hLine := quote_forall_distribution_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates antecedent consequent index
    hPayloadBound hLogicalCertificate hCurrent
  have hFormulaAt := intrinsic_zfc_quote_formula_code_at (Γ := Γ)
    (.imp (.forallE sort (.imp antecedent consequent))
      (.imp (.forallE sort antecedent) (.forallE sort consequent)))
  simpa only [row_instance] using FirstOrder.Derives.conj_intro
    (formula_condition_of_equality checked_verifier _ _
      (Metatheory.Derives.equality_symm hCurrent) hFormulaAt) hLine

theorem intrinsic_zfc_forall_distribution_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (ForallDistributionRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map forall_distribution_row_formula_code))
        (standard_sequence (rows.map forall_distribution_row_certificate_code)) := by
  apply intro_of_mapped_rows intrinsic_zfc_row_support checked_verifier rows
    forall_distribution_row_formula_code forall_distribution_row_certificate_code hNonempty
    (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega rows.length)
  · intro row _
    exact intrinsic_zfc_forall_distribution_formula_code_member row.antecedent row.consequent
  · intro row _
    exact intrinsic_zfc_forall_distribution_certificate_member row.antecedent row.consequent
  · intro index hIndex hCurrent hCertificate
    let row := rows[index]
    exact intrinsic_zfc_forall_distribution_row_instance _ _ row.antecedent row.consequent index
      (intrinsic_zfc_forall_distribution_branch_certificate_member row.antecedent row.consequent)
      hCertificate hCurrent

structure VacuousForallRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  body : Formula σ [] free

def vacuous_forall_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : VacuousForallRow σ sort free) : SetOpenTerm [] :=
  intrinsic_vacuous_forall_axiom_code_term
    (quote row.body : SetOpenTerm [])

def vacuous_forall_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : VacuousForallRow σ sort free) : SetOpenTerm [] :=
  vacuous_forall_certificate_code_term
    (quote row.body : SetOpenTerm [])

def vacuous_forall_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : VacuousForallRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (vacuous_forall_row_branch_code row)

theorem intrinsic_zfc_vacuous_forall_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ}
    (body : Formula σ [] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      intrinsic_vacuous_forall_axiom_code_term
        (quote body : SetOpenTerm []) ∈ₘ syntax_formula_code_set_term := by
  let code : SetOpenTerm [] := quote body
  have hZero := finite_numeral_mem_formal_language_encoding_theory (free := []) (Γ := []) 0
  have hBodyBound := formula_code_at_code_mem_of_derives _ _ (quote_formula_code_at body)
  have hBodyAtOne : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(Sₘ(numₘ(0)), code) := by
    simpa [code, finite_numeral_term] using quote_formula_code_at_of_depth body 1 (by simp)
  have hAllBound := formula_code_at_code_mem_of_derives _ _
    (formula_code_at_universal_intro (numₘ(0)) code hZero hBodyAtOne)
  have hZeroCarrier := FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory hZero
  have hBodyRelatedOne : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, Sₘ(numₘ(0)), code) := by
    simpa [code, finite_numeral_term] using
      related_quote_formula_code_at_of_depth body 1 (by simp)
  have hAllRelated := related_formula_universal_code_at_intro
    (numₘ(0)) code hZeroCarrier hBodyRelatedOne hBodyBound
  exact FirstOrder.Derives.theory_weaken
    intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
    (intrinsic_syntax_carrier_formula_mem_of_related (numₘ(0)) _
      (related_formula_implication_code_at_intro (numₘ(0)) code (all_codeₘ(code))
        hZeroCarrier (related_quote_formula_code_at body) hAllRelated hBodyBound hAllBound))

theorem intrinsic_zfc_vacuous_forall_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ}
    (body : Formula σ [] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      vacuous_forall_certificate_code_term
        (quote body : SetOpenTerm []) ∈ₘ ωₘ := by
  apply godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
  · exact intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 9
  · exact intrinsic_zfc_quote_formula_mem_omega body

theorem intrinsic_zfc_vacuous_forall_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ}
    (body : Formula σ [] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code
        (vacuous_forall_certificate_code_term
          (quote body : SetOpenTerm [])) ∈ₘ ωₘ := by
  exact intrinsic_zfc_logical_certificate_mem_omega _
    (intrinsic_zfc_vacuous_forall_branch_certificate_member body)

theorem intrinsic_zfc_vacuous_forall_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (row : VacuousForallRow σ sort free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      vacuous_forall_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code (vacuous_forall_row_branch_code row))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        vacuous_forall_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  let bodyCode : SetOpenTerm [] := quote row.body
  let formulaCode : SetOpenTerm [] :=
    intrinsic_vacuous_forall_axiom_code_term bodyCode
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at
    certificates (vacuous_forall_certificate_code_term bodyCode)
    index (by simpa [vacuous_forall_row_branch_code, bodyCode] using hBranchBound)
    (by simpa [vacuous_forall_row_certificate_code, vacuous_forall_row_branch_code,
      bodyCode] using hLogicalCertificate)
  have hLine := quote_vacuous_forall_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates row.body index hPayloadBound
    (by simpa [vacuous_forall_row_certificate_code,
      vacuous_forall_row_branch_code, bodyCode] using hLogicalCertificate)
    (by simpa [vacuous_forall_row_formula_code, bodyCode] using hCurrent)
  have hZero := finite_numeral_mem_formal_language_encoding_theory (free := []) (Γ := []) 0
  have hBodyAtOne : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(Sₘ(numₘ(0)), bodyCode) := by
    simpa [bodyCode, finite_numeral_term] using
      quote_formula_code_at_of_depth row.body 1 (by simp)
  have hFormulaAtFormal := formula_code_at_implication_intro
    (numₘ(0)) bodyCode (all_codeₘ(bodyCode)) hZero
    (quote_formula_code_at row.body)
    (formula_code_at_universal_intro (numₘ(0)) bodyCode hZero hBodyAtOne)
  have hFormulaAt : Γ ⊢ₘ[intrinsic_zfc_theory]
      formula_code_atₘ(numₘ(0), formulaCode) :=
    FirstOrder.Derives.context_weaken (by simp)
      (FirstOrder.Derives.theory_weaken
        formal_language_encoding_theory_subset_intrinsic_zfc_theory hFormulaAtFormal)
  simpa only [row_instance] using FirstOrder.Derives.conj_intro
    (formula_condition_of_equality checked_verifier _ _
      (Metatheory.Derives.equality_symm hCurrent) hFormulaAt) hLine

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
