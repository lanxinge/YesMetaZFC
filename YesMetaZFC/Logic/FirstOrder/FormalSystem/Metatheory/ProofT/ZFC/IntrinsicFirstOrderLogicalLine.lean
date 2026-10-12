import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.OpenBoundFormulaCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier

/-!
# ZFC 一阶逻辑证书的内在行构造

本模块把 specialization 与等式替换的 Quine quotation 直接装入内在逻辑分支。
所有见证由 bound 上下文索引，不经过旧 token 回放、变量名或 freshness 桥接。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC
namespace IntrinsicFirstOrderLogicalLine

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition
open IntrinsicLogicalCertificate

set_option autoImplicit false

/-- specialization 的直接 payload 码。 -/
abbrev specialization_payload_code_term
    {free : SetContext}
    (body replacement result : SetOpenTerm free) : SetOpenTerm free :=
  godel_pairₘ(body, godel_pairₘ(replacement, result))

/-- specialization 的直接分支证书码。 -/
abbrev specialization_certificate_code_term
    {free : SetContext}
    (body replacement result : SetOpenTerm free) : SetOpenTerm free :=
  godel_pairₘ(numₘ(7),
    specialization_payload_code_term body replacement result)

/-- 等式替换的直接 payload 码。 -/
abbrev equality_substitution_payload_code_term
    {free : SetContext}
    (left right body leftResult rightResult : SetOpenTerm free) :
    SetOpenTerm free :=
  godel_pairₘ(left,
    godel_pairₘ(right,
      godel_pairₘ(body,
        godel_pairₘ(leftResult, rightResult))))

/-- 等式替换的直接分支证书码。 -/
abbrev equality_substitution_certificate_code_term
    {free : SetContext}
    (left right body leftResult rightResult : SetOpenTerm free) :
    SetOpenTerm free :=
  godel_pairₘ(numₘ(10),
    equality_substitution_payload_code_term
      left right body leftResult rightResult)

/-- 全称分配的直接 payload 码。 -/
abbrev forall_distribution_payload_code_term
    {free : SetContext}
    (antecedent consequent : SetOpenTerm free) : SetOpenTerm free :=
  godel_pairₘ(antecedent, consequent)

/-- 全称分配的直接分支证书码。 -/
abbrev forall_distribution_certificate_code_term
    {free : SetContext}
    (antecedent consequent : SetOpenTerm free) : SetOpenTerm free :=
  godel_pairₘ(numₘ(8),
    forall_distribution_payload_code_term antecedent consequent)

/-- 空泛全称的直接分支证书码。 -/
abbrev vacuous_forall_certificate_code_term
    {free : SetContext} (body : SetOpenTerm free) : SetOpenTerm free :=
  godel_pairₘ(numₘ(9), body)

/-- 等式自反的直接分支证书码。 -/
abbrev equality_reflexivity_certificate_code_term
    {free : SetContext} (term : SetOpenTerm free) : SetOpenTerm free :=
  godel_pairₘ(numₘ(11), term)

private theorem lift_expression_derives
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    {φ : SetOpenFormula []}
    (hφ : ([] : Context signature []) ⊢ₘ[expression_encoding_theory] φ) :
    Γ ⊢ₘ[T] φ :=
  FirstOrder.Derives.context_weaken
    (Γ := ([] : Context signature [])) (Δ := Γ) (by intro φ hφ; cases hφ)
    (FirstOrder.Derives.theory_weaken hExpression hφ)

private theorem lift_formal_derives
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    {φ : SetOpenFormula []}
    (hφ : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory] φ) :
    Γ ⊢ₘ[T] φ :=
  lift_expression_derives hExpression
    (FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_expression_encoding_theory hφ)

private theorem expression_pairing_extends
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory) :
    Theory.Extends T godel_pairing_core_theory :=
  fun hSentence => hExpression
    (godel_pairing_core_theory_subset_expression_encoding_theory hSentence)

/-- 任一已登记逻辑分支直接生成统一 checked 行。 -/
theorem logical_branch_line_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (branch : BoundedBinaryBranch free)
    (hBranchMem : branch ∈ logical_branches)
    (sequence certificates certificate : SetOpenTerm free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index)) certificate)
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code certificate)
    (hBranch : Γ ⊢ₘ[T]
      branch.condition_closed (sequence ·ₘ numₘ(index)) certificate) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  have hLogicalList : Γ ⊢ₘ[T]
      bounded_binary_condition_list
        (logical_branches (free := free))
        (sequence ·ₘ numₘ(index)) certificate :=
    bounded_binary_condition_list_of_mem hBranchMem hBranch
  have hLogical : Γ ⊢ₘ[T]
      IntrinsicVerifier.checked_verifier.logical_condition
        sequence certificates (numₘ(index)) certificate := by
    change Γ ⊢ₘ[T]
      logical_condition_template
        sequence certificates (numₘ(index)) certificate
    rw [logical_condition_template_apply]
    exact hLogicalList
  exact IntrinsicLogicalLine.line_instance_intro
    IntrinsicVerifier.checked_verifier sequence certificates certificate index
    hPayloadBound hLogicalCertificate hLogical

/-- 四个类型化见证直接生成 specialization 分支。 -/
theorem specialization_branch_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (formula certificate payload body replacement result : SetOpenTerm free)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hBody : Γ ⊢ₘ[T] body ∈ₘ ωₘ)
    (hReplacement : Γ ⊢ₘ[T] replacement ∈ₘ ωₘ)
    (hResult : Γ ⊢ₘ[T] result ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(7), payload))
    (hPayloadCode : Γ ⊢ₘ[T]
      payload ≐ₘ godel_pairₘ(body, godel_pairₘ(replacement, result)))
    (hBodyCode : Γ ⊢ₘ[T] formula_code_atₘ(numₘ(1), body))
    (hReplacementCode : Γ ⊢ₘ[T] term_code_atₘ(numₘ(0), replacement))
    (hResultCode : Γ ⊢ₘ[T] formula_code_atₘ(numₘ(0), result))
    (hOpen : Γ ⊢ₘ[T]
      formula_open_bound_condition replacement body result)
    (hFormula : Γ ⊢ₘ[T]
      formula ≐ₘ specialization_axiom_code_term body result) :
    Γ ⊢ₘ[T]
      (specialization_branch (free := free)).condition_closed
        formula certificate := by
  change Γ ⊢ₘ[T]
    bounded_witness_closure specialization_plan
      (specialization_condition
        (weaken_bound_context specialization_bound formula)
        (weaken_bound_context specialization_bound certificate))
  let assignment :
      BoundedWitnessAssignment T Γ
        (specialization_plan (free := free))
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] free) := by
    refine ⟨⟨payload, ?_⟩, ?_⟩
    · simpa [specialization_plan, BoundedWitnessAssignment] using hPayload
    refine ⟨⟨body, ?_⟩, ?_⟩
    · simpa [specialization_plan, BoundedWitnessAssignment] using hBody
    refine ⟨⟨replacement, ?_⟩, ?_⟩
    · simpa [specialization_plan, BoundedWitnessAssignment] using hReplacement
    refine ⟨⟨result, ?_⟩, PUnit.unit⟩
    simpa [specialization_plan, BoundedWitnessAssignment] using hResult
  have hMatrix : Γ ⊢ₘ[T]
      (specialization_condition
        (weaken_bound_context specialization_bound formula)
        (weaken_bound_context specialization_bound certificate)).substituteMapped
          assignment.finalSubstitution VariableSubstitution.freeId := by
    simpa [assignment, BoundedWitnessAssignment,
      BoundedWitnessAssignment.finalSubstitution,
      specialization_condition, specialization_payload,
      specialization_body, specialization_replacement,
      specialization_result, formula_code_condition,
      term_payload_condition, formula_payload_condition,
      specialization_plan, weaken_bound_context_substituteMapped,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId] using!
      FirstOrder.Derives.conj_intro hCertificate
        (FirstOrder.Derives.conj_intro hPayloadCode
          (FirstOrder.Derives.conj_intro
            (FirstOrder.Derives.conj_intro
              (FirstOrder.Derives.conj_intro hBodyCode hReplacementCode)
              hResultCode)
            (FirstOrder.Derives.conj_intro hOpen hFormula)))
  simpa using
    bounded_witness_closure_intro_assignment assignment _ hMatrix

/-- specialization 分支直接进入统一逻辑证书表并生成 checked 行。 -/
theorem specialization_line_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence certificates certificate payload body replacement result :
      SetOpenTerm free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index)) certificate)
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code certificate)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hBody : Γ ⊢ₘ[T] body ∈ₘ ωₘ)
    (hReplacement : Γ ⊢ₘ[T] replacement ∈ₘ ωₘ)
    (hResult : Γ ⊢ₘ[T] result ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(7), payload))
    (hPayloadCode : Γ ⊢ₘ[T]
      payload ≐ₘ godel_pairₘ(body, godel_pairₘ(replacement, result)))
    (hBodyCode : Γ ⊢ₘ[T] formula_code_atₘ(numₘ(1), body))
    (hReplacementCode : Γ ⊢ₘ[T] term_code_atₘ(numₘ(0), replacement))
    (hResultCode : Γ ⊢ₘ[T] formula_code_atₘ(numₘ(0), result))
    (hOpen : Γ ⊢ₘ[T]
      formula_open_bound_condition replacement body result)
    (hFormula : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        specialization_axiom_code_term body result) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  have hBranch : Γ ⊢ₘ[T]
      (specialization_branch (free := free)).condition_closed
        (sequence ·ₘ numₘ(index)) certificate :=
    specialization_branch_intro
      (sequence ·ₘ numₘ(index)) certificate payload body replacement result
      hPayload hBody hReplacement hResult hCertificate hPayloadCode
      hBodyCode hReplacementCode hResultCode hOpen hFormula
  exact logical_branch_line_intro specialization_branch
    (by simp [logical_branches, first_order_branches])
    sequence certificates certificate index hPayloadBound hLogicalCertificate hBranch

/--
宿主内在语法的 Quine quotation 直接生成 specialization checked 行。公式码、项码、
码域成员与 bound 顶槽打开正确性全部由语法核自动提供。
-/
theorem quote_specialization_line_intro
    {σ : Signature} [QuineEncoding.QuotationNumbering σ]
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index))
        (specialization_certificate_code_term
          (QuineEncoding.quote body : SetOpenTerm [])
          (QuineEncoding.quote_term replacement : SetOpenTerm [])
          (QuineEncoding.quote
            (Formula.instantiateTop replacement body) : SetOpenTerm [])))
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (specialization_certificate_code_term
            (QuineEncoding.quote body : SetOpenTerm [])
            (QuineEncoding.quote_term replacement : SetOpenTerm [])
            (QuineEncoding.quote
              (Formula.instantiateTop replacement body) : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        specialization_axiom_code_term
          (QuineEncoding.quote body : SetOpenTerm [])
          (QuineEncoding.quote
            (Formula.instantiateTop replacement body) : SetOpenTerm [])) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  let bodyCode : SetOpenTerm [] := QuineEncoding.quote body
  let replacementCode : SetOpenTerm [] := QuineEncoding.quote_term replacement
  let resultCode : SetOpenTerm [] :=
    QuineEncoding.quote (Formula.instantiateTop replacement body)
  let payloadCode : SetOpenTerm [] :=
    specialization_payload_code_term bodyCode replacementCode resultCode
  let certificateCode : SetOpenTerm [] :=
    specialization_certificate_code_term bodyCode replacementCode resultCode
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), bodyCode) := by
    simpa [bodyCode] using QuineEncoding.quote_formula_code_at body
  have hReplacementCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), replacementCode) := by
    simpa [replacementCode] using QuineEncoding.quote_term_code_at replacement
  have hResultCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), resultCode) := by
    simpa [resultCode] using
      QuineEncoding.quote_formula_code_at
        (Formula.instantiateTop replacement body)
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(1)) bodyCode hBodyCodeFormal
  have hReplacementBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        replacementCode ∈ₘ ωₘ :=
    QuineEncoding.term_code_at_code_mem_of_derives
      (numₘ(0)) replacementCode hReplacementCodeFormal
  have hResultBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        resultCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(0)) resultCode hResultCodeFormal
  have hBodyCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), bodyCode) :=
    lift_formal_derives hExpression hBodyCodeFormal
  have hReplacementCode : Γ ⊢ₘ[T]
      term_code_atₘ(numₘ(0), replacementCode) :=
    lift_formal_derives hExpression hReplacementCodeFormal
  have hResultCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(0), resultCode) :=
    lift_formal_derives hExpression hResultCodeFormal
  have hBodyBound : Γ ⊢ₘ[T] bodyCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hBodyBoundFormal
  have hReplacementBound : Γ ⊢ₘ[T] replacementCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hReplacementBoundFormal
  have hResultBound : Γ ⊢ₘ[T] resultCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hResultBoundFormal
  have hOpen : Γ ⊢ₘ[T]
      formula_open_bound_condition replacementCode bodyCode resultCode := by
    exact lift_expression_derives hExpression (by
      simpa [bodyCode, replacementCode, resultCode] using
        QuineEncoding.quote_formula_open_bound replacement body)
  have hInnerBound : Γ ⊢ₘ[T]
      godel_pairₘ(replacementCode, resultCode) ∈ₘ ωₘ :=
    godel_pairing_mem_omega_of_extends
      (expression_pairing_extends hExpression)
      replacementCode resultCode hReplacementBound hResultBound
  have hPayload : Γ ⊢ₘ[T] payloadCode ∈ₘ ωₘ := by
    exact godel_pairing_mem_omega_of_extends
      (expression_pairing_extends hExpression)
      bodyCode godel_pairₘ(replacementCode, resultCode)
      hBodyBound hInnerBound
  apply specialization_line_intro
    sequence certificates certificateCode payloadCode bodyCode
      replacementCode resultCode index
  · simpa [certificateCode, payloadCode] using hPayloadBound
  · simpa [certificateCode, payloadCode] using hLogicalCertificate
  · exact hPayload
  · exact hBodyBound
  · exact hReplacementBound
  · exact hResultBound
  · exact Metatheory.Derives.equality_refl certificateCode
  · exact Metatheory.Derives.equality_refl payloadCode
  · exact hBodyCode
  · exact hReplacementCode
  · exact hResultCode
  · exact hOpen
  · simpa [bodyCode, resultCode] using hCurrent

/-- 三个类型化见证直接生成全称分配分支。 -/
theorem forall_distribution_branch_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (formula certificate payload antecedent consequent : SetOpenTerm free)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hAntecedent : Γ ⊢ₘ[T] antecedent ∈ₘ ωₘ)
    (hConsequent : Γ ⊢ₘ[T] consequent ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(8), payload))
    (hPayloadCode : Γ ⊢ₘ[T]
      payload ≐ₘ forall_distribution_payload_code_term
        antecedent consequent)
    (hAntecedentCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), antecedent))
    (hConsequentCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), consequent))
    (hFormula : Γ ⊢ₘ[T]
      formula ≐ₘ quantifier_distribution_axiom_code_term
        antecedent consequent) :
    Γ ⊢ₘ[T]
      (forall_distribution_branch (free := free)).condition_closed
        formula certificate := by
  change Γ ⊢ₘ[T]
    bounded_witness_closure forall_distribution_plan
      (forall_distribution_condition
        (weaken_bound_context forall_distribution_bound formula)
        (weaken_bound_context forall_distribution_bound certificate))
  let assignment :
      BoundedWitnessAssignment T Γ
        (forall_distribution_plan (free := free))
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] free) := by
    refine ⟨⟨payload, ?_⟩, ?_⟩
    · simpa [forall_distribution_plan, BoundedWitnessAssignment] using hPayload
    refine ⟨⟨antecedent, ?_⟩, ?_⟩
    · simpa [forall_distribution_plan, BoundedWitnessAssignment] using hAntecedent
    refine ⟨⟨consequent, ?_⟩, PUnit.unit⟩
    simpa [forall_distribution_plan, BoundedWitnessAssignment] using hConsequent
  have hMatrix : Γ ⊢ₘ[T]
      (forall_distribution_condition
        (weaken_bound_context forall_distribution_bound formula)
        (weaken_bound_context forall_distribution_bound certificate)).substituteMapped
          assignment.finalSubstitution VariableSubstitution.freeId := by
    simpa [assignment, BoundedWitnessAssignment,
      BoundedWitnessAssignment.finalSubstitution,
      forall_distribution_condition, forall_distribution_payload,
      forall_distribution_antecedent, forall_distribution_consequent,
      forall_distribution_payload_code_term, formula_code_condition,
      forall_distribution_plan, weaken_bound_context_substituteMapped,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId] using!
      FirstOrder.Derives.conj_intro hCertificate
        (FirstOrder.Derives.conj_intro hPayloadCode
          (FirstOrder.Derives.conj_intro
            (FirstOrder.Derives.conj_intro hAntecedentCode hConsequentCode)
            hFormula))
  simpa using
    bounded_witness_closure_intro_assignment assignment _ hMatrix

/-- 全称分配分支直接进入统一逻辑证书表并生成 checked 行。 -/
theorem forall_distribution_line_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence certificates certificate payload antecedent consequent :
      SetOpenTerm free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index)) certificate)
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code certificate)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hAntecedent : Γ ⊢ₘ[T] antecedent ∈ₘ ωₘ)
    (hConsequent : Γ ⊢ₘ[T] consequent ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(8), payload))
    (hPayloadCode : Γ ⊢ₘ[T]
      payload ≐ₘ forall_distribution_payload_code_term
        antecedent consequent)
    (hAntecedentCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), antecedent))
    (hConsequentCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), consequent))
    (hFormula : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        quantifier_distribution_axiom_code_term antecedent consequent) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  have hBranch : Γ ⊢ₘ[T]
      (forall_distribution_branch (free := free)).condition_closed
        (sequence ·ₘ numₘ(index)) certificate :=
    forall_distribution_branch_intro
      (sequence ·ₘ numₘ(index)) certificate payload antecedent consequent
      hPayload hAntecedent hConsequent hCertificate hPayloadCode
      hAntecedentCode hConsequentCode hFormula
  exact logical_branch_line_intro forall_distribution_branch
    (by simp [logical_branches, first_order_branches])
    sequence certificates certificate index hPayloadBound hLogicalCertificate hBranch

/-- 宿主内在语法的 Quine quotation 直接生成全称分配 checked 行。 -/
theorem quote_forall_distribution_line_intro
    {σ : Signature} [QuineEncoding.QuotationNumbering σ]
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (antecedent consequent : Formula σ [sort] free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index))
        (forall_distribution_certificate_code_term
          (QuineEncoding.quote antecedent : SetOpenTerm [])
          (QuineEncoding.quote consequent : SetOpenTerm [])))
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (forall_distribution_certificate_code_term
            (QuineEncoding.quote antecedent : SetOpenTerm [])
            (QuineEncoding.quote consequent : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        quantifier_distribution_axiom_code_term
          (QuineEncoding.quote antecedent : SetOpenTerm [])
          (QuineEncoding.quote consequent : SetOpenTerm [])) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  let antecedentCode : SetOpenTerm [] := QuineEncoding.quote antecedent
  let consequentCode : SetOpenTerm [] := QuineEncoding.quote consequent
  let payloadCode : SetOpenTerm [] :=
    forall_distribution_payload_code_term antecedentCode consequentCode
  let certificateCode : SetOpenTerm [] :=
    forall_distribution_certificate_code_term antecedentCode consequentCode
  have hAntecedentCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), antecedentCode) := by
    simpa [antecedentCode] using
      QuineEncoding.quote_formula_code_at antecedent
  have hConsequentCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), consequentCode) := by
    simpa [consequentCode] using
      QuineEncoding.quote_formula_code_at consequent
  have hAntecedentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        antecedentCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(1)) antecedentCode hAntecedentCodeFormal
  have hConsequentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        consequentCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(1)) consequentCode hConsequentCodeFormal
  have hAntecedentCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), antecedentCode) :=
    lift_formal_derives hExpression hAntecedentCodeFormal
  have hConsequentCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), consequentCode) :=
    lift_formal_derives hExpression hConsequentCodeFormal
  have hAntecedentBound : Γ ⊢ₘ[T] antecedentCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hAntecedentBoundFormal
  have hConsequentBound : Γ ⊢ₘ[T] consequentCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hConsequentBoundFormal
  have hPayload : Γ ⊢ₘ[T] payloadCode ∈ₘ ωₘ := by
    exact godel_pairing_mem_omega_of_extends
      (expression_pairing_extends hExpression)
      antecedentCode consequentCode hAntecedentBound hConsequentBound
  apply forall_distribution_line_intro
    sequence certificates certificateCode payloadCode antecedentCode
      consequentCode index
  · simpa [certificateCode, payloadCode] using hPayloadBound
  · simpa [certificateCode, payloadCode] using hLogicalCertificate
  · exact hPayload
  · exact hAntecedentBound
  · exact hConsequentBound
  · exact Metatheory.Derives.equality_refl certificateCode
  · exact Metatheory.Derives.equality_refl payloadCode
  · exact hAntecedentCode
  · exact hConsequentCode
  · simpa [antecedentCode, consequentCode] using hCurrent

/-- 一个类型化见证直接生成空泛全称分支。 -/
theorem vacuous_forall_branch_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (formula certificate body : SetOpenTerm free)
    (hBody : Γ ⊢ₘ[T] body ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(9), body))
    (hBodyCode : Γ ⊢ₘ[T] formula_code_atₘ(numₘ(0), body))
    (hFormula : Γ ⊢ₘ[T]
      formula ≐ₘ intrinsic_vacuous_forall_axiom_code_term body) :
    Γ ⊢ₘ[T]
      (vacuous_forall_branch (free := free)).condition_closed
        formula certificate := by
  change Γ ⊢ₘ[T]
    bounded_witness_closure vacuous_forall_plan
      (vacuous_forall_condition
        (weaken_bound_context vacuous_forall_bound formula)
        (weaken_bound_context vacuous_forall_bound certificate))
  let assignment :
      BoundedWitnessAssignment T Γ
        (vacuous_forall_plan (free := free))
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] free) := by
    refine ⟨⟨body, ?_⟩, PUnit.unit⟩
    simpa [vacuous_forall_plan, BoundedWitnessAssignment] using hBody
  have hMatrix : Γ ⊢ₘ[T]
      (vacuous_forall_condition
        (weaken_bound_context vacuous_forall_bound formula)
        (weaken_bound_context vacuous_forall_bound certificate)).substituteMapped
          assignment.finalSubstitution VariableSubstitution.freeId := by
    simpa [assignment, BoundedWitnessAssignment,
      BoundedWitnessAssignment.finalSubstitution,
      vacuous_forall_condition, vacuous_forall_payload,
      intrinsic_vacuous_forall_axiom_code_term,
      formula_payload_condition, vacuous_forall_plan,
      weaken_bound_context_substituteMapped,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId] using!
      FirstOrder.Derives.conj_intro hCertificate
        (FirstOrder.Derives.conj_intro hBodyCode hFormula)
  simpa using
    bounded_witness_closure_intro_assignment assignment _ hMatrix

/-- 空泛全称分支直接进入统一逻辑证书表并生成 checked 行。 -/
theorem vacuous_forall_line_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence certificates certificate body : SetOpenTerm free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index)) certificate)
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code certificate)
    (hBody : Γ ⊢ₘ[T] body ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(9), body))
    (hBodyCode : Γ ⊢ₘ[T] formula_code_atₘ(numₘ(0), body))
    (hFormula : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        intrinsic_vacuous_forall_axiom_code_term body) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  have hBranch : Γ ⊢ₘ[T]
      (vacuous_forall_branch (free := free)).condition_closed
        (sequence ·ₘ numₘ(index)) certificate :=
    vacuous_forall_branch_intro
      (sequence ·ₘ numₘ(index)) certificate body
      hBody hCertificate hBodyCode hFormula
  exact logical_branch_line_intro vacuous_forall_branch
    (by simp [logical_branches, first_order_branches])
    sequence certificates certificate index hPayloadBound hLogicalCertificate hBranch

/-- 宿主内在语法的 Quine quotation 直接生成空泛全称 checked 行。 -/
theorem quote_vacuous_forall_line_intro
    {σ : Signature} [QuineEncoding.QuotationNumbering σ]
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    {free : SortContext σ}
    (body : Formula σ [] free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index))
        (vacuous_forall_certificate_code_term
          (QuineEncoding.quote body : SetOpenTerm [])))
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (vacuous_forall_certificate_code_term
            (QuineEncoding.quote body : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        intrinsic_vacuous_forall_axiom_code_term
          (QuineEncoding.quote body : SetOpenTerm [])) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  let bodyCode : SetOpenTerm [] := QuineEncoding.quote body
  let certificateCode : SetOpenTerm [] :=
    vacuous_forall_certificate_code_term bodyCode
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), bodyCode) := by
    simpa [bodyCode] using QuineEncoding.quote_formula_code_at body
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(0)) bodyCode hBodyCodeFormal
  have hBodyCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(0), bodyCode) :=
    lift_formal_derives hExpression hBodyCodeFormal
  have hBodyBound : Γ ⊢ₘ[T] bodyCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hBodyBoundFormal
  apply vacuous_forall_line_intro
    sequence certificates certificateCode bodyCode index
  · simpa [certificateCode] using hPayloadBound
  · simpa [certificateCode] using hLogicalCertificate
  · exact hBodyBound
  · exact Metatheory.Derives.equality_refl certificateCode
  · exact hBodyCode
  · simpa [bodyCode] using hCurrent

/-- 六个类型化见证直接生成等式替换分支。 -/
theorem equality_substitution_branch_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (formula certificate payload left right body leftResult rightResult :
      SetOpenTerm free)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hLeft : Γ ⊢ₘ[T] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[T] right ∈ₘ ωₘ)
    (hBody : Γ ⊢ₘ[T] body ∈ₘ ωₘ)
    (hLeftResult : Γ ⊢ₘ[T] leftResult ∈ₘ ωₘ)
    (hRightResult : Γ ⊢ₘ[T] rightResult ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(10), payload))
    (hPayloadCode : Γ ⊢ₘ[T]
      payload ≐ₘ equality_substitution_payload_code_term
        left right body leftResult rightResult)
    (hOpenLeft : Γ ⊢ₘ[T]
      formula_open_bound_condition left body leftResult)
    (hOpenRight : Γ ⊢ₘ[T]
      formula_open_bound_condition right body rightResult)
    (hFormula : Γ ⊢ₘ[T]
      formula ≐ₘ intrinsic_equality_substitution_axiom_code_term
        left right leftResult rightResult) :
    Γ ⊢ₘ[T]
      (equality_substitution_branch (free := free)).condition_closed
        formula certificate := by
  change Γ ⊢ₘ[T]
    bounded_witness_closure equality_substitution_plan
      (equality_substitution_condition
        (weaken_bound_context equality_substitution_bound formula)
        (weaken_bound_context equality_substitution_bound certificate))
  let assignment :
      BoundedWitnessAssignment T Γ
        (equality_substitution_plan (free := free))
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] free) := by
    refine ⟨⟨payload, ?_⟩, ?_⟩
    · simpa [equality_substitution_plan, BoundedWitnessAssignment] using hPayload
    refine ⟨⟨left, ?_⟩, ?_⟩
    · simpa [equality_substitution_plan, BoundedWitnessAssignment] using hLeft
    refine ⟨⟨right, ?_⟩, ?_⟩
    · simpa [equality_substitution_plan, BoundedWitnessAssignment] using hRight
    refine ⟨⟨body, ?_⟩, ?_⟩
    · simpa [equality_substitution_plan, BoundedWitnessAssignment] using hBody
    refine ⟨⟨leftResult, ?_⟩, ?_⟩
    · simpa [equality_substitution_plan, BoundedWitnessAssignment] using hLeftResult
    refine ⟨⟨rightResult, ?_⟩, PUnit.unit⟩
    simpa [equality_substitution_plan, BoundedWitnessAssignment] using hRightResult
  have hMatrix : Γ ⊢ₘ[T]
      (equality_substitution_condition
        (weaken_bound_context equality_substitution_bound formula)
        (weaken_bound_context equality_substitution_bound certificate)).substituteMapped
          assignment.finalSubstitution VariableSubstitution.freeId := by
    simpa [assignment, BoundedWitnessAssignment,
      BoundedWitnessAssignment.finalSubstitution,
      equality_substitution_condition, equality_substitution_payload,
      equality_substitution_left, equality_substitution_right,
      equality_substitution_body, equality_substitution_left_result,
      equality_substitution_right_result,
      intrinsic_equality_substitution_axiom_code_term,
      equality_substitution_payload_code_term,
      equality_substitution_plan, weaken_bound_context_substituteMapped,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId] using!
      FirstOrder.Derives.conj_intro hCertificate
        (FirstOrder.Derives.conj_intro hPayloadCode
          (FirstOrder.Derives.conj_intro
            (FirstOrder.Derives.conj_intro hOpenLeft hOpenRight)
            hFormula))
  simpa using
    bounded_witness_closure_intro_assignment assignment _ hMatrix

/-- 等式替换分支直接进入统一逻辑证书表并生成 checked 行。 -/
theorem equality_substitution_line_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence certificates certificate payload left right body
      leftResult rightResult : SetOpenTerm free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index)) certificate)
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code certificate)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hLeft : Γ ⊢ₘ[T] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[T] right ∈ₘ ωₘ)
    (hBody : Γ ⊢ₘ[T] body ∈ₘ ωₘ)
    (hLeftResult : Γ ⊢ₘ[T] leftResult ∈ₘ ωₘ)
    (hRightResult : Γ ⊢ₘ[T] rightResult ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(10), payload))
    (hPayloadCode : Γ ⊢ₘ[T]
      payload ≐ₘ equality_substitution_payload_code_term
        left right body leftResult rightResult)
    (hOpenLeft : Γ ⊢ₘ[T]
      formula_open_bound_condition left body leftResult)
    (hOpenRight : Γ ⊢ₘ[T]
      formula_open_bound_condition right body rightResult)
    (hFormula : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        intrinsic_equality_substitution_axiom_code_term
          left right leftResult rightResult) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  have hBranch : Γ ⊢ₘ[T]
      (equality_substitution_branch (free := free)).condition_closed
        (sequence ·ₘ numₘ(index)) certificate :=
    equality_substitution_branch_intro
      (sequence ·ₘ numₘ(index)) certificate payload left right body
        leftResult rightResult hPayload hLeft hRight hBody hLeftResult
        hRightResult hCertificate hPayloadCode hOpenLeft hOpenRight hFormula
  exact logical_branch_line_intro equality_substitution_branch
    (by simp [logical_branches, first_order_branches])
    sequence certificates certificate index hPayloadBound hLogicalCertificate hBranch

/--
宿主内在语法的 Quine quotation 直接生成等式替换 checked 行。两次 bound 顶槽打开、
全部码域成员与嵌套配对闭包均由语法核和配对核自动提供。
-/
theorem quote_equality_substitution_line_intro
    {σ : Signature} [QuineEncoding.QuotationNumbering σ]
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (left right : Term σ [] free sort)
    (body : Formula σ [sort] free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index))
        (equality_substitution_certificate_code_term
          (QuineEncoding.quote_term left : SetOpenTerm [])
          (QuineEncoding.quote_term right : SetOpenTerm [])
          (QuineEncoding.quote body : SetOpenTerm [])
          (QuineEncoding.quote
            (Formula.instantiateTop left body) : SetOpenTerm [])
          (QuineEncoding.quote
            (Formula.instantiateTop right body) : SetOpenTerm [])))
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (equality_substitution_certificate_code_term
            (QuineEncoding.quote_term left : SetOpenTerm [])
            (QuineEncoding.quote_term right : SetOpenTerm [])
            (QuineEncoding.quote body : SetOpenTerm [])
            (QuineEncoding.quote
              (Formula.instantiateTop left body) : SetOpenTerm [])
            (QuineEncoding.quote
              (Formula.instantiateTop right body) : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        intrinsic_equality_substitution_axiom_code_term
          (QuineEncoding.quote_term left : SetOpenTerm [])
          (QuineEncoding.quote_term right : SetOpenTerm [])
          (QuineEncoding.quote
            (Formula.instantiateTop left body) : SetOpenTerm [])
          (QuineEncoding.quote
            (Formula.instantiateTop right body) : SetOpenTerm [])) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  let leftCode : SetOpenTerm [] := QuineEncoding.quote_term left
  let rightCode : SetOpenTerm [] := QuineEncoding.quote_term right
  let bodyCode : SetOpenTerm [] := QuineEncoding.quote body
  let leftResultCode : SetOpenTerm [] :=
    QuineEncoding.quote (Formula.instantiateTop left body)
  let rightResultCode : SetOpenTerm [] :=
    QuineEncoding.quote (Formula.instantiateTop right body)
  let payloadCode : SetOpenTerm [] :=
    equality_substitution_payload_code_term
      leftCode rightCode bodyCode leftResultCode rightResultCode
  let certificateCode : SetOpenTerm [] :=
    equality_substitution_certificate_code_term
      leftCode rightCode bodyCode leftResultCode rightResultCode
  have hLeftCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), leftCode) := by
    simpa [leftCode] using QuineEncoding.quote_term_code_at left
  have hRightCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), rightCode) := by
    simpa [rightCode] using QuineEncoding.quote_term_code_at right
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), bodyCode) := by
    simpa [bodyCode] using QuineEncoding.quote_formula_code_at body
  have hLeftResultCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), leftResultCode) := by
    simpa [leftResultCode] using
      QuineEncoding.quote_formula_code_at
        (Formula.instantiateTop left body)
  have hRightResultCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), rightResultCode) := by
    simpa [rightResultCode] using
      QuineEncoding.quote_formula_code_at
        (Formula.instantiateTop right body)
  have hLeftBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        leftCode ∈ₘ ωₘ :=
    QuineEncoding.term_code_at_code_mem_of_derives
      (numₘ(0)) leftCode hLeftCodeFormal
  have hRightBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        rightCode ∈ₘ ωₘ :=
    QuineEncoding.term_code_at_code_mem_of_derives
      (numₘ(0)) rightCode hRightCodeFormal
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(1)) bodyCode hBodyCodeFormal
  have hLeftResultBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        leftResultCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(0)) leftResultCode hLeftResultCodeFormal
  have hRightResultBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        rightResultCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(0)) rightResultCode hRightResultCodeFormal
  have hLeftBound : Γ ⊢ₘ[T] leftCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hLeftBoundFormal
  have hRightBound : Γ ⊢ₘ[T] rightCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hRightBoundFormal
  have hBodyBound : Γ ⊢ₘ[T] bodyCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hBodyBoundFormal
  have hLeftResultBound : Γ ⊢ₘ[T] leftResultCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hLeftResultBoundFormal
  have hRightResultBound : Γ ⊢ₘ[T] rightResultCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hRightResultBoundFormal
  have hOpenLeft : Γ ⊢ₘ[T]
      formula_open_bound_condition leftCode bodyCode leftResultCode := by
    exact lift_expression_derives hExpression (by
      simpa [leftCode, bodyCode, leftResultCode] using
        QuineEncoding.quote_formula_open_bound left body)
  have hOpenRight : Γ ⊢ₘ[T]
      formula_open_bound_condition rightCode bodyCode rightResultCode := by
    exact lift_expression_derives hExpression (by
      simpa [rightCode, bodyCode, rightResultCode] using
        QuineEncoding.quote_formula_open_bound right body)
  have hResultPairBound : Γ ⊢ₘ[T]
      godel_pairₘ(leftResultCode, rightResultCode) ∈ₘ ωₘ :=
    godel_pairing_mem_omega_of_extends
      (expression_pairing_extends hExpression)
      leftResultCode rightResultCode hLeftResultBound hRightResultBound
  have hBodyPairBound : Γ ⊢ₘ[T]
      godel_pairₘ(bodyCode,
        godel_pairₘ(leftResultCode, rightResultCode)) ∈ₘ ωₘ :=
    godel_pairing_mem_omega_of_extends
      (expression_pairing_extends hExpression)
      bodyCode godel_pairₘ(leftResultCode, rightResultCode)
      hBodyBound hResultPairBound
  have hRightPairBound : Γ ⊢ₘ[T]
      godel_pairₘ(rightCode,
        godel_pairₘ(bodyCode,
          godel_pairₘ(leftResultCode, rightResultCode))) ∈ₘ ωₘ :=
    godel_pairing_mem_omega_of_extends
      (expression_pairing_extends hExpression)
      rightCode
        godel_pairₘ(bodyCode,
          godel_pairₘ(leftResultCode, rightResultCode))
      hRightBound hBodyPairBound
  have hPayload : Γ ⊢ₘ[T] payloadCode ∈ₘ ωₘ := by
    exact godel_pairing_mem_omega_of_extends
      (expression_pairing_extends hExpression)
      leftCode
        godel_pairₘ(rightCode,
          godel_pairₘ(bodyCode,
            godel_pairₘ(leftResultCode, rightResultCode)))
      hLeftBound hRightPairBound
  apply equality_substitution_line_intro
    sequence certificates certificateCode payloadCode leftCode rightCode
      bodyCode leftResultCode rightResultCode index
  · simpa [certificateCode, payloadCode] using hPayloadBound
  · simpa [certificateCode, payloadCode] using hLogicalCertificate
  · exact hPayload
  · exact hLeftBound
  · exact hRightBound
  · exact hBodyBound
  · exact hLeftResultBound
  · exact hRightResultBound
  · exact Metatheory.Derives.equality_refl certificateCode
  · exact Metatheory.Derives.equality_refl payloadCode
  · exact hOpenLeft
  · exact hOpenRight
  · simpa [leftCode, rightCode, leftResultCode, rightResultCode] using hCurrent

/-- 两个类型化见证直接生成等式自反分支。 -/
theorem equality_reflexivity_branch_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (formula certificate payload term : SetOpenTerm free)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hTerm : Γ ⊢ₘ[T] term ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(11), payload))
    (hPayloadCode : Γ ⊢ₘ[T] payload ≐ₘ term)
    (hTermCode : Γ ⊢ₘ[T] term_code_atₘ(numₘ(0), term))
    (hFormula : Γ ⊢ₘ[T]
      formula ≐ₘ equality_reflexivity_axiom_code_term term) :
    Γ ⊢ₘ[T]
      (equality_reflexivity_branch (free := free)).condition_closed
        formula certificate := by
  change Γ ⊢ₘ[T]
    bounded_witness_closure equality_reflexivity_plan
      (equality_reflexivity_condition
        (weaken_bound_context equality_reflexivity_bound formula)
        (weaken_bound_context equality_reflexivity_bound certificate))
  let assignment :
      BoundedWitnessAssignment T Γ
        (equality_reflexivity_plan (free := free))
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] free) := by
    refine ⟨⟨payload, ?_⟩, ?_⟩
    · simpa [equality_reflexivity_plan, BoundedWitnessAssignment] using hPayload
    refine ⟨⟨term, ?_⟩, PUnit.unit⟩
    simpa [equality_reflexivity_plan, BoundedWitnessAssignment] using hTerm
  have hMatrix : Γ ⊢ₘ[T]
      (equality_reflexivity_condition
        (weaken_bound_context equality_reflexivity_bound formula)
        (weaken_bound_context equality_reflexivity_bound certificate)).substituteMapped
          assignment.finalSubstitution VariableSubstitution.freeId := by
    simpa [assignment, BoundedWitnessAssignment,
      BoundedWitnessAssignment.finalSubstitution,
      equality_reflexivity_condition, equality_reflexivity_payload,
      equality_reflexivity_term, term_payload_condition,
      equality_reflexivity_plan, weaken_bound_context_substituteMapped,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId] using!
      FirstOrder.Derives.conj_intro hCertificate
        (FirstOrder.Derives.conj_intro hPayloadCode
          (FirstOrder.Derives.conj_intro hTermCode hFormula))
  simpa using
    bounded_witness_closure_intro_assignment assignment _ hMatrix

/-- 等式自反分支直接进入统一逻辑证书表并生成 checked 行。 -/
theorem equality_reflexivity_line_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence certificates certificate payload term : SetOpenTerm free)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index)) certificate)
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code certificate)
    (hPayload : Γ ⊢ₘ[T] payload ∈ₘ ωₘ)
    (hTerm : Γ ⊢ₘ[T] term ∈ₘ ωₘ)
    (hCertificate : Γ ⊢ₘ[T]
      certificate ≐ₘ godel_pairₘ(numₘ(11), payload))
    (hPayloadCode : Γ ⊢ₘ[T] payload ≐ₘ term)
    (hTermCode : Γ ⊢ₘ[T] term_code_atₘ(numₘ(0), term))
    (hFormula : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        equality_reflexivity_axiom_code_term term) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  have hBranch : Γ ⊢ₘ[T]
      (equality_reflexivity_branch (free := free)).condition_closed
        (sequence ·ₘ numₘ(index)) certificate :=
    equality_reflexivity_branch_intro
      (sequence ·ₘ numₘ(index)) certificate payload term
      hPayload hTerm hCertificate hPayloadCode hTermCode hFormula
  exact logical_branch_line_intro equality_reflexivity_branch
    (by simp [logical_branches, first_order_branches])
    sequence certificates certificate index hPayloadBound hLogicalCertificate hBranch

/-- 宿主内在语法的 Quine quotation 直接生成等式自反 checked 行。 -/
theorem quote_equality_reflexivity_line_intro
    {σ : Signature} [QuineEncoding.QuotationNumbering σ]
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (term : Term σ [] free sort)
    (index : Nat)
    (hPayloadBound : Γ ⊢ₘ[T]
      certificate_payload_bound certificates (numₘ(index))
        (equality_reflexivity_certificate_code_term
          (QuineEncoding.quote_term term : SetOpenTerm [])))
    (hLogicalCertificate : Γ ⊢ₘ[T]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (equality_reflexivity_certificate_code_term
            (QuineEncoding.quote_term term : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        equality_reflexivity_axiom_code_term
          (QuineEncoding.quote_term term : SetOpenTerm [])) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        IntrinsicVerifier.checked_verifier sequence certificates index := by
  let termCode : SetOpenTerm [] := QuineEncoding.quote_term term
  let certificateCode : SetOpenTerm [] :=
    equality_reflexivity_certificate_code_term termCode
  have hTermCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), termCode) := by
    simpa [termCode] using QuineEncoding.quote_term_code_at term
  have hTermBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        termCode ∈ₘ ωₘ :=
    QuineEncoding.term_code_at_code_mem_of_derives
      (numₘ(0)) termCode hTermCodeFormal
  have hTermCode : Γ ⊢ₘ[T] term_code_atₘ(numₘ(0), termCode) :=
    lift_formal_derives hExpression hTermCodeFormal
  have hTermBound : Γ ⊢ₘ[T] termCode ∈ₘ ωₘ :=
    lift_formal_derives hExpression hTermBoundFormal
  apply equality_reflexivity_line_intro
    sequence certificates certificateCode termCode termCode index
  · simpa [certificateCode] using hPayloadBound
  · simpa [certificateCode] using hLogicalCertificate
  · exact hTermBound
  · exact hTermBound
  · exact Metatheory.Derives.equality_refl certificateCode
  · exact Metatheory.Derives.equality_refl termCode
  · exact hTermCode
  · simpa [termCode] using hCurrent

end IntrinsicFirstOrderLogicalLine
end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
