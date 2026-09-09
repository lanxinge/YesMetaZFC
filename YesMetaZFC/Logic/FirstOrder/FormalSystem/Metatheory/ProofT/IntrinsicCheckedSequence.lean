import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedLine

/-!
# ProofT 内在 checked 序列装配

本模块把有限逐行证书与序列的结构事实一次性装配为 `CheckedVerifier.sequence_condition`。
定义域只通过已证等式连接外部长度，内部负责有限全称及等式运输；调用方不再展开
逐行 binder，也不提供自由变量编号、新鲜性或 admissibility 合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicCheckedSequence

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition

set_option autoImplicit false

/-- checked 序列在量词内部使用的规范逐行公式体。 -/
def row_body
    (verifier : CheckedVerifier)
    {free : SetContext}
    (sequence certificates : SetOpenTerm free) :
    SetFormula [SetSort.set] free :=
  let sequenceOne : SetTerm [SetSort.set] free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm [SetSort.set] free :=
    certificates.weakenBound SetSort.set
  let indexVariable : SetTerm [SetSort.set] free := .bvar .here
  verifier.formula_condition
      (sequenceOne ·ₘ indexVariable) ∧ₘ
    verifier.line_condition
      sequenceOne certificatesOne indexVariable

/-- 一个具体外部下标处的公式良构与 checked 行条件。 -/
def row_instance
    (verifier : CheckedVerifier)
    {free : SetContext}
    (sequence certificates : SetOpenTerm free)
    (index : Nat) : SetOpenFormula free :=
  verifier.formula_condition
      (sequence ·ₘ numₘ(index)) ∧ₘ
    IntrinsicCheckedLine.line_instance
      verifier sequence certificates index

theorem formula_condition_of_equality
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right)
    (hLeft : Γ ⊢ₘ[T] verifier.formula_condition left) :
    Γ ⊢ₘ[T] verifier.formula_condition right := by
  let body : SetFormula [SetSort.set] free :=
    verifier.formula_condition (.bvar .here)
  have hIffRaw := Metatheory.Derives.equality_iff_of_equality
    (T := T) (Γ := Γ) (sort := SetSort.set)
    (left := left) (right := right) (body := body) hEquality
  have hIff : Γ ⊢ₘ[T]
      verifier.formula_condition left ↔ₘ
        verifier.formula_condition right := by
    have hLeftEq :
        Formula.instantiateTop left
            (FormulaTemplate.apply_one verifier.formula_condition (.bvar .here)) =
          verifier.formula_condition left :=
      FormulaTemplate.apply_one_instantiateTop_bvar
        verifier.formula_condition left
    have hRightEq :
        Formula.instantiateTop right
            (FormulaTemplate.apply_one verifier.formula_condition (.bvar .here)) =
          verifier.formula_condition right :=
      FormulaTemplate.apply_one_instantiateTop_bvar
        verifier.formula_condition right
    simpa only [body, hLeftEq, hRightEq] using hIffRaw
  exact FirstOrder.Derives.iff_elim_left hIff hLeft

/-- 规范逐行公式以 numeral 实例化后直接恢复外部行实例。 -/
@[simp] theorem row_body_instantiateTop
    (verifier : CheckedVerifier)
    {free : SetContext}
    (sequence certificates : SetOpenTerm free)
    (index : Nat) :
    (row_body verifier sequence certificates).instantiateTop
        (numₘ(index)) =
      row_instance verifier sequence certificates index := by
  change
    (Formula.conj
      (verifier.formula_condition
        (sequence.weakenBound SetSort.set ·ₘ
          ((.bvar .here) : SetTerm [SetSort.set] free)))
      (verifier.line_condition
        (sequence.weakenBound SetSort.set)
        (certificates.weakenBound SetSort.set)
        ((.bvar .here) : SetTerm [SetSort.set] free))).instantiateTop
          (numₘ(index)) =
      Formula.conj
        (verifier.formula_condition
          (sequence ·ₘ numₘ(index)))
        (verifier.line_condition
          sequence certificates (numₘ(index)))
  rw [Formula.instantiateTop_conj]
  congr 1
  · exact FormulaTemplate.apply_one_instantiateTop
      verifier.formula_condition sequence (numₘ(index))
  · change
      Formula.substituteMapped
          (VariableSubstitution.instantiateTop (numₘ(index)))
          VariableSubstitution.freeId
          (verifier.line_condition
            (sequence.weakenBound SetSort.set)
            (certificates.weakenBound SetSort.set)
            ((.bvar .here) : SetTerm [SetSort.set] free)) =
        verifier.line_condition sequence certificates (numₘ(index))
    rw [CheckedVerifier.line_condition_substituteMapped]
    simp only [
      FormulaTemplate.term_substituteMapped_instantiateTop_weakenBound,
      Term.substituteMapped, VariableSubstitution.instantiateTop]

/--
定义域等于外部 numeral 时，由全部有限行证书装配完整 checked 序列条件。
序列空间、证书空间、共同定义域与非空性均保持为最弱的直接结构前提。
-/
theorem intro_of_numeral_domain
    {T : SetTheory}
    (C : FiniteCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (sequence certificates : SetOpenTerm free)
    (length : Nat)
    (hSequenceSpace :
      Γ ⊢ₘ[T]
        sequence ∈ₘ seq₊_spaceₘ(syntax_formula_code_set_term))
    (hCertificatesSpace :
      Γ ⊢ₘ[T] certificates ∈ₘ seq₊_spaceₘ(ωₘ))
    (hDomains :
      Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ domₘ(certificates))
    (hDomain :
      Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(length))
    (hZero :
      Γ ⊢ₘ[T] numₘ(0) ∈ₘ domₘ(sequence))
    (hRows :
      ∀ index, index < length →
        Γ ⊢ₘ[T] row_instance verifier sequence certificates index) :
    Γ ⊢ₘ[T] verifier.sequence_condition sequence certificates := by
  let lineBody : SetFormula [SetSort.set] free :=
    row_body verifier sequence certificates
  have hLineAt :
      ∀ index, index < length →
        Γ ⊢ₘ[T] lineBody.instantiateTop (numₘ(index)) := by
    intro index hIndex
    simpa only [lineBody, row_body_instantiateTop] using
      hRows index hIndex
  have hAllNumeral :
      Γ ⊢ₘ[T]
        Formula.LevyBound.boundedForall set_levy_bound
          (numₘ(length)) lineBody :=
    bounded_forall_numeral_intro C length lineBody hLineAt
  have hAllDomain : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound (domₘ(sequence)) lineBody :=
    bounded_forall_of_bound_eq hDomain hAllNumeral
  have hPrefix :
      Γ ⊢ₘ[T]
        ((((sequence ∈ₘ
              seq₊_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
            (certificates ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ
          (domₘ(sequence) ≐ₘ domₘ(certificates))) ∧ₘ
        (numₘ(0) ∈ₘ domₘ(sequence))) :=
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          hSequenceSpace hCertificatesSpace)
        hDomains)
      hZero
  simpa [CheckedVerifier.sequence_condition,
    StructuredCertificateCondition.sequence_condition,
    lineBody, row_body] using!
    FirstOrder.Derives.conj_intro hPrefix hAllDomain

/-- 正长度定义域自动给出零下标成员，不再要求调用方单独证明非空性。 -/
theorem intro_of_positive_numeral_domain
    {T : SetTheory}
    (A : ArithmeticSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (sequence certificates : SetOpenTerm free)
    (length : Nat)
    (hSequenceSpace :
      Γ ⊢ₘ[T]
        sequence ∈ₘ seq₊_spaceₘ(syntax_formula_code_set_term))
    (hCertificatesSpace :
      Γ ⊢ₘ[T] certificates ∈ₘ seq₊_spaceₘ(ωₘ))
    (hDomains :
      Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ domₘ(certificates))
    (hDomain :
      Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(length))
    (hPositive : 0 < length)
    (hRows :
      ∀ index, index < length →
        Γ ⊢ₘ[T] row_instance verifier sequence certificates index) :
    Γ ⊢ₘ[T] verifier.sequence_condition sequence certificates := by
  exact intro_of_numeral_domain
    (ArithmeticSupport.finite_core A)
    verifier sequence certificates length
    hSequenceSpace hCertificatesSpace hDomains hDomain
    (row_index_mem_of_domain
      A sequence length 0 hDomain hPositive)
    hRows

/-! ## 标准宿主序列装配 -/

private theorem omega_nonempty_of_numeral_member
    {T : SetTheory}
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (number : Nat)
    (hNumber : Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ := by
  have hImp : Γ ⊢ₘ[T]
      (numₘ(number) ∈ₘ (ωₘ : SetOpenTerm free)) ⟶ₘ
        (ωₘ ≠ₘ (∅ₘ : SetOpenTerm free)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.toArithmeticSupport.contains_empty_set hSentence)
      (member_implies_set_nonempty
        (Γ := Γ)
        (numₘ(number) : SetOpenTerm free)
        (ωₘ : SetOpenTerm free))
  exact FirstOrder.Derives.imp_elim hImp hNumber

/-- 两列外部标准元素直接生产 checked verifier 的完整序列条件。 -/
theorem intro_of_standard_sequences
    {T : SetTheory}
    (R : IntrinsicProofRowSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (elements certificates : List (SetOpenTerm free))
    (hLength : elements.length = certificates.length)
    (hLengthOmega :
      Γ ⊢ₘ[T] numₘ(elements.length) ∈ₘ ωₘ)
    (hElementMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ syntax_formula_code_set_term)
    (hCertificateMember : ∀ certificate, certificate ∈ certificates →
      Γ ⊢ₘ[T] certificate ∈ₘ ωₘ)
    (hElementsNonempty : elements ≠ [])
    (hRows : ∀ index, index < elements.length →
      Γ ⊢ₘ[T]
        row_instance verifier
          (standard_sequence elements)
          (standard_sequence certificates) index) :
    Γ ⊢ₘ[T]
      verifier.sequence_condition
        (standard_sequence elements)
        (standard_sequence certificates) := by
  let S : FiniteSequenceSpaceSupport T := R.toFiniteSequenceSpaceSupport
  have hOmegaNonempty : Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ :=
    omega_nonempty_of_numeral_member S elements.length hLengthOmega
  have hCertificatesNonempty : certificates ≠ [] := by
    intro hEmpty
    apply hElementsNonempty
    apply List.eq_nil_of_length_eq_zero
    simpa [hEmpty] using hLength
  have hCertificatesLengthOmega :
      Γ ⊢ₘ[T] numₘ(certificates.length) ∈ₘ ωₘ := by
    simpa [hLength] using hLengthOmega
  have hSequenceSpace : Γ ⊢ₘ[T]
      standard_sequence elements ∈ₘ
        seq₊_spaceₘ(syntax_formula_code_set_term) :=
    standard_sequence_mem_nonempty_sequence_space
      S elements syntax_formula_code_set_term hLengthOmega
      (R.formula_code_nonempty (Γ := Γ))
      hElementMember hElementsNonempty
  have hCertificatesSpace : Γ ⊢ₘ[T]
      standard_sequence certificates ∈ₘ seq₊_spaceₘ(ωₘ) :=
    standard_sequence_mem_nonempty_sequence_space
      S certificates ωₘ hCertificatesLengthOmega hOmegaNonempty
      hCertificateMember hCertificatesNonempty
  have hSequenceDomain : Γ ⊢ₘ[T]
      domₘ(standard_sequence elements) ≐ₘ numₘ(elements.length) :=
    standard_sequence_domain_eq
      (Γ := Γ) S.toFiniteSequenceGraphSupport
      (elements := elements)
  have hCertificatesDomain : Γ ⊢ₘ[T]
      domₘ(standard_sequence certificates) ≐ₘ
        numₘ(certificates.length) :=
    standard_sequence_domain_eq
      (Γ := Γ) S.toFiniteSequenceGraphSupport
      (elements := certificates)
  have hLengthEquality : Γ ⊢ₘ[T]
      numₘ(elements.length) ≐ₘ numₘ(certificates.length) := by
    simpa [hLength] using
      (Metatheory.Derives.equality_refl
        (T := T) (Γ := Γ) (numₘ(certificates.length)))
  have hDomains : Γ ⊢ₘ[T]
      domₘ(standard_sequence elements) ≐ₘ
        domₘ(standard_sequence certificates) :=
    Metatheory.Derives.equality_trans hSequenceDomain
      (Metatheory.Derives.equality_trans hLengthEquality
        (Metatheory.Derives.equality_symm hCertificatesDomain))
  have hPositive : 0 < elements.length := by
    cases elements with
    | nil => exact (hElementsNonempty rfl).elim
    | cons head tail => simp
  exact intro_of_positive_numeral_domain
    S.toArithmeticSupport verifier
    (standard_sequence elements)
    (standard_sequence certificates)
    elements.length
    hSequenceSpace hCertificatesSpace hDomains hSequenceDomain
    hPositive hRows

/-- 同一行列表生成两列；取值对应、长度及成员装配只证明一次。 -/
theorem intro_of_mapped_rows
    {T : SetTheory} (R : IntrinsicProofRowSupport T)
    {free : SetContext} {Γ : Context signature free} {Row : Type _}
    (verifier : CheckedVerifier) (rows : List Row)
    (formulaCode certificateCode : Row → SetOpenTerm free)
    (hNonempty : rows ≠ [])
    (hLengthOmega : Γ ⊢ₘ[T] numₘ(rows.length) ∈ₘ ωₘ)
    (hFormula : ∀ row, row ∈ rows →
      Γ ⊢ₘ[T] formulaCode row ∈ₘ syntax_formula_code_set_term)
    (hCertificate : ∀ row, row ∈ rows →
      Γ ⊢ₘ[T] certificateCode row ∈ₘ ωₘ)
    (hRow : ∀ (index : Nat) (hIndex : index < rows.length),
      Γ ⊢ₘ[T] (standard_sequence (rows.map formulaCode) ·ₘ numₘ(index)) ≐ₘ
        formulaCode rows[index] →
      Γ ⊢ₘ[T] (standard_sequence (rows.map certificateCode) ·ₘ numₘ(index)) ≐ₘ
        certificateCode rows[index] →
      Γ ⊢ₘ[T] row_instance verifier
        (standard_sequence (rows.map formulaCode))
        (standard_sequence (rows.map certificateCode)) index) :
    Γ ⊢ₘ[T] verifier.sequence_condition
      (standard_sequence (rows.map formulaCode))
      (standard_sequence (rows.map certificateCode)) := by
  apply intro_of_standard_sequences R verifier
  · simp
  · simpa using hLengthOmega
  · intro element hElement
    obtain ⟨row, hMember, rfl⟩ := List.mem_map.mp hElement
    exact hFormula row hMember
  · intro certificate hCertificateMember
    obtain ⟨row, hMember, rfl⟩ := List.mem_map.mp hCertificateMember
    exact hCertificate row hMember
  · simpa using hNonempty
  · intro index hIndex
    have hIndexRows : index < rows.length := by simpa using hIndex
    have hAt (code : Row → SetOpenTerm free) :
        Γ ⊢ₘ[T] (standard_sequence (rows.map code) ·ₘ numₘ(index)) ≐ₘ code rows[index] := by
      apply Metatheory.Derives.equality_symm
      simpa only [Nat.zero_add] using
        (standard_sequence_from_getElem?_apply_eq
          (S := R.toFiniteSequenceEvaluationSupport) (start := 0)
          (elements := rows.map code) (index := index) (element := code rows[index])
          (by simp [List.getElem?_eq_getElem hIndexRows]))
    exact hRow index hIndexRows (hAt formulaCode) (hAt certificateCode)

end IntrinsicCheckedSequence
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
