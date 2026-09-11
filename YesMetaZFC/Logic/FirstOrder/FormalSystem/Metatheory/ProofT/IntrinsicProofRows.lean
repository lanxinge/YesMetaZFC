import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomainSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSpaceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSupportTheory
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion

/-!
# ProofT 内在证明行索引

本模块只保留证明行反演中真正独立于编码器的部分：有限定义域等式把一个外部
有效索引送入对象定义域。行的具体值和公式码成员关系由上层编码器直接提供，
不再通过 `ObjectReplay`、token 序列或自由变量编号间接取得。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open QuineEncoding
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 证明行承载合同 -/

structure IntrinsicProofRowSupport (T : SetTheory)
    extends FiniteSequenceSpaceSupport T where
  formula_code_nonempty :
    ∀ {free : SetContext} {Γ : Context signature free},
      Γ ⊢ₘ[T] syntax_formula_code_set_term ≠ₘ ∅ₘ

namespace IntrinsicProofRowSupport

/-- 证明行承载支撑沿理论包含直接提升。 -/
theorem theory_weaken
    {T U : SetTheory}
    (S : IntrinsicProofRowSupport T)
    (hTU : Theory.Extends U T) :
    IntrinsicProofRowSupport U where
  toFiniteSequenceSpaceSupport :=
    S.toFiniteSequenceSpaceSupport.theory_weaken hTU
  formula_code_nonempty := by
    intro free Γ
    exact FirstOrder.Derives.theory_weaken hTU
      (S.formula_code_nonempty (Γ := Γ))

end IntrinsicProofRowSupport

def intrinsic_proof_row_theory : SetTheory :=
  Theory.union intrinsic_syntax_carrier_theory
    finite_sequence_support_theory

derive_theory_subset intrinsic_syntax_carrier_theory ⊆ intrinsic_proof_row_theory

derive_theory_subset finite_sequence_support_theory ⊆ intrinsic_proof_row_theory

theorem intrinsic_finite_sequence_space_support :
    FiniteSequenceSpaceSupport intrinsic_proof_row_theory :=
  finite_sequence_space_support_of_extends
    finite_sequence_support_theory_subset_intrinsic_proof_row_theory

theorem intrinsic_proof_row_support :
    IntrinsicProofRowSupport intrinsic_proof_row_theory where
  toFiniteSequenceSpaceSupport := intrinsic_finite_sequence_space_support
  formula_code_nonempty := by
    intro free Γ
    exact FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_proof_row_theory
      (intrinsic_syntax_carrier_formula_code_nonempty (Γ := Γ))

theorem intrinsic_proof_row_formula_code_nonempty
    {T : SetTheory} (S : IntrinsicProofRowSupport T)
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[T] syntax_formula_code_set_term ≠ₘ ∅ₘ := by
  exact S.formula_code_nonempty

theorem intrinsic_proof_row_numeral_mem_omega
    (number : Nat) :
    ([] : Context signature []) ⊢ₘ[intrinsic_proof_row_theory]
      (numₘ(number) : SetOpenTerm []) ∈ₘ ωₘ := by
  exact FirstOrder.Derives.theory_weaken
    intrinsic_syntax_carrier_theory_subset_intrinsic_proof_row_theory
    (FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      (finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) number))

theorem intrinsic_proof_row_quote_formula_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_proof_row_theory]
      (quote formula : SetOpenTerm []) ∈ₘ syntax_formula_code_set_term := by
  exact FirstOrder.Derives.theory_weaken
    intrinsic_syntax_carrier_theory_subset_intrinsic_proof_row_theory
     (intrinsic_syntax_carrier_quote_formula_mem formula)

theorem intrinsic_proof_row_quote_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_proof_row_theory]
      formula_code_atₘ(
        numₘ(bound.length),
        (quote formula : SetOpenTerm [])) := by
  exact FirstOrder.Derives.theory_weaken
    intrinsic_syntax_carrier_theory_subset_intrinsic_proof_row_theory
    (FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      (QuineEncoding.quote_formula_code_at formula))

theorem intrinsic_proof_row_quote_formula_element_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formulas : List (Formula σ bound free))
    {element : SetOpenTerm []}
    (hElement : element ∈ formulas.map
      (fun formula => (quote formula : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[intrinsic_proof_row_theory]
      element ∈ₘ syntax_formula_code_set_term := by
  rcases List.mem_map.mp hElement with ⟨formula, _, rfl⟩
  exact intrinsic_proof_row_quote_formula_mem formula

/-- 规范有限图在有效行位置的函数值等式。 -/
theorem row_value_of_standard_sequence
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (start : Nat) {elements : List (SetOpenTerm free)}
    (index : Nat) (hIndex : index < elements.length) :
    Γ ⊢ₘ[T]
      elements[index] ≐ₘ
        (standard_sequence_from start elements ·ₘ
          numₘ(start + index)) := by
  have hGet : elements[index]? = some elements[index] :=
    List.getElem?_eq_getElem hIndex
  exact standard_sequence_from_getElem?_apply_eq
    (Γ := Γ) S start hGet

/-- 规范证明行图在有效行位置的值等式。 -/
theorem proof_row_value_of_graph
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (rows : List (List Nat))
    (index : Nat) (hIndex : index < rows.length) :
    Γ ⊢ₘ[T]
      nat_sequence_graph_term rows[index] ≐ₘ
        (proof_sequence_graph_term rows ·ₘ numₘ(index)) := by
  let mappedRows : List (SetOpenTerm free) :=
    rows.map (fun row =>
      nat_sequence_graph_term (bound := []) (free := free) row)
  have hMappedIndex :
      index < mappedRows.length := by
    simpa [mappedRows] using hIndex
  simpa [mappedRows, proof_sequence_graph_term, standard_sequence] using
    (row_value_of_standard_sequence
      S
      (Γ := Γ)
      0
      (elements := mappedRows)
      index hMappedIndex)

/-- 规范证明行图的有效行值属于结构化公式码载体。 -/
theorem row_syntax_formula_mem_of_graph
    {T : SetTheory} (S : IntrinsicProofRowSupport T)
    {free : SetContext} {Γ : Context signature free}
    (rows : List (List Nat))
    (index : Nat) (hIndex : index < rows.length)
    (hSequence : Γ ⊢ₘ[T]
      proof_sequence_graph_term rows ∈ₘ
        seq₊_spaceₘ(syntax_formula_code_set_term)) :
    Γ ⊢ₘ[T]
      nat_sequence_graph_term rows[index] ∈ₘ
        syntax_formula_code_set_term := by
  have hFormulaCodeNonempty : Γ ⊢ₘ[T]
      syntax_formula_code_set_term ≠ₘ ∅ₘ :=
    intrinsic_proof_row_formula_code_nonempty S (Γ := Γ)
  have hOrdinary : Γ ⊢ₘ[T]
      proof_sequence_graph_term rows ∈ₘ
        seq_spaceₘ(syntax_formula_code_set_term) :=
    nonempty_sequence_space_member_implies_sequence_space
      S.toFiniteSequenceSpaceSupport syntax_formula_code_set_term
        (proof_sequence_graph_term rows)
      hFormulaCodeNonempty hSequence
  have hDomain : Γ ⊢ₘ[T]
      domₘ(proof_sequence_graph_term rows) ≐ₘ numₘ(rows.length) :=
    proof_sequence_graph_domain_eq
      (Γ := Γ) S.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport rows
  have hIndexMember : Γ ⊢ₘ[T]
      numₘ(index) ∈ₘ domₘ(proof_sequence_graph_term rows) :=
    row_index_mem_of_domain
      S.toFiniteSequenceSpaceSupport.toArithmeticSupport
      (proof_sequence_graph_term rows)
      rows.length index hDomain hIndex
  have hApplication : Γ ⊢ₘ[T]
      (proof_sequence_graph_term rows ·ₘ numₘ(index)) ∈ₘ
        syntax_formula_code_set_term :=
    sequence_space_member_application_mem
      S.toFiniteSequenceSpaceSupport syntax_formula_code_set_term
        (proof_sequence_graph_term rows) (numₘ(index))
      hFormulaCodeNonempty hOrdinary hIndexMember
  have hValue := proof_row_value_of_graph
    (Γ := Γ)
    S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport rows index hIndex
  exact FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality
      (nat_sequence_graph_term rows[index])
      (proof_sequence_graph_term rows ·ₘ numₘ(index))
      syntax_formula_code_set_term hValue)
    hApplication

theorem intrinsic_proof_row_formula_mem_of_graph
    {free : SetContext} {Γ : Context signature free}
    (rows : List (List Nat))
    (index : Nat) (hIndex : index < rows.length)
    (hSequence : Γ ⊢ₘ[intrinsic_proof_row_theory]
      proof_sequence_graph_term rows ∈ₘ
        seq₊_spaceₘ(syntax_formula_code_set_term)) :
    Γ ⊢ₘ[intrinsic_proof_row_theory]
      nat_sequence_graph_term rows[index] ∈ₘ
        syntax_formula_code_set_term :=
  row_syntax_formula_mem_of_graph
    intrinsic_proof_row_support rows index hIndex hSequence

private theorem numeral_ne_in_free_context
    {T : SetTheory}
    (A : ArithmeticSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    {left right : Nat}
    (hNe : left ≠ right) :
    Γ ⊢ₘ[T] ¬ₘ (numₘ(left) ≐ₘ numₘ(right)) := by
  have hClosed := A.numeral_arithmetic.numeral_ne hNe
  have hRenamed : ([] : Context signature free) ⊢ₘ[T]
      ¬ₘ (numₘ(left) ≐ₘ numₘ(right)) := by
    simpa [Formula.renameFree, Formula.rename, Renaming.free,
      Formula.renameMapped, Arguments.renameMapped,
      finite_numeral_term_renameMapped] using
      (FirstOrder.Derives.free_renaming
        (T := T)
        (VariableRenaming.empty : VariableRenaming [] free)
        hClosed)
  exact FirstOrder.Derives.context_weaken
    (Γ := ([] : Context signature free))
    (Δ := Γ)
    (by simp)
    hRenamed

/-- 不同自然数列表对应的内在有限图在对象层不可相等。 -/
theorem nat_sequence_graph_ne
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    {left right : List Nat}
    (hNe : left ≠ right) :
    Γ ⊢ₘ[T]
      ¬ₘ (nat_sequence_graph_term (bound := []) (free := free) left ≐ₘ
        nat_sequence_graph_term (bound := []) (free := free) right) := by
  let leftSequence : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free) left
  let rightSequence : SetOpenTerm free :=
    nat_sequence_graph_term (bound := []) (free := free) right
  let leftElements : List (SetOpenTerm free) :=
    left.map (fun token => numₘ(token))
  let rightElements : List (SetOpenTerm free) :=
    right.map (fun token => numₘ(token))
  let equality : SetOpenFormula free := leftSequence ≐ₘ rightSequence
  let Δ : Context signature free := equality :: Γ
  have hEquality : Δ ⊢ₘ[T] leftSequence ≐ₘ rightSequence := by
    simpa [equality, Δ] using
      (FirstOrder.Derives.assumption
        (T := T) (Γ := Δ) (formula := equality) (by simp [Δ]))
  apply FirstOrder.Derives.neg_intro
  by_cases hLength : left.length = right.length
  · have hWitness :
        ∃ (index : Nat) (hLeftIndex : index < left.length)
          (hRightIndex : index < right.length),
          left[index] ≠ right[index] :=
      Classical.byContradiction fun hNoWitness => by
        apply hNe
        apply List.ext_getElem hLength
        intro index hLeftIndex hRightIndex
        exact Classical.byContradiction fun hToken =>
          hNoWitness ⟨index, hLeftIndex, hRightIndex, hToken⟩
    rcases hWitness with
      ⟨index, hLeftIndex, hRightIndex, hToken⟩
    let leftToken := left[index]
    let rightToken := right[index]
    have hLeftGet :
        leftElements[index]? =
          some (numₘ(leftToken)) := by
      simp [leftElements, leftToken, hLeftIndex]
    have hRightGet :
        rightElements[index]? =
          some (numₘ(rightToken)) := by
      simp [rightElements, rightToken, hRightIndex]
    have hLeftValue : Δ ⊢ₘ[T]
        (leftSequence ·ₘ numₘ(index)) ≐ₘ numₘ(leftToken) := by
      have hValue :=
        standard_sequence_from_getElem?_apply_eq
          (Γ := Δ) S 0 hLeftGet
      exact Metatheory.Derives.equality_symm <| by
        simpa [leftSequence, nat_sequence_graph_term, standard_sequence] using
          hValue
    have hRightValue : Δ ⊢ₘ[T]
        (rightSequence ·ₘ numₘ(index)) ≐ₘ numₘ(rightToken) := by
      have hValue :=
        standard_sequence_from_getElem?_apply_eq
          (Γ := Δ) S 0 hRightGet
      exact Metatheory.Derives.equality_symm <| by
        simpa [rightSequence, nat_sequence_graph_term, standard_sequence] using
          hValue
    have hApplicationEquality : Δ ⊢ₘ[T]
        (leftSequence ·ₘ numₘ(index)) ≐ₘ
          (rightSequence ·ₘ numₘ(index)) :=
      function_application_term_congr_function_of_equality
        leftSequence rightSequence (numₘ(index)) hEquality
    have hLeftValueSymm : Δ ⊢ₘ[T]
        numₘ(leftToken) ≐ₘ (leftSequence ·ₘ numₘ(index)) :=
      Metatheory.Derives.equality_symm hLeftValue
    have hLeftToRightApplication : Δ ⊢ₘ[T]
        numₘ(leftToken) ≐ₘ (rightSequence ·ₘ numₘ(index)) :=
      Metatheory.Derives.equality_trans
        hLeftValueSymm hApplicationEquality
    have hTokenEquality : Δ ⊢ₘ[T]
        numₘ(leftToken) ≐ₘ numₘ(rightToken) :=
      Metatheory.Derives.equality_trans
        hLeftToRightApplication hRightValue
    exact FirstOrder.Derives.neg_elim
      hTokenEquality
      (FirstOrder.Derives.context_weaken_cons
        (numeral_ne_in_free_context
          S.toArithmeticSupport
          (Γ := Γ)
          hToken))
  · have hLeftDomain : Δ ⊢ₘ[T]
        domₘ(leftSequence) ≐ₘ numₘ(left.length) := by
      simpa [leftSequence] using
        (nat_sequence_graph_domain_eq
          (Γ := Δ) S.toFiniteSequenceGraphSupport left)
    have hRightDomain : Δ ⊢ₘ[T]
        domₘ(rightSequence) ≐ₘ numₘ(right.length) := by
      simpa [rightSequence] using
        (nat_sequence_graph_domain_eq
          (Γ := Δ) S.toFiniteSequenceGraphSupport right)
    let domainContext : SetTerm [SetSort.set] free :=
      domₘ(.bvar .here)
    have hDomainEquality : Δ ⊢ₘ[T]
        domₘ(leftSequence) ≐ₘ domₘ(rightSequence) := by
      simpa [domainContext] using!
        (Metatheory.Derives.term_context_congr_of_equality
          (T := T) (Γ := Δ) domainContext hEquality)
    have hLeftDomainSymm : Δ ⊢ₘ[T]
        numₘ(left.length) ≐ₘ domₘ(leftSequence) :=
      Metatheory.Derives.equality_symm hLeftDomain
    have hLeftLengthToRightDomain : Δ ⊢ₘ[T]
        numₘ(left.length) ≐ₘ domₘ(rightSequence) :=
      Metatheory.Derives.equality_trans
        hLeftDomainSymm hDomainEquality
    have hLengthEquality : Δ ⊢ₘ[T]
        numₘ(left.length) ≐ₘ numₘ(right.length) :=
      Metatheory.Derives.equality_trans
        hLeftLengthToRightDomain hRightDomain
    exact FirstOrder.Derives.neg_elim
      hLengthEquality
      (FirstOrder.Derives.context_weaken_cons
        (numeral_ne_in_free_context
          S.toArithmeticSupport
          (Γ := Γ)
          hLength))

/-! ## 等式上下文归一 -/

/-- 将等式左端下的矛盾上下文直接迁移到等式右端。 -/
theorem falsum_of_equality_context_transport
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (left right conclusion : SetOpenTerm free)
    (hValue : Γ ⊢ₘ[T] left ≐ₘ right)
    (hMismatch :
      (conclusion ≐ₘ left) :: Γ ⊢ₘ[T] Formula.falsum) :
    (conclusion ≐ₘ right) :: Γ ⊢ₘ[T] Formula.falsum := by
  let body : SetFormula [SetSort.set] free :=
    (conclusion.weakenBound SetSort.set) ≐ₘ (.bvar .here)
  have hIff : Γ ⊢ₘ[T]
      (conclusion ≐ₘ left) ↔ₘ (conclusion ≐ₘ right) := by
    simpa [body] using!
      (Metatheory.Derives.equality_iff_of_equality
        (T := T) (Γ := Γ)
        (sort := SetSort.set)
        (left := left) (right := right)
        (body := body) hValue)
  have hNeg : Γ ⊢ₘ[T] ¬ₘ(conclusion ≐ₘ left) :=
    FirstOrder.Derives.neg_intro hMismatch
  have hRight : (conclusion ≐ₘ right) :: Γ ⊢ₘ[T]
      conclusion ≐ₘ right :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hLeft : (conclusion ≐ₘ right) :: Γ ⊢ₘ[T]
      conclusion ≐ₘ left :=
    FirstOrder.Derives.iff_elim_right
      (FirstOrder.Derives.context_weaken_cons hIff) hRight
  exact FirstOrder.Derives.neg_elim hLeft
    (FirstOrder.Derives.context_weaken_cons hNeg)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
