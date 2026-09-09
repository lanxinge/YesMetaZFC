import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows

/-!
# ProofT 内在终端条件

终端条件对结论项的等式运输直接由类型化公式模板完成。这里不再选择编号变量、
计算自由支撑或证明替换与新鲜性的旁证；量化变量由 `proof_sequence_terminal_condition`
自身的 bound 上下文携带。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 终端条件的单结论项模板；顶部 bound 槽保留待替换的结论项。 -/
def terminal_condition_template
    {free : SetContext}
    (sequence : SetOpenTerm free) :
    SetFormula [SetSort.set] free :=
  let body : SetOpenFormula (SetSort.set :: free) :=
    proof_sequence_terminal_condition
      (sequence.weakenFree SetSort.set) (.fvar .here)
  body.abstractFreeTop

/-- 终端条件的单序列项模板；顶部 free 槽保留待替换的序列项。 -/
def terminal_sequence_template
    {free : SetContext}
    (conclusion : SetOpenTerm free) :
    SetFormula [SetSort.set] free :=
  let body : SetOpenFormula (SetSort.set :: free) :=
    proof_sequence_terminal_condition
      (.fvar .here) (conclusion.weakenFree SetSort.set)
  body.abstractFreeTop

/-- 终端条件沿结论项等式保持。 -/
theorem terminal_condition_of_conclusion_eq
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right)
    (hTerminal :
      Γ ⊢ₘ[T]
        proof_sequence_terminal_condition sequence left) :
    Γ ⊢ₘ[T]
      proof_sequence_terminal_condition sequence right := by
  let body : SetFormula [SetSort.set] free :=
    terminal_condition_template sequence
  have hIff :
      Γ ⊢ₘ[T]
        body.instantiateTop left ↔ₘ body.instantiateTop right :=
    Metatheory.Derives.equality_iff_of_equality body hEquality
  have hLeft : Γ ⊢ₘ[T] body.instantiateTop left := by
    change Γ ⊢ₘ[T]
      (Formula.abstractFreeTop
        (proof_sequence_terminal_condition
          (sequence.weakenFree SetSort.set) (.fvar .here))).instantiateTop left
    rw [Formula.instantiateTop_abstractFreeTop]
    simpa [proof_sequence_terminal_condition, Formula.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Substitution.instantiateFreeTop, Formula.LevyBound.boundedExists,
      Formula.LevyBound.membership, Formula.abstractFreeTop,
      Substitution.abstractFreeTop, VariableSubstitution.abstractFreeTop,
      VariableSubstitution.abstractBound, Term.substituteMapped,
      Arguments.substituteMapped] using! hTerminal
  have hRight : Γ ⊢ₘ[T] body.instantiateTop right :=
    FirstOrder.Derives.iff_elim_left hIff hLeft
  change Γ ⊢ₘ[T]
    (Formula.abstractFreeTop
      (proof_sequence_terminal_condition
        (sequence.weakenFree SetSort.set) (.fvar .here))).instantiateTop right at hRight
  rw [Formula.instantiateTop_abstractFreeTop] at hRight
  simpa [proof_sequence_terminal_condition, Formula.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Substitution.instantiateFreeTop, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, Formula.abstractFreeTop,
    Substitution.abstractFreeTop, VariableSubstitution.abstractFreeTop,
    VariableSubstitution.abstractBound, Term.substituteMapped,
    Arguments.substituteMapped] using! hRight

/-- 终端条件沿序列项等式保持。 -/
theorem terminal_condition_of_sequence_eq
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (left right conclusion : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right)
    (hTerminal :
      Γ ⊢ₘ[T]
        proof_sequence_terminal_condition left conclusion) :
    Γ ⊢ₘ[T]
      proof_sequence_terminal_condition right conclusion := by
  let body : SetFormula [SetSort.set] free :=
    terminal_sequence_template conclusion
  have hIff :
      Γ ⊢ₘ[T]
        body.instantiateTop left ↔ₘ body.instantiateTop right :=
    Metatheory.Derives.equality_iff_of_equality body hEquality
  have hLeft : Γ ⊢ₘ[T] body.instantiateTop left := by
    change Γ ⊢ₘ[T]
      (Formula.abstractFreeTop
        (proof_sequence_terminal_condition
          (.fvar .here) (conclusion.weakenFree SetSort.set))).instantiateTop left
    rw [Formula.instantiateTop_abstractFreeTop]
    simpa [proof_sequence_terminal_condition, Formula.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Substitution.instantiateFreeTop, Formula.LevyBound.boundedExists,
      Formula.LevyBound.membership, Formula.abstractFreeTop,
      Substitution.abstractFreeTop, VariableSubstitution.abstractFreeTop,
      VariableSubstitution.abstractBound, Term.substituteMapped,
      Arguments.substituteMapped] using! hTerminal
  have hRight : Γ ⊢ₘ[T] body.instantiateTop right :=
    FirstOrder.Derives.iff_elim_left hIff hLeft
  change Γ ⊢ₘ[T]
    (Formula.abstractFreeTop
      (proof_sequence_terminal_condition
        (.fvar .here) (conclusion.weakenFree SetSort.set))).instantiateTop right at hRight
  rw [Formula.instantiateTop_abstractFreeTop] at hRight
  simpa [proof_sequence_terminal_condition, Formula.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Substitution.instantiateFreeTop, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, Formula.abstractFreeTop,
    Substitution.abstractFreeTop, VariableSubstitution.abstractFreeTop,
    VariableSubstitution.abstractBound, Term.substituteMapped,
    Arguments.substituteMapped] using! hRight

/-! ## 有限定义域的末行消去 -/

private theorem open_term_bound_substitute_newest
    {free : SetContext}
    (term : SetOpenTerm free) :
    (term.weakenBound SetSort.set).substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := signature) (free := free)
            SetSort.set))
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken SetSort.set)) =
      term.weakenFree SetSort.set := by
  exact Term.openBoundTop_weakenBound SetSort.set term

/-- 有限定义域的终端条件在最后值不匹配时推出矛盾。 -/
theorem terminal_falsum_of_domain_eq
    {T : SetTheory}
    (C : FiniteCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence conclusion : SetOpenTerm free)
    (length : Nat)
    (hDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(length))
    (hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition sequence conclusion)
    (hMismatch :
      ∀ index, index < length → length = index + 1 →
        (conclusion ≐ₘ (sequence ·ₘ numₘ(index))) :: Γ
          ⊢ₘ[T] Formula.falsum) :
    Γ ⊢ₘ[T] Formula.falsum := by
  let sequenceOne : SetTerm [SetSort.set] free :=
    sequence.weakenBound SetSort.set
  let conclusionOne : SetTerm [SetSort.set] free :=
    conclusion.weakenBound SetSort.set
  let body : SetFormula [SetSort.set] free :=
    (domₘ(sequenceOne) ≐ₘ Sₘ(.bvar .here)) ∧ₘ
      (conclusionOne ≐ₘ (sequenceOne ·ₘ .bvar .here))
  have hExist : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound
        (domₘ(sequence)) body := by
    simpa [proof_sequence_terminal_condition, body, sequenceOne,
      conclusionOne] using hTerminal
  apply bounded_exists_elim
    (domₘ(sequence)) body Formula.falsum hExist
  let opened : SetOpenFormula (SetSort.set :: free) :=
    Formula.openBoundTop (σ := signature) SetSort.set
      (bounded_exists_body (domₘ(sequence)) body)
  let Δ : Context signature (SetSort.set :: free) :=
    opened :: FreshVariable.extendContext SetSort.set Γ
  change Δ ⊢ₘ[T] Formula.falsum
  let witness : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  have hOpened : Δ ⊢ₘ[T] opened :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hOpened' : Δ ⊢ₘ[T]
      (witness ∈ₘ domₘ(sequence.weakenFree SetSort.set)) ∧ₘ
        ((domₘ(sequence.weakenFree SetSort.set) ≐ₘ Sₘ(witness)) ∧ₘ
          (conclusion.weakenFree SetSort.set ≐ₘ
            (sequence.weakenFree SetSort.set ·ₘ witness))) := by
    simpa [opened, bounded_exists_body, body, sequenceOne,
      conclusionOne, witness,
      Formula.openBoundTop, Formula.LevyBound.membership,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateTop,
      VariableSubstitution.of_renaming, VariableSubstitution.freeId,
      VariableSubstitution.boundId, open_term_bound_substitute_newest,
      Term.renameMapped, Arguments.renameMapped,
      VariableRenaming.comp, VariableRenaming.id,
      VariableRenaming.weaken] using! hOpened
  have hWitnessMember : Δ ⊢ₘ[T]
      witness ∈ₘ domₘ(sequence.weakenFree SetSort.set) := by
    exact FirstOrder.Derives.conj_elim_left hOpened'
  have hLast : Δ ⊢ₘ[T]
      (domₘ(sequence.weakenFree SetSort.set) ≐ₘ Sₘ(witness)) ∧ₘ
        (conclusion.weakenFree SetSort.set ≐ₘ
          (sequence.weakenFree SetSort.set ·ₘ witness)) := by
    exact FirstOrder.Derives.conj_elim_right hOpened'
  have hDomainAt : Δ ⊢ₘ[T]
      domₘ(sequence.weakenFree SetSort.set) ≐ₘ
        (numₘ(length)).weakenFree SetSort.set := by
    have hWeakened := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set) hDomain
    have hBase : FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
        domₘ(sequence.weakenFree SetSort.set) ≐ₘ
          (numₘ(length)).weakenFree SetSort.set := by
      simpa only [FreshVariable.extendContext, Formula.weakenFree,
        Formula.renameFree, Renaming.weakenFree] using! hWeakened
    exact FirstOrder.Derives.context_weaken_cons hBase
  have hIndexMember : Δ ⊢ₘ[T] witness ∈ₘ numₘ(length) := by
    simpa only [finite_numeral_term_weakenFree] using
      (FirstOrder.Derives.iff_elim_left
        (membership_right_iff_of_equality
          witness
          (domₘ(sequence.weakenFree SetSort.set))
          ((numₘ(length)).weakenFree SetSort.set)
          hDomainAt)
        hWitnessMember)
  refine C.member_elim length witness Formula.falsum ?_ ?_
  · exact hIndexMember
  · intro index hIndex
    let Ε : Context signature (SetSort.set :: free) :=
      (witness ≐ₘ numₘ(index)) :: Δ
    have hIndexEquality : Ε ⊢ₘ[T]
        witness ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Ε])
    have hDomainWitness : Δ ⊢ₘ[T]
        domₘ(sequence.weakenFree SetSort.set) ≐ₘ Sₘ(witness) :=
      FirstOrder.Derives.conj_elim_left hLast
    have hConclusionWitness : Δ ⊢ₘ[T]
        conclusion.weakenFree SetSort.set ≐ₘ
          (sequence.weakenFree SetSort.set ·ₘ witness) :=
      FirstOrder.Derives.conj_elim_right hLast
    have hDomainWitnessAt : Ε ⊢ₘ[T]
        domₘ(sequence.weakenFree SetSort.set) ≐ₘ Sₘ(witness) :=
      FirstOrder.Derives.context_weaken_cons hDomainWitness
    have hSuccessorEquality : Ε ⊢ₘ[T]
        Sₘ(witness) ≐ₘ Sₘ(numₘ(index)) :=
      successor_term_congr_of_equality
        witness (numₘ(index)) hIndexEquality
    have hDomainIndex : Ε ⊢ₘ[T]
        domₘ(sequence.weakenFree SetSort.set) ≐ₘ
          (numₘ(index + 1)).weakenFree SetSort.set := by
      simpa [finite_numeral_term, successor_term] using
        Metatheory.Derives.equality_trans
          hDomainWitnessAt hSuccessorEquality
    have hDomainAt' : Ε ⊢ₘ[T]
        domₘ(sequence.weakenFree SetSort.set) ≐ₘ
          (numₘ(length)).weakenFree SetSort.set :=
      FirstOrder.Derives.context_weaken_cons hDomainAt
    have hLengthEquality : Ε ⊢ₘ[T]
        (numₘ(length)).weakenFree SetSort.set ≐ₘ
          (numₘ(index + 1)).weakenFree SetSort.set :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hDomainAt') hDomainIndex
    by_cases hLastIndex : length = index + 1
    · have hConclusionWitnessAt : Ε ⊢ₘ[T]
          conclusion.weakenFree SetSort.set ≐ₘ
            (sequence.weakenFree SetSort.set ·ₘ witness) :=
        FirstOrder.Derives.context_weaken_cons hConclusionWitness
      have hApplicationEquality : Ε ⊢ₘ[T]
          (sequence.weakenFree SetSort.set ·ₘ witness) ≐ₘ
            (sequence.weakenFree SetSort.set ·ₘ numₘ(index)) :=
        function_application_term_congr_argument_of_equality
          (sequence.weakenFree SetSort.set) witness (numₘ(index))
          hIndexEquality
      have hTargetEquality : Ε ⊢ₘ[T]
          conclusion.weakenFree SetSort.set ≐ₘ
            (sequence.weakenFree SetSort.set ·ₘ numₘ(index)) :=
        Metatheory.Derives.equality_trans
          hConclusionWitnessAt
          (Metatheory.Derives.equality_trans
            hApplicationEquality
            (Metatheory.Derives.equality_refl
              (T := T) (Γ := Ε)
              (sequence.weakenFree SetSort.set ·ₘ numₘ(index))))
      have hMismatchAt :
          ((conclusion.weakenFree SetSort.set ≐ₘ
              (sequence.weakenFree SetSort.set ·ₘ numₘ(index))) ::
            FreshVariable.extendContext SetSort.set Γ) ⊢ₘ[T]
            Formula.falsum := by
        have hRenamed := FirstOrder.Derives.free_renaming
          (T := T) (VariableRenaming.weaken SetSort.set)
          (hMismatch index hIndex hLastIndex)
        have hHead :
            Formula.renameFree (VariableRenaming.weaken SetSort.set)
                (conclusion ≐ₘ (sequence ·ₘ numₘ(index))) =
              conclusion.weakenFree SetSort.set ≐ₘ
                (sequence.weakenFree SetSort.set ·ₘ numₘ(index)) := by
          simp [Formula.renameFree, Formula.rename, Renaming.free,
            Formula.renameMapped, Term.weakenFree, Term.rename,
            Renaming.weakenFree, Term.renameMapped, Arguments.renameMapped]
        have hTail :
            List.map (Formula.renameFree (VariableRenaming.weaken SetSort.set)) Γ =
              FreshVariable.extendContext SetSort.set Γ := by
          rfl
        change
          (Formula.renameFree (VariableRenaming.weaken SetSort.set)
              (conclusion ≐ₘ (sequence ·ₘ numₘ(index))) ::
            List.map (Formula.renameFree (VariableRenaming.weaken SetSort.set)) Γ) ⊢ₘ[T]
            Formula.renameFree (VariableRenaming.weaken SetSort.set)
              Formula.falsum at hRenamed
        rw [hHead, hTail] at hRenamed
        simpa [Formula.renameFree, Formula.rename, Renaming.free,
          Formula.renameMapped] using hRenamed
      have hNegMismatch :
          FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
            ¬ₘ (conclusion.weakenFree SetSort.set ≐ₘ
              (sequence.weakenFree SetSort.set ·ₘ numₘ(index))) :=
        FirstOrder.Derives.neg_intro hMismatchAt
      exact FirstOrder.Derives.neg_elim
        hTargetEquality
        (FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hNegMismatch))
    · exact FirstOrder.Derives.neg_elim
        hLengthEquality
        (FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons (by
            have hNumeralNe := C.numeral_ne hLastIndex
            have hNumeralNeAt :
                FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
                  ¬ₘ ((numₘ(length)).weakenFree SetSort.set ≐ₘ
                    (numₘ(index + 1)).weakenFree SetSort.set) := by
              have hRenamed :
                  ([] : Context signature (SetSort.set :: free)) ⊢ₘ[T]
                    ¬ₘ (numₘ(length) ≐ₘ numₘ(index + 1)) := by
                simpa [Formula.renameFree, Formula.rename, Renaming.free,
                  Formula.renameMapped, Term.weakenFree, Term.rename,
                  Renaming.weakenFree, Term.renameMapped,
                  Arguments.renameMapped, finite_numeral_term, successor_term,
                  VariableRenaming.empty] using
                  FirstOrder.Derives.free_renaming
                    (T := T)
                    (VariableRenaming.empty :
                      VariableRenaming [] (SetSort.set :: free))
                    hNumeralNe
              simpa only [finite_numeral_term_weakenFree] using
                (FirstOrder.Derives.context_weaken
                  (Γ := ([] : Context signature (SetSort.set :: free)))
                  (Δ := FreshVariable.extendContext SetSort.set Γ)
                  (by simp) hRenamed)
            exact hNumeralNeAt)))

/-- 标准有限图按外部列表值不匹配时直接推出矛盾。 -/
theorem terminal_falsum_of_standard_sequence_mismatch
    {T : SetTheory}
    (C : FiniteCore T)
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (conclusion : SetOpenTerm free)
    (hDomain : Γ ⊢ₘ[T]
      domₘ(standard_sequence elements) ≐ₘ numₘ(elements.length))
    (hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition
        (standard_sequence elements) conclusion)
    (hMismatch :
      ∀ (index : Nat) (hIndex : index < elements.length),
        elements.length = index + 1 →
        (conclusion ≐ₘ elements[index]'hIndex) :: Γ
          ⊢ₘ[T] Formula.falsum) :
    Γ ⊢ₘ[T] Formula.falsum := by
  apply terminal_falsum_of_domain_eq
    C (standard_sequence elements) conclusion elements.length
    hDomain hTerminal
  intro index hIndex hLast
  apply falsum_of_equality_context_transport
    (elements[index]'hIndex)
    (standard_sequence elements ·ₘ numₘ(index)) conclusion
  · simpa [standard_sequence] using (row_value_of_standard_sequence (Γ := Γ) S 0 index hIndex)
  · exact hMismatch index hIndex hLast

/-- 证明行图按外部行值不匹配时直接推出矛盾。 -/
theorem terminal_falsum_of_proof_sequence_row_mismatch
    {T : SetTheory}
    (C : FiniteCore T)
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (conclusion : SetOpenTerm free)
    (hDomain : Γ ⊢ₘ[T]
      domₘ(proof_sequence_graph_term rows) ≐ₘ numₘ(rows.length))
    (hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition
        (proof_sequence_graph_term rows) conclusion)
    (hMismatch :
      ∀ (index : Nat) (hIndex : index < rows.length),
        rows.length = index + 1 →
        (conclusion ≐ₘ
            nat_sequence_graph_term (rows[index]'hIndex)) :: Γ
          ⊢ₘ[T] Formula.falsum) :
    Γ ⊢ₘ[T] Formula.falsum := by
  apply terminal_falsum_of_standard_sequence_mismatch C S
    (rows.map nat_sequence_graph_term) conclusion
  · simpa [proof_sequence_graph_term, standard_sequence] using hDomain
  · exact hTerminal
  · simpa only [List.length_map, List.getElem_map] using hMismatch

/-- 证明行列表与目标行列表不匹配时，终端条件直接矛盾。 -/
theorem terminal_falsum_of_proof_sequence_list_mismatch
    {T : SetTheory}
    (C : FiniteCore T)
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (rows : List (List Nat))
    (targetRow : List Nat)
    (conclusion : SetOpenTerm free)
    (hConclusion : Γ ⊢ₘ[T]
      conclusion ≐ₘ nat_sequence_graph_term targetRow)
    (hDomain : Γ ⊢ₘ[T]
      domₘ(proof_sequence_graph_term rows) ≐ₘ numₘ(rows.length))
    (hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition
        (proof_sequence_graph_term rows) conclusion)
    (hMismatch :
      ∀ (index : Nat) (hIndex : index < rows.length),
        rows.length = index + 1 →
        targetRow ≠ rows[index]'hIndex) :
    Γ ⊢ₘ[T] Formula.falsum := by
  apply terminal_falsum_of_proof_sequence_row_mismatch
    C S rows conclusion hDomain hTerminal
  intro index hIndex hLast
  apply FirstOrder.Derives.neg_elim
    (Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        (FirstOrder.Derives.context_weaken_cons hConclusion))
      (FirstOrder.Derives.assumption List.mem_cons_self))
  exact FirstOrder.Derives.context_weaken_cons
    (nat_sequence_graph_ne (Γ := Γ) S (hMismatch index hIndex hLast))

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
