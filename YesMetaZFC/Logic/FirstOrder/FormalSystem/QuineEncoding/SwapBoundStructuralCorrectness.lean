import YesMetaZFC.Logic.FirstOrder.BoundRenaming
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.TransformStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaTransformStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NumeralArithmetic

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace QuineEncoding

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols

set_option autoImplicit false

private theorem finite_numeral_ne_expression
    {left right : Nat} (hNe : left ≠ right) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      ¬ₘ (numₘ(left) ≐ₘ numₘ(right)) := by
  exact ProofT.numeral_ne
    (hIrreflexive := fun {formula} hFormula =>
      membership_irreflexive_theory_subset_expression_encoding_theory hFormula)
    (hSuccessor := fun {formula} hFormula =>
      formal_language_encoding_theory_subset_expression_encoding_theory
        (successor_operator_theory_subset_formal_language_encoding_theory hFormula))
    hNe

private theorem term_swap_bound_scope
    (depth variableIndex source target : SetOpenTerm [])
    (hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ depth)
    (hSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      Sₘ(variableIndex) ∈ₘ depth)
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(depth, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(depth, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex (numₘ(0)) source target := by
  derive_prop

private theorem formula_swap_bound_scope
    (depth variableIndex source target : SetOpenTerm [])
    (hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ depth)
    (hSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      Sₘ(variableIndex) ∈ₘ depth)
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(depth, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(depth, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex (numₘ(0)) source target := by
  derive_prop

private theorem term_list_swap_bound_scope
    (depth length variableIndex source target : SetOpenTerm [])
    (hLength : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      length ∈ₘ ωₘ)
    (hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ depth)
    (hSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      Sₘ(variableIndex) ∈ₘ depth)
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(depth, length, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(depth, length, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex (numₘ(0)) source target := by

  dsimp [syntax_transform_scope_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro (FirstOrder.Derives.eq_refl _)
  apply FirstOrder.Derives.exists_intro length
  rw [Formula.instantiateTop_abstractFreeTop]
  simp only [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
    Term.substituteMapped_weakenFree_instantiateFreeTop]
  derive_prop


private theorem term_swap_bound_free_shape
    (depth variableIndex : SetOpenTerm []) (index : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex (numₘ(0))
        (free_var_codeₘ(numₘ(index)))
        (free_var_codeₘ(numₘ(index))) := by

  have hIndex := finite_numeral_mem_expression (free := []) (Γ := []) index
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
    rw [Formula.instantiateTop_abstractFreeTop]
    simp only [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
      Term.substituteMapped_weakenFree_instantiateFreeTop]
    derive_prop


private theorem term_swap_bound_first_shape
    (depth variableIndex : SetOpenTerm [])
    (hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ depth)
    (_hSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      Sₘ(variableIndex) ∈ₘ depth) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex (numₘ(0))
        (bound_var_codeₘ(variableIndex))
        (bound_var_codeₘ(Sₘ(variableIndex))) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro variableIndex
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term] using!
      FirstOrder.Derives.conj_intro
        (Metatheory.Derives.equality_refl
          (bound_var_codeₘ(variableIndex) : SetOpenTerm []))
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.conj_intro
                (Metatheory.Derives.equality_refl
                  (syntax_transform_operation_term .swapBound :
                    SetOpenTerm []))
                (FirstOrder.Derives.conj_intro hVariable
                  (FirstOrder.Derives.disj_intro_left
                    (FirstOrder.Derives.conj_intro
                      (Metatheory.Derives.equality_refl variableIndex)
                      (Metatheory.Derives.equality_refl
                        (bound_var_codeₘ(Sₘ(variableIndex)) :
                          SetOpenTerm [])))))))))

private theorem term_swap_bound_second_shape
    (depth variableIndex : SetOpenTerm [])
    (_hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ depth)
    (hSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      Sₘ(variableIndex) ∈ₘ depth) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex (numₘ(0))
        (bound_var_codeₘ(Sₘ(variableIndex)))
        (bound_var_codeₘ(variableIndex)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (Sₘ(variableIndex))
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term] using!
      FirstOrder.Derives.conj_intro
        (Metatheory.Derives.equality_refl
          (bound_var_codeₘ(Sₘ(variableIndex)) : SetOpenTerm []))
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.conj_intro
                (Metatheory.Derives.equality_refl
                  (syntax_transform_operation_term .swapBound :
                    SetOpenTerm []))
                (FirstOrder.Derives.conj_intro hSuccessor
                  (FirstOrder.Derives.disj_intro_right
                    (FirstOrder.Derives.disj_intro_left
                      (FirstOrder.Derives.conj_intro
                        (Metatheory.Derives.equality_refl
                          (Sₘ(variableIndex)))
                        (Metatheory.Derives.equality_refl
                          (bound_var_codeₘ(variableIndex) :
                            SetOpenTerm []))))))))))

private theorem term_swap_bound_preserve_shape
    (depth variableIndex : SetOpenTerm []) (index : Nat)
    (hIndexDepth : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ depth)
    (hIndexNe : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      ¬ₘ ((numₘ(index) : SetOpenTerm []) ≐ₘ variableIndex))
    (hIndexSuccessorNe : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      ¬ₘ ((numₘ(index) : SetOpenTerm []) ≐ₘ Sₘ(variableIndex))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex (numₘ(0))
        (bound_var_codeₘ(numₘ(index))) (bound_var_codeₘ(numₘ(index))) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
    rw [Formula.instantiateTop_abstractFreeTop]
    simp only [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
      Term.substituteMapped_weakenFree_instantiateFreeTop]
    derive_prop


private theorem bound_variable_swap_bound_shape
    {σ : Signature} [QuotationNumbering σ]
    (offset : Nat) (prefixContext : SortContext σ)
    {first second resultSort : σ.SortSymbol}
    (entry : Variable (prefixContext ++ [first, second]) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .swapBound)
        (numₘ(offset + prefixContext.length + 2))
        (numₘ(offset + prefixContext.length))
        (numₘ(0))
        (bound_var_codeₘ(numₘ(offset + entry.index)))
        (bound_var_codeₘ(numₘ(offset +
          (VariableRenaming.swapAt prefixContext entry).index))) := by
  induction prefixContext generalizing offset with
  | nil =>
      cases entry with
      | here =>
          have hVariable := finite_numeral_mem_of_lt_expression
            (Γ := ([] : Context signature []))
            (show offset < offset + 2 by omega)
          have hSuccessor := finite_numeral_mem_of_lt_expression
            (Γ := ([] : Context signature []))
            (show offset + 1 < offset + 2 by omega)
          simpa [VariableRenaming.swapAt, Variable.index] using!
            term_swap_bound_first_shape
              (numₘ(offset + 2)) (numₘ(offset)) hVariable hSuccessor
      | there previous =>
          cases previous with
          | here =>
              have hVariable := finite_numeral_mem_of_lt_expression
                (Γ := ([] : Context signature []))
                (show offset < offset + 2 by omega)
              have hSuccessor := finite_numeral_mem_of_lt_expression
                (Γ := ([] : Context signature []))
                (show offset + 1 < offset + 2 by omega)
              simpa [VariableRenaming.swapAt, Variable.index] using!
                term_swap_bound_second_shape
                  (numₘ(offset + 2)) (numₘ(offset)) hVariable hSuccessor
          | there impossible => cases impossible
  | cons head tail ih =>
      cases entry with
      | here =>
          have hIndexDepth := finite_numeral_mem_of_lt_expression
            (Γ := ([] : Context signature []))
            (show offset < offset + tail.length + 1 + 2 by omega)
          have hIndexNe := finite_numeral_ne_expression (by
            show offset ≠ offset + tail.length + 1
            omega)
          have hIndexSuccessorNe := finite_numeral_ne_expression (by
            show offset ≠ offset + tail.length + 1 + 1
            omega)
          simpa [VariableRenaming.swapAt, Variable.index] using!
            term_swap_bound_preserve_shape
              (numₘ(offset + tail.length + 1 + 2))
              (numₘ(offset + tail.length + 1))
              offset hIndexDepth hIndexNe hIndexSuccessorNe
      | there previous =>
          simpa [VariableRenaming.swapAt, Variable.index, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using
            ih (offset := offset + 1) previous

private theorem quote_term_swap_bound_at_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second resultSort : σ.SortSymbol}
    (term : Term σ (prefixContext ++ [first, second]) free resultSort)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .swapBound)
        (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length))
        (numₘ(0))
        (quote_term term : SetOpenTerm [])
        (quote_term
          (Term.swapBoundAt prefixContext term) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term
          (Term.swapBoundAt prefixContext term) : SetOpenTerm [])) := by
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        numₘ(prefixContext.length + 2),
        (quote_term term : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression term
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        numₘ(prefixContext.length + 2),
        (quote_term (Term.swapBoundAt prefixContext term) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression (Term.swapBoundAt prefixContext term)
  have hVariable := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length < prefixContext.length + 2 by omega)
  have hSuccessor := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length + 1 < prefixContext.length + 2 by omega)
  apply syntax_transform_intro .term .swapBound
    (prefixContext.length + 2) prefixContext.length (numₘ(0))
    (quote_term term : SetOpenTerm [])
    (quote_term (Term.swapBoundAt prefixContext term) : SetOpenTerm [])
  · exact quote_term_code_mem_expression term
  · exact quote_term_code_mem_expression
      (Term.swapBoundAt prefixContext term)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_swap_bound_scope
      (numₘ(prefixContext.length + 2))
      (numₘ(prefixContext.length))
      (quote_term term : SetOpenTerm [])
      (quote_term (Term.swapBoundAt prefixContext term) : SetOpenTerm [])
      hVariable hSuccessor hSourceAt hTargetAt
  · exact hShape

private theorem quote_arguments_swap_bound_at_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (prefixContext ++ [first, second]) free sorts)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .swapBound)
        (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length))
        (numₘ(0))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (Arguments.swapBoundAt prefixContext arguments) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.swapBoundAt prefixContext arguments) : SetOpenTerm [])) := by
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        numₘ(prefixContext.length + 2), numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_arguments_code_at_expression arguments
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        numₘ(prefixContext.length + 2), numₘ(sorts.length),
        (quote_arguments (Arguments.swapBoundAt prefixContext arguments) :
          SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_arguments_code_at_expression
        (Arguments.swapBoundAt prefixContext arguments)
  have hVariable := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length < prefixContext.length + 2 by omega)
  have hSuccessor := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length + 1 < prefixContext.length + 2 by omega)
  apply syntax_transform_intro .termList .swapBound
    (prefixContext.length + 2) prefixContext.length (numₘ(0))
    (quote_arguments arguments : SetOpenTerm [])
    (quote_arguments (Arguments.swapBoundAt prefixContext arguments) :
      SetOpenTerm [])
  · exact quote_arguments_code_mem_expression arguments
  · exact quote_arguments_code_mem_expression
      (Arguments.swapBoundAt prefixContext arguments)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_list_swap_bound_scope
      (numₘ(prefixContext.length + 2))
      (numₘ(sorts.length))
      (numₘ(prefixContext.length))
      (quote_arguments arguments : SetOpenTerm [])
      (quote_arguments (Arguments.swapBoundAt prefixContext arguments) :
        SetOpenTerm [])
      (finite_numeral_mem_expression (Γ := []) sorts.length)
      hVariable hSuccessor hSourceAt hTargetAt
  · exact hShape

private theorem quote_bound_variable_swap_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second resultSort : σ.SortSymbol}
    (entry : Variable (prefixContext ++ [first, second]) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_term
          (.bvar entry : Term σ (prefixContext ++ [first, second]) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.swapBoundAt prefixContext
            (.bvar entry : Term σ (prefixContext ++ [first, second]) free resultSort)) :
          SetOpenTerm [])) := by
  apply quote_term_swap_bound_at_of_shape
  simpa [quote_term, Term.swapBoundAt, Term.renameMapped,
    VariableRenaming.swapAt, Variable.index] using
    bound_variable_swap_bound_shape (offset := 0) prefixContext entry

private theorem quote_free_variable_swap_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second resultSort : σ.SortSymbol}
    (entry : Variable free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_term
          (.fvar entry : Term σ (prefixContext ++ [first, second]) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.swapBoundAt prefixContext
            (.fvar entry : Term σ (prefixContext ++ [first, second]) free resultSort)) :
          SetOpenTerm [])) := by
  apply quote_term_swap_bound_at_of_shape
  simpa [quote_term, Term.swapBoundAt, Term.renameMapped] using!
    term_swap_bound_free_shape
      (numₘ(prefixContext.length + 2))
      (numₘ(prefixContext.length)) entry.index

mutual

theorem quote_term_swap_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second resultSort : σ.SortSymbol}
    (term : Term σ (prefixContext ++ [first, second]) free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term (Term.swapBoundAt prefixContext term) : SetOpenTerm [])) := by
  match term with
  | .bvar entry =>
      exact quote_bound_variable_swap_bound_at entry
  | .fvar entry =>
      exact quote_free_variable_swap_bound_at entry
  | .app function arguments =>
      have ih := quote_arguments_swap_bound_at arguments
      cases hDomain : σ.funcDomain function with
      | nil =>
          apply quote_term_swap_bound_at_of_shape
          simpa [quote_term, hDomain, Term.swapBoundAt,
            Arguments.swapBoundAt, Term.renameMapped,
            Arguments.renameMapped] using
            syntax_transform_constant_shape (syntax_transform_operation_term .swapBound)
              (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length)) (numₘ(0))
              (numₘ(QuotationNumbering.function_number function))
              (finite_numeral_mem_expression (Γ := [])
                (QuotationNumbering.function_number function))
      | cons head tail =>
          apply quote_term_swap_bound_at_of_shape
          simpa [quote_term, hDomain, Term.swapBoundAt,
            Arguments.swapBoundAt, Term.renameMapped,
            Arguments.renameMapped] using
            syntax_transform_application_shape (syntax_transform_operation_term .swapBound)
              (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length)) (numₘ(0))
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function))
              (quote_arguments arguments : SetOpenTerm [])
              (quote_arguments
                (Arguments.swapBoundAt prefixContext arguments) : SetOpenTerm [])
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature [])) (σ.funcArity function))
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature []))
                (QuotationNumbering.function_number function))
              ih

theorem quote_arguments_swap_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (prefixContext ++ [first, second]) free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.swapBoundAt prefixContext arguments) : SetOpenTerm [])) := by
  match arguments with
  | .nil =>
      apply quote_arguments_swap_bound_at_of_shape
      simpa [quote_arguments, Arguments.swapBoundAt,
        Term.swapBoundAt, Term.renameMapped,
        Arguments.renameMapped] using
        syntax_transform_nil_shape (T := expression_encoding_theory) (Γ := [])
          (syntax_transform_operation_term .swapBound)
          (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length)) (numₘ(0))
  | @Arguments.cons _ _ _ sort sorts head tail =>
      have ihTail := quote_arguments_swap_bound_at tail
      have ihHead := quote_term_swap_bound_at head
      apply quote_arguments_swap_bound_at_of_shape
      simpa [quote_arguments, Arguments.swapBoundAt,
        Term.swapBoundAt, Term.renameMapped,
        Arguments.renameMapped] using
        syntax_transform_cons_shape (syntax_transform_operation_term .swapBound)
          (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length)) (numₘ(0))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term (Term.swapBoundAt prefixContext head) : SetOpenTerm [])
          (quote_arguments
            (Arguments.swapBoundAt prefixContext tail) : SetOpenTerm [])
          ihHead ihTail

end

private theorem quote_hilbert_swap_bound_at_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second : σ.SortSymbol}
    (formula : Formula σ (prefixContext ++ [first, second]) free)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .swapBound)
        (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length))
        (numₘ(0))
        (quote_hilbert formula : SetOpenTerm [])
        (quote_hilbert
          (Formula.swapBoundAt prefixContext formula) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext formula) : SetOpenTerm [])) := by
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(
        numₘ(prefixContext.length + 2),
        (quote_hilbert formula : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_hilbert_code_at_expression formula
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(
        numₘ(prefixContext.length + 2),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext formula) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_hilbert_code_at_expression
        (Formula.swapBoundAt prefixContext formula)
  have hVariable := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length < prefixContext.length + 2 by omega)
  have hSuccessor := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length + 1 < prefixContext.length + 2 by omega)
  apply syntax_transform_intro .formula .swapBound
    (prefixContext.length + 2) prefixContext.length (numₘ(0))
    (quote_hilbert formula : SetOpenTerm [])
    (quote_hilbert
      (Formula.swapBoundAt prefixContext formula) : SetOpenTerm [])
  · exact quote_hilbert_code_mem_expression formula
  · exact quote_hilbert_code_mem_expression
      (Formula.swapBoundAt prefixContext formula)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact formula_swap_bound_scope
      (numₘ(prefixContext.length + 2))
      (numₘ(prefixContext.length))
      (quote_hilbert formula : SetOpenTerm [])
      (quote_hilbert
        (Formula.swapBoundAt prefixContext formula) : SetOpenTerm [])
      hVariable hSuccessor hSourceAt hTargetAt
  · exact hShape

private theorem quote_hilbert_neg_swap_bound
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second : σ.SortSymbol}
    (body : Formula σ (prefixContext ++ [first, second]) free)
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext body) : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.neg body) : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext (.neg body)) : SetOpenTerm [])) := by
  apply quote_hilbert_swap_bound_at_of_shape
  simpa [quote_hilbert, Formula.swapBoundAt, Formula.renameMapped] using
    formula_transform_negation_shape
      .swapBound (numₘ(prefixContext.length)) (numₘ(0))
      (numₘ(prefixContext.length + 2))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (Formula.swapBoundAt prefixContext body) : SetOpenTerm []) hBody

private theorem quote_hilbert_imp_swap_bound
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second : σ.SortSymbol}
    (left right : Formula σ (prefixContext ++ [first, second]) free)
    (hLeft : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert left : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext left) : SetOpenTerm [])))
    (hRight : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert right : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext right) : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.imp left right) : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext (.imp left right)) :
          SetOpenTerm [])) := by
  apply quote_hilbert_swap_bound_at_of_shape
  simpa [quote_hilbert, Formula.swapBoundAt, Formula.renameMapped] using
    formula_transform_implication_shape
      .swapBound (numₘ(prefixContext.length)) (numₘ(0))
      (numₘ(prefixContext.length + 2))
      (quote_hilbert left : SetOpenTerm [])
      (quote_hilbert right : SetOpenTerm [])
      (quote_hilbert
        (Formula.swapBoundAt prefixContext left) : SetOpenTerm [])
      (quote_hilbert
        (Formula.swapBoundAt prefixContext right) : SetOpenTerm []) hLeft hRight

private theorem quote_hilbert_all_swap_bound
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second quantified : σ.SortSymbol}
    (body : Formula σ (quantified :: (prefixContext ++ [first, second])) free)
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ((quantified :: prefixContext).length + 2),
        numₘ((quantified :: prefixContext).length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt (quantified :: prefixContext) body) :
          SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.forallE quantified body) : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext (.forallE quantified body)) :
          SetOpenTerm [])) := by
  apply quote_hilbert_swap_bound_at_of_shape
  simpa [quote_hilbert, Formula.swapBoundAt, Formula.renameMapped,
    VariableRenaming.swapAt_cons_eq, List.length_cons,
    finite_numeral_term] using
    formula_transform_universal_swap_shape
      (numₘ(prefixContext.length)) (numₘ(0))
      (numₘ(prefixContext.length + 2))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (Formula.swapBoundAt (quantified :: prefixContext) body) :
        SetOpenTerm []) hBody

private theorem quote_hilbert_equality_swap_bound
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second sort : σ.SortSymbol}
    (left right : Term σ (prefixContext ++ [first, second]) free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.equal left right) : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext (.equal left right)) :
          SetOpenTerm [])) := by
  apply quote_hilbert_swap_bound_at_of_shape
  simpa [quote_hilbert, Formula.swapBoundAt, Formula.renameMapped] using!
    formula_transform_binary_shape
      .swapBound (numₘ(prefixContext.length)) (numₘ(0))
      .equality (Or.inl rfl)
      (numₘ(prefixContext.length + 2))
      (quote_term left : SetOpenTerm [])
      (quote_term right : SetOpenTerm [])
      (quote_term (Term.swapBoundAt prefixContext left) : SetOpenTerm [])
      (quote_term (Term.swapBoundAt prefixContext right) : SetOpenTerm [])
      (quote_term_swap_bound_at left)
      (quote_term_swap_bound_at right)

private theorem arguments_swap_bound_at_cast
    {σ : Signature} {free prefixContext rest : SortContext σ}
    {first second : σ.SortSymbol}
    {sourceSorts targetSorts : List σ.SortSymbol}
    (hSorts : sourceSorts = targetSorts)
    (arguments : Arguments σ
      (prefixContext ++ first :: second :: rest) free sourceSorts) :
    Arguments.swapBoundAt prefixContext (hSorts ▸ arguments) =
      hSorts ▸ Arguments.swapBoundAt prefixContext arguments := by
  cases hSorts
  rfl

private theorem quote_hilbert_relation_swap_bound
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second : σ.SortSymbol}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ (prefixContext ++ [first, second]) free
      (σ.relDomain relation)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.rel relation arguments) : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext (.rel relation arguments)) :
          SetOpenTerm [])) := by
  generalize hKind : QuotationNumbering.relation_kind relation = kind
  cases kind with
  | membership =>
      generalize hTypedArguments :
        (QuotationNumbering.membership_domain relation hKind ▸ arguments) =
          typedArguments
      cases typedArguments with
      | cons left rest =>
          cases rest with
          | cons right tail =>
              cases tail with
              | nil =>
                  have hTargetTyped :
                      QuotationNumbering.membership_domain relation hKind ▸
                          Arguments.swapBoundAt prefixContext arguments =
                        Arguments.cons
                          (Term.swapBoundAt prefixContext left)
                          (Arguments.cons
                            (Term.swapBoundAt prefixContext right)
                            Arguments.nil) := by
                    have hMapped := congrArg
                      (fun typedArguments =>
                        Arguments.swapBoundAt prefixContext typedArguments)
                      hTypedArguments
                    rw [← arguments_swap_bound_at_cast]
                    simpa [Arguments.swapBoundAt, Term.swapBoundAt,
                      Arguments.renameMapped, Term.renameMapped] using hMapped
                  have hSourceQuote :
                      quote_relation relation arguments =
                        mem_codeₘ(
                          (quote_term left : SetOpenTerm []),
                          (quote_term right : SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq
                      relation arguments hKind]
                    exact quote_membership_arguments_cons_eq
                      relation arguments hKind left right hTypedArguments
                  have hTargetQuote :
                      quote_relation relation
                          (Arguments.swapBoundAt prefixContext arguments) =
                        mem_codeₘ(
                          (quote_term
                            (Term.swapBoundAt prefixContext left) :
                            SetOpenTerm []),
                          (quote_term
                            (Term.swapBoundAt prefixContext right) :
                            SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation
                      (Arguments.swapBoundAt prefixContext arguments) hKind]
                    exact quote_membership_arguments_cons_eq
                      relation (Arguments.swapBoundAt prefixContext arguments)
                      hKind (Term.swapBoundAt prefixContext left)
                      (Term.swapBoundAt prefixContext right) hTargetTyped
                  apply quote_hilbert_swap_bound_at_of_shape
                  change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
                    syntax_transform_shape_condition
                      (syntax_code_kind_term .formula)
                      (syntax_transform_operation_term .swapBound)
                      (numₘ(prefixContext.length + 2))
                      (numₘ(prefixContext.length)) (numₘ(0))
                      (quote_relation relation arguments)
                      (quote_relation relation
                        (Arguments.swapBoundAt prefixContext arguments))
                  rw [hSourceQuote, hTargetQuote]
                  exact formula_transform_binary_shape
                    .swapBound (numₘ(prefixContext.length)) (numₘ(0))
                    .membership (Or.inr rfl)
                    (numₘ(prefixContext.length + 2))
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    (quote_term
                      (Term.swapBoundAt prefixContext left) : SetOpenTerm [])
                    (quote_term
                      (Term.swapBoundAt prefixContext right) : SetOpenTerm [])
                    (quote_term_swap_bound_at left)
                    (quote_term_swap_bound_at right)
  | predicate =>
      have hSourceQuote := quote_relation_predicate_eq
        relation arguments hKind
      have hTargetQuote := quote_relation_predicate_eq relation
        (Arguments.swapBoundAt prefixContext arguments) hKind
      apply quote_hilbert_swap_bound_at_of_shape
      change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transform_shape_condition
          (syntax_code_kind_term .formula)
          (syntax_transform_operation_term .swapBound)
          (numₘ(prefixContext.length + 2)) (numₘ(prefixContext.length))
          (numₘ(0))
          (quote_relation relation arguments)
          (quote_relation relation
            (Arguments.swapBoundAt prefixContext arguments))
      rw [hSourceQuote, hTargetQuote]
      exact formula_transform_predicate_shape
        .swapBound (numₘ(prefixContext.length)) (numₘ(0))
        (numₘ(prefixContext.length + 2))
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (Arguments.swapBoundAt prefixContext arguments) : SetOpenTerm [])
        (finite_numeral_mem_expression
          (Γ := ([] : Context signature [])) (σ.relArity relation))
        (finite_numeral_mem_expression
          (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation))
        (quote_arguments_swap_bound_at arguments)

theorem quote_hilbert_formula_swap_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {first second : σ.SortSymbol}
    (formula : Formula σ (prefixContext ++ [first, second]) free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        numₘ(prefixContext.length + 2), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (Formula.swapBoundAt prefixContext formula) : SetOpenTerm [])) := by
  have h := Formula.hilbertize_induction QuotationNumbering.objectSort
    (motive := fun {currentBound currentFree} currentFormula =>
      ∀ (tailBound : SortContext σ) (first second : σ.SortSymbol)
          (hBound : currentBound = tailBound ++ [first, second]),
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          syntax_transformₘ(
            syntax_code_kind_term .formula,
            syntax_transform_operation_term .swapBound,
            numₘ(tailBound.length + 2), numₘ(tailBound.length),
            (numₘ(0) : SetOpenTerm []),
            (quote_hilbert (hBound ▸ currentFormula) : SetOpenTerm []),
            (quote_hilbert
              (Formula.swapBoundAt tailBound (hBound ▸ currentFormula)) :
              SetOpenTerm [])))
    (fun {currentBound currentFree} relation arguments => by
      intro tailBound first second hBound
      cases hBound
      exact quote_hilbert_relation_swap_bound relation arguments)
    (fun {currentBound currentFree} {sort} left right => by
      intro tailBound first second hBound
      cases hBound
      exact quote_hilbert_equality_swap_bound left right)
    (fun {currentBound currentFree} body ih => by
      intro tailBound first second hBound
      cases hBound
      exact quote_hilbert_neg_swap_bound body
        (ih tailBound first second rfl))
    (fun {currentBound currentFree} left right ihLeft ihRight => by
      intro tailBound first second hBound
      cases hBound
      exact quote_hilbert_imp_swap_bound left right
        (ihLeft tailBound first second rfl)
        (ihRight tailBound first second rfl))
    (fun {currentBound currentFree} quantified body ih => by
      intro tailBound first second hBound
      cases hBound
      exact quote_hilbert_all_swap_bound body
        (ih (quantified :: tailBound) first second rfl))
    formula prefixContext first second rfl
  simpa only [Formula.swapBoundAt, ← Formula.hilbertize_renameMapped, quote_hilbert_hilbertize] using h

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
