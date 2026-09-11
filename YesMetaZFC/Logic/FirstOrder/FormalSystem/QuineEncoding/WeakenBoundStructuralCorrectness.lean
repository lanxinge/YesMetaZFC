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

private theorem finite_numeral_not_mem_expression
    {left right : Nat} (h : ¬ left < right) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      ¬ₘ ((numₘ(left) : SetOpenTerm []) ∈ₘ numₘ(right)) :=
  ProofT.numeral_not_mem_of_not_lt
    (hEmpty := fun {_formula} hFormula =>
      empty_set_symbol_theory_subset_expression_encoding_theory hFormula)
    (hIrreflexive := fun {_formula} hFormula =>
      membership_irreflexive_theory_subset_expression_encoding_theory hFormula)
    (hSuccessor := fun {_formula} hFormula =>
      formal_language_encoding_theory_subset_expression_encoding_theory
        (successor_operator_theory_subset_formal_language_encoding_theory
          hFormula)) h

private theorem term_weaken_bound_scope
    (depth variableIndex source target : SetOpenTerm [])
    (hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ Sₘ(depth))
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(depth, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(Sₘ(depth), target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .weakenBound)
        depth variableIndex (numₘ(0)) source target := by
  derive_prop

private theorem formula_weaken_bound_scope
    (depth variableIndex source target : SetOpenTerm [])
    (hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ Sₘ(depth))
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(depth, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(Sₘ(depth), target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .weakenBound)
        depth variableIndex (numₘ(0)) source target := by
  derive_prop

private theorem term_list_weaken_bound_scope
    (depth length variableIndex source target : SetOpenTerm [])
    (hLength : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      length ∈ₘ ωₘ)
    (hVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      variableIndex ∈ₘ Sₘ(depth))
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(depth, length, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(Sₘ(depth), length, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .weakenBound)
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


private theorem term_weaken_bound_free_shape
    (depth variableIndex : SetOpenTerm []) (index : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .weakenBound)
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


private theorem term_weaken_bound_preserve_shape
    (depth variableIndex : SetOpenTerm []) (index : Nat)
    (hIndexDepth : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ depth)
    (hIndexVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ variableIndex) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .weakenBound)
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


private theorem term_weaken_bound_shift_shape
    (depth variableIndex : SetOpenTerm []) (index : Nat)
    (hIndexDepth : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ depth)
    (hIndexNotVariable : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      ¬ₘ ((numₘ(index) : SetOpenTerm []) ∈ₘ variableIndex)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .weakenBound)
        depth variableIndex (numₘ(0))
        (bound_var_codeₘ(numₘ(index)))
        (bound_var_codeₘ(Sₘ(numₘ(index)))) := by
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


private theorem bound_variable_weaken_bound_shape
    {σ : Signature} [QuotationNumbering σ]
    {prefixContext rest : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (entry : Variable (prefixContext ++ rest) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .weakenBound)
        (numₘ((prefixContext ++ rest).length))
        (numₘ(prefixContext.length))
        (numₘ(0))
        (bound_var_codeₘ(numₘ(entry.index)))
        (bound_var_codeₘ(numₘ(
          (VariableRenaming.weakenAt
            (introduced := introduced) prefixContext entry).index))) := by
  by_cases hIndex : entry.index < prefixContext.length
  · have hDepth : entry.index < (prefixContext ++ rest).length := by
      simpa [List.length_append] using entry.index_lt_length
    have hIndexDepth := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature [])) hDepth
    have hIndexVariable := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature [])) hIndex
    simpa [VariableRenaming.weakenAt_index, hIndex,
      finite_numeral_term, List.length_append] using
      term_weaken_bound_preserve_shape
        (numₘ((prefixContext ++ rest).length))
        (numₘ(prefixContext.length)) entry.index hIndexDepth hIndexVariable
  · have hDepth : entry.index < (prefixContext ++ rest).length := by
      simpa [List.length_append] using entry.index_lt_length
    have hIndexDepth := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature [])) hDepth
    have hIndexNotVariable := finite_numeral_not_mem_expression hIndex
    simpa [VariableRenaming.weakenAt_index, hIndex,
      finite_numeral_term, List.length_append] using
      term_weaken_bound_shift_shape
        (numₘ((prefixContext ++ rest).length))
        (numₘ(prefixContext.length)) entry.index hIndexDepth
        hIndexNotVariable

/-! ## 结构递归 -/

private theorem quote_term_weaken_bound_at_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (term : Term σ (prefixContext ++ rest) free resultSort)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .weakenBound)
        (numₘ((prefixContext ++ rest).length))
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_term term : SetOpenTerm [])
        (quote_term
          (Term.weakenBoundAt (introduced := introduced) prefixContext term) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term
          (Term.weakenBoundAt (introduced := introduced) prefixContext term) :
          SetOpenTerm [])) := by
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        numₘ((prefixContext ++ rest).length),
        (quote_term term : SetOpenTerm [])) := by
    exact quote_term_code_at_expression term
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        Sₘ(numₘ((prefixContext ++ rest).length)),
        (quote_term
          (Term.weakenBoundAt (introduced := introduced) prefixContext term) :
          SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term, Nat.add_assoc] using
      quote_term_code_at_expression
        (Term.weakenBoundAt (introduced := introduced) prefixContext term)
  have hVariable := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length < (prefixContext ++ rest).length + 1 by
      simp [List.length_append]
      omega)
  apply syntax_transform_intro .term .weakenBound
    (prefixContext ++ rest).length prefixContext.length (numₘ(0))
    (quote_term term : SetOpenTerm [])
    (quote_term
      (Term.weakenBoundAt (introduced := introduced) prefixContext term) :
      SetOpenTerm [])
  · exact quote_term_code_mem_expression term
  · exact quote_term_code_mem_expression
      (Term.weakenBoundAt (introduced := introduced) prefixContext term)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_weaken_bound_scope
      (numₘ((prefixContext ++ rest).length))
      (numₘ(prefixContext.length))
      (quote_term term : SetOpenTerm [])
      (quote_term
        (Term.weakenBoundAt (introduced := introduced) prefixContext term) :
        SetOpenTerm [])
      hVariable hSourceAt hTargetAt
  · exact hShape

private theorem quote_arguments_weaken_bound_at_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (prefixContext ++ rest) free sorts)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .weakenBound)
        (numₘ((prefixContext ++ rest).length))
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (Arguments.weakenBoundAt (introduced := introduced)
            prefixContext arguments) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.weakenBoundAt (introduced := introduced)
            prefixContext arguments) : SetOpenTerm [])) := by
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        numₘ((prefixContext ++ rest).length), numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
    exact quote_arguments_code_at_expression arguments
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        Sₘ(numₘ((prefixContext ++ rest).length)), numₘ(sorts.length),
        (quote_arguments
          (Arguments.weakenBoundAt (introduced := introduced)
            prefixContext arguments) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term, Nat.add_assoc] using
      quote_arguments_code_at_expression
        (Arguments.weakenBoundAt (introduced := introduced)
          prefixContext arguments)
  have hVariable := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length < (prefixContext ++ rest).length + 1 by
      simp [List.length_append]
      omega)
  apply syntax_transform_intro .termList .weakenBound
    (prefixContext ++ rest).length prefixContext.length (numₘ(0))
    (quote_arguments arguments : SetOpenTerm [])
    (quote_arguments
      (Arguments.weakenBoundAt (introduced := introduced)
        prefixContext arguments) : SetOpenTerm [])
  · exact quote_arguments_code_mem_expression arguments
  · exact quote_arguments_code_mem_expression
      (Arguments.weakenBoundAt (introduced := introduced)
        prefixContext arguments)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_list_weaken_bound_scope
      (numₘ((prefixContext ++ rest).length))
      (numₘ(sorts.length))
      (numₘ(prefixContext.length))
      (quote_arguments arguments : SetOpenTerm [])
      (quote_arguments
        (Arguments.weakenBoundAt (introduced := introduced)
          prefixContext arguments) : SetOpenTerm [])
      (finite_numeral_mem_expression (Γ := []) sorts.length)
      hVariable hSourceAt hTargetAt
  · exact hShape

private theorem quote_bound_variable_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (entry : Variable (prefixContext ++ rest) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_term
          (.bvar entry : Term σ (prefixContext ++ rest) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.weakenBoundAt (introduced := introduced) prefixContext
            (.bvar entry : Term σ (prefixContext ++ rest) free resultSort)) :
          SetOpenTerm [])) := by
  apply quote_term_weaken_bound_at_of_shape
  simpa [quote_term, Term.weakenBoundAt, Term.renameMapped,
    VariableRenaming.weakenAt, Variable.index] using
    bound_variable_weaken_bound_shape (introduced := introduced) entry

private theorem quote_free_variable_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (entry : Variable free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_term
          (.fvar entry : Term σ (prefixContext ++ rest) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.weakenBoundAt (introduced := introduced) prefixContext
            (.fvar entry : Term σ (prefixContext ++ rest) free resultSort)) :
          SetOpenTerm [])) := by
  apply quote_term_weaken_bound_at_of_shape
  simpa [quote_term, Term.weakenBoundAt, Term.renameMapped] using!
    term_weaken_bound_free_shape
      (numₘ((prefixContext ++ rest).length))
      (numₘ(prefixContext.length)) entry.index

mutual

theorem quote_term_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (term : Term σ (prefixContext ++ rest) free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term
          (Term.weakenBoundAt (introduced := introduced) prefixContext term) :
          SetOpenTerm [])) := by
  match term with
  | .bvar entry =>
      exact quote_bound_variable_weaken_bound_at entry
  | .fvar entry =>
      exact quote_free_variable_weaken_bound_at entry
  | .app function arguments =>
      have ih := quote_arguments_weaken_bound_at (introduced := introduced) arguments
      cases hDomain : σ.funcDomain function with
      | nil =>
          apply quote_term_weaken_bound_at_of_shape
          simpa [quote_term, hDomain, Term.weakenBoundAt,
            Term.renameMapped, Arguments.weakenBoundAt,
            Arguments.renameMapped] using
            syntax_transform_constant_shape (syntax_transform_operation_term .weakenBound)
              (numₘ((prefixContext ++ rest).length)) (numₘ(prefixContext.length)) (numₘ(0))
              (numₘ(QuotationNumbering.function_number function))
              (finite_numeral_mem_expression (Γ := [])
                (QuotationNumbering.function_number function))
      | cons head tail =>
          apply quote_term_weaken_bound_at_of_shape
          simpa [quote_term, hDomain, Term.weakenBoundAt,
            Term.renameMapped, Arguments.weakenBoundAt,
            Arguments.renameMapped] using
            syntax_transform_application_shape (syntax_transform_operation_term .weakenBound)
              (numₘ((prefixContext ++ rest).length)) (numₘ(prefixContext.length)) (numₘ(0))
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function))
              (quote_arguments arguments : SetOpenTerm [])
              (quote_arguments
                (Arguments.weakenBoundAt (introduced := introduced)
                  prefixContext arguments) : SetOpenTerm [])
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature [])) (σ.funcArity function))
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature []))
                (QuotationNumbering.function_number function))
              ih

theorem quote_arguments_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (prefixContext ++ rest) free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.weakenBoundAt (introduced := introduced)
            prefixContext arguments) : SetOpenTerm [])) := by
  match arguments with
  | .nil =>
      apply quote_arguments_weaken_bound_at_of_shape
      simpa [quote_arguments, Arguments.weakenBoundAt,
        Arguments.renameMapped] using
        syntax_transform_nil_shape (T := expression_encoding_theory) (Γ := [])
          (syntax_transform_operation_term .weakenBound)
          (numₘ((prefixContext ++ rest).length)) (numₘ(prefixContext.length)) (numₘ(0))
  | @Arguments.cons _ _ _ sort sorts head tail =>
      have ihTail := quote_arguments_weaken_bound_at (introduced := introduced) tail
      have ihHead := quote_term_weaken_bound_at (introduced := introduced) head
      apply quote_arguments_weaken_bound_at_of_shape
      simpa [quote_arguments, Term.weakenBoundAt,
        Arguments.weakenBoundAt, Term.renameMapped,
        Arguments.renameMapped] using
        syntax_transform_cons_shape (syntax_transform_operation_term .weakenBound)
          (numₘ((prefixContext ++ rest).length)) (numₘ(prefixContext.length)) (numₘ(0))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term
            (Term.weakenBoundAt (introduced := introduced)
              prefixContext head) : SetOpenTerm [])
          (quote_arguments
            (Arguments.weakenBoundAt (introduced := introduced)
              prefixContext tail) : SetOpenTerm [])
          ihHead ihTail

end

private theorem quote_hilbert_weaken_bound_at_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol}
    (formula : Formula σ (prefixContext ++ rest) free)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .weakenBound)
        (numₘ((prefixContext ++ rest).length))
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_hilbert formula : SetOpenTerm [])
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext formula) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext formula) : SetOpenTerm [])) := by
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(
        numₘ((prefixContext ++ rest).length),
        (quote_hilbert formula : SetOpenTerm [])) := by
    exact quote_hilbert_code_at_expression formula
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(
        Sₘ(numₘ((prefixContext ++ rest).length)),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext formula) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term, Nat.add_assoc] using
      quote_hilbert_code_at_expression
        (Formula.weakenBoundAt (introduced := introduced)
          prefixContext formula)
  have hVariable := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature []))
    (show prefixContext.length < (prefixContext ++ rest).length + 1 by
      simp [List.length_append]
      omega)
  apply syntax_transform_intro .formula .weakenBound
    (prefixContext ++ rest).length prefixContext.length (numₘ(0))
    (quote_hilbert formula : SetOpenTerm [])
    (quote_hilbert
      (Formula.weakenBoundAt (introduced := introduced)
        prefixContext formula) : SetOpenTerm [])
  · exact quote_hilbert_code_mem_expression formula
  · exact quote_hilbert_code_mem_expression
      (Formula.weakenBoundAt (introduced := introduced)
        prefixContext formula)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact formula_weaken_bound_scope
      (numₘ((prefixContext ++ rest).length))
      (numₘ(prefixContext.length))
      (quote_hilbert formula : SetOpenTerm [])
      (quote_hilbert
        (Formula.weakenBoundAt (introduced := introduced)
          prefixContext formula) : SetOpenTerm [])
      hVariable hSourceAt hTargetAt
  · exact hShape

private theorem quote_hilbert_neg_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol}
    (body : Formula σ (prefixContext ++ rest) free)
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext body) : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.neg body) : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext (.neg body)) : SetOpenTerm [])) := by
  apply quote_hilbert_weaken_bound_at_of_shape
  simpa [quote_hilbert, Formula.weakenBoundAt, Formula.renameMapped] using
    formula_transform_negation_shape
      .weakenBound (numₘ(prefixContext.length)) (numₘ(0))
      (numₘ((prefixContext ++ rest).length))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (Formula.weakenBoundAt (introduced := introduced)
          prefixContext body) : SetOpenTerm []) hBody

private theorem quote_hilbert_imp_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol}
    (left right : Formula σ (prefixContext ++ rest) free)
    (hLeft : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert left : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext left) : SetOpenTerm [])))
    (hRight : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert right : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext right) : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.imp left right) : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext (.imp left right)) : SetOpenTerm [])) := by
  apply quote_hilbert_weaken_bound_at_of_shape
  simpa [quote_hilbert, Formula.weakenBoundAt, Formula.renameMapped] using
    formula_transform_implication_shape
      .weakenBound (numₘ(prefixContext.length)) (numₘ(0))
      (numₘ((prefixContext ++ rest).length))
      (quote_hilbert left : SetOpenTerm [])
      (quote_hilbert right : SetOpenTerm [])
      (quote_hilbert
        (Formula.weakenBoundAt (introduced := introduced)
          prefixContext left) : SetOpenTerm [])
      (quote_hilbert
        (Formula.weakenBoundAt (introduced := introduced)
          prefixContext right) : SetOpenTerm []) hLeft hRight

private theorem quote_hilbert_all_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced quantified : σ.SortSymbol}
    (body : Formula σ ((quantified :: prefixContext) ++ rest) free)
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ(((quantified :: prefixContext) ++ rest).length),
        numₘ((quantified :: prefixContext).length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            (quantified :: prefixContext) body) : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length), numₘ(prefixContext.length),
        (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.forallE quantified body) : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext (.forallE quantified body)) : SetOpenTerm [])) := by
  apply quote_hilbert_weaken_bound_at_of_shape
  simpa [quote_hilbert, Formula.weakenBoundAt, Formula.renameMapped,
    VariableRenaming.weakenAt_cons_eq, List.length_cons,
    List.length_append, finite_numeral_term] using
    formula_transform_universal_weaken_shape
      (numₘ(prefixContext.length)) (numₘ(0))
      (numₘ((prefixContext ++ rest).length))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (Formula.weakenBoundAt (introduced := introduced)
          (quantified :: prefixContext) body) : SetOpenTerm []) hBody

private theorem quote_hilbert_equality_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced sort : σ.SortSymbol}
    (left right : Term σ (prefixContext ++ rest) free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.equal left right) : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext (.equal left right)) : SetOpenTerm [])) := by
  apply quote_hilbert_weaken_bound_at_of_shape
  simpa [quote_hilbert, Formula.weakenBoundAt, Formula.renameMapped] using!
    formula_transform_binary_shape
      .weakenBound (numₘ(prefixContext.length)) (numₘ(0)) .equality
      (Or.inl rfl)
      (numₘ((prefixContext ++ rest).length))
      (quote_term left : SetOpenTerm [])
      (quote_term right : SetOpenTerm [])
      (quote_term
        (Term.weakenBoundAt (introduced := introduced)
          prefixContext left) : SetOpenTerm [])
      (quote_term
        (Term.weakenBoundAt (introduced := introduced)
          prefixContext right) : SetOpenTerm [])
      (quote_term_weaken_bound_at left)
      (quote_term_weaken_bound_at right)

private theorem arguments_weaken_bound_at_cast
    {σ : Signature}
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol}
    {sourceSorts targetSorts : List σ.SortSymbol}
    (hSorts : sourceSorts = targetSorts)
    (arguments : Arguments σ (prefixContext ++ rest) free sourceSorts) :
    Arguments.weakenBoundAt (introduced := introduced) prefixContext
        (hSorts ▸ arguments) =
      hSorts ▸ Arguments.weakenBoundAt (introduced := introduced)
        prefixContext arguments := by
  cases hSorts
  rfl

private theorem quote_hilbert_relation_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ (prefixContext ++ rest) free
      (σ.relDomain relation)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert (.rel relation arguments) : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext (.rel relation arguments)) : SetOpenTerm [])) := by
  generalize hKind : QuotationNumbering.relation_kind relation = kind
  cases kind with
  | membership =>
      generalize hTypedArguments :
        (QuotationNumbering.membership_domain relation hKind ▸ arguments) =
          typedArguments
      cases typedArguments with
      | cons left restArguments =>
          cases restArguments with
          | cons right tail =>
              cases tail with
              | nil =>
                  have hTargetTyped :
                      QuotationNumbering.membership_domain relation hKind ▸
                          Arguments.weakenBoundAt
                            (introduced := introduced) prefixContext arguments =
                        Arguments.cons
                          (Term.weakenBoundAt (introduced := introduced)
                            prefixContext left)
                          (Arguments.cons
                            (Term.weakenBoundAt (introduced := introduced)
                              prefixContext right)
                            Arguments.nil) := by
                    have hMapped := congrArg
                      (fun typedArguments =>
                        Arguments.weakenBoundAt (introduced := introduced)
                          prefixContext typedArguments)
                      hTypedArguments
                    rw [← arguments_weaken_bound_at_cast]
                    simpa [Arguments.weakenBoundAt, Term.weakenBoundAt,
                      Arguments.renameMapped, Term.renameMapped] using hMapped
                  have hSourceQuote :
                      quote_relation relation arguments =
                        mem_codeₘ(
                          (quote_term left : SetOpenTerm []),
                          (quote_term right : SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation arguments hKind]
                    exact quote_membership_arguments_cons_eq
                      relation arguments hKind left right hTypedArguments
                  have hTargetQuote :
                      quote_relation relation
                          (Arguments.weakenBoundAt
                            (introduced := introduced) prefixContext arguments) =
                        mem_codeₘ(
                          (quote_term
                            (Term.weakenBoundAt (introduced := introduced)
                              prefixContext left) : SetOpenTerm []),
                          (quote_term
                            (Term.weakenBoundAt (introduced := introduced)
                              prefixContext right) : SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation
                      (Arguments.weakenBoundAt
                        (introduced := introduced) prefixContext arguments) hKind]
                    exact quote_membership_arguments_cons_eq
                      relation (Arguments.weakenBoundAt
                        (introduced := introduced) prefixContext arguments)
                      hKind (Term.weakenBoundAt (introduced := introduced)
                        prefixContext left)
                      (Term.weakenBoundAt (introduced := introduced)
                        prefixContext right) hTargetTyped
                  apply quote_hilbert_weaken_bound_at_of_shape
                  change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
                    syntax_transform_shape_condition
                      (syntax_code_kind_term .formula)
                      (syntax_transform_operation_term .weakenBound)
                      (numₘ((prefixContext ++ rest).length))
                      (numₘ(prefixContext.length)) (numₘ(0))
                      (quote_relation relation arguments)
                      (quote_relation relation
                        (Arguments.weakenBoundAt
                          (introduced := introduced) prefixContext arguments))
                  rw [hSourceQuote, hTargetQuote]
                  exact formula_transform_binary_shape
                    .weakenBound (numₘ(prefixContext.length)) (numₘ(0))
                    .membership (Or.inr rfl)
                    (numₘ((prefixContext ++ rest).length))
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    (quote_term
                      (Term.weakenBoundAt (introduced := introduced)
                        prefixContext left) : SetOpenTerm [])
                    (quote_term
                      (Term.weakenBoundAt (introduced := introduced)
                        prefixContext right) : SetOpenTerm [])
                    (quote_term_weaken_bound_at left)
                    (quote_term_weaken_bound_at right)
  | predicate =>
      have hSourceQuote := quote_relation_predicate_eq relation arguments hKind
      have hTargetQuote := quote_relation_predicate_eq relation
        (Arguments.weakenBoundAt (introduced := introduced)
          prefixContext arguments) hKind
      apply quote_hilbert_weaken_bound_at_of_shape
      change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transform_shape_condition
          (syntax_code_kind_term .formula)
          (syntax_transform_operation_term .weakenBound)
          (numₘ((prefixContext ++ rest).length))
          (numₘ(prefixContext.length)) (numₘ(0))
          (quote_relation relation arguments)
          (quote_relation relation
            (Arguments.weakenBoundAt (introduced := introduced)
              prefixContext arguments))
      rw [hSourceQuote, hTargetQuote]
      exact formula_transform_predicate_shape
        .weakenBound (numₘ(prefixContext.length)) (numₘ(0))
        (numₘ((prefixContext ++ rest).length))
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (Arguments.weakenBoundAt (introduced := introduced)
            prefixContext arguments) : SetOpenTerm [])
        (finite_numeral_mem_expression
          (Γ := ([] : Context signature [])) (σ.relArity relation))
        (finite_numeral_mem_expression
          (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation))
        (quote_arguments_weaken_bound_at arguments)

theorem quote_hilbert_formula_weaken_bound_at
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext rest : SortContext σ}
    {introduced : σ.SortSymbol}
    (formula : Formula σ (prefixContext ++ rest) free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        numₘ((prefixContext ++ rest).length),
        numₘ(prefixContext.length), (numₘ(0) : SetOpenTerm []),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (Formula.weakenBoundAt (introduced := introduced)
            prefixContext formula) : SetOpenTerm [])) := by
  have h := Formula.hilbertize_induction QuotationNumbering.objectSort
    (motive := fun {currentBound currentFree} currentFormula =>
      ∀ (tailBound tailRest : SortContext σ) (introduced : σ.SortSymbol)
          (hBound : currentBound = tailBound ++ tailRest),
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          syntax_transformₘ(
            syntax_code_kind_term .formula,
            syntax_transform_operation_term .weakenBound,
            numₘ((tailBound ++ tailRest).length),
            numₘ(tailBound.length), (numₘ(0) : SetOpenTerm []),
            (quote_hilbert (hBound ▸ currentFormula) : SetOpenTerm []),
            (quote_hilbert
              (Formula.weakenBoundAt (introduced := introduced) tailBound
                (hBound ▸ currentFormula)) : SetOpenTerm [])))
    (fun {currentBound currentFree} relation arguments => by
      intro tailBound tailRest introduced hBound
      cases hBound
      exact quote_hilbert_relation_weaken_bound_at relation arguments)
    (fun {currentBound currentFree} {sort} left right => by
      intro tailBound tailRest introduced hBound
      cases hBound
      exact quote_hilbert_equality_weaken_bound_at left right)
    (fun {currentBound currentFree} body ih => by
      intro tailBound tailRest introduced hBound
      cases hBound
      exact quote_hilbert_neg_weaken_bound_at body
        (ih tailBound tailRest introduced rfl))
    (fun {currentBound currentFree} left right ihLeft ihRight => by
      intro tailBound tailRest introduced hBound
      cases hBound
      exact quote_hilbert_imp_weaken_bound_at left right
        (ihLeft tailBound tailRest introduced rfl)
        (ihRight tailBound tailRest introduced rfl))
    (fun {currentBound currentFree} quantified body ih => by
      intro tailBound tailRest introduced hBound
      cases hBound
      exact quote_hilbert_all_weaken_bound_at
        (prefixContext := tailBound) (rest := tailRest)
        (quantified := quantified) body
        (ih (quantified :: tailBound) tailRest introduced rfl))
    formula prefixContext rest introduced rfl
  simpa only [Formula.weakenBoundAt, ← Formula.hilbertize_renameMapped, quote_hilbert_hilbertize] using h

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
