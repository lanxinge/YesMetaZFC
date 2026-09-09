import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.OpenBoundStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaTransformStructuralCorrectness

/-!
# bound 尾槽打开的公式 quotation 正确性

公式递归保持不变量 `currentBound = prefixContext ++ [introduced]`。进入量词时只把
局部 binder 加到 `prefixContext` 前端；被消去的尾槽与 bound-closed replacement 始终不变。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace QuineEncoding

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols

set_option autoImplicit false

private theorem formula_open_bound_scope
    (depth replacement source target : SetOpenTerm [])
    (hReplacement : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ(replacement))
    (hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(Sₘ(depth), source))
    (hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(depth, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement source target := by
  derive_prop

private theorem quote_hilbert_open_bound_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ} {introduced : σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (formula : Formula σ (prefixContext ++ [introduced]) free)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .openBound)
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_term replacement : SetOpenTerm [])
        (quote_hilbert formula : SetOpenTerm [])
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement formula) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement formula) :
          SetOpenTerm [])) := by
  have hReplacementAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ((quote_term replacement : SetOpenTerm [])) := by
    simpa using! quote_term_code_at_expression replacement
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(Sₘ(numₘ(prefixContext.length)),
        (quote_hilbert formula : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_hilbert_code_at_expression formula
  have hTargetAt := quote_hilbert_code_at_expression
    (Formula.instantiateLastBound prefixContext replacement formula)
  apply syntax_transform_intro .formula .openBound prefixContext.length 0
    (quote_term replacement : SetOpenTerm [])
  · exact quote_hilbert_code_mem_expression formula
  · exact quote_hilbert_code_mem_expression
      (Formula.instantiateLastBound prefixContext replacement formula)
  · exact quote_term_code_mem_expression replacement
  · exact formula_open_bound_scope
      (numₘ(prefixContext.length)) _ _ _
      hReplacementAt hSourceAt hTargetAt
  · exact hShape

private theorem quote_hilbert_neg_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ} {introduced : σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (body : Formula σ (prefixContext ++ [introduced]) free)
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement body) :
          SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert (.neg body) : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement (.neg body)) :
          SetOpenTerm [])) := by
  apply quote_hilbert_open_bound_last_of_shape replacement
  simpa [quote_hilbert, Formula.instantiateLastBound,
    Formula.substitute, Formula.substituteMapped] using!
    formula_transform_negation_shape
      .openBound (numₘ(0)) (quote_term replacement : SetOpenTerm [])
      (numₘ(prefixContext.length))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (Formula.instantiateLastBound prefixContext replacement body) :
        SetOpenTerm []) hBody

private theorem quote_hilbert_imp_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ} {introduced : σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (left right : Formula σ (prefixContext ++ [introduced]) free)
    (hLeft : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert left : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement left) :
          SetOpenTerm [])))
    (hRight : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert right : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement right) :
          SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert (.imp left right) : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement (.imp left right)) :
          SetOpenTerm [])) := by
  apply quote_hilbert_open_bound_last_of_shape replacement
  simpa [quote_hilbert, Formula.instantiateLastBound,
    Formula.substitute, Formula.substituteMapped] using!
    formula_transform_implication_shape
      .openBound (numₘ(0)) (quote_term replacement : SetOpenTerm [])
      (numₘ(prefixContext.length))
      (quote_hilbert left : SetOpenTerm [])
      (quote_hilbert right : SetOpenTerm [])
      (quote_hilbert
        (Formula.instantiateLastBound prefixContext replacement left) :
        SetOpenTerm [])
      (quote_hilbert
        (Formula.instantiateLastBound prefixContext replacement right) :
        SetOpenTerm []) hLeft hRight

private theorem quote_hilbert_all_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {introduced quantified : σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (body : Formula σ
      (quantified :: (prefixContext ++ [introduced])) free)
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ((quantified :: prefixContext).length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound
            (quantified :: prefixContext) replacement body) :
          SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert (.forallE quantified body) : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement
            (.forallE quantified body)) : SetOpenTerm [])) := by
  apply quote_hilbert_open_bound_last_of_shape replacement
  simpa [quote_hilbert, Formula.instantiateLastBound_forallE,
    List.length_cons, finite_numeral_term] using
    formula_transform_universal_preserve_shape
      .openBound (Or.inr (Or.inr (Or.inl rfl)))
      (numₘ(0)) (quote_term replacement : SetOpenTerm [])
      (numₘ(prefixContext.length))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (Formula.instantiateLastBound
          (quantified :: prefixContext) replacement body) :
        SetOpenTerm []) hBody

private theorem quote_hilbert_relation_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ} {introduced : σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (relation : σ.RelSymbol)
    (arguments : Arguments σ (prefixContext ++ [introduced]) free
      (σ.relDomain relation)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert (.rel relation arguments) : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement
            (.rel relation arguments)) : SetOpenTerm [])) := by
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
                          Arguments.instantiateLastBound
                            prefixContext replacement arguments =
                        Arguments.cons
                          (Term.instantiateLastBound
                            prefixContext replacement left)
                          (Arguments.cons
                            (Term.instantiateLastBound
                              prefixContext replacement right)
                            Arguments.nil) := by
                    have hMapped := congrArg
                      (fun typedArguments =>
                        Arguments.instantiateLastBound
                          prefixContext replacement typedArguments)
                      hTypedArguments
                    rw [← Arguments.instantiateLastBound_cast]
                    simpa [Arguments.instantiateLastBound,
                      Substitution.instantiateLastBound,
                      Arguments.substitute, Arguments.substituteMapped,
                      Term.instantiateLastBound, Term.substitute,
                      Term.substituteMapped] using hMapped
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
                          (Arguments.instantiateLastBound
                            prefixContext replacement arguments) =
                        mem_codeₘ(
                          (quote_term
                            (Term.instantiateLastBound
                              prefixContext replacement left) :
                            SetOpenTerm []),
                          (quote_term
                            (Term.instantiateLastBound
                              prefixContext replacement right) :
                            SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation
                      (Arguments.instantiateLastBound
                        prefixContext replacement arguments) hKind]
                    exact quote_membership_arguments_cons_eq relation
                      (Arguments.instantiateLastBound
                        prefixContext replacement arguments) hKind
                      (Term.instantiateLastBound
                        prefixContext replacement left)
                      (Term.instantiateLastBound
                        prefixContext replacement right)
                      hTargetTyped
                  apply quote_hilbert_open_bound_last_of_shape replacement
                  change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
                    syntax_transform_shape_condition
                      (syntax_code_kind_term .formula)
                      (syntax_transform_operation_term .openBound)
                      (numₘ(prefixContext.length)) (numₘ(0))
                      (quote_term replacement : SetOpenTerm [])
                      (quote_relation relation arguments)
                      (quote_relation relation
                        (Arguments.instantiateLastBound
                          prefixContext replacement arguments))
                  rw [hSourceQuote, hTargetQuote]
                  exact formula_transform_binary_shape
                    .openBound (numₘ(0))
                    (quote_term replacement : SetOpenTerm [])
                    .membership (Or.inr rfl)
                    (numₘ(prefixContext.length))
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    (quote_term
                      (Term.instantiateLastBound
                        prefixContext replacement left) : SetOpenTerm [])
                    (quote_term
                      (Term.instantiateLastBound
                        prefixContext replacement right) : SetOpenTerm [])
                    (quote_term_open_bound_last replacement left)
                    (quote_term_open_bound_last replacement right)
  | predicate =>
      have hSourceQuote := quote_relation_predicate_eq
        relation arguments hKind
      have hTargetQuote := quote_relation_predicate_eq relation
        (Arguments.instantiateLastBound prefixContext replacement arguments)
        hKind
      apply quote_hilbert_open_bound_last_of_shape replacement
      change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transform_shape_condition
          (syntax_code_kind_term .formula)
          (syntax_transform_operation_term .openBound)
          (numₘ(prefixContext.length)) (numₘ(0))
          (quote_term replacement : SetOpenTerm [])
          (quote_relation relation arguments)
          (quote_relation relation
            (Arguments.instantiateLastBound
              prefixContext replacement arguments))
      rw [hSourceQuote, hTargetQuote]
      exact formula_transform_predicate_shape
        .openBound (numₘ(0))
        (quote_term replacement : SetOpenTerm [])
        (numₘ(prefixContext.length))
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (Arguments.instantiateLastBound
            prefixContext replacement arguments) : SetOpenTerm [])
        (finite_numeral_mem_expression (σ.relArity relation))
        (finite_numeral_mem_expression
          (QuotationNumbering.relation_number relation))
        (quote_arguments_open_bound_last replacement arguments)

private theorem quote_hilbert_equality_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ}
    {introduced sort : σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (left right : Term σ (prefixContext ++ [introduced]) free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert (.equal left right) : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement
            (.equal left right)) : SetOpenTerm [])) := by
  apply quote_hilbert_open_bound_last_of_shape replacement
  simpa [quote_hilbert, Formula.instantiateLastBound,
    Substitution.instantiateLastBound, Formula.substitute,
    Formula.substituteMapped, Term.instantiateLastBound,
    Term.substitute] using
    formula_transform_binary_shape
      .openBound (numₘ(0))
      (quote_term replacement : SetOpenTerm [])
      .equality (Or.inl rfl)
      (numₘ(prefixContext.length))
      (quote_term left : SetOpenTerm [])
      (quote_term right : SetOpenTerm [])
      (quote_term
        (Term.instantiateLastBound prefixContext replacement left) :
        SetOpenTerm [])
      (quote_term
        (Term.instantiateLastBound prefixContext replacement right) :
        SetOpenTerm [])
      (quote_term_open_bound_last replacement left)
      (quote_term_open_bound_last replacement right)

/-- Hilbert 公式 quotation 与 bound 尾槽闭项实例化交换。 -/
theorem quote_hilbert_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free prefixContext : SortContext σ} {introduced : σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (formula : Formula σ (prefixContext ++ [introduced]) free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (Formula.instantiateLastBound prefixContext replacement formula) :
          SetOpenTerm [])) := by
  have h := Formula.hilbertize_induction QuotationNumbering.objectSort
    (motive := fun {currentBound currentFree} currentFormula =>
      ∀ (tailBound : SortContext σ) (introduced : σ.SortSymbol)
          (replacement : Term σ [] currentFree introduced)
          (hBound : currentBound = tailBound ++ [introduced]),
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          syntax_transformₘ(
            syntax_code_kind_term .formula,
            syntax_transform_operation_term .openBound,
            numₘ(tailBound.length), numₘ(0),
            (quote_term replacement : SetOpenTerm []),
            (quote_hilbert (hBound ▸ currentFormula) : SetOpenTerm []),
            (quote_hilbert
              (Formula.instantiateLastBound tailBound replacement
                (hBound ▸ currentFormula)) : SetOpenTerm [])))
    (fun {currentBound currentFree} relation arguments => by
      intro tailBound introduced replacement hBound
      cases hBound
      exact quote_hilbert_relation_open_bound_last
        replacement relation arguments)
    (fun {currentBound currentFree} {sort} left right => by
      intro tailBound introduced replacement hBound
      cases hBound
      exact quote_hilbert_equality_open_bound_last replacement left right)
    (fun {currentBound currentFree} body ih => by
      intro tailBound introduced replacement hBound
      cases hBound
      exact quote_hilbert_neg_open_bound_last replacement body
        (ih tailBound introduced replacement rfl))
    (fun {currentBound currentFree} left right ihLeft ihRight => by
      intro tailBound introduced replacement hBound
      cases hBound
      exact quote_hilbert_imp_open_bound_last replacement left right
        (ihLeft tailBound introduced replacement rfl)
        (ihRight tailBound introduced replacement rfl))
    (fun {currentBound currentFree} quantified body ih => by
      intro tailBound introduced replacement hBound
      cases hBound
      exact quote_hilbert_all_open_bound_last replacement body
        (ih (quantified :: tailBound) introduced replacement rfl))
    formula prefixContext introduced replacement rfl
  simpa only [Formula.instantiateLastBound, ← Formula.hilbertize_substitute, quote_hilbert_hilbertize] using h

/-- 公共公式 quotation 实现规范的 bound 顶槽打开。 -/
theorem quote_formula_open_bound
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (formula : Formula σ [sort] free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_open_bound_condition
        (quote_term replacement : SetOpenTerm [])
        (quote formula : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement formula) :
          SetOpenTerm []) := by
  simpa [formula_open_bound_condition, quote,
    Formula.instantiateLastBound_nil] using
    (quote_hilbert_open_bound_last (prefixContext := []) replacement
      (Formula.hilbertize QuotationNumbering.objectSort formula))

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
