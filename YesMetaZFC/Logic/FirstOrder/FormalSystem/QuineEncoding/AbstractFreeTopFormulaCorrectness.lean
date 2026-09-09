import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.AbstractFreeTopStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaTransformStructuralCorrectness

/-!
# 顶部自由变量抽象的公式 quotation 正确性

本层在项与参数列递归已经闭合的基础上，只处理 Hilbert 公式码的六种结构节点。
高层逻辑构造先由 `quote_hilbert` 展开为这些节点，不再重复承担变量、码域与 scope 义务。
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

private theorem formula_abstract_free_top_scope
    (depth source target : SetOpenTerm [])
    (hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(depth, source))
    (hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(Sₘ(depth), target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0)) source target := by
  derive_prop

private theorem quote_hilbert_abstract_free_top_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (formula : Formula σ bound (introduced :: free))
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .abstractFreeTop)
        (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
        (quote_hilbert formula : SetOpenTerm [])
        (quote_hilbert
          (formula.abstractFreeTopLast bound introduced) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (formula.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  have hSourceAt := quote_hilbert_code_at_expression formula
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(
        Sₘ(numₘ(bound.length)),
        (quote_hilbert
          (formula.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_hilbert_code_at_expression
        (formula.abstractFreeTopLast bound introduced)
  apply syntax_transform_intro .formula .abstractFreeTop
    bound.length 0 (numₘ(0))
  · exact quote_hilbert_code_mem_expression formula
  · exact quote_hilbert_code_mem_expression
      (formula.abstractFreeTopLast bound introduced)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact formula_abstract_free_top_scope
      (numₘ(bound.length)) _ _ hSourceAt hTargetAt
  · exact hShape


private theorem quote_hilbert_neg_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (body : Formula σ bound (introduced :: free))
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (body.abstractFreeTopLast bound introduced) : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert (.neg body) : SetOpenTerm []),
        (quote_hilbert
          ((.neg body : Formula σ bound (introduced :: free))
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  apply quote_hilbert_abstract_free_top_last_of_shape
  simpa [quote_hilbert, Formula.abstractFreeTopLast,
    Substitution.abstractFreeTopLast, Formula.substitute,
    Formula.substituteMapped] using
    formula_transform_negation_shape
      .abstractFreeTop (numₘ(0)) (numₘ(0))
      (numₘ(bound.length))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (body.abstractFreeTopLast bound introduced) : SetOpenTerm [])
      hBody

private theorem quote_hilbert_imp_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound (introduced :: free))
    (hLeft : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert left : SetOpenTerm []),
        (quote_hilbert
          (left.abstractFreeTopLast bound introduced) : SetOpenTerm [])))
    (hRight : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert right : SetOpenTerm []),
        (quote_hilbert
          (right.abstractFreeTopLast bound introduced) : SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert (.imp left right) : SetOpenTerm []),
        (quote_hilbert
          ((.imp left right : Formula σ bound (introduced :: free))
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  apply quote_hilbert_abstract_free_top_last_of_shape
  simpa [quote_hilbert, Formula.abstractFreeTopLast,
    Substitution.abstractFreeTopLast, Formula.substitute,
    Formula.substituteMapped] using
    formula_transform_implication_shape
      .abstractFreeTop (numₘ(0)) (numₘ(0))
      (numₘ(bound.length))
      (quote_hilbert left : SetOpenTerm [])
      (quote_hilbert right : SetOpenTerm [])
      (quote_hilbert
        (left.abstractFreeTopLast bound introduced) : SetOpenTerm [])
      (quote_hilbert
        (right.abstractFreeTopLast bound introduced) : SetOpenTerm [])
      hLeft hRight

private theorem quote_hilbert_all_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {introduced quantified : σ.SortSymbol}
    (body : Formula σ (quantified :: bound) (introduced :: free))
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ((quantified :: bound).length), numₘ(0), numₘ(0),
        (quote_hilbert body : SetOpenTerm []),
        (quote_hilbert
          (body.abstractFreeTopLast (quantified :: bound) introduced) :
          SetOpenTerm []))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert (.forallE quantified body) : SetOpenTerm []),
        (quote_hilbert
          ((.forallE quantified body : Formula σ bound (introduced :: free))
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  apply quote_hilbert_abstract_free_top_last_of_shape
  simpa [quote_hilbert, Formula.abstractFreeTopLast,
    Formula.substitute, Formula.substituteMapped,
    Substitution.abstractFreeTopLast_cons,
    List.length_cons, finite_numeral_term] using!
    formula_transform_universal_preserve_shape
      .abstractFreeTop (Or.inr (Or.inr (Or.inr rfl)))
      (numₘ(0)) (numₘ(0))
      (numₘ(bound.length))
      (quote_hilbert body : SetOpenTerm [])
      (quote_hilbert
        (body.abstractFreeTopLast (quantified :: bound) introduced) :
        SetOpenTerm []) hBody

private theorem quote_hilbert_relation_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound (introduced :: free)
      (σ.relDomain relation)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert (.rel relation arguments) : SetOpenTerm []),
        (quote_hilbert
          ((.rel relation arguments : Formula σ bound (introduced :: free))
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
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
                          arguments.abstractFreeTopLast bound introduced =
                        Arguments.cons
                          (left.abstractFreeTopLast bound introduced)
                          (Arguments.cons
                            (right.abstractFreeTopLast bound introduced)
                            Arguments.nil) := by
                    have hMapped := congrArg
                      (fun typedArguments =>
                        typedArguments.abstractFreeTopLast bound introduced)
                      hTypedArguments
                    rw [← Arguments.abstractFreeTopLast_cast]
                    simpa [Arguments.abstractFreeTopLast,
                      Substitution.abstractFreeTopLast,
                      Arguments.substitute, Arguments.substituteMapped,
                      Term.abstractFreeTopLast, Term.substitute,
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
                          (arguments.abstractFreeTopLast bound introduced) =
                        mem_codeₘ(
                          (quote_term
                            (left.abstractFreeTopLast bound introduced) :
                            SetOpenTerm []),
                          (quote_term
                            (right.abstractFreeTopLast bound introduced) :
                            SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation
                      (arguments.abstractFreeTopLast bound introduced) hKind]
                    exact quote_membership_arguments_cons_eq relation
                      (arguments.abstractFreeTopLast bound introduced) hKind
                      (left.abstractFreeTopLast bound introduced)
                      (right.abstractFreeTopLast bound introduced)
                      hTargetTyped
                  apply quote_hilbert_abstract_free_top_last_of_shape
                  change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
                    syntax_transform_shape_condition
                      (syntax_code_kind_term .formula)
                      (syntax_transform_operation_term .abstractFreeTop)
                      (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
                      (quote_relation relation arguments)
                      (quote_relation relation
                        (arguments.abstractFreeTopLast bound introduced))
                  rw [hSourceQuote, hTargetQuote]
                  exact formula_transform_binary_shape
                    .abstractFreeTop (numₘ(0)) (numₘ(0))
                    .membership (Or.inr rfl)
                    (numₘ(bound.length))
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    (quote_term
                      (left.abstractFreeTopLast bound introduced) :
                      SetOpenTerm [])
                    (quote_term
                      (right.abstractFreeTopLast bound introduced) :
                      SetOpenTerm [])
                    (quote_term_abstract_free_top_last left)
                    (quote_term_abstract_free_top_last right)
  | predicate =>
      have hSourceQuote := quote_relation_predicate_eq
        relation arguments hKind
      have hTargetQuote := quote_relation_predicate_eq relation
        (arguments.abstractFreeTopLast bound introduced) hKind
      apply quote_hilbert_abstract_free_top_last_of_shape
      change ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        syntax_transform_shape_condition
          (syntax_code_kind_term .formula)
          (syntax_transform_operation_term .abstractFreeTop)
          (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
          (quote_relation relation arguments)
          (quote_relation relation
            (arguments.abstractFreeTopLast bound introduced))
      rw [hSourceQuote, hTargetQuote]
      exact formula_transform_predicate_shape
        .abstractFreeTop (numₘ(0)) (numₘ(0))
        (numₘ(bound.length))
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])
        (finite_numeral_mem_expression (σ.relArity relation))
        (finite_numeral_mem_expression
          (QuotationNumbering.relation_number relation))
        (quote_arguments_abstract_free_top_last arguments)

private theorem quote_hilbert_equality_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (left right : Term σ bound (introduced :: free) sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert (.equal left right) : SetOpenTerm []),
        (quote_hilbert
          ((.equal left right : Formula σ bound (introduced :: free))
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  apply quote_hilbert_abstract_free_top_last_of_shape
  simpa [quote_hilbert, Formula.abstractFreeTopLast,
    Substitution.abstractFreeTopLast, Formula.substitute,
    Formula.substituteMapped, Term.abstractFreeTopLast,
    Term.substitute] using
    formula_transform_binary_shape
      .abstractFreeTop (numₘ(0)) (numₘ(0))
      .equality (Or.inl rfl)
      (numₘ(bound.length))
      (quote_term left : SetOpenTerm [])
      (quote_term right : SetOpenTerm [])
      (quote_term (left.abstractFreeTopLast bound introduced) :
        SetOpenTerm [])
      (quote_term (right.abstractFreeTopLast bound introduced) :
        SetOpenTerm [])
      (quote_term_abstract_free_top_last left)
      (quote_term_abstract_free_top_last right)

/-- Hilbert 公式 quotation 与尾槽自由变量抽象交换。 -/
theorem quote_hilbert_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (formula : Formula σ bound (introduced :: free)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_hilbert formula : SetOpenTerm []),
        (quote_hilbert
          (formula.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
  have h := Formula.hilbertize_induction QuotationNumbering.objectSort
    (motive := fun {currentBound currentFree} currentFormula =>
      ∀ (tail : SortContext σ) (head : σ.SortSymbol)
          (hFree : currentFree = head :: tail),
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          syntax_transformₘ(
            syntax_code_kind_term .formula,
            syntax_transform_operation_term .abstractFreeTop,
            numₘ(currentBound.length), numₘ(0), numₘ(0),
            (quote_hilbert (hFree ▸ currentFormula) : SetOpenTerm []),
            (quote_hilbert
              ((hFree ▸ currentFormula).abstractFreeTopLast
                currentBound head) : SetOpenTerm [])))
    (fun {currentBound currentFree}
        relation arguments => by
      intro tail head hFree
      cases hFree
      exact quote_hilbert_relation_abstract_free_top_last relation arguments)
    (fun {currentBound currentFree}
        {sort} left right => by
      intro tail head hFree
      cases hFree
      exact quote_hilbert_equality_abstract_free_top_last left right)
    (fun {currentBound currentFree} body ih => by
      intro tail head hFree
      cases hFree
      exact quote_hilbert_neg_abstract_free_top_last
        body (ih tail head rfl))
    (fun {currentBound currentFree}
        left right ihLeft ihRight => by
      intro tail head hFree
      cases hFree
      exact quote_hilbert_imp_abstract_free_top_last
        left right (ihLeft tail head rfl) (ihRight tail head rfl))
    (fun {currentBound currentFree}
        sort body ih => by
      intro tail head hFree
      cases hFree
      exact quote_hilbert_all_abstract_free_top_last
        body (ih tail head rfl))
    formula free introduced rfl
  simpa only [Formula.abstractFreeTopLast, ← Formula.hilbertize_substitute, quote_hilbert_hilbertize] using h

/-- 公共公式 quotation 实现规范的顶部自由变量抽象。 -/
theorem quote_formula_abstract_free_top
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {sort : σ.SortSymbol}
    (formula : Formula σ [] (sort :: free)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_abstract_free_top_condition
        (quote formula : SetOpenTerm [])
        (quote formula.abstractFreeTop : SetOpenTerm []) := by
  simpa [formula_abstract_free_top_condition, quote,
    Formula.hilbertize_abstractFreeTop,
    Formula.abstractFreeTopLast_nil] using
    (quote_hilbert_abstract_free_top_last
      (Formula.hilbertize QuotationNumbering.objectSort formula))

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
