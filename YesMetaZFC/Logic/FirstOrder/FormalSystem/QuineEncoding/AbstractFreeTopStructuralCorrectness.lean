import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.TransformStructuralCorrectness

/-!
# 顶部自由变量抽象的 quotation 正确性

对象侧结构变换在递归进入量词时保留局部 binder 的 de Bruijn 位置，并把根部待抽象
自由变量放到这些局部 binder 之后。本模块用尾扩展上下文表达这一递归不变量，根上下文
为空时即退化为公共 `Formula.abstractFreeTop`。
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


private theorem term_abstract_free_top_scope
    (depth source target : SetOpenTerm [])
    (hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(depth, source))
    (hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(Sₘ(depth), target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0)) source target := by
  derive_prop

private theorem term_list_abstract_free_top_scope
    (depth length source target : SetOpenTerm [])
    (hLength : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      length ∈ₘ ωₘ)
    (hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(depth, length, source))
    (hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(Sₘ(depth), length, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0)) source target := by

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


private theorem term_abstract_free_top_bound_shape
    (depth index : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      index ∈ₘ depth) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (bound_var_codeₘ(index)) (bound_var_codeₘ(index)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro index
    rw [Formula.instantiateTop_abstractFreeTop]
    simp only [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
      Term.substituteMapped_weakenFree_instantiateFreeTop]
    derive_prop


private theorem term_abstract_free_top_here_shape
    (depth : SetOpenTerm []) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (free_var_codeₘ(numₘ(0))) (bound_var_codeₘ(depth)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro (numₘ(0) : SetOpenTerm [])
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      free_variable_code_term, bound_variable_code_term,
      structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term] using
      FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := []) 0)
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (free_var_codeₘ(numₘ(0)) : SetOpenTerm []))
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.conj_intro
                    (Metatheory.Derives.equality_refl
                      (syntax_transform_operation_term .abstractFreeTop :
                        SetOpenTerm []))
                    (FirstOrder.Derives.disj_intro_left
                      (FirstOrder.Derives.conj_intro
                        (Metatheory.Derives.equality_refl
                          (numₘ(0) : SetOpenTerm []))
                        (Metatheory.Derives.equality_refl
                          (bound_var_codeₘ(depth) : SetOpenTerm []))))))))))

private theorem term_abstract_free_top_there_shape
    (depth : SetOpenTerm []) (previous : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        depth (numₘ(0)) (numₘ(0))
        (free_var_codeₘ(Sₘ(numₘ(previous))))
        (free_var_codeₘ(numₘ(previous))) := by
  have hPrevious : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(previous) : SetOpenTerm []) ∈ₘ Sₘ(numₘ(previous)) := by
    simpa [finite_numeral_term] using
      finite_numeral_mem_of_lt_expression
        (Γ := ([] : Context signature [])) (Nat.lt_succ_self previous)
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro
      (Sₘ(numₘ(previous)) : SetOpenTerm [])
    rw [Formula.instantiateTop_abstractFreeTop]
    simp only [Formula.instantiateFreeTop, Formula.substitute,
      Substitution.instantiateFreeTop, Formula.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      Term.substituteMapped, Arguments.substituteMapped,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      free_variable_code_term,
      structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term]
    apply FirstOrder.Derives.conj_intro
    · exact finite_numeral_mem_expression (Γ := []) (previous + 1)
    · apply FirstOrder.Derives.conj_intro
      · exact Metatheory.Derives.equality_refl
          (free_var_codeₘ(Sₘ(numₘ(previous))) : SetOpenTerm [])
      · apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.disj_intro_right
        apply FirstOrder.Derives.conj_intro
        · exact Metatheory.Derives.equality_refl
            (syntax_transform_operation_term .abstractFreeTop :
              SetOpenTerm [])
        · apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.exists_intro
            (numₘ(previous) : SetOpenTerm [])
          simpa [Formula.instantiateFreeTop,
            Substitution.instantiateFreeTop,
            Formula.instantiateTop, Substitution.instantiateTop,
            Formula.substitute, Formula.substituteMapped,
            Term.instantiateTop, Term.substituteFree,
            Term.substitute, Term.substituteMapped,
            Arguments.substituteMapped,
            syntax_set_levy_bound, Formula.LevyBound.membership,
            VariableSubstitution.instantiateFreeTop,
            VariableSubstitution.instantiateTop,
            VariableSubstitution.liftFree,
            VariableSubstitution.weakenBound,
            VariableSubstitution.boundId, VariableSubstitution.freeId,
            structural_list_code_term, structural_node_code_term,
            structural_raw_node_code_term, godel_pairing_term] using!
            FirstOrder.Derives.conj_intro hPrevious
              (FirstOrder.Derives.conj_intro
                (Metatheory.Derives.equality_refl
                  (Sₘ(numₘ(previous)) : SetOpenTerm []))
                (Metatheory.Derives.equality_refl
                  (free_var_codeₘ(numₘ(previous)) : SetOpenTerm [])))

private theorem quote_term_abstract_free_top_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (term : Term σ bound (introduced :: free) resultSort)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .abstractFreeTop)
        (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
        (quote_term term : SetOpenTerm [])
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term term : SetOpenTerm []),
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
  have hSourceAt := quote_term_code_at_expression term
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        Sₘ(numₘ(bound.length)),
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression
        (term.abstractFreeTopLast bound introduced)
  apply syntax_transform_intro .term .abstractFreeTop
    bound.length 0 (numₘ(0))
  · exact quote_term_code_mem_expression term
  · exact quote_term_code_mem_expression
      (term.abstractFreeTopLast bound introduced)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_abstract_free_top_scope
      (numₘ(bound.length)) _ _ hSourceAt hTargetAt
  · exact hShape

private theorem quote_arguments_abstract_free_top_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    {introduced : σ.SortSymbol}
    (arguments : Arguments σ bound (introduced :: free) sorts)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .abstractFreeTop)
        (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) : SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  have hSourceAt := quote_arguments_code_at_expression arguments
  have hTargetAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        Sₘ(numₘ(bound.length)), numₘ(sorts.length),
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_arguments_code_at_expression
        (arguments.abstractFreeTopLast bound introduced)
  apply syntax_transform_intro .termList .abstractFreeTop
    bound.length 0 (numₘ(0))
  · exact quote_arguments_code_mem_expression arguments
  · exact quote_arguments_code_mem_expression
      (arguments.abstractFreeTopLast bound introduced)
  · exact finite_numeral_mem_expression (Γ := []) 0
  · exact term_list_abstract_free_top_scope
      (numₘ(bound.length)) (numₘ(sorts.length)) _ _
      (finite_numeral_mem_expression (Γ := []) sorts.length)
      hSourceAt hTargetAt
  · exact hShape

private theorem quote_bound_variable_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (entry : Variable bound resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term
          (.bvar entry : Term σ bound (introduced :: free) resultSort) :
          SetOpenTerm []),
        (quote_term
          ((.bvar entry : Term σ bound (introduced :: free) resultSort)
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  apply quote_term_abstract_free_top_last_of_shape
  have hIndex := finite_numeral_mem_of_lt_expression
    (Γ := ([] : Context signature [])) entry.index_lt_length
  simpa [Term.abstractFreeTopLast, Substitution.abstractFreeTopLast,
      Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
      quote_term, Variable.index_appendRight] using
      term_abstract_free_top_bound_shape
        (numₘ(bound.length)) (numₘ(entry.index)) hIndex

private theorem quote_free_variable_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (entry : Variable (introduced :: free) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term (.fvar entry : Term σ bound
          (introduced :: free) resultSort) : SetOpenTerm []),
        (quote_term
          ((.fvar entry : Term σ bound (introduced :: free) resultSort)
            |>.abstractFreeTopLast bound introduced) : SetOpenTerm [])) := by
  apply quote_term_abstract_free_top_last_of_shape
  cases entry with
  | here =>
      simpa [Term.abstractFreeTopLast, Substitution.abstractFreeTopLast,
        Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
        quote_term, Variable.index, Variable.index_last] using
        term_abstract_free_top_here_shape (numₘ(bound.length))
  | there previous =>
      simpa [Term.abstractFreeTopLast, Substitution.abstractFreeTopLast,
        Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
        quote_term, Variable.index, finite_numeral_term] using
        term_abstract_free_top_there_shape
          (numₘ(bound.length)) previous.index

mutual

/-- 项 quotation 与尾槽自由变量抽象交换。 -/
theorem quote_term_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (term : Term σ bound (introduced :: free) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_term term : SetOpenTerm []),
        (quote_term (term.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
  match term with
  | .bvar entry =>
      exact quote_bound_variable_abstract_free_top_last entry
  | .fvar entry =>
      exact quote_free_variable_abstract_free_top_last entry
  | .app function arguments =>
      have ih := quote_arguments_abstract_free_top_last arguments
      cases hDomain : σ.funcDomain function with
      | nil =>
          apply quote_term_abstract_free_top_last_of_shape
          simpa [quote_term, hDomain, Term.abstractFreeTopLast,
            Substitution.abstractFreeTopLast, Term.substitute,
            Term.substituteMapped, Arguments.substituteMapped] using
            syntax_transform_constant_shape (syntax_transform_operation_term .abstractFreeTop)
              (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
              (numₘ(QuotationNumbering.function_number function))
              (finite_numeral_mem_expression (Γ := [])
                (QuotationNumbering.function_number function))
      | cons head tail =>
          apply quote_term_abstract_free_top_last_of_shape
          simpa [quote_term, hDomain, Term.abstractFreeTopLast,
            Arguments.abstractFreeTopLast, Substitution.abstractFreeTopLast,
            Term.substitute, Arguments.substitute, Term.substituteMapped,
            Arguments.substituteMapped] using
            syntax_transform_application_shape (syntax_transform_operation_term .abstractFreeTop)
              (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function))
              (quote_arguments arguments : SetOpenTerm [])
              (quote_arguments
                (arguments.abstractFreeTopLast bound introduced) :
                SetOpenTerm [])
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature [])) (σ.funcArity function))
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature []))
                (QuotationNumbering.function_number function))
              ih

/-- 参数列 quotation 与尾槽自由变量抽象交换。 -/
theorem quote_arguments_abstract_free_top_last
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    {introduced : σ.SortSymbol}
    (arguments : Arguments σ bound (introduced :: free) sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .abstractFreeTop,
        numₘ(bound.length), numₘ(0), numₘ(0),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (arguments.abstractFreeTopLast bound introduced) :
          SetOpenTerm [])) := by
  match arguments with
  | .nil =>
      apply quote_arguments_abstract_free_top_last_of_shape
      simpa [quote_arguments, Arguments.abstractFreeTopLast,
        Substitution.abstractFreeTopLast, Arguments.substitute,
        Arguments.substituteMapped] using
        syntax_transform_nil_shape (T := expression_encoding_theory) (Γ := [])
          (syntax_transform_operation_term .abstractFreeTop)
          (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
  | @Arguments.cons _ _ _ sort sorts head tail =>
      have ihTail := quote_arguments_abstract_free_top_last tail
      have ihHead := quote_term_abstract_free_top_last head
      apply quote_arguments_abstract_free_top_last_of_shape
      simpa [quote_arguments, Term.abstractFreeTopLast,
        Arguments.abstractFreeTopLast, Substitution.abstractFreeTopLast,
        Term.substitute, Arguments.substitute, Term.substituteMapped,
        Arguments.substituteMapped] using
        syntax_transform_cons_shape (syntax_transform_operation_term .abstractFreeTop)
          (numₘ(bound.length)) (numₘ(0)) (numₘ(0))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term (head.abstractFreeTopLast bound introduced) :
            SetOpenTerm [])
          (quote_arguments
            (tail.abstractFreeTopLast bound introduced) : SetOpenTerm [])
          ihHead ihTail

end

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
