import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.TransformStructuralCorrectness

/-!
# bound 尾槽打开的项与参数列 quotation 正确性

对象层 `openBound` 删除当前 de Bruijn 深度对应的唯一尾槽，并以 bound-closed 项码
替换。宿主侧使用 `instantiateLastBound` 表达同一操作；局部 binder 只提升 replacement，
因此不需要新鲜性、可替换性或停机旁证。
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

/-! ## scope -/

private theorem term_open_bound_scope
    (depth replacement source target : SetOpenTerm [])
    (hReplacement : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ(replacement))
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(Sₘ(depth), source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(depth, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement source target := by
  derive_prop

private theorem term_list_open_bound_scope
    (depth length replacement source target : SetOpenTerm [])
    (hLength : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      length ∈ₘ ωₘ)
    (hReplacement : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ(replacement))
    (hSource : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(Sₘ(depth), length, source))
    (hTarget : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(depth, length, target)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement source target := by

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


private theorem term_open_bound_free_shape
    (depth replacement : SetOpenTerm []) (index : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
        (free_var_codeₘ(numₘ(index))) (free_var_codeₘ(numₘ(index))) := by

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


private theorem term_open_bound_bound_preserve_shape
    (depth replacement : SetOpenTerm []) (index : Nat)
    (hIndexDepth : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ depth)
    (hIndexSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (numₘ(index) : SetOpenTerm []) ∈ₘ Sₘ(depth)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
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


private theorem term_open_bound_bound_hit_shape
    (depth replacement : SetOpenTerm [])
    (hDepthSuccessor : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      depth ∈ₘ Sₘ(depth)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        depth (numₘ(0)) replacement
        (bound_var_codeₘ(depth)) replacement := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro depth
    rw [Formula.instantiateTop_abstractFreeTop]
    simp only [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
      Term.substituteMapped_weakenFree_instantiateFreeTop]
    derive_prop


private theorem quote_term_open_bound_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (term : Term σ (prefixContext ++ [sort]) free resultSort)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .term)
        (syntax_transform_operation_term .openBound)
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_term replacement : SetOpenTerm [])
        (quote_term term : SetOpenTerm [])
        (quote_term
          (Term.instantiateLastBound prefixContext replacement term) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement term) :
          SetOpenTerm [])) := by
  have hReplacementAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ((quote_term replacement : SetOpenTerm [])) := by
    simpa using! quote_term_code_at_expression replacement
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(Sₘ(numₘ(prefixContext.length)),
        (quote_term term : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_term_code_at_expression term
  have hTargetAt := quote_term_code_at_expression
    (Term.instantiateLastBound prefixContext replacement term)
  apply syntax_transform_intro .term .openBound prefixContext.length 0
    (quote_term replacement : SetOpenTerm [])
  · exact quote_term_code_mem_expression term
  · exact quote_term_code_mem_expression
      (Term.instantiateLastBound prefixContext replacement term)
  · exact quote_term_code_mem_expression replacement
  · exact term_open_bound_scope
      (numₘ(prefixContext.length)) _ _ _
      hReplacementAt hSourceAt hTargetAt
  · exact hShape

private theorem quote_arguments_open_bound_last_of_shape
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (arguments : Arguments σ (prefixContext ++ [sort]) free sorts)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .termList)
        (syntax_transform_operation_term .openBound)
        (numₘ(prefixContext.length)) (numₘ(0))
        (quote_term replacement : SetOpenTerm [])
        (quote_arguments arguments : SetOpenTerm [])
        (quote_arguments
          (Arguments.instantiateLastBound prefixContext replacement arguments) :
          SetOpenTerm [])) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.instantiateLastBound prefixContext replacement arguments) :
          SetOpenTerm [])) := by
  have hReplacementAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_codeₘ((quote_term replacement : SetOpenTerm [])) := by
    simpa using! quote_term_code_at_expression replacement
  have hSourceAt : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(Sₘ(numₘ(prefixContext.length)), numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
    simpa [List.length_append, finite_numeral_term] using
      quote_arguments_code_at_expression arguments
  have hTargetAt := quote_arguments_code_at_expression
    (Arguments.instantiateLastBound prefixContext replacement arguments)
  apply syntax_transform_intro .termList .openBound prefixContext.length 0
    (quote_term replacement : SetOpenTerm [])
  · exact quote_arguments_code_mem_expression arguments
  · exact quote_arguments_code_mem_expression
      (Arguments.instantiateLastBound prefixContext replacement arguments)
  · exact quote_term_code_mem_expression replacement
  · exact term_list_open_bound_scope
      (numₘ(prefixContext.length)) (numₘ(sorts.length)) _ _ _
      (finite_numeral_mem_expression (Γ := []) sorts.length)
      hReplacementAt hSourceAt hTargetAt
  · exact hShape

private theorem quote_bound_variable_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (entry : Variable (prefixContext ++ [sort]) resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term
          (.bvar entry : Term σ (prefixContext ++ [sort]) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement
            (.bvar entry : Term σ (prefixContext ++ [sort]) free resultSort)) :
          SetOpenTerm [])) := by
  rcases VariableSubstitution.instantiateLastBound_bvar
      prefixContext replacement entry with
    ⟨target, hIndex, hTarget⟩ | ⟨hSort, hIndex, hTarget⟩
  · apply quote_term_open_bound_last_of_shape replacement
    have hDepth : entry.index < prefixContext.length := by
      simpa [hIndex] using target.index_lt_length
    have hIndexDepth := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature [])) hDepth
    have hIndexSuccessor := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature [])) (Nat.lt_succ_of_lt hDepth)
    simpa [Term.instantiateLastBound, Substitution.instantiateLastBound,
      Term.substitute, Term.substituteMapped, quote_term, hTarget, hIndex,
      finite_numeral_term] using
      term_open_bound_bound_preserve_shape
        (numₘ(prefixContext.length))
        (quote_term replacement : SetOpenTerm []) entry.index
        hIndexDepth hIndexSuccessor
  · subst resultSort
    apply quote_term_open_bound_last_of_shape replacement
    have hDepthSuccessor := finite_numeral_mem_of_lt_expression
      (Γ := ([] : Context signature []))
      (Nat.lt_succ_self prefixContext.length)
    simpa [Term.instantiateLastBound, Substitution.instantiateLastBound,
      Term.substitute, Term.substituteMapped, quote_term, hTarget, hIndex,
      finite_numeral_term] using
      term_open_bound_bound_hit_shape
        (numₘ(prefixContext.length))
        (quote_term replacement : SetOpenTerm []) hDepthSuccessor

private theorem quote_free_variable_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort) (entry : Variable free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term
          (.fvar entry : Term σ (prefixContext ++ [sort]) free resultSort) :
          SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement
            (.fvar entry : Term σ (prefixContext ++ [sort]) free resultSort)) :
          SetOpenTerm [])) := by
  apply quote_term_open_bound_last_of_shape replacement
  simpa [Term.instantiateLastBound, Substitution.instantiateLastBound,
    Term.substitute, Term.substituteMapped, quote_term] using!
    term_open_bound_free_shape
      (numₘ(prefixContext.length))
      (quote_term replacement : SetOpenTerm []) entry.index

mutual

/-- 项 quotation 与 bound 尾槽闭项实例化交换。 -/
theorem quote_term_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (term : Term σ (prefixContext ++ [sort]) free resultSort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_term term : SetOpenTerm []),
        (quote_term
          (Term.instantiateLastBound prefixContext replacement term) :
          SetOpenTerm [])) := by
  match term with
  | .bvar entry =>
      exact quote_bound_variable_open_bound_last replacement entry
  | .fvar entry =>
      exact quote_free_variable_open_bound_last replacement entry
  | .app function arguments =>
      have ih := quote_arguments_open_bound_last replacement arguments
      cases hDomain : σ.funcDomain function with
      | nil =>
          apply quote_term_open_bound_last_of_shape replacement
          simpa [quote_term, hDomain, Term.instantiateLastBound,
            Substitution.instantiateLastBound, Term.substitute,
            Term.substituteMapped, Arguments.substituteMapped] using
            syntax_transform_constant_shape (syntax_transform_operation_term .openBound)
              (numₘ(prefixContext.length)) (numₘ(0)) (quote_term replacement : SetOpenTerm [])
              (numₘ(QuotationNumbering.function_number function))
              (finite_numeral_mem_expression (Γ := [])
                (QuotationNumbering.function_number function))
      | cons head tail =>
          apply quote_term_open_bound_last_of_shape replacement
          simpa [quote_term, hDomain, Term.instantiateLastBound,
            Arguments.instantiateLastBound,
            Substitution.instantiateLastBound, Term.substitute,
            Arguments.substitute, Term.substituteMapped,
            Arguments.substituteMapped] using
            syntax_transform_application_shape (syntax_transform_operation_term .openBound)
              (numₘ(prefixContext.length)) (numₘ(0)) (quote_term replacement : SetOpenTerm [])
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function))
              (quote_arguments arguments : SetOpenTerm [])
              (quote_arguments
                (Arguments.instantiateLastBound
                  prefixContext replacement arguments) : SetOpenTerm [])
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature [])) (σ.funcArity function))
              (finite_numeral_mem_expression
                (Γ := ([] : Context signature []))
                (QuotationNumbering.function_number function))
              ih

/-- 参数列 quotation 与 bound 尾槽闭项实例化交换。 -/
theorem quote_arguments_open_bound_last
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ} {prefixContext : SortContext σ}
    {introduced : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (replacement : Term σ [] free introduced)
    (arguments : Arguments σ (prefixContext ++ [introduced]) free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term .openBound,
        numₘ(prefixContext.length), numₘ(0),
        (quote_term replacement : SetOpenTerm []),
        (quote_arguments arguments : SetOpenTerm []),
        (quote_arguments
          (Arguments.instantiateLastBound prefixContext replacement arguments) :
          SetOpenTerm [])) := by
  match arguments with
  | .nil =>
      apply quote_arguments_open_bound_last_of_shape replacement
      simpa [quote_arguments, Arguments.instantiateLastBound,
        Substitution.instantiateLastBound, Arguments.substitute,
        Arguments.substituteMapped] using
        syntax_transform_nil_shape (T := expression_encoding_theory) (Γ := [])
          (syntax_transform_operation_term .openBound)
          (numₘ(prefixContext.length)) (numₘ(0)) (quote_term replacement : SetOpenTerm [])
  | @Arguments.cons _ _ _ sort sorts head tail =>
      have ihTail := quote_arguments_open_bound_last replacement tail
      have ihHead := quote_term_open_bound_last replacement head
      apply quote_arguments_open_bound_last_of_shape replacement
      simpa [quote_arguments, Term.instantiateLastBound,
        Arguments.instantiateLastBound,
        Substitution.instantiateLastBound, Term.substitute,
        Arguments.substitute, Term.substituteMapped,
        Arguments.substituteMapped] using
        syntax_transform_cons_shape (syntax_transform_operation_term .openBound)
          (numₘ(prefixContext.length)) (numₘ(0)) (quote_term replacement : SetOpenTerm [])
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          (quote_term
            (Term.instantiateLastBound prefixContext replacement head) :
            SetOpenTerm [])
          (quote_arguments
            (Arguments.instantiateLastBound prefixContext replacement tail) :
            SetOpenTerm [])
          ihHead ihTail

end

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
