import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols
set_option autoImplicit false
mutual
def Term.free_index_occurs {σ : Signature} {bound free : SortContext σ}
    {sort : σ.SortSymbol} (index : Nat) : Term σ bound free sort → Prop
  | .bvar _ => False
  | .fvar entry => entry.index = index
  | .app _ arguments => Arguments.free_index_occurs index arguments
def Arguments.free_index_occurs {σ : Signature} {bound free : SortContext σ}
    {sorts : List σ.SortSymbol} (index : Nat) : Arguments σ bound free sorts → Prop
  | .nil => False
  | .cons head tail =>
      Term.free_index_occurs index head ∨
        Arguments.free_index_occurs index tail
def Formula.free_index_occurs {σ : Signature} {bound free : SortContext σ}
    (index : Nat) : Formula σ bound free → Prop
  | .falsum => False
  | .truth => False
  | .rel _ arguments => Arguments.free_index_occurs index arguments
  | .equal left right =>
      Term.free_index_occurs index left ∨
        Term.free_index_occurs index right
  | .neg body => Formula.free_index_occurs index body
  | .conj left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .disj left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .imp left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .iff left right =>
      Formula.free_index_occurs index left ∨
        Formula.free_index_occurs index right
  | .forallE _ body => Formula.free_index_occurs index body
  | .existsE _ body => Formula.free_index_occurs index body
end
private theorem finite_numeral_mem_expression_encoding {free : SetContext} {Γ : Context signature free} (number : Nat) :
    Γ ⊢ₘ[expression_encoding_theory] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)
private theorem structural_node_mem_expression_encoding_leaf {free : SetContext} {Γ : Context signature free}
    (tag : StructuralCodeTag) (fields : List (SetOpenTerm free))
    (hFields : ∀ field, field ∈ fields →
      Γ ⊢ₘ[formal_language_encoding_theory] field ∈ₘ ωₘ) :
    Γ ⊢ₘ[expression_encoding_theory]
      structural_node_code_term tag fields ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (structural_node_code_mem_formal_language_encoding_theory
      (Γ := Γ) tag fields hFields)
private theorem arguments_free_index_occurs_nil {σ : Signature}
    {bound free : SortContext σ}
    (index : Nat)
    (arguments : Arguments σ bound free []) :
    ¬ Arguments.free_index_occurs index arguments := by
  cases arguments
  simp [Arguments.free_index_occurs]
private theorem arguments_free_index_occurs_cast {σ : Signature}
    {bound free : SortContext σ}
    {sorts₁ sorts₂ : List σ.SortSymbol}
    (index : Nat) (h : sorts₁ = sorts₂)
    (arguments : Arguments σ bound free sorts₁) :
    Arguments.free_index_occurs index (h ▸ arguments) ↔
      Arguments.free_index_occurs index arguments := by
  subst h
  rfl
private theorem free_variable_occurs_term_leaf (index : Nat) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .term,
        numₘ(index),
        (free_var_codeₘ(numₘ(index)) : SetOpenTerm [])) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .term)
      (numₘ(index))
      (free_var_codeₘ(numₘ(index)) : SetOpenTerm []))
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 0
      · exact finite_numeral_mem_expression_encoding (Γ := []) index
    · exact structural_node_mem_expression_encoding_leaf
        (Γ := []) StructuralCodeTag.freeVariable [numₘ(index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with rfl | hField
          · exact finite_numeral_mem_formal_language_encoding_theory
              (Γ := []) index
          · contradiction)
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .term : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_left
      apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
      simpa [free_variable_occurs_definition_instance,
        free_variable_occurs_condition,
        structural_list_code_term, Formula.substituteFree,
        Substitution.free_map, Formula.substitute,
        Formula.substituteMapped, Term.substituteFree,
        Term.substitute, Term.substituteMapped,
        Arguments.substituteMapped, Term.instantiateFreeTop,
        Arguments.instantiateFreeTop, Substitution.instantiateFreeTop,
        VariableSubstitution.instantiateFreeTop,
        structural_raw_node_code_term, godel_pairing_term,
        free_variable_code_term, term_weaken_free_two,
        term_weaken_free_three,
        VariableSubstitution.liftFree] using! FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression_encoding (Γ := []) index)
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (free_var_codeₘ(numₘ(index)) : SetOpenTerm []))
            (Metatheory.Derives.equality_refl
            (numₘ(index) : SetOpenTerm [])))
private theorem free_variable_occurs_application_intro
    (index code arity symbol arguments : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hArity :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        arity ∈ₘ ωₘ)
    (hSymbol :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        symbol ∈ₘ ωₘ)
    (hOccurrence :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        free_var_occursₘ(
          syntax_code_kind_term .termList, index, arguments))
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ app_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .term, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .term) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 0
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .term : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_right
      dsimp
      apply FirstOrder.Derives.existsFreePrefix_intro
        (.cons arguments (.cons symbol (.cons arity .nil)))
      simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
        Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
        Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
        Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
        structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
        godel_pairing_term, application_code_term, term_weaken_free_three] using
        FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro hArity hSymbol)
          (FirstOrder.Derives.conj_intro hCode hOccurrence)

private theorem free_variable_occurs_cons_intro
    (index code head tail : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ code_consₘ(head, tail))
    (hBranch :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        (free_var_occursₘ(syntax_code_kind_term .term, index, head) ∨ₘ
          free_var_occursₘ(syntax_code_kind_term .termList, index, tail))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .termList, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .termList) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 1
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .termList : SetOpenTerm [])
    · dsimp
      apply FirstOrder.Derives.existsFreePrefix_intro
        (.cons tail (.cons head .nil))
      simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
        Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
        Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
        Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
        structural_raw_node_code_term, godel_pairing_term, term_weaken_free_two] using
        FirstOrder.Derives.conj_intro hCode hBranch

private theorem free_variable_occurs_binary_formula_intro
    (tag : StructuralCodeTag)
    (hTag : tag = .equality ∨ tag = .membership)
    (index code left right : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ structural_node_code_term tag [left, right])
    (hBranch :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        (free_var_occursₘ(syntax_code_kind_term .term, index, left) ∨ₘ
          free_var_occursₘ(syntax_code_kind_term .term, index, right))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · rcases hTag with hTag | hTag
      all_goals
        first
        | have : tag = .equality := hTag
          apply FirstOrder.Derives.disj_intro_left
        | have : tag = .membership := hTag
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_left
      all_goals
        dsimp
        apply FirstOrder.Derives.existsFreePrefix_intro
          (.cons right (.cons left .nil))
        simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
          Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
          Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
          Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
          structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
          godel_pairing_term, term_weaken_free_two, hTag] using
          FirstOrder.Derives.conj_intro hCode hBranch

private theorem free_variable_occurs_unary_formula_intro
    (tag : StructuralCodeTag)
    (hTag : tag = .negation ∨ tag = .universal)
    (index code body : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ structural_node_code_term tag [body])
    (hBody :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        free_var_occursₘ(syntax_code_kind_term .formula, index, body)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · rcases hTag with hTag | hTag
      all_goals
        first
        | have : tag = .negation := hTag
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_left
        | have : tag = .universal := hTag
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
          apply FirstOrder.Derives.disj_intro_right
      all_goals
        dsimp
        apply FirstOrder.Derives.existsFreePrefix_intro
          (.cons body .nil)
        simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
          Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
          Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
          Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
          structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
          godel_pairing_term, hTag] using
          FirstOrder.Derives.conj_intro hCode hBody

private theorem free_variable_occurs_implication_formula_intro
    (index code left right : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ imp_codeₘ(left, right))
    (hBranch :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        (free_var_occursₘ(
            syntax_code_kind_term .formula, index, left) ∨ₘ
          free_var_occursₘ(
            syntax_code_kind_term .formula, index, right))) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_left
      dsimp
      apply FirstOrder.Derives.existsFreePrefix_intro
        (.cons right (.cons left .nil))
      simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
        Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
        Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
        Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
        structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
        godel_pairing_term, implication_formula_code_term, term_weaken_free_two] using
        FirstOrder.Derives.conj_intro hCode hBranch

private theorem free_variable_occurs_predicate_formula_intro
    (index code arity symbol arguments : SetOpenTerm [])
    (hIndex :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        index ∈ₘ ωₘ)
    (hCodeMem :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ∈ₘ ωₘ)
    (hArity :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        arity ∈ₘ ωₘ)
    (hSymbol :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        symbol ∈ₘ ωₘ)
    (hArguments :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        free_var_occursₘ(
          syntax_code_kind_term .termList, index, arguments))
    (hCode :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        code ≐ₘ pred_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(syntax_code_kind_term .formula, index, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (free_variable_occurs_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term .formula) index code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · apply FirstOrder.Derives.conj_intro
      · exact finite_numeral_mem_expression_encoding (Γ := []) 2
      · exact hIndex
    · exact hCodeMem
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.conj_intro
    · exact Metatheory.Derives.equality_refl
        (syntax_code_kind_term .formula : SetOpenTerm [])
    · apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_right
      apply FirstOrder.Derives.disj_intro_left
      dsimp
      apply FirstOrder.Derives.existsFreePrefix_intro
        (.cons arguments (.cons symbol (.cons arity .nil)))
      simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
        Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
        Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
        Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
        structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
        godel_pairing_term, predicate_formula_code_term, term_weaken_free_three] using
        FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro hArity hSymbol)
          (FirstOrder.Derives.conj_intro hCode hArguments)

mutual

theorem quote_term_free_index_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (index : Nat) (term : Term σ bound free sort)
    (h : Term.free_index_occurs index term) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .term,
        numₘ(index),
        (quote_term term : SetOpenTerm [])) := by
  match term with
  | .bvar _ => exact False.elim h
  | .fvar entry =>
      have hIndex : entry.index = index := h
      rw [← hIndex]
      simpa [quote_term] using free_variable_occurs_term_leaf entry.index
  | .app function arguments =>
      have hArguments : Arguments.free_index_occurs index arguments := h
      have hOccurs := quote_arguments_free_index_occurs index arguments hArguments
      cases hDomain : σ.funcDomain function with
      | nil =>
          exact False.elim (arguments_free_index_occurs_nil index (hDomain ▸ arguments)
            ((arguments_free_index_occurs_cast index hDomain arguments).2 hArguments))
      | cons head tail =>
          apply free_variable_occurs_application_intro
            _ _ (numₘ(σ.funcArity function))
            (numₘ(QuotationNumbering.function_number function))
            (quote_arguments arguments)
            (finite_numeral_mem_expression index)
            (quote_term_code_mem_expression (.app function arguments))
            (finite_numeral_mem_expression (σ.funcArity function))
            (finite_numeral_mem_expression (QuotationNumbering.function_number function))
            hOccurs
          simpa [quote_term, hDomain] using
            Metatheory.Derives.equality_refl (quote_term (.app function arguments))

theorem quote_arguments_free_index_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (index : Nat) (arguments : Arguments σ bound free sorts)
    (h : Arguments.free_index_occurs index arguments) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .termList,
        numₘ(index),
        (quote_arguments arguments : SetOpenTerm [])) := by
  match arguments with
  | .nil => exact False.elim h
  | .cons head tail =>
      apply free_variable_occurs_cons_intro _ _ (quote_term head) (quote_arguments tail)
        (finite_numeral_mem_expression index)
        (quote_arguments_code_mem_expression (.cons head tail))
        (Metatheory.Derives.equality_refl _)
      exact h.elim
        (fun hHead => FirstOrder.Derives.disj_intro_left
          (quote_term_free_index_occurs index head hHead))
        (fun hTail => FirstOrder.Derives.disj_intro_right
          (quote_arguments_free_index_occurs index tail hTail))

end

private theorem formula_quote_code_mem_expression_encoding
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote formula : SetOpenTerm []) ∈ₘ ωₘ := by
  exact FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (formula_code_at_code_mem_of_derives
      (numₘ(bound.length))
      (quote formula : SetOpenTerm [])
      (quote_formula_code_at formula))
/-- 将宿主语法中的出现性沿三个 Hilbert 基础构造运输。 -/
private abbrev QuotedOccurs {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} (index : Nat) (formula : Formula σ bound free) :=
  ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
    free_var_occursₘ(syntax_code_kind_term .formula, numₘ(index), quote formula)

private theorem quotedOccurs_neg {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {index : Nat} {body : Formula σ bound free}
    (h : QuotedOccurs index body) : QuotedOccurs index (.neg body) := by
  exact free_variable_occurs_unary_formula_intro .negation (Or.inl rfl)
    _ _ _ (finite_numeral_mem_expression_encoding index)
    (formula_quote_code_mem_expression_encoding (.neg body))
    (Metatheory.Derives.equality_refl _) h

private theorem quotedOccurs_imp {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {index : Nat} {left right : Formula σ bound free}
    (h : QuotedOccurs index left ∨ QuotedOccurs index right) :
    QuotedOccurs index (.imp left right) := by
  apply free_variable_occurs_implication_formula_intro _ _ _ _
    (finite_numeral_mem_expression_encoding index)
    (formula_quote_code_mem_expression_encoding (.imp left right))
    (Metatheory.Derives.equality_refl _)
  exact h.elim FirstOrder.Derives.disj_intro_left FirstOrder.Derives.disj_intro_right

private theorem quotedOccurs_all {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {index : Nat} {sort : σ.SortSymbol}
    {body : Formula σ (sort :: bound) free} (h : QuotedOccurs index body) :
    QuotedOccurs index (.forallE sort body) := by
  exact free_variable_occurs_unary_formula_intro .universal (Or.inr rfl)
    _ _ _ (finite_numeral_mem_expression_encoding index)
    (formula_quote_code_mem_expression_encoding (.forallE sort body))
    (Metatheory.Derives.equality_refl _) h

theorem quote_formula_free_index_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (index : Nat) (formula : Formula σ bound free)
    (h : Formula.free_index_occurs index formula) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .formula,
        numₘ(index),
        (quote formula : SetOpenTerm [])) := by
  refine Formula.rec
    (motive := fun bound free formula =>
      Formula.free_index_occurs index formula →
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          free_var_occursₘ(
            syntax_code_kind_term .formula,
            numₘ(index),
            (quote formula : SetOpenTerm [])))
    (fun h => by simp [Formula.free_index_occurs] at h)
    (fun h => by simp [Formula.free_index_occurs] at h)
    (fun {bound free} relation arguments h => by
      have hArguments : Arguments.free_index_occurs index arguments := by
        simpa [Formula.free_index_occurs] using h
      generalize hKind : QuotationNumbering.relation_kind relation = kind
      cases kind with
      | membership =>
          generalize hTypedArguments :
            (QuotationNumbering.membership_domain relation hKind ▸ arguments) =
              typedArguments
          have hTypedOccurrence :
              Arguments.free_index_occurs index typedArguments := by
            rw [← hTypedArguments]
            exact (arguments_free_index_occurs_cast index
              (QuotationNumbering.membership_domain relation hKind)
              arguments).2 hArguments
          cases typedArguments with
          | cons left rest =>
              cases rest with
              | cons right tail =>
                  cases tail with
                  | nil =>
                      have hOccurrence :
                          Term.free_index_occurs index left ∨
                            Term.free_index_occurs index right := by
                        simpa [Arguments.free_index_occurs] using
                          hTypedOccurrence
                      have hQuoteRelation :
                          quote_relation relation arguments =
                            mem_codeₘ(
                              (quote_term left : SetOpenTerm []),
                              (quote_term right : SetOpenTerm [])) := by
                        rw [quote_relation_membership_eq
                          relation arguments hKind]
                        exact quote_membership_arguments_cons_eq
                          relation arguments hKind left right hTypedArguments
                      have hQuote :
                          quote (.rel relation arguments) =
                            mem_codeₘ(
                              (quote_term left : SetOpenTerm []),
                              (quote_term right : SetOpenTerm [])) := by
                        simpa [quote, Formula.hilbertize,
                          quote_hilbert] using hQuoteRelation
                      apply free_variable_occurs_binary_formula_intro
                        .membership (Or.inr rfl) _ _ (quote_term left) (quote_term right)
                        (finite_numeral_mem_expression index)
                        (formula_quote_code_mem_expression_encoding (.rel relation arguments))
                        (by rw [hQuote]; exact Metatheory.Derives.equality_refl _)
                      exact hOccurrence.elim
                        (fun hLeft => FirstOrder.Derives.disj_intro_left
                          (quote_term_free_index_occurs index left hLeft))
                        (fun hRight => FirstOrder.Derives.disj_intro_right
                          (quote_term_free_index_occurs index right hRight))
      | predicate =>
          have hQuoteRelation :
              quote_relation relation arguments =
                pred_codeₘ(
                  numₘ(σ.relArity relation),
                  numₘ(QuotationNumbering.relation_number relation),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            exact quote_relation_predicate_eq
              relation arguments hKind
          have hQuote :
              quote (.rel relation arguments) =
                pred_codeₘ(
                  numₘ(σ.relArity relation),
                  numₘ(QuotationNumbering.relation_number relation),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [quote, Formula.hilbertize,
              quote_hilbert] using hQuoteRelation
          apply free_variable_occurs_predicate_formula_intro
            _ _ (numₘ(σ.relArity relation))
            (numₘ(QuotationNumbering.relation_number relation))
            (quote_arguments arguments)
            (finite_numeral_mem_expression index)
            (formula_quote_code_mem_expression_encoding (.rel relation arguments))
            (finite_numeral_mem_expression (σ.relArity relation))
            (finite_numeral_mem_expression (QuotationNumbering.relation_number relation))
            (quote_arguments_free_index_occurs index arguments hArguments)
          rw [hQuote]
          exact Metatheory.Derives.equality_refl _)
    (fun {bound free} {sort} left right h => by
      apply free_variable_occurs_binary_formula_intro .equality (Or.inl rfl)
        _ _ _ _ (finite_numeral_mem_expression_encoding index)
        (formula_quote_code_mem_expression_encoding (.equal left right))
        (Metatheory.Derives.equality_refl _)
      exact h.elim
        (fun hLeft => FirstOrder.Derives.disj_intro_left
          (quote_term_free_index_occurs index left hLeft))
        (fun hRight => FirstOrder.Derives.disj_intro_right
          (quote_term_free_index_occurs index right hRight)))
    (fun body ih h => by
      simp only [Formula.free_index_occurs] at h
      exact quotedOccurs_neg (ih h))
    (fun left right ihLeft ihRight h => by
      simp only [Formula.free_index_occurs] at h
      exact quotedOccurs_neg (quotedOccurs_imp
        (h.elim (fun h => Or.inl (ihLeft h))
          (fun h => Or.inr (quotedOccurs_neg (ihRight h))))))
    (fun left right ihLeft ihRight h => by
      simp only [Formula.free_index_occurs] at h
      exact quotedOccurs_imp (h.elim
        (fun h => Or.inl (quotedOccurs_neg (ihLeft h)))
        (fun h => Or.inr (ihRight h))))
    (fun left right ihLeft ihRight h => by
      simp only [Formula.free_index_occurs] at h
      exact quotedOccurs_imp (h.elim (fun h => Or.inl (ihLeft h))
        (fun h => Or.inr (ihRight h))))
    (fun left right ihLeft ihRight h => by
      simp only [Formula.free_index_occurs] at h
      exact quotedOccurs_neg (quotedOccurs_imp (right := .neg (.imp right left)) (Or.inl
        (quotedOccurs_imp (h.elim (fun h => Or.inl (ihLeft h))
          (fun h => Or.inr (ihRight h)))))))
    (fun sort body ih h => by
      simp only [Formula.free_index_occurs] at h
      exact quotedOccurs_all (ih h))
    (fun sort body ih h => by
      simp only [Formula.free_index_occurs] at h
      simpa only [QuotedOccurs, quote, Formula.hilbertize, quote_hilbert] using
        (quotedOccurs_neg (quotedOccurs_all (quotedOccurs_neg (ih h)))))
    formula h
theorem quote_free_variable_term_occurs
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (entry : Variable free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      free_var_occursₘ(
        syntax_code_kind_term .term,
        numₘ(entry.index),
        (quote_term
          (bound := bound) (free := free) (sort := sort)
          (Term.fvar entry) : SetOpenTerm [])) := by
  simpa [quote_term] using free_variable_occurs_term_leaf entry.index
end YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
