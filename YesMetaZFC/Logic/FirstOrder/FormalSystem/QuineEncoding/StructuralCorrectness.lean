import YesMetaZFC.Logic.FirstOrder.Derivation.QuantifierBlock
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormalSystem
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.DefinitionContracts

/-!
# 结构 quotation 的对象侧正确性

本层只证明最底层的闭包事实与项码分支。quotation 本身是宿主内在语法的总函数，
对象侧只需验证其结果满足结构递归谓词；不再引入独立的编码值、良构证书或停机证书。
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

private derive_theory_subset infinity_theory ⊆ formal_language_encoding_theory

private theorem godel_pairing_core_subset_formal_language_encoding_theory
    {sentence : SetSentence}
    (hSentence : godel_pairing_core_theory sentence) :
    formal_language_encoding_theory sentence :=
  natural_addition_bound_theory_subset_formal_language_encoding_theory
    (natural_exponentiation_bound_theory_subset_addition_bound_theory
      (godel_pairing_core_theory_subset_bound_theory hSentence))

theorem finite_numeral_mem_formal_language_encoding_theory
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ := by
  exact FirstOrder.Derives.theory_weaken
    (T := infinity_theory)
    (U := formal_language_encoding_theory)
    (by
      intro sentence hSentence
      exact infinity_theory_subset_formal_language_encoding_theory hSentence)
    (infinity_finite_numeral_mem_omega number)

theorem finite_numeral_mem_of_lt_formal_language_encoding_theory
    {free : SetContext} {Γ : Context signature free}
    {left right : Nat} (hLt : left < right) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      (numₘ(left) : SetOpenTerm free) ∈ₘ numₘ(right) := by
  exact FirstOrder.Derives.theory_weaken
    (T := successor_operator_theory)
    (U := formal_language_encoding_theory)
    successor_operator_theory_subset_formal_language_encoding_theory
    (finite_numeral_mem_of_lt hLt)

theorem successor_mem_omega_formal_language_encoding_theory
    {free : SetContext} {Γ : Context signature free}
    (number : SetOpenTerm free)
    (hNumber : Γ ⊢ₘ[formal_language_encoding_theory] number ∈ₘ ωₘ) :
    Γ ⊢ₘ[formal_language_encoding_theory] Sₘ(number) ∈ₘ ωₘ := by
  have hClosure := FirstOrder.Derives.theory_weaken
    (T := infinity_theory)
    (U := formal_language_encoding_theory)
    (by
      intro sentence hSentence
      exact infinity_theory_subset_formal_language_encoding_theory hSentence)
    (FirstOrder.Derives.conj_elim_right
      (infinity_omega_inductive_condition_derives
        (free := free) (Γ := Γ)))
  have hInstance := FirstOrder.Derives.forall_elim
    (term := number) hClosure
  simpa [infinity_condition] using!
    FirstOrder.Derives.imp_elim hInstance hNumber

theorem godel_pair_mem_formal_language_encoding_theory
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeft : Γ ⊢ₘ[formal_language_encoding_theory] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[formal_language_encoding_theory] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      godel_pairₘ(left, right) ∈ₘ ωₘ := by
  have hDefinition := FirstOrder.Derives.theory_weaken
    (T := godel_pairing_core_theory)
    (U := formal_language_encoding_theory)
    (by
      intro sentence hSentence
      exact godel_pairing_core_subset_formal_language_encoding_theory hSentence)
    (godel_pairing_definition_instance_derives
      (Γ := Γ) left right godel_pairₘ(left, right))
  have hIff := FirstOrder.Derives.imp_elim hDefinition
    (FirstOrder.Derives.conj_intro hLeft hRight)
  have hCondition := FirstOrder.Derives.iff_elim_left hIff
    (Metatheory.Derives.equality_refl godel_pairₘ(left, right))
  exact FirstOrder.Derives.conj_elim_left hCondition

theorem structural_raw_node_mem_formal_language_encoding_theory
    {free : SetContext} {Γ : Context signature free}
    (tag : StructuralCodeTag) (payload : SetOpenTerm free)
    (hPayload : Γ ⊢ₘ[formal_language_encoding_theory] payload ∈ₘ ωₘ) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      structural_raw_node_code_term tag payload ∈ₘ ωₘ := by
  have hTag := finite_numeral_mem_formal_language_encoding_theory
    (Γ := Γ) (structural_code_tag tag)
  have hPair := godel_pair_mem_formal_language_encoding_theory
    (Γ := Γ) (numₘ(structural_code_tag tag)) payload hTag hPayload
  exact successor_mem_omega_formal_language_encoding_theory
    (godel_pairₘ(numₘ(structural_code_tag tag), payload)) hPair

theorem structural_list_code_mem_formal_language_encoding_theory
    {free : SetContext} {Γ : Context signature free}
    (fields : List (SetOpenTerm free))
    (hFields : ∀ field, field ∈ fields →
      Γ ⊢ₘ[formal_language_encoding_theory] field ∈ₘ ωₘ) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      structural_list_code_term fields ∈ₘ ωₘ := by
  induction fields with
  | nil =>
      exact structural_raw_node_mem_formal_language_encoding_theory
        (Γ := Γ) .listNil ∅ₘ
        (finite_numeral_mem_formal_language_encoding_theory (Γ := Γ) 0)
  | cons head tail ih =>
      have hPair := godel_pair_mem_formal_language_encoding_theory
        (Γ := Γ) head (structural_list_code_term tail)
        (hFields head (by simp))
        (ih (by
          intro field hField
          exact hFields field (by simp [hField])))
      exact structural_raw_node_mem_formal_language_encoding_theory
        (Γ := Γ) .listCons (godel_pairₘ(head, structural_list_code_term tail)) hPair

theorem structural_node_code_mem_formal_language_encoding_theory
    {free : SetContext} {Γ : Context signature free}
    (tag : StructuralCodeTag) (fields : List (SetOpenTerm free))
    (hFields : ∀ field, field ∈ fields →
      Γ ⊢ₘ[formal_language_encoding_theory] field ∈ₘ ωₘ) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      structural_node_code_term tag fields ∈ₘ ωₘ :=
  structural_raw_node_mem_formal_language_encoding_theory tag
    (structural_list_code_term fields)
    (structural_list_code_mem_formal_language_encoding_theory fields hFields)

private theorem free_variable_code_condition_derives
    (index : Nat) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_free_variable_condition
        (free_var_codeₘ(numₘ(index)) : SetOpenTerm []) := by
  unfold term_code_free_variable_condition
  apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
  simpa using! FirstOrder.Derives.conj_intro
    (finite_numeral_mem_formal_language_encoding_theory (Γ := []) index)
    (Metatheory.Derives.equality_refl
      (free_var_codeₘ(numₘ(index)) : SetOpenTerm []))

private theorem term_code_at_of_free_variable_branch
    (depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_free_variable_condition code) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (term_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
  apply FirstOrder.Derives.conj_intro
  · exact FirstOrder.Derives.conj_intro hDepth hCode
  · apply FirstOrder.Derives.disj_intro_left
    exact hBranch

private theorem term_code_at_of_constant_branch
    (depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_constant_condition code) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (term_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
  apply FirstOrder.Derives.conj_intro
  · exact FirstOrder.Derives.conj_intro hDepth hCode
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    exact hBranch

private theorem constant_code_condition_derives
    (symbol : Nat) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_constant_condition
        (const_codeₘ(numₘ(symbol)) : SetOpenTerm []) := by
  unfold term_code_constant_condition
  apply FirstOrder.Derives.exists_intro (numₘ(symbol) : SetOpenTerm [])
  simpa using! FirstOrder.Derives.conj_intro
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) symbol)
    (Metatheory.Derives.equality_refl
      (const_codeₘ(numₘ(symbol)) : SetOpenTerm []))

private theorem bound_variable_code_condition_derives
    (depth index : Nat) (hIndex : index < depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_bound_variable_condition
        (numₘ(depth) : SetOpenTerm [])
        (bound_var_codeₘ(numₘ(index)) : SetOpenTerm []) := by
  unfold term_code_bound_variable_condition
  apply FirstOrder.Derives.exists_intro (numₘ(index) : SetOpenTerm [])
  simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    structural_list_code_term, structural_node_code_term,
    structural_raw_node_code_term, godel_pairing_term] using!
    FirstOrder.Derives.conj_intro
    (finite_numeral_mem_of_lt_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) hIndex)
    (Metatheory.Derives.equality_refl
      (bound_var_codeₘ(numₘ(index)) : SetOpenTerm []))

private theorem term_code_at_of_bound_variable_branch
    (depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_bound_variable_condition depth code) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (term_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
  apply FirstOrder.Derives.conj_intro
  · exact FirstOrder.Derives.conj_intro hDepth hCode
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    exact hBranch

private theorem term_code_at_of_application_branch
    (depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_application_condition depth code) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (term_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
  apply FirstOrder.Derives.conj_intro
  · exact FirstOrder.Derives.conj_intro hDepth hCode
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    exact hBranch

theorem term_code_at_code_mem_of_derives
    (depth code : SetOpenTerm [])
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, code)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (term_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
    hCode
  exact FirstOrder.Derives.conj_elim_right
    (FirstOrder.Derives.conj_elim_left hCondition)

theorem term_list_code_at_code_mem_of_derives
    (depth length code : SetOpenTerm [])
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_list_code_atₘ(depth, length, code)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (term_list_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth length code)
    hCode
  exact FirstOrder.Derives.conj_elim_right
    (FirstOrder.Derives.conj_elim_left hCondition)

private theorem term_list_code_cons_condition_intro
    (depth length code previousLength head tail : SetOpenTerm [])
    (hPreviousLength :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        previousLength ∈ₘ ωₘ)
    (hLength :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        length ≐ₘ Sₘ(previousLength))
    (hHead :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, head))
    (hTail :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_list_code_atₘ(depth, previousLength, tail))
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        code ≐ₘ code_consₘ(head, tail)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_list_code_cons_condition depth length code := by
  unfold term_list_code_cons_condition
  apply FirstOrder.Derives.existsFreePrefix_intro
    (.cons previousLength (.cons head (.cons tail .nil)))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_raw_node_code_term, godel_pairing_term, term_weaken_free_three] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hPreviousLength hLength)
      (FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hHead hTail) hCode)

private theorem term_code_application_condition_intro
    (depth code arity symbol arguments : SetOpenTerm [])
    (hArity :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        arity ∈ₘ ωₘ)
    (hSymbol :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        symbol ∈ₘ ωₘ)
    (hArguments :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_list_code_atₘ(depth, arity, arguments))
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        code ≐ₘ app_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_application_condition depth code := by
  unfold term_code_application_condition
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
      (FirstOrder.Derives.conj_intro hArguments hCode)

private theorem term_list_code_at_of_nil_branch
    (depth length code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      depth ∈ₘ ωₘ)
    (hLength : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      length ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ)
    (hLengthZero : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      length ≐ₘ numₘ(0))
    (hCodeNil : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ≐ₘ code_nilₘ) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_list_code_atₘ(depth, length, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (term_list_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth length code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · exact FirstOrder.Derives.conj_intro hDepth hLength
    · exact hCode
  · apply FirstOrder.Derives.disj_intro_left
    exact FirstOrder.Derives.conj_intro hLengthZero hCodeNil

private theorem term_list_code_at_of_cons_branch
    (depth length code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      depth ∈ₘ ωₘ)
    (hLength : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      length ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_list_code_cons_condition depth length code) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_list_code_atₘ(depth, length, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (term_list_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth length code)
  apply FirstOrder.Derives.conj_intro
  · apply FirstOrder.Derives.conj_intro
    · exact FirstOrder.Derives.conj_intro hDepth hLength
    · exact hCode
  · apply FirstOrder.Derives.disj_intro_right
    exact hBranch

theorem quote_free_variable_term_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (entry : Variable free sort) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(
        numₘ(bound.length),
        (quote_term
          (bound := bound) (free := free) (sort := sort)
          (Term.fvar entry) : SetOpenTerm [])) := by
  have hDepth := finite_numeral_mem_formal_language_encoding_theory
    (Γ := ([] : Context signature [])) bound.length
  have hCode := structural_node_code_mem_formal_language_encoding_theory
    (Γ := ([] : Context signature [])) StructuralCodeTag.freeVariable
    [numₘ(entry.index)] (by
      intro field hField
      simp only [List.mem_cons, List.not_mem_nil] at hField
      rcases hField with hField | hField
      · simpa [hField] using
          (finite_numeral_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature [])) entry.index)
      · contradiction)
  have hInstance := term_code_at_of_free_variable_branch
    (numₘ(bound.length))
    (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) bound.length)
    (structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) StructuralCodeTag.freeVariable
      [numₘ(entry.index)] (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) entry.index)
        · contradiction))
    (free_variable_code_condition_derives entry.index)
  simpa [quote_term] using hInstance

theorem quote_constant_term_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {function : σ.FuncSymbol}
    (hDomain : σ.funcDomain function = []) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(
        numₘ(bound.length),
        (quote_term
          (bound := bound) (free := free)
          (Term.app function (hDomain ▸ .nil)) : SetOpenTerm [])) := by
  have hCode := structural_node_code_mem_formal_language_encoding_theory
    (Γ := ([] : Context signature [])) StructuralCodeTag.constant
    [numₘ(QuotationNumbering.function_number function)] (by
      intro field hField
      simp only [List.mem_cons, List.not_mem_nil] at hField
      rcases hField with hField | hField
      · simpa [hField] using
          (finite_numeral_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (QuotationNumbering.function_number function))
      · contradiction)
  have hInstance := term_code_at_of_constant_branch
    (numₘ(bound.length))
    (const_codeₘ(numₘ(QuotationNumbering.function_number function)) : SetOpenTerm [])
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) bound.length)
    hCode
    (constant_code_condition_derives
      (QuotationNumbering.function_number function))
  simpa [quote_term, hDomain] using hInstance

theorem quote_bound_variable_term_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (entry : Variable bound sort) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(
        numₘ(bound.length),
        (quote_term
          (bound := bound) (free := free) (sort := sort)
          (Term.bvar entry) : SetOpenTerm [])) := by
  have hIndex : entry.index < bound.length := entry.index_lt_length
  have hCode := structural_node_code_mem_formal_language_encoding_theory
    (Γ := ([] : Context signature [])) StructuralCodeTag.boundVariable
    [numₘ(entry.index)] (by
      intro field hField
      simp only [List.mem_cons, List.not_mem_nil] at hField
      rcases hField with hField | hField
      · simpa [hField] using
          (finite_numeral_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature [])) entry.index)
      · contradiction)
  have hInstance := term_code_at_of_bound_variable_branch
    (numₘ(bound.length))
    (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) bound.length)
    hCode
    (bound_variable_code_condition_derives
      bound.length entry.index hIndex)
  simpa [quote_term] using hInstance

/-! ## 项与参数列的递归正确性 -/

mutual

/-- 类型化项在不小于其 bound 上下文长度的任意外部深度下都满足项码递归谓词。 -/
theorem quote_term_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(
        numₘ(depth),
        (quote_term term : SetOpenTerm [])) := by
  match term with
  | .bvar entry =>
      have hIndex : entry.index < depth :=
        Nat.lt_of_lt_of_le entry.index_lt_length hBound
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hCode := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.boundVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hInstance := term_code_at_of_bound_variable_branch
        (numₘ(depth))
        (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hDepth hCode
        (bound_variable_code_condition_derives depth entry.index hIndex)
      simpa [quote_term] using hInstance
  | .fvar entry =>
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hCode := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.freeVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hInstance := term_code_at_of_free_variable_branch
        (numₘ(depth))
        (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hDepth hCode
        (free_variable_code_condition_derives entry.index)
      simpa [quote_term] using hInstance
  | .app function arguments =>
      have ih := quote_arguments_term_list_code_at_of_depth arguments
      cases hDomain : σ.funcDomain function with
      | nil =>
          have hCode := structural_node_code_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature [])) StructuralCodeTag.constant
            [numₘ(QuotationNumbering.function_number function)] (by
              intro field hField
              simp only [List.mem_cons, List.not_mem_nil] at hField
              rcases hField with hField | hField
              · simpa [hField] using
                  (finite_numeral_mem_formal_language_encoding_theory
                    (Γ := ([] : Context signature []))
                    (QuotationNumbering.function_number function))
              · contradiction)
          have hInstance := term_code_at_of_constant_branch
            (numₘ(depth))
            (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
              SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) depth)
            hCode
            (constant_code_condition_derives
              (QuotationNumbering.function_number function))
          simpa [quote_term, hDomain] using hInstance
      | cons head tail =>
          have hArguments :
              ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
                term_list_code_atₘ(
                  numₘ(depth),
                  numₘ(σ.funcArity function),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [Signature.funcArity, hDomain] using ih depth hBound
          have hArgumentsCode := term_list_code_at_code_mem_of_derives
            (numₘ(depth))
            (numₘ(σ.funcArity function))
            (quote_arguments arguments : SetOpenTerm [])
            hArguments
          have hCode :
              ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
                app_codeₘ(
                  numₘ(σ.funcArity function),
                  numₘ(QuotationNumbering.function_number function),
                  (quote_arguments arguments : SetOpenTerm [])) ∈ₘ ωₘ := by
            simpa [structural_node_code_term, structural_list_code_term] using!
              (structural_node_code_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) StructuralCodeTag.application
                [numₘ(σ.funcArity function),
                  numₘ(QuotationNumbering.function_number function),
                  (quote_arguments arguments : SetOpenTerm [])] (by
                    intro field hField
                    simp only [List.mem_cons, List.not_mem_nil] at hField
                    rcases hField with hField | hField
                    · simpa [hField] using
                        (finite_numeral_mem_formal_language_encoding_theory
                          (Γ := ([] : Context signature []))
                          (σ.funcArity function))
                    · rcases hField with hField | hField
                      · simpa [hField] using
                          (finite_numeral_mem_formal_language_encoding_theory
                            (Γ := ([] : Context signature []))
                            (QuotationNumbering.function_number function))
                      · rcases hField with hField | hField
                        · simpa [hField] using hArgumentsCode
                        · contradiction))
          have hInstance := term_code_at_of_application_branch
            (numₘ(depth))
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) :
              SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) depth)
            hCode
            (term_code_application_condition_intro
              (numₘ(depth))
              (app_codeₘ(
                numₘ(σ.funcArity function),
                numₘ(QuotationNumbering.function_number function),
                (quote_arguments arguments : SetOpenTerm [])) :
                SetOpenTerm [])
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function))
              (quote_arguments arguments : SetOpenTerm [])
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) (σ.funcArity function))
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature []))
                (QuotationNumbering.function_number function))
              hArguments
              (Metatheory.Derives.equality_refl
                (app_codeₘ(
                  numₘ(σ.funcArity function),
                  numₘ(QuotationNumbering.function_number function),
                  (quote_arguments arguments : SetOpenTerm [])) :
                  SetOpenTerm [])))
          simpa [quote_term, hDomain] using hInstance

/-- 当前深度的识别直接复用任意合法深度定理。 -/
theorem quote_term_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(
        numₘ(bound.length),
        (quote_term term : SetOpenTerm [])) := by
  exact quote_term_code_at_of_depth term bound.length (Nat.le_refl _)

theorem quote_arguments_term_list_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_list_code_atₘ(
        numₘ(depth),
        numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
  match arguments with
  | .nil =>
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hLength := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) 0
      have hCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (code_nilₘ : SetOpenTerm []) ∈ₘ ωₘ := by
        exact structural_raw_node_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.listNil ∅ₘ
          (finite_numeral_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature [])) 0)
      simpa [quote_arguments] using
        (term_list_code_at_of_nil_branch
          (numₘ(depth)) (numₘ(0)) (code_nilₘ : SetOpenTerm [])
          hDepth hLength hCode
          (Metatheory.Derives.equality_refl (numₘ(0) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl (code_nilₘ : SetOpenTerm [])))
  | @Arguments.cons _ _ _ sort sorts head tail =>
      have ihTail := quote_arguments_term_list_code_at_of_depth tail
      have ihHead := quote_term_code_at_of_depth head
      have hDepth := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) depth
      have hPreviousLength := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) sorts.length
      have hLengthMem := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) (sort :: sorts).length
      have hLength :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            numₘ((sort :: sorts).length) ≐ₘ Sₘ(numₘ(sorts.length)) := by
        simpa [finite_numeral_term] using
          (Metatheory.Derives.equality_refl
            (Sₘ(numₘ(sorts.length)) : SetOpenTerm []))
      have hHead := ihHead depth hBound
      have hTail := ihTail depth hBound
      have hHeadCode := term_code_at_code_mem_of_derives
        (numₘ(depth))
        (quote_term head : SetOpenTerm []) hHead
      have hTailCode := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm []) hTail
      have hCode :
          ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
            (code_consₘ(
              (quote_term head : SetOpenTerm []),
              (quote_arguments tail : SetOpenTerm [])) :
              SetOpenTerm []) ∈ₘ ωₘ := by
        exact structural_raw_node_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
          (godel_pairₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])))
          (godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (quote_term head : SetOpenTerm [])
            (quote_arguments tail : SetOpenTerm [])
            hHeadCode hTailCode)
      have hBranch := term_list_code_cons_condition_intro
        (numₘ(depth))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(sorts.length))
        (quote_term head : SetOpenTerm [])
        (quote_arguments tail : SetOpenTerm [])
        hPreviousLength hLength hHead hTail
        (Metatheory.Derives.equality_refl
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := term_list_code_at_of_cons_branch
        (numₘ(depth))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hLengthMem hCode hBranch
      simpa [quote_arguments] using hResult

end

theorem quote_arguments_term_list_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_list_code_atₘ(
        numₘ(bound.length),
        numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
  exact quote_arguments_term_list_code_at_of_depth arguments bound.length (Nat.le_refl _)

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
