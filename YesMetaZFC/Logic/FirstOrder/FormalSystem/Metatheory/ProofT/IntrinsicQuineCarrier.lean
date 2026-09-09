import YesMetaZFC.Logic.FirstOrder.Derivation.QuantifierBlock
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# Quine 结构码的相关语法承载

本模块把宿主内在语法的 Quine quotation 接入相关项、参数列和公式承载集合。
所有见证都来自 `Term`、`Arguments` 与 `Formula` 的结构递归；承载理论只负责
提供相关语法递归方程及 `NonlogicalSym = ω` 的对象侧合同。
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

private theorem formal_to_carrier
    {free : SetContext} {Γ : Context signature free}
    {φ : SetOpenFormula free}
    (hφ : Γ ⊢ₘ[formal_language_encoding_theory] φ) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory] φ :=
  FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory hφ

private theorem omega_mem_carrier
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  formal_to_carrier
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)

private theorem nonlogical_symbol_mem_of_omega
    (code : SetOpenTerm [])
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ NonlogicalSymₘ := by
  have hEquality :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        NonlogicalSymₘ ≐ₘ ωₘ := by
    exact FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (by simpa using!
        related_symbol_definition_axiom_derives)
  exact FirstOrder.Derives.iff_elim_right
    (membership_right_iff_of_equality
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      code NonlogicalSymₘ ωₘ hEquality)
    (formal_to_carrier hCode)

private theorem related_term_code_free_condition_intro
    (index code : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      index ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ free_var_codeₘ(index)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_free_condition code := by
  unfold related_term_code_free_condition
  apply FirstOrder.Derives.exists_intro index
  simpa using! FirstOrder.Derives.conj_intro hIndex hCode

private theorem related_term_code_bound_condition_intro
    (depth index code : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      index ∈ₘ depth)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ bound_var_codeₘ(index)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_bound_condition depth code := by
  unfold related_term_code_bound_condition
  apply FirstOrder.Derives.exists_intro index
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_instantiateFreeTop,
    Arguments.substituteMapped_weakenFree_instantiateFreeTop] using
    FirstOrder.Derives.conj_intro hIndex hCode

private theorem related_term_code_constant_condition_intro
    (symbols index code : SetOpenTerm [])
    (hIndex : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      constant_interpretation_key_term index ∈ₘ symbols)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ const_codeₘ(index)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_constant_condition symbols code := by
  unfold related_term_code_constant_condition
  apply FirstOrder.Derives.exists_intro index
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_instantiateFreeTop,
    Arguments.substituteMapped_weakenFree_instantiateFreeTop,
    constant_interpretation_key_term] using
    FirstOrder.Derives.conj_intro hIndex hCode

private theorem related_term_code_at_of_condition
    (symbols depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_free_condition code ∨ₘ
        (related_term_code_bound_condition depth code ∨ₘ
          (related_term_code_constant_condition symbols code ∨ₘ
            related_term_code_application_condition symbols depth code))) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_term_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth code))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hDepth hCode) hBranch

private theorem related_term_list_code_at_of_condition
    (symbols depth length code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLength : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      length ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      (length ≐ₘ numₘ(0)) ∧ₘ (code ≐ₘ code_nilₘ) ∨ₘ
        related_term_list_code_cons_condition symbols depth length code) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, length, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_term_list_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth length code))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hDepth hLength) hCode) hBranch

private theorem related_term_list_code_cons_condition_intro
    (symbols depth length code previousLength head tail : SetOpenTerm [])
    (hPreviousLength : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      previousLength ∈ₘ ωₘ)
    (hLength : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      length ≐ₘ Sₘ(previousLength))
    (hHead : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, head))
    (hTail : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, previousLength, tail))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ code_consₘ(head, tail)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_cons_condition symbols depth length code := by
  unfold related_term_list_code_cons_condition
  apply FirstOrder.Derives.existsFreePrefix_intro (.cons previousLength (.cons head (.cons tail .nil)))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term,
    term_weaken_free_three] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hPreviousLength hLength)
      (FirstOrder.Derives.conj_intro (FirstOrder.Derives.conj_intro hHead hTail) hCode)

private theorem related_term_code_application_condition_intro
    (symbols depth code arity symbol arguments : SetOpenTerm [])
    (hArity : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      arity ∈ₘ ωₘ)
    (hKey : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      function_interpretation_key_term arity symbol ∈ₘ symbols)
    (hArguments : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, arity, arguments))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ app_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_application_condition symbols depth code := by
  unfold related_term_code_application_condition
  apply FirstOrder.Derives.existsFreePrefix_intro (.cons arguments (.cons symbol (.cons arity .nil)))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term,
    term_weaken_free_three, function_interpretation_key_term, application_code_term] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hArity hKey)
      (FirstOrder.Derives.conj_intro hArguments hCode)

mutual

theorem related_quote_term_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote_term term : SetOpenTerm [])) := by
  match term with
  | .bvar entry =>
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.boundVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hCode := formal_to_carrier hCodeFormal
      have hIndex := formal_to_carrier
        (finite_numeral_mem_of_lt_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (Nat.lt_of_lt_of_le entry.index_lt_length hBound))
      have hBranch := related_term_code_bound_condition_intro
        (numₘ(depth))
        (numₘ(entry.index))
        (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hIndex
        (Metatheory.Derives.equality_refl
          (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm []))
      have hResult := related_term_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (bound_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        hDepth hCode
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))
      simpa [quote_term] using hResult
  | .fvar entry =>
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.freeVariable
        [numₘ(entry.index)] (by
          intro field hField
          simp only [List.mem_cons, List.not_mem_nil] at hField
          rcases hField with hField | hField
          · simpa [hField] using
              (finite_numeral_mem_formal_language_encoding_theory
                (Γ := ([] : Context signature [])) entry.index)
          · contradiction)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_code_free_condition_intro
        (numₘ(entry.index))
        (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        (omega_mem_carrier entry.index)
        (Metatheory.Derives.equality_refl
          (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm []))
      have hResult := related_term_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (free_var_codeₘ(numₘ(entry.index)) : SetOpenTerm [])
        (omega_mem_carrier depth) hCode
        (FirstOrder.Derives.disj_intro_left hBranch)
      simpa [quote_term] using hResult
  | .app function arguments =>
      have ih := related_quote_arguments_term_list_code_at_of_depth arguments
      cases hDomain : σ.funcDomain function with
      | nil =>
          have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
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
          have hCode := formal_to_carrier hCodeFormal
          have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm [])
            (numₘ(QuotationNumbering.function_number function) : SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) 0)
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature []))
              (QuotationNumbering.function_number function))
          have hKey := nonlogical_symbol_mem_of_omega
            (godel_pairₘ(
              numₘ(0),
              numₘ(QuotationNumbering.function_number function)) : SetOpenTerm [])
            hKeyOmega
          have hBranch := related_term_code_constant_condition_intro
            NonlogicalSymₘ
            (numₘ(QuotationNumbering.function_number function))
            (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
              SetOpenTerm [])
            hKey
            (Metatheory.Derives.equality_refl
              (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
                SetOpenTerm []))
          have hResult := related_term_code_at_of_condition
            NonlogicalSymₘ
            (numₘ(depth))
            (const_codeₘ(numₘ(QuotationNumbering.function_number function)) :
              SetOpenTerm [])
            (omega_mem_carrier depth) hCode
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_left hBranch)))
          simpa [quote_term, hDomain] using hResult
      | cons head tail =>
          have hArguments :
              ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
                related_term_list_code_atₘ(
                  NonlogicalSymₘ,
                  numₘ(depth),
                  numₘ(σ.funcArity function),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [Signature.funcArity, hDomain] using ih depth hBound
          have hArgumentsDirect :
              ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
                term_list_code_atₘ(
                  numₘ(depth),
                  numₘ(σ.funcArity function),
                  (quote_arguments arguments : SetOpenTerm [])) := by
            simpa [Signature.funcArity, hDomain] using
              (quote_arguments_term_list_code_at_of_depth
                (σ := σ) (bound := bound) (free := free) arguments depth hBound)
          have hArgumentsCode := term_list_code_at_code_mem_of_derives
            (numₘ(depth))
            (numₘ(σ.funcArity function))
            (quote_arguments arguments : SetOpenTerm [])
            hArgumentsDirect
          have hKeyInner := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(σ.funcArity function) : SetOpenTerm [])
            (numₘ(QuotationNumbering.function_number function) : SetOpenTerm [])
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) (σ.funcArity function))
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature []))
              (QuotationNumbering.function_number function))
          have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
            (Γ := ([] : Context signature []))
            (numₘ(1) : SetOpenTerm [])
            (godel_pairₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function)))
            (finite_numeral_mem_formal_language_encoding_theory
              (Γ := ([] : Context signature [])) 1)
            hKeyInner
          have hKey := nonlogical_symbol_mem_of_omega
            (function_interpretation_key_term
              (numₘ(σ.funcArity function))
              (numₘ(QuotationNumbering.function_number function)))
            (by simpa [function_interpretation_key_term] using hKeyOmega)
          have hCodeFormal := structural_node_code_mem_formal_language_encoding_theory
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
                    · contradiction)
          have hCode := formal_to_carrier hCodeFormal
          have hBranch := related_term_code_application_condition_intro
            NonlogicalSymₘ
            (numₘ(depth))
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
            (numₘ(σ.funcArity function))
            (numₘ(QuotationNumbering.function_number function))
            (quote_arguments arguments : SetOpenTerm [])
            (omega_mem_carrier (σ.funcArity function))
            hKey hArguments
            (Metatheory.Derives.equality_refl
              (app_codeₘ(
                numₘ(σ.funcArity function),
                numₘ(QuotationNumbering.function_number function),
                (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm []))
          have hResult := related_term_code_at_of_condition
            NonlogicalSymₘ
            (numₘ(depth))
            (app_codeₘ(
              numₘ(σ.funcArity function),
              numₘ(QuotationNumbering.function_number function),
              (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
            (omega_mem_carrier depth) hCode
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.disj_intro_right hBranch)))
          simpa [quote_term, hDomain] using hResult

theorem related_quote_term_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        (quote_term term : SetOpenTerm [])) := by
  exact related_quote_term_code_at_of_depth term bound.length (Nat.le_refl _)

theorem related_quote_arguments_term_list_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
  match arguments with
  | .nil =>
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) 0
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listNil ∅ₘ
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 0)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            ((numₘ(0) ≐ₘ numₘ(0)) ∧ₘ
              (code_nilₘ ≐ₘ code_nilₘ)) ∨ₘ
              related_term_list_code_cons_condition
                NonlogicalSymₘ (numₘ(depth)) (numₘ(0))
                (code_nilₘ : SetOpenTerm []) := by
        apply FirstOrder.Derives.disj_intro_left
        exact FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (numₘ(0) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (code_nilₘ : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ(0))
        (code_nilₘ : SetOpenTerm [])
        hDepth hLength hCode hBranch
      simpa [quote_arguments] using hResult
  | @Arguments.cons _ _ _ sort sorts head tail =>
      have ihTail := related_quote_arguments_term_list_code_at_of_depth tail
      have ihHead := related_quote_term_code_at_of_depth head
      have hDepth := omega_mem_carrier
        (Γ := ([] : Context signature [])) depth
      have hPreviousLength := omega_mem_carrier
        (Γ := ([] : Context signature [])) sorts.length
      have hLengthMem := omega_mem_carrier
        (Γ := ([] : Context signature [])) (sort :: sorts).length
      have hLength :
          ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
            numₘ((sort :: sorts).length) ≐ₘ Sₘ(numₘ(sorts.length)) := by
        simpa [finite_numeral_term] using
          (Metatheory.Derives.equality_refl
            (T := intrinsic_syntax_carrier_theory)
            (Γ := ([] : Context signature []))
            (Sₘ(numₘ(sorts.length)) : SetOpenTerm []))
      have hHead := ihHead depth hBound
      have hTail := ihTail depth hBound
      have hHeadDirect := quote_term_code_at_of_depth
        (σ := σ) (bound := bound) (free := free) head depth hBound
      have hHeadCode := term_code_at_code_mem_of_derives
        (numₘ(depth))
        (quote_term head : SetOpenTerm [])
        hHeadDirect
      have hTailDirect := quote_arguments_term_list_code_at_of_depth
        (σ := σ) (bound := bound) (free := free) tail depth hBound
      have hTailCode := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(sorts.length))
        (quote_arguments tail : SetOpenTerm [])
        hTailDirect
      have hCodeFormal := structural_raw_node_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) StructuralCodeTag.listCons
        (godel_pairₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])))
        (godel_pair_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (quote_term head : SetOpenTerm [])
          (quote_arguments tail : SetOpenTerm [])
          hHeadCode hTailCode)
      have hCode := formal_to_carrier hCodeFormal
      have hBranch := related_term_list_code_cons_condition_intro
        NonlogicalSymₘ
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
          (T := intrinsic_syntax_carrier_theory)
          (Γ := ([] : Context signature []))
          (code_consₘ(
            (quote_term head : SetOpenTerm []),
            (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := related_term_list_code_at_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (numₘ((sort :: sorts).length))
        (code_consₘ(
          (quote_term head : SetOpenTerm []),
          (quote_arguments tail : SetOpenTerm [])) : SetOpenTerm [])
        hDepth hLengthMem hCode
        (FirstOrder.Derives.disj_intro_right hBranch)
      simpa [quote_arguments] using hResult

end

theorem related_quote_arguments_term_list_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) := by
  exact related_quote_arguments_term_list_code_at_of_depth arguments bound.length (Nat.le_refl _)

theorem related_formula_negation_condition_intro
    (symbols depth code body : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, body))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ neg_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_negation_condition symbols depth code := by
  unfold related_formula_negation_condition
  apply FirstOrder.Derives.existsFreePrefix_intro (.cons body .nil)
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term,
    negation_formula_code_term] using
    FirstOrder.Derives.conj_intro hBody hCode

theorem related_formula_term_binary_condition_intro
    (symbols depth code : SetOpenTerm [])
    (tag : StructuralCodeTag)
    (left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(symbols, depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ structural_node_code_term tag [left, right]) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_binary_condition symbols depth code tag := by
  unfold related_formula_binary_condition
  apply FirstOrder.Derives.existsFreePrefix_intro (.cons right (.cons left .nil))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term,
    term_weaken_free_two] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hLeft hRight) hCode

theorem related_formula_implication_condition_intro
    (symbols depth code left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ imp_codeₘ(left, right)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_implication_condition symbols depth code := by
  unfold related_formula_implication_condition
  apply FirstOrder.Derives.existsFreePrefix_intro (.cons right (.cons left .nil))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term,
    term_weaken_free_two, implication_formula_code_term] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hLeft hRight) hCode

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
