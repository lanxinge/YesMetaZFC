import YesMetaZFC.Logic.FirstOrder.Derivation.QuantifierBlock
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineCarrier

/-!
# Quine 公式码的相关语法承载

本模块只负责公式节点的相关承载构造；项与参数列的宿主递归接口由
`IntrinsicQuineCarrier` 提供。
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

private theorem ifc_formal_to_carrier
    {free : SetContext} {Γ : Context signature free}
    {φ : SetOpenFormula free}
    (hφ : Γ ⊢ₘ[formal_language_encoding_theory] φ) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory] φ :=
  FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory hφ

private theorem ifc_omega_mem
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[intrinsic_syntax_carrier_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  ifc_formal_to_carrier
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)

private theorem ifc_nonlogical_symbol_mem_of_omega
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
      (by simpa using! related_symbol_definition_axiom_derives)
  exact FirstOrder.Derives.iff_elim_right
    (membership_right_iff_of_equality
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      code NonlogicalSymₘ ωₘ hEquality)
    (ifc_formal_to_carrier hCode)

private theorem ifc_related_formula_of_condition
    (symbols depth code : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ ωₘ)
    (hBranch : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_binary_condition symbols depth code .equality ∨ₘ
        (related_formula_binary_condition symbols depth code .membership ∨ₘ
          (related_formula_predicate_condition symbols depth code ∨ₘ
            (related_formula_negation_condition symbols depth code ∨ₘ
              (related_formula_implication_condition symbols depth code ∨ₘ
                related_formula_universal_condition symbols depth code))))) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.theory_weaken
      semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
      (related_formula_code_at_definition_instance_derives
        (Γ := ([] : Context signature [])) symbols depth code))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hDepth hCode) hBranch

private theorem ifc_related_formula_predicate_condition_intro
    (symbols depth code arity symbol arguments : SetOpenTerm [])
    (hArity : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      arity ∈ₘ ωₘ)
    (hKey : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      predicate_interpretation_key_term arity symbol ∈ₘ symbols)
    (hArguments : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_list_code_atₘ(symbols, depth, arity, arguments))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ pred_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_predicate_condition symbols depth code := by
  unfold related_formula_predicate_condition
  apply FirstOrder.Derives.existsFreePrefix_intro (.cons arguments (.cons symbol (.cons arity .nil)))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term,
    term_weaken_free_three, predicate_interpretation_key_term, predicate_formula_code_term] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hArity hKey)
      (FirstOrder.Derives.conj_intro hArguments hCode)

private theorem ifc_related_formula_universal_condition_intro
    (symbols depth code body : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(symbols, Sₘ(depth), body))
    (hCode : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ≐ₘ all_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_universal_condition symbols depth code := by
  unfold related_formula_universal_condition
  apply FirstOrder.Derives.existsFreePrefix_intro (.cons body .nil)
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term,
    universal_formula_code_term] using
    FirstOrder.Derives.conj_intro hBody hCode

private theorem ifc_structural_node_code_mem
    (tag : StructuralCodeTag) (fields : List (SetOpenTerm []))
    (hFields : ∀ field ∈ fields,
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        field ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      structural_node_code_term tag fields ∈ₘ ωₘ :=
  ifc_formal_to_carrier
    (structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) tag fields hFields)

private theorem ifc_quote_term_code_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      (quote_term term : SetOpenTerm []) ∈ₘ ωₘ :=
  term_code_at_code_mem_of_derives
    (numₘ(bound.length))
    (quote_term term : SetOpenTerm [])
    (quote_term_code_at term)

private theorem ifc_quote_formula_code_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      (quote_hilbert formula : SetOpenTerm []) ∈ₘ ωₘ :=
  formula_code_at_code_mem_of_derives
    (numₘ(bound.length))
    (quote_hilbert formula : SetOpenTerm [])
    (quote_hilbert_formula_code_at formula)

private theorem ifc_related_formula_equality
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth,
        structural_node_code_term .equality [left, right]) := by
  have hCode := ifc_structural_node_code_mem .equality [left, right] (by
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil] at hField
    rcases hField with hField | hField
    · simpa [hField] using hLeftCode
    · rcases hField with hField | hField
      · simpa [hField] using hRightCode
      · contradiction)
  have hBranch := related_formula_term_binary_condition_intro
    NonlogicalSymₘ depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm [])
    .equality left right hLeft hRight
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (structural_node_code_term .equality [left, right] : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm [])
    hDepth
    (by simpa using hCode)
    (FirstOrder.Derives.disj_intro_left hBranch)

theorem related_formula_equality_code_at_intro
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_term_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth,
        structural_node_code_term .equality [left, right]) :=
  ifc_related_formula_equality depth left right hDepth hLeft hRight
    hLeftCode hRightCode

private theorem ifc_related_formula_negation
    (depth body : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, body))
    (hBodyCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      body ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth, neg_codeₘ(body)) := by
  have hCode := ifc_structural_node_code_mem StructuralCodeTag.negation [body] (by
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil] at hField
    rcases hField with hField | hField
    · simpa [hField] using hBodyCode
    · contradiction)
  have hBranch := related_formula_negation_condition_intro
    NonlogicalSymₘ depth (neg_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (neg_codeₘ(body) : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth (neg_codeₘ(body) : SetOpenTerm []) hDepth
    (by simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))))

private theorem ifc_related_formula_implication
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth, imp_codeₘ(left, right)) := by
  have hCode := ifc_structural_node_code_mem StructuralCodeTag.implication
    [left, right] (by
      intro field hField
      simp only [List.mem_cons, List.not_mem_nil] at hField
      rcases hField with hField | hField
      · simpa [hField] using hLeftCode
      · rcases hField with hField | hField
        · simpa [hField] using hRightCode
        · contradiction)
  have hBranch := related_formula_implication_condition_intro
    NonlogicalSymₘ depth (imp_codeₘ(left, right) : SetOpenTerm []) left right
    hLeft hRight
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (imp_codeₘ(left, right) : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth (imp_codeₘ(left, right) : SetOpenTerm []) hDepth
    (by simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))))

private theorem ifc_related_formula_universal
    (depth body : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, Sₘ(depth), body))
    (hBodyCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      body ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ, depth, all_codeₘ(body)) := by
  have hCode := ifc_structural_node_code_mem StructuralCodeTag.universal [body] (by
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil] at hField
    rcases hField with hField | hField
    · simpa [hField] using hBodyCode
    · contradiction)
  have hBranch := ifc_related_formula_universal_condition_intro
    NonlogicalSymₘ depth (all_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (T := intrinsic_syntax_carrier_theory)
      (Γ := ([] : Context signature []))
      (all_codeₘ(body) : SetOpenTerm []))
  exact ifc_related_formula_of_condition
    NonlogicalSymₘ depth (all_codeₘ(body) : SetOpenTerm []) hDepth
    (by simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right hBranch)))))

theorem related_formula_implication_code_at_intro
    (depth left right : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hLeft : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, right))
    (hLeftCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      left ∈ₘ ωₘ)
    (hRightCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      right ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, imp_codeₘ(left, right)) :=
  ifc_related_formula_implication depth left right hDepth hLeft hRight
    hLeftCode hRightCode

theorem related_formula_universal_code_at_intro
    (depth body : SetOpenTerm [])
    (hDepth : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      depth ∈ₘ ωₘ)
    (hBody : ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, Sₘ(depth), body))
    (hBodyCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      body ∈ₘ ωₘ) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(NonlogicalSymₘ, depth, all_codeₘ(body)) :=
  ifc_related_formula_universal depth body hDepth hBody hBodyCode

theorem related_quote_relation_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote_relation relation arguments : SetOpenTerm [])) := by
  have hDepth := ifc_omega_mem
    (Γ := ([] : Context signature [])) depth
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
                  have hLeft := related_quote_term_code_at_of_depth left depth hBound
                  have hRight := related_quote_term_code_at_of_depth right depth hBound
                  have hLeftFormal := quote_term_code_at_of_depth left depth hBound
                  have hRightFormal := quote_term_code_at_of_depth right depth hBound
                  have hLeftCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term left : SetOpenTerm []) hLeftFormal
                  have hRightCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term right : SetOpenTerm []) hRightFormal
                  have hCodeFormal :=
                    structural_node_code_mem_formal_language_encoding_theory
                      (Γ := ([] : Context signature []))
                      StructuralCodeTag.membership
                      [(quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])] (by
                        intro field hField
                        simp only [List.mem_cons, List.not_mem_nil] at hField
                        rcases hField with hField | hField
                        · simpa [hField] using hLeftCode
                        · rcases hField with hField | hField
                          · simpa [hField] using hRightCode
                          · contradiction)
                  have hCode := ifc_formal_to_carrier hCodeFormal
                  have hBranch := related_formula_term_binary_condition_intro
                    NonlogicalSymₘ
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
                    StructuralCodeTag.membership
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    hLeft hRight
                    (Metatheory.Derives.equality_refl
                      (mem_codeₘ(
                        (quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])) :
                        SetOpenTerm []))
                  have hResult := ifc_related_formula_of_condition
                    NonlogicalSymₘ
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) : SetOpenTerm [])
                    hDepth
                    (by
                      simpa [structural_node_code_term,
                        structural_list_code_term] using! hCode)
                    (FirstOrder.Derives.disj_intro_right
                      (FirstOrder.Derives.disj_intro_left hBranch))
                  have hQuote :
                      quote_relation relation arguments =
                        mem_codeₘ(
                          (quote_term left : SetOpenTerm []),
                          (quote_term right : SetOpenTerm [])) := by
                    rw [quote_relation_membership_eq relation arguments hKind]
                    apply quote_membership_arguments_cons_eq
                      relation arguments hKind left right
                    exact hTypedArguments
                  rw [hQuote]
                  exact hResult
  | predicate =>
      have hArguments := related_quote_arguments_term_list_code_at_of_depth arguments depth hBound
      have hArgumentsDirect := quote_arguments_term_list_code_at_of_depth arguments depth hBound
      have hArity := ifc_omega_mem (Γ := ([] : Context signature []))
        (σ.relArity relation)
      have hArgumentsCode := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(σ.relArity relation))
        (quote_arguments arguments : SetOpenTerm [])
        (by simpa [Signature.relArity] using hArgumentsDirect)
      have hArityFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) (σ.relArity relation)
      have hSymbolFormal := finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation)
      have hKeyInner := godel_pair_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
        (numₘ(σ.relArity relation) : SetOpenTerm [])
        (numₘ(QuotationNumbering.relation_number relation) : SetOpenTerm [])
        hArityFormal hSymbolFormal
      have hKeyOmega := godel_pair_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature []))
        (numₘ(2) : SetOpenTerm [])
        (godel_pairₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation)))
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 2)
        hKeyInner
      have hKey := ifc_nonlogical_symbol_mem_of_omega
        (predicate_interpretation_key_term
          (numₘ(σ.relArity relation))
          (numₘ(QuotationNumbering.relation_number relation)))
        (by simpa [predicate_interpretation_key_term] using hKeyOmega)
      have hCodeFormal :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.predicate
          [numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using hArityFormal
            · rcases hField with hField | hField
              · simpa [hField] using hSymbolFormal
              · rcases hField with hField | hField
                · simpa [hField] using hArgumentsCode
                · contradiction)
      have hCode := ifc_formal_to_carrier hCodeFormal
      have hBranch := ifc_related_formula_predicate_condition_intro
        NonlogicalSymₘ
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        hArity hKey hArguments
        (Metatheory.Derives.equality_refl
          (pred_codeₘ(
            numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm []))
      have hResult := ifc_related_formula_of_condition
        NonlogicalSymₘ
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) : SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using!
            hCode)
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))
      rw [quote_relation_predicate_eq relation arguments hKind]
      exact hResult
theorem related_quote_hilbert_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote_hilbert formula : SetOpenTerm [])) := by
  let natural (code : SetOpenTerm []) :=
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory] code ∈ₘ ωₘ
  have unary (tag : StructuralCodeTag) (body : SetOpenTerm []) (hBody : natural body) :
      natural (structural_node_code_term tag [body]) :=
    structural_node_code_mem_formal_language_encoding_theory tag [body] (by
      intro field hField
      rcases List.mem_singleton.mp hField with rfl
      exact hBody)
  have binary (tag : StructuralCodeTag) (left right : SetOpenTerm [])
      (hLeft : natural left) (hRight : natural right) :
      natural (structural_node_code_term tag [left, right]) :=
    structural_node_code_mem_formal_language_encoding_theory tag [left, right] (by
      intro field hField
      rcases List.mem_cons.mp hField with rfl | hField
      · exact hLeft
      · rcases List.mem_singleton.mp hField with rfl
        exact hRight)
  let closure : _root_.YesMetaZFC.Automation.QuotationInduction.FormulaClosure σ
      (fun depth code => natural code ∧
        ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
          related_formula_code_atₘ(NonlogicalSymₘ, numₘ(depth), code)) := {
    relation := fun relation arguments depth hBound =>
      ⟨ifc_quote_formula_code_mem (.rel relation arguments),
        related_quote_relation_formula_code_at_of_depth relation arguments depth hBound⟩
    equality := fun left right depth hBound =>
      ⟨ifc_quote_formula_code_mem (.equal left right),
        ifc_related_formula_equality (numₘ(depth)) (quote_term left) (quote_term right)
          (ifc_omega_mem depth)
          (related_quote_term_code_at_of_depth left depth hBound)
          (related_quote_term_code_at_of_depth right depth hBound)
          (ifc_quote_term_code_mem left) (ifc_quote_term_code_mem right)⟩
    negation := fun depth body hBody =>
      ⟨unary .negation body hBody.1,
        ifc_related_formula_negation (numₘ(depth)) body (ifc_omega_mem depth) hBody.2 hBody.1⟩
    implication := fun depth left right hLeft hRight =>
      ⟨binary .implication left right hLeft.1 hRight.1,
        ifc_related_formula_implication (numₘ(depth)) left right (ifc_omega_mem depth)
          hLeft.2 hRight.2 hLeft.1 hRight.1⟩
    universal := fun depth body hBody =>
      ⟨unary .universal body hBody.1,
        ifc_related_formula_universal (numₘ(depth)) body (ifc_omega_mem depth)
          (by simpa only [finite_numeral_term] using hBody.2) hBody.1⟩
  }
  exact (closure.quote_hilbert formula depth hBound).2

theorem related_quote_hilbert_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        (quote_hilbert formula : SetOpenTerm [])) := by
  exact related_quote_hilbert_formula_code_at_of_depth
    (σ := σ) (bound := bound) (free := free)
    formula bound.length (Nat.le_refl _)

theorem related_quote_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(depth),
        (quote formula : SetOpenTerm [])) := by
  simpa [quote] using
    (related_quote_hilbert_formula_code_at_of_depth
      (σ := σ) (bound := bound) (free := free)
      (Formula.hilbertize QuotationNumbering.objectSort formula) depth hBound)

theorem related_quote_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
        NonlogicalSymₘ,
        numₘ(bound.length),
        (quote formula : SetOpenTerm [])) := by
  exact related_quote_formula_code_at_of_depth
    (σ := σ) (bound := bound) (free := free)
    formula bound.length (Nat.le_refl _)

theorem intrinsic_syntax_carrier_formula_mem_of_related
    (depth code : SetOpenTerm [])
    (hFormulaAt :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, depth, code)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      code ∈ₘ syntax_formula_code_set_term := by
  let symbols : SetOpenTerm [] := NonlogicalSymₘ
  have hCondition :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_condition symbols code := by
    unfold related_formula_code_condition
    apply FirstOrder.Derives.exists_intro depth
    rw [Formula.instantiateTop_abstractFreeTop]
    change ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      Formula.substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.instantiateFreeTop depth)
        (related_formula_code_atₘ(
          symbols.weakenFree SetSort.set,
          (.fvar .here),
          code.weakenFree SetSort.set))
    simpa [symbols, Formula.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.boundId,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop,
      Formula.substituteMapped_weakenFree_instantiateFreeTop] using hFormulaAt
  have hSubset := related_nonlogical_symbol_set_subset_derives
    (Γ := ([] : Context signature []))
  have hSetEq :
      (syntax_formula_code_set_term : SetOpenTerm []) =
        RelFormulaCodeₘ(symbols) := by
    rfl
  have hDefinition := FirstOrder.Derives.theory_weaken
    semantic_interpretation_theory_subset_intrinsic_syntax_carrier_theory
    (related_formula_set_definition_instance_derives
      (Γ := ([] : Context signature [])) symbols syntax_formula_code_set_term)
  have hIff := FirstOrder.Derives.imp_elim hDefinition hSubset
  have hSpec := FirstOrder.Derives.iff_elim_left hIff
    (by
      rw [hSetEq]
      exact Metatheory.Derives.equality_refl
        (T := intrinsic_syntax_carrier_theory)
        (Γ := ([] : Context signature []))
        (RelFormulaCodeₘ(symbols)))
  have hAt := FirstOrder.Derives.forall_elim
    (term := code) hSpec
  have hAt' :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        code ∈ₘ syntax_formula_code_set_term ↔ₘ
          related_formula_code_condition symbols code := by
    simpa [related_formula_set_spec, related_formula_code_condition,
      Formula.instantiateFreeTop,
      Substitution.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Term.substituteFree, Term.substitute,
      Term.substituteMapped, Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop,
      Formula.substituteMapped_weakenFree_instantiateFreeTop] using hAt
  exact FirstOrder.Derives.iff_elim_right hAt' hCondition

theorem intrinsic_syntax_carrier_quote_formula_mem
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      (quote formula : SetOpenTerm []) ∈ₘ syntax_formula_code_set_term := by
  exact intrinsic_syntax_carrier_formula_mem_of_related
    (numₘ(bound.length)) (quote formula : SetOpenTerm [])
    (related_quote_formula_code_at formula)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
