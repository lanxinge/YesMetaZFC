import YesMetaZFC.Automation.QuotationInduction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.StructuralCorrectness

/-!
# 公式结构 quotation 的对象侧正确性

本层在项与参数列正确性的基础上，逐构造子证明公式码递归方程。见证直接来自内在
语法构造，不引入 token、字符串、可满足性或额外的新鲜性假设。
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

/-- 连续实例化两个自由槽等于一次双槽替换。 -/
theorem two_free_substitution_beta
    {body : SetOpenFormula [SetSort.set, SetSort.set]}
    (first second : SetOpenTerm []) :
    Formula.instantiateFreeTop first
      (Formula.substituteFree
        (VariableSubstitution.liftFree SetSort.set
          (VariableSubstitution.instantiateFreeTop second)) body) =
      Formula.substituteFree
        (VariableSubstitution.cons first
          (VariableSubstitution.cons second VariableSubstitution.empty)) body := by
  change
    Formula.substitute (Substitution.instantiateFreeTop first)
      (Formula.substitute
        (Substitution.free_map
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.instantiateFreeTop second))) body) =
      Formula.substitute
        (Substitution.free_map
          (VariableSubstitution.cons first
            (VariableSubstitution.cons second VariableSubstitution.empty))) body
  rw [Formula.substitute_comp]
  simp only [Substitution.comp, Substitution.instantiateFreeTop,
    Substitution.free_map]
  congr 1
  change Substitution.map _ _ = Substitution.map _ _
  congr
  funext resultSort entry
  cases entry with
  | here =>
      simp [ VariableSubstitution.cons, VariableSubstitution.liftFree,
        VariableSubstitution.instantiateFreeTop,
        Term.substituteMapped]
  | there previous =>
      cases resultSort
      cases previous with
      | here =>
          simpa [Term.weakenFree, Term.rename, Renaming.weakenFree,
            Renaming.free, Term.renameMapped] using!
            (Term.substituteMapped_weakenFree_instantiateFreeTop
              (σ := signature) SetSort.set first second)
      | there impossible =>
          cases impossible

theorem gq_closed_two_weaken_substitute
    (τ : VariableSubstitution signature [SetSort.set, SetSort.set] [] [])
    {resultSort : signature.SortSymbol}
    (term : Term signature [] [] resultSort) :
    Term.substituteMapped VariableSubstitution.boundId τ
        ((term.weakenFree SetSort.set).weakenFree SetSort.set) =
      term := by
  simp only [Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree]

private theorem formula_code_binary_atomic_condition_intro
    (tag : StructuralCodeTag)
    (depth code left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      term_code_atₘ(depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ≐ₘ structural_node_code_term tag [left, right]) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_binary_atomic_condition tag depth code := by
  unfold formula_code_binary_atomic_condition
  apply FirstOrder.Derives.existsFreePrefix_intro
    (.cons right (.cons left .nil))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term, term_weaken_free_two] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hLeft hRight) hCode

private theorem formula_code_negation_condition_intro
    (depth code body : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, body))
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ≐ₘ neg_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_negation_condition depth code := by
  unfold formula_code_negation_condition
  apply FirstOrder.Derives.existsFreePrefix_intro
    (.cons body .nil)
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term, negation_formula_code_term] using
    FirstOrder.Derives.conj_intro hBody hCode

private theorem formula_code_implication_condition_intro
    (depth code left right : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, left))
    (hRight : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, right))
    (hCode : ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ≐ₘ imp_codeₘ(left, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_implication_condition depth code := by
  unfold formula_code_implication_condition
  apply FirstOrder.Derives.existsFreePrefix_intro
    (.cons right (.cons left .nil))
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term, implication_formula_code_term, term_weaken_free_two] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hLeft hRight) hCode

private theorem formula_code_predicate_condition_intro
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
        code ≐ₘ pred_codeₘ(arity, symbol, arguments)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_predicate_condition depth code := by
  unfold formula_code_predicate_condition
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
      (FirstOrder.Derives.conj_intro hArguments hCode)

private theorem formula_code_universal_condition_intro
    (depth code body : SetOpenTerm [])
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(depth), body))
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        code ≐ₘ all_codeₘ(body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_universal_condition depth code := by
  unfold formula_code_universal_condition
  apply FirstOrder.Derives.existsFreePrefix_intro
    (.cons body .nil)
  simpa [Arguments.substitutionWith, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.freeId,
    Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
    structural_node_code_term, structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term, universal_formula_code_term] using
    FirstOrder.Derives.conj_intro hBody hCode

private theorem formula_code_at_of_condition_branch
    (depth code : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        code ∈ₘ ωₘ)
    (hBranch :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_binary_atomic_condition .equality depth code ∨ₘ
          (formula_code_binary_atomic_condition .membership depth code ∨ₘ
            (formula_code_predicate_condition depth code ∨ₘ
              (formula_code_negation_condition depth code ∨ₘ
                (formula_code_implication_condition depth code ∨ₘ
                  formula_code_universal_condition depth code))))) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, code) := by
  apply FirstOrder.Derives.iff_elim_right
    (formula_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hDepth hCode) hBranch

theorem formula_code_at_code_mem_of_derives
    (depth code : SetOpenTerm [])
    (hCode :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, code)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      code ∈ₘ ωₘ := by
  have hCondition := FirstOrder.Derives.iff_elim_left
    (formula_code_at_definition_instance_derives
      (Γ := ([] : Context signature [])) depth code)
    hCode
  exact FirstOrder.Derives.conj_elim_right
    (FirstOrder.Derives.conj_elim_left hCondition)

private theorem formula_code_at_of_negation
    (depth body : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, neg_codeₘ(body)) := by
  have hBodyCode := formula_code_at_code_mem_of_derives depth body hBody
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) StructuralCodeTag.negation [body]
      (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hBodyCode
        · contradiction)
  have hBranch := formula_code_negation_condition_intro
    depth (neg_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (neg_codeₘ(body) : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (neg_codeₘ(body) : SetOpenTerm []) hDepth
    (by
      simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))))

private theorem formula_code_at_of_implication
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, imp_codeₘ(left, right)) := by
  have hLeftCode := formula_code_at_code_mem_of_derives depth left hLeft
  have hRightCode := formula_code_at_code_mem_of_derives depth right hRight
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) StructuralCodeTag.implication
      [left, right] (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hLeftCode
        · rcases hField with hField | hField
          · simpa [hField] using hRightCode
          · contradiction)
  have hBranch := formula_code_implication_condition_intro
    depth (imp_codeₘ(left, right) : SetOpenTerm []) left right
    hLeft hRight
    (Metatheory.Derives.equality_refl
      (imp_codeₘ(left, right) : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (imp_codeₘ(left, right) : SetOpenTerm []) hDepth
    (by
      simpa [structural_node_code_term, structural_list_code_term] using! hCode)
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))))

private theorem formula_code_at_of_universal
    (depth body : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(depth), body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, all_codeₘ(body)) := by
  have hBodyCode := formula_code_at_code_mem_of_derives
    (Sₘ(depth) : SetOpenTerm []) body hBody
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) StructuralCodeTag.universal [body]
      (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hBodyCode
        · contradiction)
  have hBranch := formula_code_universal_condition_intro
    depth (all_codeₘ(body) : SetOpenTerm []) body hBody
    (Metatheory.Derives.equality_refl
      (all_codeₘ(body) : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (all_codeₘ(body) : SetOpenTerm []) hDepth
    (by
      simpa [structural_node_code_term, structural_list_code_term] using! hCode)
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right
                  (FirstOrder.Derives.disj_intro_right hBranch)))))

theorem formula_code_at_implication_intro
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, imp_codeₘ(left, right)) :=
  formula_code_at_of_implication depth left right hDepth hLeft hRight

theorem formula_code_at_universal_intro
    (depth body : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hBody :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(depth), body)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(depth, all_codeₘ(body)) :=
  formula_code_at_of_universal depth body hDepth hBody

private theorem formula_code_at_of_equality
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        depth, structural_node_code_term .equality [left, right]) := by
  have hLeftCode := term_code_at_code_mem_of_derives depth left hLeft
  have hRightCode := term_code_at_code_mem_of_derives depth right hRight
  have hCode :=
    structural_node_code_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) .equality [left, right] (by
        intro field hField
        simp only [List.mem_cons, List.not_mem_nil] at hField
        rcases hField with hField | hField
        · simpa [hField] using hLeftCode
        · rcases hField with hField | hField
          · simpa [hField] using hRightCode
          · contradiction)
  have hBranch := formula_code_binary_atomic_condition_intro
    .equality depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm [])
    left right hLeft hRight
    (Metatheory.Derives.equality_refl
      (structural_node_code_term .equality [left, right] : SetOpenTerm []))
  exact formula_code_at_of_condition_branch depth
    (structural_node_code_term .equality [left, right] : SetOpenTerm []) hDepth
    (by
      simpa using hCode)
    (FirstOrder.Derives.disj_intro_left hBranch)

theorem formula_code_at_equality_intro
    (depth left right : SetOpenTerm [])
    (hDepth :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        depth ∈ₘ ωₘ)
    (hLeft :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, left))
    (hRight :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(depth, right)) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        depth, structural_node_code_term .equality [left, right]) :=
  formula_code_at_of_equality depth left right hDepth hLeft hRight

/-! ## 外部深度提升 -/

/-- 类型化关系原子在不小于其 bound 上下文长度的任意外部深度下都满足公式码递归谓词。 -/
theorem quote_relation_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (depth : Nat) (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(depth),
        (quote_relation relation arguments : SetOpenTerm [])) := by
  have hDepth := finite_numeral_mem_formal_language_encoding_theory
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
                  have hLeft := quote_term_code_at_of_depth
                    left depth hBound
                  have hRight := quote_term_code_at_of_depth
                    right depth hBound
                  have hLeftCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term left : SetOpenTerm []) hLeft
                  have hRightCode := term_code_at_code_mem_of_derives
                    (numₘ(depth))
                    (quote_term right : SetOpenTerm []) hRight
                  have hCode :=
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
                  have hBranch := formula_code_binary_atomic_condition_intro
                    StructuralCodeTag.membership
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) :
                      SetOpenTerm [])
                    (quote_term left : SetOpenTerm [])
                    (quote_term right : SetOpenTerm [])
                    hLeft hRight
                    (Metatheory.Derives.equality_refl
                      (mem_codeₘ(
                        (quote_term left : SetOpenTerm []),
                        (quote_term right : SetOpenTerm [])) :
                        SetOpenTerm []))
                  have hResult := formula_code_at_of_condition_branch
                    (numₘ(depth))
                    (mem_codeₘ(
                      (quote_term left : SetOpenTerm []),
                      (quote_term right : SetOpenTerm [])) :
                      SetOpenTerm [])
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
                    rw [quote_relation_membership_eq
                      relation arguments hKind]
                    apply quote_membership_arguments_cons_eq
                      relation arguments hKind left right
                    exact hTypedArguments
                  rw [hQuote]
                  exact hResult
  | predicate =>
      have hArguments := quote_arguments_term_list_code_at_of_depth
        arguments depth hBound
      have hArgumentsCode := term_list_code_at_code_mem_of_derives
        (numₘ(depth))
        (numₘ(σ.relArity relation))
        (quote_arguments arguments : SetOpenTerm [])
        (by simpa [Signature.relArity] using hArguments)
      have hCode :=
        structural_node_code_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) StructuralCodeTag.predicate
          [numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])] (by
            intro field hField
            simp only [List.mem_cons, List.not_mem_nil] at hField
            rcases hField with hField | hField
            · simpa [hField] using
                (finite_numeral_mem_formal_language_encoding_theory
                  (Γ := ([] : Context signature [])) (σ.relArity relation))
            · rcases hField with hField | hField
              · simpa [hField] using
                  (finite_numeral_mem_formal_language_encoding_theory
                    (Γ := ([] : Context signature []))
                    (QuotationNumbering.relation_number relation))
              · rcases hField with hField | hField
                · simpa [hField] using hArgumentsCode
                · contradiction)
      have hBranch := formula_code_predicate_condition_intro
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) :
          SetOpenTerm [])
        (numₘ(σ.relArity relation))
        (numₘ(QuotationNumbering.relation_number relation))
        (quote_arguments arguments : SetOpenTerm [])
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) (σ.relArity relation))
        (finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature []))
          (QuotationNumbering.relation_number relation))
        (by simpa [Signature.relArity] using hArguments)
        (Metatheory.Derives.equality_refl
          (pred_codeₘ(
            numₘ(σ.relArity relation),
            numₘ(QuotationNumbering.relation_number relation),
            (quote_arguments arguments : SetOpenTerm [])) :
            SetOpenTerm []))
      have hResult := formula_code_at_of_condition_branch
        (numₘ(depth))
        (pred_codeₘ(
          numₘ(σ.relArity relation),
          numₘ(QuotationNumbering.relation_number relation),
          (quote_arguments arguments : SetOpenTerm [])) :
          SetOpenTerm [])
        hDepth
        (by
          simpa [structural_node_code_term, structural_list_code_term] using!
            hCode)
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))
      rw [quote_relation_predicate_eq relation arguments hKind]
      exact hResult

/-- 类型化 Hilbert 公式在不小于其 bound 上下文长度的任意外部深度下都满足公式码递归谓词。 -/
theorem quote_hilbert_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(depth),
        (quote_hilbert formula : SetOpenTerm [])) := by
  let closure : _root_.YesMetaZFC.Automation.QuotationInduction.FormulaClosure σ
      (fun depth code => ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(depth), code)) := {
    relation := fun relation arguments depth hBound =>
      quote_relation_formula_code_at_of_depth relation arguments depth hBound
    equality := fun left right depth hBound =>
      formula_code_at_of_equality (numₘ(depth)) (quote_term left) (quote_term right)
        (finite_numeral_mem_formal_language_encoding_theory depth)
        (quote_term_code_at_of_depth left depth hBound)
        (quote_term_code_at_of_depth right depth hBound)
    negation := fun depth body hBody =>
      formula_code_at_of_negation (numₘ(depth)) body
        (finite_numeral_mem_formal_language_encoding_theory depth) hBody
    implication := fun depth left right hLeft hRight =>
      formula_code_at_of_implication (numₘ(depth)) left right
        (finite_numeral_mem_formal_language_encoding_theory depth) hLeft hRight
    universal := fun depth body hBody =>
      formula_code_at_of_universal (numₘ(depth)) body
        (finite_numeral_mem_formal_language_encoding_theory depth)
        (by simpa only [finite_numeral_term] using hBody)
  }
  exact closure.quote_hilbert formula depth hBound

theorem quote_formula_code_at_of_depth
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat)
    (hBound : bound.length ≤ depth) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(depth),
        (quote formula : SetOpenTerm [])) := by
  simpa [quote] using
    (quote_hilbert_formula_code_at_of_depth
      (σ := σ) (bound := bound) (free := free)
      (Formula.hilbertize QuotationNumbering.objectSort formula)
      depth hBound)

theorem quote_hilbert_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(bound.length),
        (quote_hilbert formula : SetOpenTerm [])) := by
  exact quote_hilbert_formula_code_at_of_depth formula bound.length (Nat.le_refl _)

theorem quote_formula_code_at
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      formula_code_atₘ(
        numₘ(bound.length),
        (quote formula : SetOpenTerm [])) := by
  simpa [quote] using
    (quote_hilbert_formula_code_at
      (σ := σ) (bound := bound) (free := free)
      (Formula.hilbertize QuotationNumbering.objectSort formula))

/-! ## 表达式理论共享的 quotation 码域与深度事实 -/

theorem finite_numeral_mem_expression
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[expression_encoding_theory]
      (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (finite_numeral_mem_formal_language_encoding_theory
      (Γ := Γ) number)

theorem finite_numeral_mem_of_lt_expression
    {free : SetContext} {Γ : Context signature free}
    {left right : Nat} (h : left < right) :
    Γ ⊢ₘ[expression_encoding_theory]
      (numₘ(left) : SetOpenTerm free) ∈ₘ numₘ(right) :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (finite_numeral_mem_of_lt_formal_language_encoding_theory
      (Γ := Γ) h)

theorem quote_term_code_at_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_code_atₘ(
        numₘ(bound.length),
        (quote_term term : SetOpenTerm [])) :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (quote_term_code_at term)

theorem quote_term_code_mem_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote_term term : SetOpenTerm []) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (term_code_at_code_mem_of_derives
      (numₘ(bound.length)) (quote_term term : SetOpenTerm [])
      (quote_term_code_at term))

theorem quote_arguments_code_at_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      term_list_code_atₘ(
        numₘ(bound.length), numₘ(sorts.length),
        (quote_arguments arguments : SetOpenTerm [])) :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (quote_arguments_term_list_code_at arguments)

theorem quote_arguments_code_mem_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote_arguments arguments : SetOpenTerm []) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (term_list_code_at_code_mem_of_derives
      (numₘ(bound.length)) (numₘ(sorts.length))
      (quote_arguments arguments : SetOpenTerm [])
      (quote_arguments_term_list_code_at arguments))

theorem quote_hilbert_code_at_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      formula_code_atₘ(
        numₘ(bound.length),
        (quote_hilbert formula : SetOpenTerm [])) :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (quote_hilbert_formula_code_at formula)

theorem quote_hilbert_code_mem_expression
    {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (quote_hilbert formula : SetOpenTerm []) ∈ₘ ωₘ :=
  FirstOrder.Derives.theory_weaken
    (T := formal_language_encoding_theory)
    (U := expression_encoding_theory)
    formal_language_encoding_theory_subset_expression_encoding_theory
    (formula_code_at_code_mem_of_derives
      (numₘ(bound.length)) (quote_hilbert formula : SetOpenTerm [])
      (quote_hilbert_formula_code_at formula))

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
