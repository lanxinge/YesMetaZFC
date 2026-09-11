import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding

/-!
# 一阶逻辑语义解释系统

语义层直接消费结构化 Quine 语法码。相对语言由结构节点中的符号描述决定；项值
和参数列值都是直接递归关系，不再引入覆盖所有项的全局求值函数。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

private abbrev weaken_set_two {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
  term_weaken_free_two term

private abbrev weaken_set_three {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  term_weaken_free_three term

private def weaken_set_four {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: SetSort.set :: SetSort.set :: free)
    SetSort.set SetSort.set (weaken_set_three term)

private def weaken_set_five {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: free)
    SetSort.set SetSort.set (weaken_set_four term)

private def exists_set_four {bound free : SetContext}
    (body : SetFormula bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set

private def exists_set_five {bound free : SetContext}
    (body : SetFormula bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-! ## 结构解释键 -/

abbrev constant_interpretation_key_term {bound free : SetContext}
    (symbol : SetTerm bound free) : SetTerm bound free :=
  godel_pairₘ(numₘ(0), symbol)

abbrev function_interpretation_key_term {bound free : SetContext}
    (arity symbol : SetTerm bound free) : SetTerm bound free :=
  godel_pairₘ(numₘ(1), godel_pairₘ(arity, symbol))

abbrev predicate_interpretation_key_term {bound free : SetContext}
    (arity symbol : SetTerm bound free) : SetTerm bound free :=
  godel_pairₘ(numₘ(2), godel_pairₘ(arity, symbol))

/-! ## 相对结构语法 -/

def related_term_code_free_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeOne := code.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((index ∈ₘ ωₘ) ∧ₘ (codeOne ≐ₘ free_var_codeₘ(index)))
    |>.existsFreeTop SetSort.set

def related_term_code_bound_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  let depthOne := depth.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((index ∈ₘ depthOne) ∧ₘ (codeOne ≐ₘ bound_var_codeₘ(index)))
    |>.existsFreeTop SetSort.set

def related_term_code_constant_condition {bound free : SetContext}
    (symbols code : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((((constant_interpretation_key_term index) ∈ₘ symbolsOne) ∧ₘ
      (codeOne ≐ₘ const_codeₘ(index))))
    |>.existsFreeTop SetSort.set

def related_term_code_application_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  let symbolsThree := weaken_set_three symbols
  let depthThree := weaken_set_three depth
  let codeThree := weaken_set_three code
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let arguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ
      (function_interpretation_key_term arity symbol ∈ₘ symbolsThree)) ∧ₘ
    (related_term_list_code_atₘ(symbolsThree, depthThree, arity, arguments) ∧ₘ
      (codeThree ≐ₘ app_codeₘ(arity, symbol, arguments))))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def related_term_code_at_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  ((depth ∈ₘ ωₘ) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    (related_term_code_free_condition code ∨ₘ
      (related_term_code_bound_condition depth code ∨ₘ
        (related_term_code_constant_condition symbols code ∨ₘ
          related_term_code_application_condition symbols depth code)))

def related_term_code_at_definition_instance {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  related_term_code_atₘ(symbols, depth, code) ↔ₘ
    related_term_code_at_condition symbols depth code

def related_term_list_code_cons_condition {bound free : SetContext}
    (symbols depth length code : SetTerm bound free) : SetFormula bound free :=
  let symbolsThree := weaken_set_three symbols
  let depthThree := weaken_set_three depth
  let lengthThree := weaken_set_three length
  let codeThree := weaken_set_three code
  let previousLength : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  let head : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar (.there .here)
  let tail : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  (((previousLength ∈ₘ ωₘ) ∧ₘ
      (lengthThree ≐ₘ Sₘ(previousLength))) ∧ₘ
    ((related_term_code_atₘ(symbolsThree, depthThree, head) ∧ₘ
      related_term_list_code_atₘ(symbolsThree, depthThree, previousLength, tail)) ∧ₘ
      (codeThree ≐ₘ code_consₘ(head, tail))))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def related_term_list_code_at_condition {bound free : SetContext}
    (symbols depth length code : SetTerm bound free) : SetFormula bound free :=
  (((depth ∈ₘ ωₘ) ∧ₘ (length ∈ₘ ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    (((length ≐ₘ numₘ(0)) ∧ₘ (code ≐ₘ code_nilₘ)) ∨ₘ
      related_term_list_code_cons_condition symbols depth length code)

def related_term_list_code_at_definition_instance {bound free : SetContext}
    (symbols depth length code : SetTerm bound free) : SetFormula bound free :=
  related_term_list_code_atₘ(symbols, depth, length, code) ↔ₘ
    related_term_list_code_at_condition symbols depth length code

def related_formula_binary_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free)
    (tag : StructuralCodeTag) : SetFormula bound free :=
  let symbolsTwo := weaken_set_two symbols
  let depthTwo := weaken_set_two depth
  let codeTwo := weaken_set_two code
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  ((related_term_code_atₘ(symbolsTwo, depthTwo, left) ∧ₘ
      related_term_code_atₘ(symbolsTwo, depthTwo, right)) ∧ₘ
    (codeTwo ≐ₘ structural_node_code_term tag [left, right]))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def related_formula_predicate_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  let symbolsThree := weaken_set_three symbols
  let depthThree := weaken_set_three depth
  let codeThree := weaken_set_three code
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let arguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ
      (predicate_interpretation_key_term arity symbol ∈ₘ symbolsThree)) ∧ₘ
    (related_term_list_code_atₘ(symbolsThree, depthThree, arity, arguments) ∧ₘ
      (codeThree ≐ₘ pred_codeₘ(arity, symbol, arguments))))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def related_formula_negation_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let depthOne := depth.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  (related_formula_code_atₘ(symbolsOne, depthOne, body) ∧ₘ
    (codeOne ≐ₘ neg_codeₘ(body)))
    |>.existsFreeTop SetSort.set

def related_formula_implication_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  let symbolsTwo := weaken_set_two symbols
  let depthTwo := weaken_set_two depth
  let codeTwo := weaken_set_two code
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  ((related_formula_code_atₘ(symbolsTwo, depthTwo, left) ∧ₘ
      related_formula_code_atₘ(symbolsTwo, depthTwo, right)) ∧ₘ
    (codeTwo ≐ₘ imp_codeₘ(left, right)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def related_formula_universal_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let depthOne := depth.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  (related_formula_code_atₘ(symbolsOne, Sₘ(depthOne), body) ∧ₘ
    (codeOne ≐ₘ all_codeₘ(body)))
    |>.existsFreeTop SetSort.set

def related_formula_code_at_condition {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  ((depth ∈ₘ ωₘ) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    (related_formula_binary_condition symbols depth code .equality ∨ₘ
      (related_formula_binary_condition symbols depth code .membership ∨ₘ
        (related_formula_predicate_condition symbols depth code ∨ₘ
          (related_formula_negation_condition symbols depth code ∨ₘ
            (related_formula_implication_condition symbols depth code ∨ₘ
              related_formula_universal_condition symbols depth code)))))

def related_formula_code_at_definition_instance {bound free : SetContext}
    (symbols depth code : SetTerm bound free) : SetFormula bound free :=
  related_formula_code_atₘ(symbols, depth, code) ↔ₘ
    related_formula_code_at_condition symbols depth code

def related_term_code_condition {bound free : SetContext}
    (symbols code : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let depth : SetTerm bound (SetSort.set :: free) := .fvar .here
  related_term_code_atₘ(symbolsOne, depth, codeOne)
    |>.existsFreeTop SetSort.set

def related_term_list_code_condition {bound free : SetContext}
    (symbols length code : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let lengthOne := length.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let depth : SetTerm bound (SetSort.set :: free) := .fvar .here
  related_term_list_code_atₘ(symbolsOne, depth, lengthOne, codeOne)
    |>.existsFreeTop SetSort.set

def related_formula_code_condition {bound free : SetContext}
    (symbols code : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let depth : SetTerm bound (SetSort.set :: free) := .fvar .here
  related_formula_code_atₘ(symbolsOne, depth, codeOne)
    |>.existsFreeTop SetSort.set

def related_term_set_spec {bound free : SetContext}
    (symbols candidate : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let candidateOne := candidate.weakenFree SetSort.set
  let code : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((code ∈ₘ candidateOne) ↔ₘ related_term_code_condition symbolsOne code)
    |>.forallFreeTop SetSort.set

def related_formula_set_spec {bound free : SetContext}
    (symbols candidate : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let candidateOne := candidate.weakenFree SetSort.set
  let code : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((code ∈ₘ candidateOne) ↔ₘ related_formula_code_condition symbolsOne code)
    |>.forallFreeTop SetSort.set

def related_nonlogical_symbol_set_definition_axiom : SetSentence :=
  NonlogicalSymₘ ≐ₘ ωₘ

def related_term_set_definition_instance {bound free : SetContext}
    (symbols candidate : SetTerm bound free) : SetFormula bound free :=
  (symbols ⊆ₘ NonlogicalSymₘ) ⟶ₘ
    ((candidate ≐ₘ RelTermCodeₘ(symbols)) ↔ₘ
      related_term_set_spec symbols candidate)

def related_term_set_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (related_term_set_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def related_formula_set_definition_instance {bound free : SetContext}
    (symbols candidate : SetTerm bound free) : SetFormula bound free :=
  (symbols ⊆ₘ NonlogicalSymₘ) ⟶ₘ
    ((candidate ≐ₘ RelFormulaCodeₘ(symbols)) ↔ₘ
      related_formula_set_spec symbols candidate)

def related_formula_set_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (related_formula_set_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 结构语义替换自然性 -/

@[simp] theorem related_term_code_at_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (symbols depth code : SetTerm bound sourceFree) :
    (related_term_code_at_definition_instance symbols depth code).substituteFree τ =
      related_term_code_at_definition_instance
        (symbols.substituteFree τ) (depth.substituteFree τ)
        (code.substituteFree τ) := by
  simp [related_term_code_at_definition_instance,
    related_term_code_at_condition, related_term_code_free_condition,
    related_term_code_bound_condition, related_term_code_constant_condition,
    related_term_code_application_condition, weaken_set_three, term_weaken_free_three,
    structural_list_code_term, structural_raw_node_code_term,
    godel_pairing_term, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped, Term.substituteFree,
    Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
    Term.substituteMapped_weakenFree_boundId,
    VariableSubstitution.liftFree]
  repeat' constructor

@[simp] theorem related_term_list_code_at_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (symbols depth length code : SetTerm bound sourceFree) :
    (related_term_list_code_at_definition_instance
      symbols depth length code).substituteFree τ =
      related_term_list_code_at_definition_instance
        (symbols.substituteFree τ) (depth.substituteFree τ)
        (length.substituteFree τ) (code.substituteFree τ) := by
  simp [related_term_list_code_at_definition_instance,
    related_term_list_code_at_condition,
    related_term_list_code_cons_condition, weaken_set_three, term_weaken_free_three,
    structural_list_code_term,
    structural_raw_node_code_term, godel_pairing_term,
    Formula.substituteFree, Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteFree, Term.substitute,
    Term.substituteMapped, Arguments.substituteMapped,
    Term.substituteMapped_weakenFree_boundId,
    VariableSubstitution.liftFree]
  repeat' constructor

@[simp] theorem related_formula_code_at_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (symbols depth code : SetTerm bound sourceFree) :
    (related_formula_code_at_definition_instance
      symbols depth code).substituteFree τ =
      related_formula_code_at_definition_instance
        (symbols.substituteFree τ) (depth.substituteFree τ)
        (code.substituteFree τ) := by
  simp [related_formula_code_at_definition_instance,
    related_formula_code_at_condition, related_formula_binary_condition,
    related_formula_predicate_condition, related_formula_negation_condition,
    related_formula_implication_condition,
    related_formula_universal_condition, weaken_set_two, weaken_set_three,
    term_weaken_free_two, term_weaken_free_three,
    structural_list_code_term, structural_node_code_term,
    structural_raw_node_code_term, godel_pairing_term,
    Formula.substituteFree, Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteFree, Term.substitute,
    Term.substituteMapped, Arguments.substituteMapped,
    Term.substituteMapped_weakenFree_boundId,
    VariableSubstitution.liftFree]
  repeat' constructor

@[simp] theorem related_formula_set_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (symbols candidate : SetTerm bound sourceFree) :
    (related_formula_set_definition_instance symbols candidate).substituteFree τ =
      related_formula_set_definition_instance
        (symbols.substituteFree τ) (candidate.substituteFree τ) := by
  simp [related_formula_set_definition_instance,
    related_formula_set_spec, related_formula_code_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped, Term.substituteFree,
    Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
    Term.substituteMapped_weakenFree_boundId,
    VariableSubstitution.liftFree]
  repeat' constructor

def related_term_code_at_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (related_term_code_at_definition_instance
      (.fvar (.there (.there .here)) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set]))

def related_term_list_code_at_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (related_term_list_code_at_definition_instance
      (.fvar (.there (.there (.there .here))) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set]))

def related_formula_code_at_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (related_formula_code_at_definition_instance
      (.fvar (.there (.there .here)) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set]))

def related_syntax_definition_axiom : SetSentence :=
  related_term_code_at_definition_axiom ∧ₘ
    (related_term_list_code_at_definition_axiom ∧ₘ
      (related_formula_code_at_definition_axiom ∧ₘ
        (related_term_set_definition_axiom ∧ₘ
          related_formula_set_definition_axiom)))

/-! ## 结构 -/

def structure_constant_condition {bound free : SetContext}
    (carrier interpretation symbols : SetTerm bound free) : SetFormula bound free :=
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let symbol : SetTerm bound (SetSort.set :: free) := .fvar .here
  (((symbol ∈ₘ ωₘ) ∧ₘ
      (constant_interpretation_key_term symbol ∈ₘ symbolsOne)) ⟶ₘ
    ((interpretationOne ·ₘ constant_interpretation_key_term symbol) ∈ₘ carrierOne))
    |>.forallFreeTop SetSort.set

def structure_function_condition {bound free : SetContext}
    (interpretation symbols : SetTerm bound free) : SetFormula bound free :=
  let interpretationTwo := weaken_set_two interpretation
  let symbolsTwo := weaken_set_two symbols
  let arity : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let symbol : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ
      (function_interpretation_key_term arity symbol ∈ₘ symbolsTwo)) ⟶ₘ
    is_function_formula
      (interpretationTwo ·ₘ function_interpretation_key_term arity symbol))
    |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

def structure_predicate_condition {bound free : SetContext}
    (interpretation symbols : SetTerm bound free) : SetFormula bound free :=
  let interpretationTwo := weaken_set_two interpretation
  let symbolsTwo := weaken_set_two symbols
  let arity : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let symbol : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ
      (predicate_interpretation_key_term arity symbol ∈ₘ symbolsTwo)) ⟶ₘ
    is_relation_formula
      (interpretationTwo ·ₘ predicate_interpretation_key_term arity symbol))
    |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

def structure_condition {bound free : SetContext}
    (carrier interpretation symbols : SetTerm bound free) : SetFormula bound free :=
  (carrier ≠ₘ ∅ₘ) ∧ₘ
    ((symbols ⊆ₘ NonlogicalSymₘ) ∧ₘ
      (is_function_formula interpretation ∧ₘ
        (domₘ(interpretation) ≐ₘ symbols))) ∧ₘ
    (structure_constant_condition carrier interpretation symbols ∧ₘ
      (structure_function_condition interpretation symbols ∧ₘ
        structure_predicate_condition interpretation symbols))

def structure_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let carrier : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let interpretation : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there .here)
     let symbols : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] :=
       .fvar .here
     structureₘ(carrier, interpretation, symbols) ↔ₘ
       structure_condition carrier interpretation symbols)

/-! ## 直接项值关系 -/

abbrev assignment_space_term {bound free : SetContext}
    (carrier : SetTerm bound free) : SetTerm bound free :=
  Mapₘ(ωₘ, carrier)

def term_value_variable_condition {bound free : SetContext}
    (assignment term value : SetTerm bound free) : SetFormula bound free :=
  let assignmentOne := assignment.weakenFree SetSort.set
  let termOne := term.weakenFree SetSort.set
  let valueOne := value.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  (((index ∈ₘ ωₘ) ∧ₘ
      ((termOne ≐ₘ free_var_codeₘ(index)) ∨ₘ
        (termOne ≐ₘ bound_var_codeₘ(index)))) ∧ₘ
    (valueOne ≐ₘ (assignmentOne ·ₘ termOne)))
    |>.existsFreeTop SetSort.set

def term_value_constant_condition {bound free : SetContext}
    (interpretation symbols term value : SetTerm bound free) : SetFormula bound free :=
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let termOne := term.weakenFree SetSort.set
  let valueOne := value.weakenFree SetSort.set
  let symbol : SetTerm bound (SetSort.set :: free) := .fvar .here
  let body := (((constant_interpretation_key_term symbol ∈ₘ symbolsOne) ∧ₘ
      (termOne ≐ₘ const_codeₘ(symbol))) ∧ₘ
    (valueOne ≐ₘ
      (interpretationOne ·ₘ constant_interpretation_key_term symbol)))
  body.existsFreeTop SetSort.set

def term_value_application_condition {bound free : SetContext}
    (carrier interpretation symbols assignment term value : SetTerm bound free) :
    SetFormula bound free :=
  let carrierFour := weaken_set_four carrier
  let interpretationFour := weaken_set_four interpretation
  let symbolsFour := weaken_set_four symbols
  let assignmentFour := weaken_set_four assignment
  let termFour := weaken_set_four term
  let valueFour := weaken_set_four value
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let arguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let values : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  let body := (((((arity ∈ₘ ωₘ) ∧ₘ
      (function_interpretation_key_term arity symbol ∈ₘ symbolsFour)) ∧ₘ
      related_term_list_code_condition symbolsFour arity arguments) ∧ₘ
      (termFour ≐ₘ app_codeₘ(arity, symbol, arguments))) ∧ₘ
    (term_list_valueₘ(carrierFour, interpretationFour, symbolsFour,
        assignmentFour, arity, arguments, values) ∧ₘ
      (valueFour ≐ₘ
        ((interpretationFour ·ₘ function_interpretation_key_term arity symbol) ·ₘ
          values))))
  exists_set_four body

def term_value_condition {bound free : SetContext}
    (carrier interpretation symbols assignment term value : SetTerm bound free) :
    SetFormula bound free :=
  ((structureₘ(carrier, interpretation, symbols) ∧ₘ
      (assignment ∈ₘ assignment_space_term carrier)) ∧ₘ
    (((term ∈ₘ RelTermCodeₘ(symbols)) ∧ₘ (value ∈ₘ carrier)) ∧ₘ
      (term_value_variable_condition assignment term value ∨ₘ
        (term_value_constant_condition interpretation symbols term value ∨ₘ
          term_value_application_condition carrier interpretation symbols assignment term value))))

def term_list_value_condition {bound free : SetContext}
    (carrier interpretation symbols assignment length arguments values : SetTerm bound free) :
    SetFormula bound free :=
  let carrierFive := weaken_set_five carrier
  let interpretationFive := weaken_set_five interpretation
  let symbolsFive := weaken_set_five symbols
  let assignmentFive := weaken_set_five assignment
  let lengthFive := weaken_set_five length
  let argumentsFive := weaken_set_five arguments
  let valuesFive := weaken_set_five values
  let previousLength : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there (.there .here))))
  let head : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let tail : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let headValue : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let tailValues : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  let consCase :=
    ((((previousLength ∈ₘ ωₘ) ∧ₘ
        (lengthFive ≐ₘ Sₘ(previousLength))) ∧ₘ
      ((argumentsFive ≐ₘ code_consₘ(head, tail)) ∧ₘ
        (valuesFive ≐ₘ code_consₘ(headValue, tailValues)))) ∧ₘ
      (term_valueₘ(carrierFive, interpretationFive, symbolsFive,
          assignmentFive, head, headValue) ∧ₘ
        term_list_valueₘ(carrierFive, interpretationFive, symbolsFive,
          assignmentFive, previousLength, tail, tailValues)))
  let consCaseClosed := exists_set_five consCase
  ((length ≐ₘ numₘ(0)) ∧ₘ
      ((arguments ≐ₘ code_nilₘ) ∧ₘ (values ≐ₘ code_nilₘ))) ∨ₘ consCaseClosed

def term_value_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let carrier : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there (.there .here)))))
     let interpretation : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there .here))))
     let symbols : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there .here)))
     let assignment : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let term : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there .here)
     let value : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar .here
     term_valueₘ(carrier, interpretation, symbols, assignment, term, value) ↔ₘ
       term_value_condition carrier interpretation symbols assignment term value)

def term_list_value_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let carrier : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there (.there (.there .here))))))
     let interpretation : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there (.there .here)))))
     let symbols : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there .here))))
     let assignment : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there .here)))
     let length : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] := .fvar (.there (.there .here))
     let arguments : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] := .fvar (.there .here)
     let values : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] := .fvar .here
     term_list_valueₘ(carrier, interpretation, symbols, assignment,
       length, arguments, values) ↔ₘ
       term_list_value_condition carrier interpretation symbols assignment
         length arguments values)

/-! ## 理论组合 -/

def related_symbol_semantics_theory : SetTheory :=
  Theory.insert related_nonlogical_symbol_set_definition_axiom
    logical_rule_encoding_theory

def related_syntax_semantics_theory : SetTheory :=
  Theory.insert related_syntax_definition_axiom related_symbol_semantics_theory

def structure_semantics_theory : SetTheory :=
  Theory.insert structure_definition_axiom related_syntax_semantics_theory

def term_value_semantics_theory : SetTheory :=
  Theory.insert (term_value_definition_axiom ∧ₘ term_list_value_definition_axiom)
    structure_semantics_theory

def semantic_interpretation_theory : SetTheory :=
  term_value_semantics_theory

derive_theory_subset logical_rule_encoding_theory ⊆ related_symbol_semantics_theory

derive_theory_subset related_symbol_semantics_theory ⊆ related_syntax_semantics_theory

derive_theory_subset related_syntax_semantics_theory ⊆ structure_semantics_theory

derive_theory_subset structure_semantics_theory ⊆ term_value_semantics_theory

derive_theory_subset term_value_semantics_theory ⊆ semantic_interpretation_theory

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
