import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncoding

/-!
# 结构公式上的 Hilbert 规则编码

逻辑规则只消费结构公式码。全称节点没有具名变量字段；全称闭包、特化和等式替换
分别调用统一变换图的 closeFree、openBound 与 substituteFree 分支。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/- 模式参数和生成步骤使用存在见证；真正的闭包规则保留全称量词。 -/
private def exists_one {bound free : SetContext}
    (body : SetFormula bound (SetSort.set :: free)) : SetFormula bound free :=
  body.existsFreeTop SetSort.set

private def exists_two {bound free : SetContext}
    (body : SetFormula bound ([SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set

private def exists_three {bound free : SetContext}
    (body : SetFormula bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

private def exists_four {bound free : SetContext}
    (body : SetFormula bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set

private def close_three {bound free : SetContext}
    (body : SetFormula bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.forallFreeTop SetSort.set |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

private def weaken_two {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: free) SetSort.set SetSort.set
    (@Term.weakenFree signature bound free
      SetSort.set SetSort.set term)

private def weaken_three {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: SetSort.set :: free) SetSort.set SetSort.set
    (@Term.weakenFree signature bound
      (SetSort.set :: free) SetSort.set SetSort.set
      (@Term.weakenFree signature bound free
        SetSort.set SetSort.set term))

private def weaken_four {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: SetSort.set :: SetSort.set :: free)
    SetSort.set SetSort.set
    (@Term.weakenFree signature bound
      (SetSort.set :: SetSort.set :: free) SetSort.set SetSort.set
      (@Term.weakenFree signature bound
        (SetSort.set :: free) SetSort.set SetSort.set
        (@Term.weakenFree signature bound free
          SetSort.set SetSort.set term)))

/-! ## 命题公理 -/

abbrev implication_distribution_axiom_code_term {bound free : SetContext}
    (antecedent middle consequent : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(imp_codeₘ(antecedent, imp_codeₘ(middle, consequent)),
    imp_codeₘ(imp_codeₘ(antecedent, middle), imp_codeₘ(antecedent, consequent)))

abbrev self_implication_axiom_code_term {bound free : SetContext}
    (formula : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(formula, imp_codeₘ(formula, formula))

abbrev weakening_axiom_code_term {bound free : SetContext}
    (formula extra : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(formula, imp_codeₘ(extra, formula))

abbrev contradiction_axiom_code_term {bound free : SetContext}
    (formula conclusion : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(formula, imp_codeₘ(neg_codeₘ(formula), conclusion))

abbrev classical_axiom_code_term {bound free : SetContext}
    (formula : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(imp_codeₘ(neg_codeₘ(formula), formula), formula)

abbrev explosion_axiom_code_term {bound free : SetContext}
    (formula conclusion : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(neg_codeₘ(formula), imp_codeₘ(formula, conclusion))

abbrev case_analysis_axiom_code_term {bound free : SetContext}
    (formula conclusion : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(imp_codeₘ(formula, conclusion),
    imp_codeₘ(imp_codeₘ(neg_codeₘ(formula), conclusion), conclusion))

def implication_distribution_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeThree := weaken_three code
  let antecedent : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let middle : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let consequent : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_three (((formula_codeₘ(antecedent) ∧ₘ
      formula_codeₘ(middle)) ∧ₘ formula_codeₘ(consequent)) ∧ₘ
    (codeThree ≐ₘ
      implication_distribution_axiom_code_term antecedent middle consequent))

def self_implication_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeOne := code.weakenFree SetSort.set
  let formula : SetTerm bound (SetSort.set :: free) := .fvar .here
  exists_one (formula_codeₘ(formula) ∧ₘ
    (codeOne ≐ₘ self_implication_axiom_code_term formula))

private def binary_propositional_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free)
    (constructor :
      SetTerm bound ([SetSort.set, SetSort.set] ++ free) →
      SetTerm bound ([SetSort.set, SetSort.set] ++ free) →
      SetTerm bound ([SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  let codeTwo := weaken_two code
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_two (((formula_codeₘ(left) ∧ₘ formula_codeₘ(right)) ∧ₘ
    (codeTwo ≐ₘ constructor left right)))

def weakening_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  binary_propositional_axiom_condition code weakening_axiom_code_term

def contradiction_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  binary_propositional_axiom_condition code contradiction_axiom_code_term

def classical_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeOne := code.weakenFree SetSort.set
  let formula : SetTerm bound (SetSort.set :: free) := .fvar .here
  exists_one (formula_codeₘ(formula) ∧ₘ
    (codeOne ≐ₘ classical_axiom_code_term formula))

def explosion_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  binary_propositional_axiom_condition code explosion_axiom_code_term

def case_analysis_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  binary_propositional_axiom_condition code case_analysis_axiom_code_term

def propositional_axiom_schema_definition_axiom : SetSentence :=
  let code : SetOpenTerm [SetSort.set] := .fvar .here
  let p₁ := (code ∈ₘ ImpDistribAxiomsₘ) ↔ₘ implication_distribution_axiom_condition code
  let p₂ := (code ∈ₘ SelfImpAxiomsₘ) ↔ₘ self_implication_axiom_condition code
  let p₃ := (code ∈ₘ WeakeningAxiomsₘ) ↔ₘ weakening_axiom_condition code
  let p₄ := (code ∈ₘ ContradictionAxiomsₘ) ↔ₘ contradiction_axiom_condition code
  let p₅ := (code ∈ₘ ClassicalAxiomsₘ) ↔ₘ classical_axiom_condition code
  let p₆ := (code ∈ₘ ExplosionAxiomsₘ) ↔ₘ explosion_axiom_condition code
  let p₇ := (code ∈ₘ CaseAnalysisAxiomsₘ) ↔ₘ case_analysis_axiom_condition code
  let body := p₁ ∧ₘ (p₂ ∧ₘ (p₃ ∧ₘ (p₄ ∧ₘ (p₅ ∧ₘ (p₆ ∧ₘ p₇)))))
  body.forallFreeTop SetSort.set

/-! ## 全称规则 -/

abbrev specialization_axiom_code_term {bound free : SetContext}
    (body result : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(all_codeₘ(body), result)

abbrev quantifier_distribution_axiom_code_term {bound free : SetContext}
    (antecedent consequent : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(all_codeₘ(imp_codeₘ(antecedent, consequent)),
    imp_codeₘ(all_codeₘ(antecedent), all_codeₘ(consequent)))

abbrev vacuous_quantifier_axiom_code_term {bound free : SetContext}
    (antecedent body : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(antecedent, all_codeₘ(body))

def canonical_free_variable_code_condition {bound free : SetContext}
    (variableIndex : SetTerm bound free) : SetFormula bound free :=
  variableIndex ∈ₘ ωₘ

def canonical_forall_closure_code_condition {bound free : SetContext}
    (sourceCode variableIndex targetCode : SetTerm bound free) :
    SetFormula bound free :=
  let sourceOne := sourceCode.weakenFree SetSort.set
  let variableOne := variableIndex.weakenFree SetSort.set
  let targetOne := targetCode.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  (canonical_free_variable_code_condition variableOne ∧ₘ
    ((formula_close_free_condition variableOne sourceOne body) ∧ₘ
      (targetOne ≐ₘ all_codeₘ(body))))
    |>.existsFreeTop SetSort.set

def specialization_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeThree := weaken_three code
  let body : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let replacement : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let result : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_three (((formula_code_atₘ(numₘ(1), body) ∧ₘ
      term_codeₘ(replacement)) ∧ₘ formula_codeₘ(result)) ∧ₘ
    ((formula_open_bound_condition replacement body result) ∧ₘ
      (codeThree ≐ₘ specialization_axiom_code_term body result)))

def quantifier_distribution_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeTwo := weaken_two code
  let antecedent : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let consequent : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_two ((formula_code_atₘ(numₘ(1), antecedent) ∧ₘ
      formula_code_atₘ(numₘ(1), consequent)) ∧ₘ
    (codeTwo ≐ₘ
      quantifier_distribution_axiom_code_term antecedent consequent))

def vacuous_quantifier_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeThree := weaken_three code
  let antecedent : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let variableIndex : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let body : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_three (((formula_codeₘ(antecedent) ∧ₘ
      canonical_free_variable_code_condition variableIndex) ∧ₘ
      ¬ₘ formula_free_variable_occurs variableIndex antecedent) ∧ₘ
    ((formula_close_free_condition variableIndex antecedent body) ∧ₘ
      (codeThree ≐ₘ
        vacuous_quantifier_axiom_code_term antecedent body)))

def quantifier_axiom_schema_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let code : SetOpenTerm [SetSort.set] := .fvar .here
     ((code ∈ₘ SpecializationAxiomsₘ) ↔ₘ specialization_axiom_condition code) ∧ₘ
       (((code ∈ₘ ForallDistribAxiomsₘ) ↔ₘ quantifier_distribution_axiom_condition code) ∧ₘ
         ((code ∈ₘ VacuousForallAxiomsₘ) ↔ₘ vacuous_quantifier_axiom_condition code)))

/-! ## 等式规则 -/

abbrev equality_substitution_axiom_code_term {bound free : SetContext}
    (variableIndex replacement body result : SetTerm bound free) :
    SetTerm bound free :=
  imp_codeₘ(eq_codeₘ(free_var_codeₘ(variableIndex), replacement),
    imp_codeₘ(body, result))

abbrev equality_reflexivity_axiom_code_term {bound free : SetContext}
    (term : SetTerm bound free) : SetTerm bound free :=
  eq_codeₘ(term, term)

def equality_substitution_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeFour := weaken_four code
  let variableIndex : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let replacement : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let body : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let result : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  exists_four ((((canonical_free_variable_code_condition variableIndex ∧ₘ
      term_codeₘ(replacement)) ∧ₘ
      (formula_codeₘ(body) ∧ₘ formula_codeₘ(result))) ∧ₘ
      formula_free_substitution_condition
        variableIndex replacement body result) ∧ₘ
    (codeFour ≐ₘ equality_substitution_axiom_code_term
      variableIndex replacement body result))

def equality_reflexivity_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeOne := code.weakenFree SetSort.set
  let term : SetTerm bound (SetSort.set :: free) := .fvar .here
  exists_one (term_codeₘ(term) ∧ₘ
    (codeOne ≐ₘ equality_reflexivity_axiom_code_term term))

def equality_axiom_schema_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let code : SetOpenTerm [SetSort.set] := .fvar .here
     ((code ∈ₘ EqualitySubstAxiomsₘ) ↔ₘ equality_substitution_axiom_condition code) ∧ₘ
       ((code ∈ₘ EqualityReflAxiomsₘ) ↔ₘ equality_reflexivity_axiom_condition code))

/-! ## 逻辑公理闭包与 modus ponens -/

def base_logical_axiom_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  (code ∈ₘ ImpDistribAxiomsₘ) ∨ₘ
    ((code ∈ₘ SelfImpAxiomsₘ) ∨ₘ
    ((code ∈ₘ WeakeningAxiomsₘ) ∨ₘ
    ((code ∈ₘ ContradictionAxiomsₘ) ∨ₘ
    ((code ∈ₘ ClassicalAxiomsₘ) ∨ₘ
    ((code ∈ₘ ExplosionAxiomsₘ) ∨ₘ
    ((code ∈ₘ CaseAnalysisAxiomsₘ) ∨ₘ
    ((code ∈ₘ SpecializationAxiomsₘ) ∨ₘ
    ((code ∈ₘ ForallDistribAxiomsₘ) ∨ₘ
    ((code ∈ₘ VacuousForallAxiomsₘ) ∨ₘ
    ((code ∈ₘ EqualitySubstAxiomsₘ) ∨ₘ
      code ∈ₘ EqualityReflAxiomsₘ))))))))))

def base_logical_axiom_set_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let code : SetOpenTerm [SetSort.set] := .fvar .here
     (code ∈ₘ BaseLogicAxiomsₘ) ↔ₘ base_logical_axiom_condition code)

def logical_axiom_code_closed_condition {bound free : SetContext}
    (candidate : SetTerm bound free) : SetFormula bound free :=
  let candidateThree := weaken_three candidate
  let source : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let variableIndex : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let target : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  (BaseLogicAxiomsₘ ⊆ₘ candidate) ∧ₘ
    close_three (((source ∈ₘ candidateThree) ∧ₘ
      canonical_forall_closure_code_condition source variableIndex target) ⟶ₘ
      (target ∈ₘ candidateThree))

def logical_axiom_code_generation_condition {bound free : SetContext}
    (candidate code : SetTerm bound free) : SetFormula bound free :=
  let candidateTwo := weaken_two candidate
  let codeTwo := weaken_two code
  let source : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let variableIndex : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  base_logical_axiom_condition code ∨ₘ
    exists_two ((source ∈ₘ candidateTwo) ∧ₘ
      canonical_forall_closure_code_condition
        source variableIndex codeTwo)

def logical_axiom_code_generated_condition {bound free : SetContext}
    (candidate : SetTerm bound free) : SetFormula bound free :=
  let candidateOne := candidate.weakenFree SetSort.set
  let code : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((code ∈ₘ candidateOne) ↔ₘ
    logical_axiom_code_generation_condition candidateOne code)
    |>.forallFreeTop SetSort.set

def logical_axiom_set_spec {bound free : SetContext}
    (candidate : SetTerm bound free) : SetFormula bound free :=
  logical_axiom_code_closed_condition candidate ∧ₘ
    logical_axiom_code_generated_condition candidate

def logical_axiom_set_definition_axiom : SetSentence :=
  logical_axiom_set_spec (LogicAxiomsₘ : SetOpenTerm [])

def is_logical_axiom_code_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let code : SetOpenTerm [SetSort.set] := .fvar .here
     logical_axiom_codeₘ(code) ↔ₘ code ∈ₘ LogicAxiomsₘ)

def logical_axiom_code_definition_axiom : SetSentence :=
  base_logical_axiom_set_definition_axiom ∧ₘ
    (logical_axiom_set_definition_axiom ∧ₘ
      is_logical_axiom_code_definition_axiom)

def modus_ponens_condition {bound free : SetContext}
    (premise implication conclusion : SetTerm bound free) :
    SetFormula bound free :=
  ((formula_codeₘ(premise) ∧ₘ formula_codeₘ(implication)) ∧ₘ
    formula_codeₘ(conclusion)) ∧ₘ
    (implication ≐ₘ imp_codeₘ(premise, conclusion))

def modus_ponens_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let premise : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let implication : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there .here)
     let conclusion : SetOpenTerm [SetSort.set, SetSort.set, SetSort.set] := .fvar .here
     (modus_ponensₘ(premise, implication, conclusion) ↔ₘ
       modus_ponens_condition premise implication conclusion))

def propositional_axiom_schema_theory : SetTheory :=
  Theory.insert propositional_axiom_schema_definition_axiom
    expression_encoding_theory

def quantifier_axiom_schema_theory : SetTheory :=
  Theory.insert quantifier_axiom_schema_definition_axiom
    propositional_axiom_schema_theory

def equality_axiom_schema_theory : SetTheory :=
  Theory.insert equality_axiom_schema_definition_axiom
    quantifier_axiom_schema_theory

def logical_axiom_code_theory : SetTheory :=
  Theory.insert logical_axiom_code_definition_axiom
    equality_axiom_schema_theory

def logical_rule_encoding_theory : SetTheory :=
  Theory.insert modus_ponens_definition_axiom
    logical_axiom_code_theory

derive_theory_subset expression_encoding_theory ⊆ propositional_axiom_schema_theory

derive_theory_subset propositional_axiom_schema_theory ⊆ quantifier_axiom_schema_theory

derive_theory_subset quantifier_axiom_schema_theory ⊆ equality_axiom_schema_theory

derive_theory_subset equality_axiom_schema_theory ⊆ logical_axiom_code_theory

derive_theory_subset logical_axiom_code_theory ⊆ logical_rule_encoding_theory

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
