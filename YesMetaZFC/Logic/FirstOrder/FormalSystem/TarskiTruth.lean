import YesMetaZFC.Logic.FirstOrder.FormalSystem.SemanticInterpretation

/-!
# 一阶逻辑塔斯基真谓词

本模块在结构化 Quine 语法上直接定义公式阶段、满足、真、模型、语义后承与普遍真。
量词采用 de Bruijn 赋值压栈：新值写入第零个 bound 变量，旧 bound 变量整体后移；
因此语义核不再携带变量新鲜性见证，也不再依赖全局项求值函数。
这里给出集合结构的满足关系及对象定义规格；原支撑理论的无参数真值
不可定义性见 `ProofT.ZFC.ReducedTarski`，其证明直接消费实际对角固定点。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

private def weaken_set_two {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound (SetSort.set :: free)
    SetSort.set SetSort.set
    (@Term.weakenFree signature bound free SetSort.set SetSort.set term)

private def weaken_set_three {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound (SetSort.set :: SetSort.set :: free)
    SetSort.set SetSort.set (weaken_set_two term)

private def weaken_set_four {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: SetSort.set :: SetSort.set :: free)
    SetSort.set SetSort.set (weaken_set_three term)

private def exists_set_two {bound free : SetContext}
    (body : SetFormula bound ([SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set

private def exists_set_four {bound free : SetContext}
    (body : SetFormula bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set |>.existsFreeTop SetSort.set

private def forall_set_two {bound free : SetContext}
    (body : SetFormula bound ([SetSort.set, SetSort.set] ++ free)) :
    SetFormula bound free :=
  body.forallFreeTop SetSort.set |>.forallFreeTop SetSort.set

/-! ## 公式构造阶段 -/

def formula_stage_zero_condition {bound free : SetContext}
    (symbols formula : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let depth : SetTerm bound (SetSort.set :: free) := .fvar .here
  (formula ∈ₘ RelFormulaCodeₘ(symbols)) ∧ₘ
    ((((depth ∈ₘ ωₘ) ∧ₘ
      (related_formula_binary_condition symbolsOne depth formulaOne .equality ∨ₘ
        (related_formula_binary_condition symbolsOne depth formulaOne .membership ∨ₘ
          related_formula_predicate_condition symbolsOne depth formulaOne)))
      |>.existsFreeTop SetSort.set))

def formula_stage_negation_condition {bound free : SetContext}
    (symbols stage formula : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let stageOne := stage.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((body ∈ₘ FormulaStageₘ(symbolsOne, stageOne)) ∧ₘ
    (formulaOne ≐ₘ neg_codeₘ(body))).existsFreeTop SetSort.set

def formula_stage_implication_condition {bound free : SetContext}
    (symbols stage formula : SetTerm bound free) : SetFormula bound free :=
  let symbolsTwo := weaken_set_two symbols
  let stageTwo := weaken_set_two stage
  let formulaTwo := weaken_set_two formula
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_set_two (((left ∈ₘ FormulaStageₘ(symbolsTwo, stageTwo)) ∧ₘ
    (right ∈ₘ FormulaStageₘ(symbolsTwo, stageTwo))) ∧ₘ
    (formulaTwo ≐ₘ imp_codeₘ(left, right)))

def formula_stage_universal_condition {bound free : SetContext}
    (symbols stage formula : SetTerm bound free) : SetFormula bound free :=
  let symbolsOne := symbols.weakenFree SetSort.set
  let stageOne := stage.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((body ∈ₘ FormulaStageₘ(symbolsOne, stageOne)) ∧ₘ
    (formulaOne ≐ₘ all_codeₘ(body))).existsFreeTop SetSort.set

def formula_stage_successor_condition {bound free : SetContext}
    (symbols stage formula : SetTerm bound free) : SetFormula bound free :=
  (formula ∈ₘ RelFormulaCodeₘ(symbols)) ∧ₘ
    ((formula ∈ₘ FormulaStageₘ(symbols, stage)) ∨ₘ
      (formula_stage_negation_condition symbols stage formula ∨ₘ
        (formula_stage_implication_condition symbols stage formula ∨ₘ
          formula_stage_universal_condition symbols stage formula)))

def formula_stage_set_definition_axiom : SetSentence :=
  let zeroAxiom : SetSentence :=
    Metatheory.Formula.forall_close
      (let symbols : SetOpenTerm [SetSort.set, SetSort.set] :=
         .fvar (.there .here)
       let formula : SetOpenTerm [SetSort.set, SetSort.set] := .fvar .here
       (symbols ⊆ₘ NonlogicalSymₘ) ⟶ₘ
         ((formula ∈ₘ FormulaStageₘ(symbols, numₘ(0))) ↔ₘ
           formula_stage_zero_condition symbols formula))
  let successorAxiom : SetSentence :=
    Metatheory.Formula.forall_close
      (let symbols : SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set] :=
         .fvar (.there (.there .here))
       let stage : SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set] := .fvar (.there .here)
       let formula : SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set] := .fvar .here
       ((symbols ⊆ₘ NonlogicalSymₘ) ∧ₘ (stage ∈ₘ ωₘ)) ⟶ₘ
         ((formula ∈ₘ FormulaStageₘ(symbols, Sₘ(stage))) ↔ₘ
           formula_stage_successor_condition symbols stage formula))
  zeroAxiom ∧ₘ successorAxiom

/-! ## 原子公式满足 -/

def equality_atomic_satisfaction_condition {bound free : SetContext}
    (carrier interpretation symbols assignment formula : SetTerm bound free) :
    SetFormula bound free :=
  let carrierFour := weaken_set_four carrier
  let interpretationFour := weaken_set_four interpretation
  let symbolsFour := weaken_set_four symbols
  let assignmentFour := weaken_set_four assignment
  let formulaFour := weaken_set_four formula
  let left : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let right : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let leftValue : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let rightValue : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_set_four (((formulaFour ≐ₘ eq_codeₘ(left, right)) ∧ₘ
    term_valueₘ(carrierFour, interpretationFour, symbolsFour,
      assignmentFour, left, leftValue)) ∧ₘ
    (term_valueₘ(carrierFour, interpretationFour, symbolsFour,
      assignmentFour, right, rightValue) ∧ₘ (leftValue ≐ₘ rightValue)))

def membership_atomic_satisfaction_condition {bound free : SetContext}
    (carrier interpretation symbols assignment formula : SetTerm bound free) :
    SetFormula bound free :=
  let carrierFour := weaken_set_four carrier
  let interpretationFour := weaken_set_four interpretation
  let symbolsFour := weaken_set_four symbols
  let assignmentFour := weaken_set_four assignment
  let formulaFour := weaken_set_four formula
  let left : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let right : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let leftValue : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let rightValue : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_set_four (((formulaFour ≐ₘ mem_codeₘ(left, right)) ∧ₘ
    term_valueₘ(carrierFour, interpretationFour, symbolsFour,
      assignmentFour, left, leftValue)) ∧ₘ
    (term_valueₘ(carrierFour, interpretationFour, symbolsFour,
      assignmentFour, right, rightValue) ∧ₘ (leftValue ∈ₘ rightValue)))

def predicate_atomic_satisfaction_condition {bound free : SetContext}
    (carrier interpretation symbols assignment formula : SetTerm bound free) :
    SetFormula bound free :=
  let carrierFour := weaken_set_four carrier
  let interpretationFour := weaken_set_four interpretation
  let symbolsFour := weaken_set_four symbols
  let assignmentFour := weaken_set_four assignment
  let formulaFour := weaken_set_four formula
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
  let key := predicate_interpretation_key_term arity symbol
  exists_set_four (((((arity ∈ₘ ωₘ) ∧ₘ (key ∈ₘ symbolsFour)) ∧ₘ
    (related_term_list_code_condition symbolsFour arity arguments ∧ₘ
      (formulaFour ≐ₘ pred_codeₘ(arity, symbol, arguments)))) ∧ₘ
    term_list_valueₘ(carrierFour, interpretationFour, symbolsFour,
      assignmentFour, arity, arguments, values)) ∧ₘ
    (values ∈ₘ (interpretationFour ·ₘ key)))

def atomic_satisfaction_condition {bound free : SetContext}
    (carrier interpretation symbols assignment formula : SetTerm bound free) :
    SetFormula bound free :=
  ((structureₘ(carrier, interpretation, symbols) ∧ₘ
      (assignment ∈ₘ assignment_space_term carrier)) ∧ₘ
    formula_stage_zero_condition symbols formula) ∧ₘ
    (equality_atomic_satisfaction_condition
      carrier interpretation symbols assignment formula ∨ₘ
      (membership_atomic_satisfaction_condition
        carrier interpretation symbols assignment formula ∨ₘ
        predicate_atomic_satisfaction_condition
          carrier interpretation symbols assignment formula))

def atomic_satisfaction_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let carrier : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there .here))))
     let interpretation : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there .here)))
     let symbols : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let assignment : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there .here)
     let formula : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar .here
     atomic_satisfiesₘ(carrier, interpretation, symbols, assignment, formula) ↔ₘ
       atomic_satisfaction_condition
         carrier interpretation symbols assignment formula)

/-! ## de Bruijn 赋值压栈 -/

def assignment_update_condition {bound free : SetContext}
    (carrier assignment value updated : SetTerm bound free) :
    SetFormula bound free :=
  let assignmentOne := assignment.weakenFree SetSort.set
  let updatedOne := updated.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((updated ∈ₘ assignment_space_term carrier) ∧ₘ
    ((updated ·ₘ bound_var_codeₘ(numₘ(0))) ≐ₘ value)) ∧ₘ
    ((((index ∈ₘ ωₘ) ⟶ₘ
      (((updatedOne ·ₘ free_var_codeₘ(index)) ≐ₘ
          (assignmentOne ·ₘ free_var_codeₘ(index))) ∧ₘ
        ((updatedOne ·ₘ bound_var_codeₘ(Sₘ(index))) ≐ₘ
          (assignmentOne ·ₘ bound_var_codeₘ(index)))))
      |>.forallFreeTop SetSort.set))

private def updated_satisfaction_witness_condition {bound free : SetContext}
    (stage carrier interpretation symbols assignment body value :
      SetTerm bound free) : SetFormula bound free :=
  let stageOne := stage.weakenFree SetSort.set
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let assignmentOne := assignment.weakenFree SetSort.set
  let bodyOne := body.weakenFree SetSort.set
  let valueOne := value.weakenFree SetSort.set
  let updated : SetTerm bound (SetSort.set :: free) := .fvar .here
  (assignment_update_condition carrierOne assignmentOne valueOne updated ∧ₘ
    satisfies_stageₘ(stageOne, carrierOne, interpretationOne, symbolsOne,
      updated, bodyOne)).existsFreeTop SetSort.set

private def universal_body_satisfaction_condition {bound free : SetContext}
    (stage carrier interpretation symbols assignment body : SetTerm bound free) :
    SetFormula bound free :=
  let stageOne := stage.weakenFree SetSort.set
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let assignmentOne := assignment.weakenFree SetSort.set
  let bodyOne := body.weakenFree SetSort.set
  let value : SetTerm bound (SetSort.set :: free) := .fvar .here
  (((value ∈ₘ carrierOne) ⟶ₘ
    updated_satisfaction_witness_condition stageOne carrierOne interpretationOne
      symbolsOne assignmentOne bodyOne value).forallFreeTop SetSort.set)

/-! ## 分阶段满足关系 -/

def negation_satisfaction_successor_condition {bound free : SetContext}
    (stage carrier interpretation symbols assignment formula :
      SetTerm bound free) : SetFormula bound free :=
  let stageOne := stage.weakenFree SetSort.set
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let assignmentOne := assignment.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  (((body ∈ₘ FormulaStageₘ(symbolsOne, stageOne)) ∧ₘ
    (formulaOne ≐ₘ neg_codeₘ(body))) ∧ₘ
    ¬ₘ satisfies_stageₘ(stageOne, carrierOne, interpretationOne, symbolsOne,
      assignmentOne, body)).existsFreeTop SetSort.set

def implication_satisfaction_successor_condition {bound free : SetContext}
    (stage carrier interpretation symbols assignment formula :
      SetTerm bound free) : SetFormula bound free :=
  let stageTwo := weaken_set_two stage
  let carrierTwo := weaken_set_two carrier
  let interpretationTwo := weaken_set_two interpretation
  let symbolsTwo := weaken_set_two symbols
  let assignmentTwo := weaken_set_two assignment
  let formulaTwo := weaken_set_two formula
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  exists_set_two ((((left ∈ₘ FormulaStageₘ(symbolsTwo, stageTwo)) ∧ₘ
    (right ∈ₘ FormulaStageₘ(symbolsTwo, stageTwo))) ∧ₘ
    (formulaTwo ≐ₘ imp_codeₘ(left, right))) ∧ₘ
    (¬ₘ satisfies_stageₘ(stageTwo, carrierTwo, interpretationTwo, symbolsTwo,
      assignmentTwo, left) ∨ₘ
      satisfies_stageₘ(stageTwo, carrierTwo, interpretationTwo, symbolsTwo,
        assignmentTwo, right)))

def universal_satisfaction_successor_condition {bound free : SetContext}
    (stage carrier interpretation symbols assignment formula :
      SetTerm bound free) : SetFormula bound free :=
  let stageOne := stage.weakenFree SetSort.set
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let assignmentOne := assignment.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  (((body ∈ₘ FormulaStageₘ(symbolsOne, stageOne)) ∧ₘ
    (formulaOne ≐ₘ all_codeₘ(body))) ∧ₘ
    universal_body_satisfaction_condition stageOne carrierOne interpretationOne
      symbolsOne assignmentOne body).existsFreeTop SetSort.set

def formula_satisfaction_successor_condition {bound free : SetContext}
    (stage carrier interpretation symbols assignment formula :
      SetTerm bound free) : SetFormula bound free :=
  atomic_satisfiesₘ(carrier, interpretation, symbols, assignment, formula) ∨ₘ
    (negation_satisfaction_successor_condition
      stage carrier interpretation symbols assignment formula ∨ₘ
      (implication_satisfaction_successor_condition
        stage carrier interpretation symbols assignment formula ∨ₘ
        universal_satisfaction_successor_condition
          stage carrier interpretation symbols assignment formula))

def formula_satisfaction_at_stage_condition {bound free : SetContext}
    (stage carrier interpretation symbols assignment formula :
      SetTerm bound free) : SetFormula bound free :=
  let stageOne := stage.weakenFree SetSort.set
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let assignmentOne := assignment.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let predecessor : SetTerm bound (SetSort.set :: free) := .fvar .here
  let successorCase :=
    (((predecessor ∈ₘ ωₘ) ∧ₘ (stageOne ≐ₘ Sₘ(predecessor))) ∧ₘ
      formula_satisfaction_successor_condition predecessor carrierOne
        interpretationOne symbolsOne assignmentOne formulaOne)
      |>.existsFreeTop SetSort.set
  ((structureₘ(carrier, interpretation, symbols) ∧ₘ
      (assignment ∈ₘ assignment_space_term carrier)) ∧ₘ
    ((stage ∈ₘ ωₘ) ∧ₘ (formula ∈ₘ FormulaStageₘ(symbols, stage)))) ∧ₘ
    (((stage ≐ₘ numₘ(0)) ∧ₘ
      atomic_satisfiesₘ(carrier, interpretation, symbols, assignment, formula)) ∨ₘ
      successorCase)

def formula_satisfaction_at_stage_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let stage : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there (.there .here)))))
     let carrier : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there .here))))
     let interpretation : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there .here)))
     let symbols : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let assignment : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] := .fvar (.there .here)
     let formula : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
          SetSort.set, SetSort.set] := .fvar .here
     satisfies_stageₘ(stage, carrier, interpretation, symbols, assignment, formula) ↔ₘ
       formula_satisfaction_at_stage_condition
         stage carrier interpretation symbols assignment formula)

def formula_satisfaction_condition {bound free : SetContext}
    (carrier interpretation symbols assignment formula : SetTerm bound free) :
    SetFormula bound free :=
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let assignmentOne := assignment.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let stage : SetTerm bound (SetSort.set :: free) := .fvar .here
  (formula ∈ₘ RelFormulaCodeₘ(symbols)) ∧ₘ
    ((((stage ∈ₘ ωₘ) ∧ₘ
      (formulaOne ∈ₘ FormulaStageₘ(symbolsOne, stage))) ∧ₘ
      satisfies_stageₘ(stage, carrierOne, interpretationOne, symbolsOne,
        assignmentOne, formulaOne)).existsFreeTop SetSort.set)

def formula_satisfaction_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let carrier : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there (.there .here))))
     let interpretation : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there .here)))
     let symbols : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let assignment : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there .here)
     let formula : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar .here
     satisfies_codeₘ(carrier, interpretation, symbols, assignment, formula) ↔ₘ
       formula_satisfaction_condition
         carrier interpretation symbols assignment formula)

/-! ## 真、模型与语义后承 -/

def truth_condition {bound free : SetContext}
    (carrier interpretation symbols formula : SetTerm bound free) :
    SetFormula bound free :=
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let formulaOne := formula.weakenFree SetSort.set
  let assignment : SetTerm bound (SetSort.set :: free) := .fvar .here
  (structureₘ(carrier, interpretation, symbols) ∧ₘ
    (formula ∈ₘ RelFormulaCodeₘ(symbols))) ∧ₘ
    (((assignment ∈ₘ assignment_space_term carrierOne) ⟶ₘ
      satisfies_codeₘ(carrierOne, interpretationOne, symbolsOne,
        assignment, formulaOne)).forallFreeTop SetSort.set)

def truth_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let carrier : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there .here)))
     let interpretation : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let symbols : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there .here)
     let formula : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] := .fvar .here
     true_inₘ(carrier, interpretation, symbols, formula) ↔ₘ
       truth_condition carrier interpretation symbols formula)

def model_condition {bound free : SetContext}
    (carrier interpretation symbols theory : SetTerm bound free) :
    SetFormula bound free :=
  let carrierOne := carrier.weakenFree SetSort.set
  let interpretationOne := interpretation.weakenFree SetSort.set
  let symbolsOne := symbols.weakenFree SetSort.set
  let theoryOne := theory.weakenFree SetSort.set
  let formula : SetTerm bound (SetSort.set :: free) := .fvar .here
  (structureₘ(carrier, interpretation, symbols) ∧ₘ
    (theory ⊆ₘ RelFormulaCodeₘ(symbols))) ∧ₘ
    (((formula ∈ₘ theoryOne) ⟶ₘ
      true_inₘ(carrierOne, interpretationOne, symbolsOne, formula))
      |>.forallFreeTop SetSort.set)

def model_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let carrier : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there (.there .here)))
     let interpretation : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there (.there .here))
     let symbols : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
       .fvar (.there .here)
     let theory : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set, SetSort.set] := .fvar .here
     model_ofₘ(carrier, interpretation, symbols, theory) ↔ₘ
       model_condition carrier interpretation symbols theory)

def logical_consequence_condition {bound free : SetContext}
    (symbols theory conclusion : SetTerm bound free) : SetFormula bound free :=
  let symbolsTwo := weaken_set_two symbols
  let theoryTwo := weaken_set_two theory
  let conclusionTwo := weaken_set_two conclusion
  let carrier : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let interpretation : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  ((symbols ⊆ₘ NonlogicalSymₘ) ∧ₘ
    ((theory ⊆ₘ RelFormulaCodeₘ(symbols)) ∧ₘ
      (conclusion ∈ₘ RelFormulaCodeₘ(symbols)))) ∧ₘ
    forall_set_two
      (structureₘ(carrier, interpretation, symbolsTwo) ⟶ₘ
        (model_ofₘ(carrier, interpretation, symbolsTwo, theoryTwo) ⟶ₘ
          true_inₘ(carrier, interpretation, symbolsTwo, conclusionTwo)))

def theorem_condition {bound free : SetContext}
    (symbols formula : SetTerm bound free) : SetFormula bound free :=
  let symbolsTwo := weaken_set_two symbols
  let formulaTwo := weaken_set_two formula
  let carrier : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let interpretation : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  ((symbols ⊆ₘ NonlogicalSymₘ) ∧ₘ
    (formula ∈ₘ RelFormulaCodeₘ(symbols))) ∧ₘ
    forall_set_two
      (structureₘ(carrier, interpretation, symbolsTwo) ⟶ₘ
        true_inₘ(carrier, interpretation, symbolsTwo, formulaTwo))

def semantic_truth_definition_axiom : SetSentence :=
  let consequenceAxiom : SetSentence :=
    Metatheory.Formula.forall_close
      (let symbols : SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set] :=
         .fvar (.there (.there .here))
       let theory : SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set] := .fvar (.there .here)
       let conclusion : SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set] := .fvar .here
       semantic_consequenceₘ(symbols, theory, conclusion) ↔ₘ
         logical_consequence_condition symbols theory conclusion)
  let validityAxiom : SetSentence :=
    Metatheory.Formula.forall_close
      (let symbols : SetOpenTerm [SetSort.set, SetSort.set] :=
         .fvar (.there .here)
       let formula : SetOpenTerm [SetSort.set, SetSort.set] := .fvar .here
       valid_codeₘ(symbols, formula) ↔ₘ theorem_condition symbols formula)
  consequenceAxiom ∧ₘ validityAxiom

/-! ## 理论组合 -/

def formula_stage_semantics_theory : SetTheory :=
  Theory.insert formula_stage_set_definition_axiom semantic_interpretation_theory

def atomic_satisfaction_semantics_theory : SetTheory :=
  Theory.insert atomic_satisfaction_definition_axiom formula_stage_semantics_theory

def staged_satisfaction_semantics_theory : SetTheory :=
  Theory.insert formula_satisfaction_at_stage_definition_axiom
    atomic_satisfaction_semantics_theory

def formula_satisfaction_semantics_theory : SetTheory :=
  Theory.insert formula_satisfaction_definition_axiom staged_satisfaction_semantics_theory

def tarski_truth_model_theory : SetTheory :=
  Theory.insert (truth_definition_axiom ∧ₘ model_definition_axiom)
    formula_satisfaction_semantics_theory

def tarski_truth_theory : SetTheory :=
  Theory.insert semantic_truth_definition_axiom tarski_truth_model_theory

derive_theory_subset semantic_interpretation_theory ⊆ formula_stage_semantics_theory

derive_theory_subset formula_stage_semantics_theory ⊆ atomic_satisfaction_semantics_theory

derive_theory_subset atomic_satisfaction_semantics_theory ⊆ staged_satisfaction_semantics_theory

derive_theory_subset staged_satisfaction_semantics_theory ⊆ formula_satisfaction_semantics_theory

derive_theory_subset formula_satisfaction_semantics_theory ⊆ tarski_truth_model_theory

derive_theory_subset tarski_truth_model_theory ⊆ tarski_truth_theory

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
