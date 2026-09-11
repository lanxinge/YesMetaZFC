import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmeticBound
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalNumeral
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.ClosedTransport

/-!
# 按深度索引的一阶结构语法编码

语法码采用 Quine 风格带标签配对，不再经过符号串、括号、拼接或 flatten：

* 每个节点是 `S(pair(tag, payload))`；
* 参数列使用独立的 `nil/cons` 标签；
* 项码、参数列码和公式码都显式索引 de Bruijn 深度；
* bound 变量分支直接要求下标属于当前深度。

三个对象谓词由严格子码递归方程定义。所有见证都限制在 `ω`，配对坐标界保证递归
调用落到严格更小的自然数，因此该语法核在任意模型内部都按模型自身的自然数绝对有界。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols

set_option autoImplicit false

/-! ## 结构码构造 -/

/-- 全局互异的结构构造子标签。 -/
inductive StructuralCodeTag where
  | listNil
  | listCons
  | freeVariable
  | boundVariable
  | constant
  | application
  | equality
  | membership
  | predicate
  | negation
  | implication
  | universal
  deriving DecidableEq, Repr

/-- 结构标签的标准自然数编号。 -/
def structural_code_tag : StructuralCodeTag → Nat
  | .listNil => 0
  | .listCons => 1
  | .freeVariable => 2
  | .boundVariable => 3
  | .constant => 4
  | .application => 5
  | .equality => 6
  | .membership => 7
  | .predicate => 8
  | .negation => 9
  | .implication => 10
  | .universal => 11

/-- 一个带标签的原始结构节点。 -/
abbrev structural_raw_node_code_term {bound free : SetContext}
    (tag : StructuralCodeTag) (payload : SetTerm bound free) :
    SetTerm bound free :=
  Sₘ(godel_pairₘ(numₘ(structural_code_tag tag), payload))

/-- Quine 参数列编码。 -/
def structural_list_code_term {bound free : SetContext} :
    List (SetTerm bound free) → SetTerm bound free
  | [] => structural_raw_node_code_term .listNil ∅ₘ
  | head :: tail =>
      structural_raw_node_code_term .listCons
        (godel_pairₘ(head, structural_list_code_term tail))

/-- 语法节点的字段由同一 Quine 参数列编码承载。 -/
abbrev structural_node_code_term {bound free : SetContext}
    (tag : StructuralCodeTag) (fields : List (SetTerm bound free)) :
    SetTerm bound free :=
  structural_raw_node_code_term tag (structural_list_code_term fields)

/-- 原始结构节点与类型化替换交换。 -/
@[simp] theorem structural_raw_node_code_term_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree)
    (tag : StructuralCodeTag)
    (payload : SetTerm sourceBound sourceFree) :
    (structural_raw_node_code_term tag payload).substituteMapped
        boundSubstitution freeSubstitution =
      structural_raw_node_code_term tag
        (payload.substituteMapped boundSubstitution freeSubstitution) := by
  simp [structural_raw_node_code_term, Term.substituteMapped,
    Arguments.substituteMapped]

/-- 结构字段列编码逐项保持类型化替换。 -/
@[simp] theorem structural_list_code_term_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree)
    (fields : List (SetTerm sourceBound sourceFree)) :
    (structural_list_code_term fields).substituteMapped
        boundSubstitution freeSubstitution =
      structural_list_code_term
        (fields.map fun field =>
          field.substituteMapped boundSubstitution freeSubstitution) := by
  induction fields with
  | nil =>
      simp [structural_list_code_term, Term.substituteMapped,
        Arguments.substituteMapped]
  | cons head tail ih =>
      simp [structural_list_code_term, Term.substituteMapped,
        Arguments.substituteMapped, ih]

/-- 完整结构节点在替换下只需变换字段。 -/
@[simp] theorem structural_node_code_term_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree)
    (tag : StructuralCodeTag)
    (fields : List (SetTerm sourceBound sourceFree)) :
    (structural_node_code_term tag fields).substituteMapped
        boundSubstitution freeSubstitution =
      structural_node_code_term tag
        (fields.map fun field =>
          field.substituteMapped boundSubstitution freeSubstitution) := by
  simp [structural_node_code_term]

abbrev free_variable_code_term {bound free : SetContext}
    (index : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .freeVariable [index]

abbrev bound_variable_code_term {bound free : SetContext}
    (index : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .boundVariable [index]

abbrev constant_code_term {bound free : SetContext}
    (symbol : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .constant [symbol]

abbrev application_code_term {bound free : SetContext}
    (arity symbol arguments : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .application [arity, symbol, arguments]

abbrev equality_formula_code_term {bound free : SetContext}
    (left right : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .equality [left, right]

abbrev membership_formula_code_term {bound free : SetContext}
    (left right : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .membership [left, right]

abbrev predicate_formula_code_term {bound free : SetContext}
    (arity symbol arguments : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .predicate [arity, symbol, arguments]

abbrev negation_formula_code_term {bound free : SetContext}
    (body : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .negation [body]

abbrev implication_formula_code_term {bound free : SetContext}
    (left right : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .implication [left, right]

abbrev universal_formula_code_term {bound free : SetContext}
    (body : SetTerm bound free) : SetTerm bound free :=
  structural_node_code_term .universal [body]

namespace Symbols

scoped notation:max "code_nilₘ" => structural_list_code_term []
scoped notation:max "code_consₘ(" head ", " tail ")" =>
  structural_raw_node_code_term StructuralCodeTag.listCons
    (godel_pairₘ(head, tail))
scoped notation:max "free_var_codeₘ(" index ")" =>
  free_variable_code_term index
scoped notation:max "bound_var_codeₘ(" index ")" =>
  bound_variable_code_term index
scoped notation:max "const_codeₘ(" symbol ")" =>
  constant_code_term symbol
scoped notation:max
  "app_codeₘ(" arity ", " symbol ", " arguments ")" =>
  application_code_term arity symbol arguments
scoped notation:max "eq_codeₘ(" left ", " right ")" =>
  equality_formula_code_term left right
scoped notation:max "mem_codeₘ(" left ", " right ")" =>
  membership_formula_code_term left right
scoped notation:max
  "pred_codeₘ(" arity ", " symbol ", " arguments ")" =>
  predicate_formula_code_term arity symbol arguments
scoped notation:max "neg_codeₘ(" body ")" =>
  negation_formula_code_term body
scoped notation:max "imp_codeₘ(" left ", " right ")" =>
  implication_formula_code_term left right
scoped notation:max "all_codeₘ(" body ")" =>
  universal_formula_code_term body

end Symbols
open scoped Symbols

/-- 当前结构语法核的公式码承载集合。

它只作为公式码的对象载体；每个元素的精确结构合法性仍由
`formula_code_atₘ` 检查，不把承载集合本身当作语法正确性的替代品。
-/
abbrev syntax_formula_code_set_term {bound free : SetContext} :
    SetTerm bound free :=
  Term.embedClosed bound free
    (related_formula_set_term related_nonlogical_symbol_set_term)

/-- 当前结构语法核的项码承载集合。 -/
abbrev syntax_term_code_set_term {bound free : SetContext} :
    SetTerm bound free :=
  Term.embedClosed bound free
    (related_term_set_term related_nonlogical_symbol_set_term)

/-! ## 上下文提升快路径 -/

def term_weaken_free_two {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: free) SetSort.set SetSort.set
    (@Term.weakenFree signature bound free
      SetSort.set SetSort.set term)

def term_weaken_free_three {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: SetSort.set :: free) SetSort.set SetSort.set
    (@Term.weakenFree signature bound
      (SetSort.set :: free) SetSort.set SetSort.set
      (@Term.weakenFree signature bound free
        SetSort.set SetSort.set term))

/-! ## 项码递归方程 -/

def term_code_free_variable_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeOne := code.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((index ∈ₘ ωₘ) ∧ₘ (codeOne ≐ₘ free_var_codeₘ(index)))
    |>.existsFreeTop SetSort.set

def term_code_bound_variable_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  let depthOne := depth.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((index ∈ₘ depthOne) ∧ₘ (codeOne ≐ₘ bound_var_codeₘ(index)))
    |>.existsFreeTop SetSort.set

def term_code_constant_condition {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  let codeOne := code.weakenFree SetSort.set
  let symbol : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((symbol ∈ₘ ωₘ) ∧ₘ (codeOne ≐ₘ const_codeₘ(symbol)))
    |>.existsFreeTop SetSort.set

def term_code_application_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  let depthThree := term_weaken_free_three depth
  let codeThree := term_weaken_free_three code
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let arguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
    (term_list_code_atₘ(depthThree, arity, arguments) ∧ₘ
      (codeThree ≐ₘ app_codeₘ(arity, symbol, arguments))))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 在给定 de Bruijn 深度下的项码一步条件。 -/
def term_code_at_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  ((depth ∈ₘ ωₘ) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    (term_code_free_variable_condition code ∨ₘ
      (term_code_bound_variable_condition depth code ∨ₘ
        (term_code_constant_condition code ∨ₘ
          term_code_application_condition depth code)))

/-- 项码递归定义实例。 -/
def term_code_at_definition_instance {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  term_code_atₘ(depth, code) ↔ₘ term_code_at_condition depth code

/-! ## 参数列码递归方程 -/

def term_list_code_cons_condition {bound free : SetContext}
    (depth length code : SetTerm bound free) : SetFormula bound free :=
  let depthThree := term_weaken_free_three depth
  let lengthThree := term_weaken_free_three length
  let codeThree := term_weaken_free_three code
  let previousLength : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  let head : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let tail : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  (((previousLength ∈ₘ ωₘ) ∧ₘ
      (lengthThree ≐ₘ Sₘ(previousLength))) ∧ₘ
    ((term_code_atₘ(depthThree, head) ∧ₘ
      term_list_code_atₘ(depthThree, previousLength, tail)) ∧ₘ
      (codeThree ≐ₘ code_consₘ(head, tail))))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 在给定深度和长度下的参数列码一步条件。 -/
def term_list_code_at_condition {bound free : SetContext}
    (depth length code : SetTerm bound free) : SetFormula bound free :=
  (((depth ∈ₘ ωₘ) ∧ₘ (length ∈ₘ ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    (((length ≐ₘ numₘ(0)) ∧ₘ (code ≐ₘ code_nilₘ)) ∨ₘ
      term_list_code_cons_condition depth length code)

/-- 参数列码递归定义实例。 -/
def term_list_code_at_definition_instance {bound free : SetContext}
    (depth length code : SetTerm bound free) : SetFormula bound free :=
  term_list_code_atₘ(depth, length, code) ↔ₘ
    term_list_code_at_condition depth length code

/-! ## 公式码递归方程 -/

def formula_code_binary_atomic_condition {bound free : SetContext}
    (tag : StructuralCodeTag) (depth code : SetTerm bound free) :
    SetFormula bound free :=
  let depthTwo := term_weaken_free_two depth
  let codeTwo := term_weaken_free_two code
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  let target :=
    structural_node_code_term tag [left, right]
  ((term_code_atₘ(depthTwo, left) ∧ₘ
      term_code_atₘ(depthTwo, right)) ∧ₘ
    (codeTwo ≐ₘ target))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def formula_code_predicate_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  let depthThree := term_weaken_free_three depth
  let codeThree := term_weaken_free_three code
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let arguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
    (term_list_code_atₘ(depthThree, arity, arguments) ∧ₘ
      (codeThree ≐ₘ pred_codeₘ(arity, symbol, arguments))))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def formula_code_negation_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  let depthOne := depth.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  (formula_code_atₘ(depthOne, body) ∧ₘ
    (codeOne ≐ₘ neg_codeₘ(body)))
    |>.existsFreeTop SetSort.set

def formula_code_implication_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  let depthTwo := term_weaken_free_two depth
  let codeTwo := term_weaken_free_two code
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  ((formula_code_atₘ(depthTwo, left) ∧ₘ
      formula_code_atₘ(depthTwo, right)) ∧ₘ
    (codeTwo ≐ₘ imp_codeₘ(left, right)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

def formula_code_universal_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  let depthOne := depth.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  (formula_code_atₘ(Sₘ(depthOne), body) ∧ₘ
    (codeOne ≐ₘ all_codeₘ(body)))
    |>.existsFreeTop SetSort.set

/-- 在给定 de Bruijn 深度下的公式码一步条件。 -/
def formula_code_at_condition {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  ((depth ∈ₘ ωₘ) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    (formula_code_binary_atomic_condition .equality depth code ∨ₘ
      (formula_code_binary_atomic_condition .membership depth code ∨ₘ
        (formula_code_predicate_condition depth code ∨ₘ
          (formula_code_negation_condition depth code ∨ₘ
            (formula_code_implication_condition depth code ∨ₘ
              formula_code_universal_condition depth code)))))

/-- 公式码递归定义实例。 -/
def formula_code_at_definition_instance {bound free : SetContext}
    (depth code : SetTerm bound free) : SetFormula bound free :=
  formula_code_atₘ(depth, code) ↔ₘ
    formula_code_at_condition depth code

/-! ## 替换自然性快路径 -/

@[simp] theorem term_code_at_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (depth code : SetTerm bound sourceFree) :
    (term_code_at_definition_instance depth code).substituteFree τ =
      term_code_at_definition_instance
        (depth.substituteFree τ) (code.substituteFree τ) := by
  simp [term_code_at_definition_instance, term_code_at_condition,
    term_code_free_variable_condition, term_code_bound_variable_condition,
    term_code_constant_condition, term_code_application_condition,
    term_weaken_free_three, structural_list_code_term,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree]
  repeat' constructor

@[simp] theorem term_list_code_at_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (depth length code : SetTerm bound sourceFree) :
    (term_list_code_at_definition_instance depth length code).substituteFree τ =
      term_list_code_at_definition_instance
        (depth.substituteFree τ) (length.substituteFree τ)
        (code.substituteFree τ) := by
  simp [term_list_code_at_definition_instance, term_list_code_at_condition,
    term_list_code_cons_condition, term_weaken_free_three,
    structural_list_code_term, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteFree,
    Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree]
  repeat' constructor

@[simp] theorem formula_code_at_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (depth code : SetTerm bound sourceFree) :
    (formula_code_at_definition_instance depth code).substituteFree τ =
      formula_code_at_definition_instance
        (depth.substituteFree τ) (code.substituteFree τ) := by
  simp [formula_code_at_definition_instance, formula_code_at_condition,
    formula_code_binary_atomic_condition, formula_code_predicate_condition,
    formula_code_negation_condition, formula_code_implication_condition,
    formula_code_universal_condition, term_weaken_free_two,
    term_weaken_free_three,
    structural_list_code_term, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteFree,
    Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree]
  repeat' constructor

/-! ## 递归定义公理与理论 -/

def structural_syntax_definition_axiom : SetSentence :=
  let termPart := Metatheory.Formula.forall_close
    (term_code_at_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))
  let listPart := Metatheory.Formula.forall_close
    (term_list_code_at_definition_instance
      (.fvar (.there (.there .here)) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm
        [SetSort.set, SetSort.set, SetSort.set]))
  let formulaPart := Metatheory.Formula.forall_close
    (formula_code_at_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))
  (termPart ∧ₘ listPart) ∧ₘ formulaPart

/-- 新形式语言编码理论只增加三条互递归结构方程。 -/
def formal_language_encoding_theory : SetTheory :=
  Theory.insert structural_syntax_definition_axiom
    (Theory.union successor_operator_theory natural_addition_bound_theory)

derive_theory_subset natural_addition_bound_theory ⊆ formal_language_encoding_theory

/-- 配数核心理论经算术有界层嵌入形式语言编码理论。 -/
derive_theory_subset godel_pairing_core_theory ⊆ formal_language_encoding_theory

derive_theory_subset successor_operator_theory ⊆ formal_language_encoding_theory

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
