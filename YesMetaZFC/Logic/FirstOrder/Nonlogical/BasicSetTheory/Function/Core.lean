import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationComposition

/-!
# 等价关系、函数与映射：核心

本模块只定义函数层的类型化公式、闭定义公理和理论边界。量词变量由 free 上下文
逐层引入；函数项与谓词项天然良构，不再携带 admissibility、闭性或变量编号证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 等价关系 -/

/-- 关系在其定义域上自反。 -/
def relation_reflexive_on_domain_condition {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  let x : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((x ∈ₘ domₘ(relation.weakenFree SetSort.set)) ⟶ₘ
    (⟨x, x⟩ₘ ∈ₘ relation.weakenFree SetSort.set))
    |>.forallFreeTop SetSort.set

/-- 关系在其定义域上对称。 -/
def relation_symmetric_on_domain_condition {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  let x : SetTerm bound (SetSort.set :: free) := .fvar .here
  let y : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let x' := x.weakenFree SetSort.set
  let relation' := (relation.weakenFree SetSort.set).weakenFree SetSort.set
  ((((x' ∈ₘ domₘ(relation')) ∧ₘ (y ∈ₘ domₘ(relation'))) ⟶ₘ
      ((⟨x', y⟩ₘ ∈ₘ relation') ⟶ₘ (⟨y, x'⟩ₘ ∈ₘ relation')))
    |>.forallFreeTop SetSort.set)
    |>.forallFreeTop SetSort.set

/-- 关系在其定义域上传递。 -/
def relation_transitive_on_domain_condition {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  let x : SetTerm bound (SetSort.set :: free) := .fvar .here
  let y : SetTerm bound (SetSort.set :: SetSort.set :: free) := .fvar .here
  let z : SetTerm bound
      (SetSort.set :: SetSort.set :: SetSort.set :: free) := .fvar .here
  let x' := (x.weakenFree SetSort.set).weakenFree SetSort.set
  let y' := y.weakenFree SetSort.set
  let relation' := ((relation.weakenFree SetSort.set).weakenFree
    SetSort.set).weakenFree SetSort.set
  ((((((x' ∈ₘ domₘ(relation')) ∧ₘ (y' ∈ₘ domₘ(relation'))) ∧ₘ
        (z ∈ₘ domₘ(relation'))) ⟶ₘ
      (((⟨x', y'⟩ₘ ∈ₘ relation') ∧ₘ (⟨y', z⟩ₘ ∈ₘ relation')) ⟶ₘ
        (⟨x', z⟩ₘ ∈ₘ relation')))
    |>.forallFreeTop SetSort.set)
    |>.forallFreeTop SetSort.set)
    |>.forallFreeTop SetSort.set

/-- 等价关系由关系性、同一载体、非空、自反、对称与传递组成。 -/
def is_equivalence_relation_condition {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  is_relation_formula relation ∧ₘ
    ((domₘ(relation) ≐ₘ ranₘ(relation)) ∧ₘ
      (set_has_member (domₘ(relation)) ∧ₘ
        (relation_reflexive_on_domain_condition relation ∧ₘ
          (relation_symmetric_on_domain_condition relation ∧ₘ
            relation_transitive_on_domain_condition relation))))

def is_equivalence_relation_definition_instance {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  is_equivalence_relation_formula relation ↔ₘ
    is_equivalence_relation_condition relation

def is_equivalence_relation_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_equivalence_relation_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-! ## 函数与映射 -/

/-- 固定输入与两个候选值后的单值条件。 -/
def function_single_valued_at_values {bound free : SetContext}
    (function input left right : SetTerm bound free) :
    SetFormula bound free :=
  ((⟨input, left⟩ₘ ∈ₘ function) ∧ₘ
    (⟨input, right⟩ₘ ∈ₘ function)) ⟶ₘ (left ≐ₘ right)

/-- 固定输入后，对两个候选值量化的单值条件。 -/
def function_single_valued_at_left {bound free : SetContext}
    (function input left : SetTerm bound free) : SetFormula bound free :=
  let right : SetTerm bound (SetSort.set :: free) := .fvar .here
  (function_single_valued_at_values
    (function.weakenFree SetSort.set)
    (input.weakenFree SetSort.set)
    (left.weakenFree SetSort.set) right)
    |>.forallFreeTop SetSort.set

/-- 固定输入后，对两个候选值量化的单值条件。 -/
def function_single_valued_at_input {bound free : SetContext}
    (function input : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: free) := .fvar .here
  (function_single_valued_at_left
    (function.weakenFree SetSort.set)
    (input.weakenFree SetSort.set) left)
    |>.forallFreeTop SetSort.set

/-- 一个关系是单值的。 -/
def function_single_valued_condition {bound free : SetContext}
    (function : SetTerm bound free) : SetFormula bound free :=
  let input : SetTerm bound (SetSort.set :: free) := .fvar .here
  (function_single_valued_at_input
    (function.weakenFree SetSort.set) input)
    |>.forallFreeTop SetSort.set

/-- 输入参数槽实例化后恢复原上下文条件。 -/
@[simp] theorem function_single_valued_at_input_instantiateFreeTop_context
    {bound free : SetContext}
    (function input : SetTerm bound free) :
    (function_single_valued_at_input
      (function.weakenFree SetSort.set)
      (.fvar .here : SetTerm bound (SetSort.set :: free))).instantiateFreeTop
        input =
      function_single_valued_at_input function input := by
  unfold function_single_valued_at_input
    function_single_valued_at_left
    function_single_valued_at_values
  rw [Formula.instantiateFreeTop_forallFreeTop]
  simp [Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop]

/-- 左值参数槽实例化后恢复原上下文条件。 -/
@[simp] theorem function_single_valued_at_left_instantiateFreeTop_context
    {bound free : SetContext}
    (function input left : SetTerm bound free) :
    (function_single_valued_at_left
      (function.weakenFree SetSort.set)
      (input.weakenFree SetSort.set)
      (.fvar .here : SetTerm bound (SetSort.set :: free))).instantiateFreeTop
        left =
      function_single_valued_at_left function input left := by
  unfold function_single_valued_at_left
    function_single_valued_at_values
  rw [Formula.instantiateFreeTop_forallFreeTop]
  simp [Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop]

/-- 右值参数槽实例化后恢复点态单值条件。 -/
@[simp] theorem function_single_valued_at_values_instantiateFreeTop_context
    {bound free : SetContext}
    (function input left right : SetTerm bound free) :
    (function_single_valued_at_values
      (function.weakenFree SetSort.set)
      (input.weakenFree SetSort.set)
      (left.weakenFree SetSort.set)
      (.fvar .here : SetTerm bound (SetSort.set :: free))).instantiateFreeTop
        right =
      function_single_valued_at_values function input left right := by
  unfold function_single_valued_at_values
  simp
  rw [Term.instantiateFreeTop_fvar_here]
  constructor <;> rfl

/-- 集合编码函数是单值关系。 -/
def is_function_condition {bound free : SetContext}
    (function : SetTerm bound free) : SetFormula bound free :=
  is_relation_formula function ∧ₘ function_single_valued_condition function

def is_function_definition_instance {bound free : SetContext}
    (function : SetTerm bound free) : SetFormula bound free :=
  is_function_formula function ↔ₘ is_function_condition function

def is_function_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_function_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-- `function` 是从 `source` 映入 `target` 的映射。 -/
def is_mapping_condition {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_function_formula function ∧ₘ
    ((source ≐ₘ domₘ(function)) ∧ₘ (ranₘ(function) ⊆ₘ target))

def is_mapping_definition_instance {bound free : SetContext}
    (function source target : SetTerm bound free) : SetFormula bound free :=
  is_mapping_formula function source target ↔ₘ
    is_mapping_condition function source target

def is_mapping_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_mapping_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 函数求值 -/

/-- 求值函数符号只在函数及定义域成员 guard 下服从图合同。 -/
def function_application_definition_instance {bound free : SetContext}
    (function argument value : SetTerm bound free) : SetFormula bound free :=
  (is_function_formula function ∧ₘ (argument ∈ₘ domₘ(function))) ⟶ₘ
    ((value ≐ₘ (function ·ₘ argument)) ↔ₘ
      (⟨argument, value⟩ₘ ∈ₘ function))

def function_application_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (function_application_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-- 函数图成员的规范投影条件。 -/
def function_graph_member_condition {bound free : SetContext}
    (function member : SetTerm bound free) : SetFormula bound free :=
  is_ordered_pair_formula member ∧ₘ
    (((member)₀ₘ ∈ₘ domₘ(function)) ∧ₘ
      ((member)₁ₘ ≐ₘ (function ·ₘ (member)₀ₘ)))

/-- 两个函数具有同一定义域且逐点相等。 -/
def function_extensional_agreement {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let input : SetTerm bound (SetSort.set :: free) := .fvar .here
  (domₘ(left) ≐ₘ domₘ(right)) ∧ₘ
    (((input ∈ₘ domₘ(left.weakenFree SetSort.set)) ⟶ₘ
      ((left.weakenFree SetSort.set ·ₘ input) ≐ₘ
        (right.weakenFree SetSort.set ·ₘ input)))
      |>.forallFreeTop SetSort.set)

/-! ## 理论边界 -/

def equivalence_relation_theory : SetTheory :=
  Theory.insert is_equivalence_relation_definition_axiom
    relation_composition_operator_theory

def function_predicate_theory : SetTheory :=
  Theory.insert is_function_definition_axiom equivalence_relation_theory

def mapping_predicate_theory : SetTheory :=
  Theory.insert is_mapping_definition_axiom function_predicate_theory

def function_application_theory : SetTheory :=
  Theory.insert function_application_definition_axiom mapping_predicate_theory

derive_theory_subset relation_composition_operator_theory ⊆ equivalence_relation_theory

derive_theory_subset equivalence_relation_theory ⊆ function_predicate_theory

derive_theory_subset function_predicate_theory ⊆ mapping_predicate_theory

derive_theory_subset mapping_predicate_theory ⊆ function_application_theory

derive_theory_subset relation_composition_operator_theory ⊆ function_predicate_theory

derive_theory_subset relation_function_theory ⊆ function_predicate_theory

derive_theory_subset relation_predicate_theory ⊆ function_predicate_theory

derive_theory_subset relation_composition_operator_theory ⊆ function_application_theory

/-! ## 项自然性 -/

/-- 关系定义域项与任意 bound/free 重命名严格交换。 -/
@[simp] theorem domain_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (relation : SetTerm sourceBound sourceFree) :
    (domₘ(relation)).renameMapped boundRenaming freeRenaming =
      domₘ(relation.renameMapped boundRenaming freeRenaming) := by
  simp [domain_term, Term.renameMapped, Arguments.renameMapped]

/-- 函数求值项与任意 bound/free 重命名严格交换。 -/
@[simp] theorem function_application_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (function argument : SetTerm sourceBound sourceFree) :
    (function ·ₘ argument).renameMapped boundRenaming freeRenaming =
      (function.renameMapped boundRenaming freeRenaming ·ₘ
        argument.renameMapped boundRenaming freeRenaming) := by
  simp [function_application_term, Term.renameMapped,
    Arguments.renameMapped]

/-! ## 函数求值的等式同态 -/

/-- 函数参数等式可直接穿过内在函数应用项。 -/
theorem function_application_term_congr_argument_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (function left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (function ·ₘ left) ≐ₘ (function ·ₘ right) := by
  let context : SetTerm [SetSort.set] free :=
    function.weakenBound SetSort.set ·ₘ (.bvar .here)
  simpa [context] using!
    Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ) context hEquality

/-- 函数项等式可直接穿过内在函数应用项。 -/
theorem function_application_term_congr_function_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right argument : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (left ·ₘ argument) ≐ₘ (right ·ₘ argument) := by
  let context : SetTerm [SetSort.set] free :=
    (.bvar .here) ·ₘ argument.weakenBound SetSort.set
  simpa [context] using!
    Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ) context hEquality

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
