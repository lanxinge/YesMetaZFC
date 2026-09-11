import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union

/-!
# 关系、定义域与值域：核心

关系谓词以及定义域、值域统一建立在内在类型语法上。两个坐标构造共享同一个
`RelationCoordinate` 参数化分离器；分离 schema 直接量化类型化参数上下文，
不再保存变量编号、admissibility、闭性证书或“函数项存在”这类自反桥接公式。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 关系谓词与双重并集 -/

/-- 关系的每个成员都是规范有序对。 -/
def is_relation_condition {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  let member : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((member ∈ₘ relation.weakenFree SetSort.set) ⟶ₘ
    is_ordered_pair_formula member)
    |>.forallFreeTop SetSort.set

/-- 关系谓词符号的开放定义实例。 -/
def is_relation_definition_instance {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  is_relation_formula relation ↔ₘ is_relation_condition relation

/-- 关系谓词符号的闭定义公理。 -/
def is_relation_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_relation_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set))

/-- 文献双重并集运算的非冗余表示。 -/
abbrev double_union_term {bound free : SetContext}
    (relation : SetTerm bound free) : SetTerm bound free :=
  ⋃ₘ ⋃ₘ relation

/-- 双重并集成员条件。 -/
abbrev double_union_member_condition {bound free : SetContext}
    (relation element : SetTerm bound free) : SetFormula bound free :=
  union_witness_condition (⋃ₘ relation) element

/-! ## 共享坐标筛选核心 -/

/-- 关系中有序对的两个坐标。 -/
inductive RelationCoordinate where
  | domain
  | range
  deriving DecidableEq, Repr

/-- 按坐标选择有序对投影项。 -/
def relation_coordinate_projection_term {bound free : SetContext}
    (coordinate : RelationCoordinate) (pair : SetTerm bound free) :
    SetTerm bound free :=
  match coordinate with
  | .domain => (pair)₀ₘ
  | .range => (pair)₁ₘ

/-- 一个元素由关系中某个有序对的指定坐标取得。 -/
def relation_coordinate_member_condition {bound free : SetContext}
    (coordinate : RelationCoordinate)
    (relation element : SetTerm bound free) : SetFormula bound free :=
  let pair : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((pair ∈ₘ relation.weakenFree SetSort.set) ∧ₘ
    (element.weakenFree SetSort.set ≐ₘ
      relation_coordinate_projection_term coordinate pair))
    |>.existsFreeTop SetSort.set

/-- `candidate` 是 `relation` 的指定坐标集合。 -/
def relation_coordinate_spec {bound free : SetContext}
    (coordinate : RelationCoordinate)
    (relation candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ double_union_term
        (relation.weakenFree SetSort.set)) ∧ₘ
      relation_coordinate_member_condition coordinate
        (relation.weakenFree SetSort.set) element)

/-- 对固定关系断言指定坐标集合存在。 -/
def relation_coordinate_exists {bound free : SetContext}
    (coordinate : RelationCoordinate)
    (relation : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (relation_coordinate_spec coordinate
      (relation.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 从任意母集中分离指定坐标。 -/
def relation_coordinate_separation_spec {bound free : SetContext}
    (coordinate : RelationCoordinate)
    (relation source candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ source.weakenFree SetSort.set) ∧ₘ
      relation_coordinate_member_condition coordinate
        (relation.weakenFree SetSort.set) element)

/-- 对固定关系与母集断言一个坐标分离结果存在。 -/
def relation_coordinate_separation_exists {bound free : SetContext}
    (coordinate : RelationCoordinate)
    (relation source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (relation_coordinate_separation_spec coordinate
      (relation.weakenFree SetSort.set)
      (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 坐标筛选条件作为公共分离谓词。 -/
def relation_coordinate_predicate {free : SetContext}
    (coordinate : RelationCoordinate) (relation : SetOpenTerm free) :
    SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (relation_coordinate_member_condition coordinate
      (relation.weakenFree SetSort.set) element).abstractFreeTop

/-! ## 定义域和值域接口 -/

abbrev relation_domain_member_condition {bound free : SetContext}
    (relation element : SetTerm bound free) : SetFormula bound free :=
  relation_coordinate_member_condition RelationCoordinate.domain
    relation element

abbrev relation_domain_spec {bound free : SetContext}
    (relation candidate : SetTerm bound free) : SetFormula bound free :=
  relation_coordinate_spec RelationCoordinate.domain relation candidate

abbrev relation_domain_exists {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  relation_coordinate_exists RelationCoordinate.domain relation

abbrev relation_range_member_condition {bound free : SetContext}
    (relation element : SetTerm bound free) : SetFormula bound free :=
  relation_coordinate_member_condition RelationCoordinate.range
    relation element

abbrev relation_range_spec {bound free : SetContext}
    (relation candidate : SetTerm bound free) : SetFormula bound free :=
  relation_coordinate_spec RelationCoordinate.range relation candidate

abbrev relation_range_exists {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  relation_coordinate_exists RelationCoordinate.range relation

/-- 定义域函数符号的开放定义实例。 -/
def domain_definition_instance {bound free : SetContext}
    (relation candidate : SetTerm bound free) : SetFormula bound free :=
  is_relation_formula relation ⟶ₘ
    ((candidate ≐ₘ domₘ(relation)) ↔ₘ
      relation_domain_spec relation candidate)

/-- 定义域函数符号的闭定义公理。 -/
def domain_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (domain_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 值域函数符号的开放定义实例。 -/
def range_definition_instance {bound free : SetContext}
    (relation candidate : SetTerm bound free) : SetFormula bound free :=
  is_relation_formula relation ⟶ₘ
    ((candidate ≐ₘ ranₘ(relation)) ↔ₘ
      relation_range_spec relation candidate)

/-- 值域函数符号的闭定义公理。 -/
def range_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (range_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 理论组合 -/

/-- 左右投影与一元并集所需的最小公共理论。 -/
def relation_base_theory : SetTheory :=
  Theory.union right_projection_operator_theory union_operator_theory

/-- 在公共基座上加入关系谓词。 -/
def relation_predicate_theory : SetTheory :=
  Theory.insert is_relation_definition_axiom relation_base_theory

/-- 在给定基座上加入某一坐标的全部类型化分离实例。 -/
def relation_coordinate_separation_theory
    (coordinate : RelationCoordinate) (base : SetTheory) : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (relation : SetOpenTerm free),
      sentence =
        (relation_coordinate_predicate coordinate relation).separation_axiom) ∨
    base sentence

/-- 加入定义域分离 schema。 -/
def relation_domain_theory : SetTheory :=
  relation_coordinate_separation_theory
    RelationCoordinate.domain relation_predicate_theory

/-- 加入定义域函数符号。 -/
def relation_domain_operator_theory : SetTheory :=
  Theory.insert domain_definition_axiom relation_domain_theory

/-- 在已有关系与定义域层上加入值域分离 schema。 -/
def relation_range_theory : SetTheory :=
  relation_coordinate_separation_theory
    RelationCoordinate.range relation_domain_operator_theory

/-- 在值域存在理论上加入值域函数符号。 -/
def relation_range_operator_theory : SetTheory :=
  Theory.insert range_definition_axiom relation_range_theory

/-! ## 结构自然性 -/

@[simp] theorem relation_coordinate_projection_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (coordinate : RelationCoordinate)
    (pair : SetTerm sourceBound sourceFree) :
    (relation_coordinate_projection_term coordinate pair).renameMapped
        boundRenaming freeRenaming =
      relation_coordinate_projection_term coordinate
        (pair.renameMapped boundRenaming freeRenaming) := by
  cases coordinate <;>
    simp [relation_coordinate_projection_term, left_projection_term,
      right_projection_term]

@[simp] theorem double_union_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (relation : SetTerm sourceBound sourceFree) :
    (double_union_term relation).renameMapped
        boundRenaming freeRenaming =
      double_union_term
        (relation.renameMapped boundRenaming freeRenaming) := by
  simp [double_union_term, union_term,
    Term.renameMapped, Arguments.renameMapped]

@[simp] theorem is_relation_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (relation : SetTerm bound sourceFree) :
    (is_relation_condition relation).renameMapped
        VariableRenaming.id ρ =
      is_relation_condition
        (relation.renameMapped VariableRenaming.id ρ) := by
  unfold is_relation_condition
  rw [Formula.renameMapped_forallFreeTop]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

@[simp] theorem relation_coordinate_member_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (coordinate : RelationCoordinate)
    (relation element : SetTerm bound sourceFree) :
    (relation_coordinate_member_condition
        coordinate relation element).renameMapped
        VariableRenaming.id ρ =
      relation_coordinate_member_condition coordinate
        (relation.renameMapped VariableRenaming.id ρ)
        (element.renameMapped VariableRenaming.id ρ) := by
  unfold relation_coordinate_member_condition
  rw [Formula.renameMapped_existsFreeTop]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [relation_coordinate_projection_term_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

@[simp] theorem relation_coordinate_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (coordinate : RelationCoordinate)
    (relation candidate : SetTerm bound sourceFree) :
    (relation_coordinate_spec coordinate relation candidate).renameMapped
        VariableRenaming.id ρ =
      relation_coordinate_spec coordinate
        (relation.renameMapped VariableRenaming.id ρ)
        (candidate.renameMapped VariableRenaming.id ρ) := by
  unfold relation_coordinate_spec
  rw [membership_specification_renameMapped]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [double_union_term_renameMapped,
    relation_coordinate_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

@[simp] theorem relation_coordinate_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (coordinate : RelationCoordinate)
    (relation candidate : SetTerm bound free) :
    (relation_coordinate_spec coordinate relation candidate).weakenFree
        introduced =
      relation_coordinate_spec coordinate
        (relation.weakenFree introduced)
        (candidate.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact relation_coordinate_spec_renameMapped
    (VariableRenaming.weaken introduced) coordinate relation candidate

@[simp] theorem relation_coordinate_exists_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (coordinate : RelationCoordinate)
    (relation : SetTerm bound sourceFree) :
    (relation_coordinate_exists coordinate relation).renameMapped
        VariableRenaming.id ρ =
      relation_coordinate_exists coordinate
        (relation.renameMapped VariableRenaming.id ρ) := by
  unfold relation_coordinate_exists
  rw [Formula.renameMapped_existsFreeTop]
  rw [relation_coordinate_spec_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

@[simp] theorem relation_coordinate_separation_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (coordinate : RelationCoordinate)
    (relation source candidate : SetTerm bound sourceFree) :
    (relation_coordinate_separation_spec coordinate
        relation source candidate).renameMapped VariableRenaming.id ρ =
      relation_coordinate_separation_spec coordinate
        (relation.renameMapped VariableRenaming.id ρ)
        (source.renameMapped VariableRenaming.id ρ)
        (candidate.renameMapped VariableRenaming.id ρ) := by
  unfold relation_coordinate_separation_spec
  rw [membership_specification_renameMapped]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [relation_coordinate_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 参数化坐标谓词在规范 fresh 元素处恢复成员条件。 -/
@[simp] theorem relation_coordinate_predicate_atNewest
    {free : SetContext} (coordinate : RelationCoordinate)
    (relation : SetOpenTerm free) :
    (relation_coordinate_predicate coordinate relation).atNewest =
      relation_coordinate_member_condition coordinate
        (relation.weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set) := by
  simp [SetPredicate.atNewest, relation_coordinate_predicate,
    relation_coordinate_member_condition, FreshVariable.newest]

/-- 谓词参数扩张后在下一规范 fresh 元素处仍命中同一快路径。 -/
@[simp] theorem relation_coordinate_predicate_weakenFree_atNewest
    {free : SetContext} (coordinate : RelationCoordinate)
    (relation : SetOpenTerm free) :
    ((relation_coordinate_predicate coordinate relation).weakenFree).atNewest =
      relation_coordinate_member_condition coordinate
        ((relation.weakenFree SetSort.set).weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := SetSort.set :: free) SetSort.set) := by
  unfold SetPredicate.atNewest SetPredicate.weakenFree
    relation_coordinate_predicate
  dsimp
  simp only [FreshVariable.newest]
  rw [Formula.instantiateTop_two_weakenings_abstractFreeTop_newest]
  change
    (relation_coordinate_member_condition coordinate
      (relation.weakenFree SetSort.set)
      (Term.newestFree
        (σ := signature) (free := free) SetSort.set)).renameMapped
        VariableRenaming.id
        (VariableRenaming.lift (introduced := SetSort.set)
          (VariableRenaming.weaken SetSort.set)) =
      relation_coordinate_member_condition coordinate
        ((relation.weakenFree SetSort.set).weakenFree SetSort.set)
        (Term.newestFree
          (σ := signature) (free := SetSort.set :: free) SetSort.set)
  rw [relation_coordinate_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-! ## 理论嵌入 -/

derive_theory_subset right_projection_operator_theory ⊆ relation_base_theory

derive_theory_subset union_operator_theory ⊆ relation_base_theory

derive_theory_subset relation_function_theory ⊆ relation_base_theory

derive_theory_subset extensionality_theory ⊆ relation_base_theory

derive_theory_subset relation_base_theory ⊆ relation_predicate_theory

derive_theory_subset relation_predicate_theory ⊆ relation_domain_theory

derive_theory_subset relation_domain_theory ⊆ relation_domain_operator_theory

derive_theory_subset relation_domain_operator_theory ⊆ relation_range_theory

derive_theory_subset relation_range_theory ⊆ relation_range_operator_theory

derive_theory_subset relation_base_theory ⊆ relation_domain_theory

derive_theory_subset relation_base_theory ⊆ relation_domain_operator_theory

derive_theory_subset relation_base_theory ⊆ relation_range_theory

derive_theory_subset relation_base_theory ⊆ relation_range_operator_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
