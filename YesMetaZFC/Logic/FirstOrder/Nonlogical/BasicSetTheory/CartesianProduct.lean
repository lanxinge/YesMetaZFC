import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union

/-!
# 笛卡尔积

笛卡尔积规格直接建立在内在类型语法上。候选积从
`𝒫ₘ(𝒫ₘ(left ∪ₘ right))` 中按“存在左右坐标且等于规范有序对”分离；
全部参数由 `SetContext` 精确记录，分离公理与函数符号定义统一经结构化全称闭包
实例化，不再携带变量编号、admissibility、闭性证书或手工 `openAt` 归约。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 复合母集与成员条件 -/

/-- 文献三重复合对应的幂集项。 -/
abbrev power_set_binary_union_term {bound free : SetContext}
    (left right : SetTerm bound free) : SetTerm bound free :=
  𝒫ₘ(left ∪ₘ right)

/-- 笛卡尔积构造使用的四重复合母集。 -/
abbrev cartesian_product_bound_term {bound free : SetContext}
    (left right : SetTerm bound free) : SetTerm bound free :=
  𝒫ₘ(power_set_binary_union_term left right)

/-- `element` 是 `left` 与 `right` 中元素组成的规范有序对。 -/
def cartesian_product_member_condition {bound free : SetContext}
    (left right element : SetTerm bound free) : SetFormula bound free :=
  let leftCoordinate : SetTerm bound (SetSort.set :: free) := .fvar .here
  let rightCoordinate : SetTerm bound
      (SetSort.set :: SetSort.set :: free) := .fvar .here
  (((leftCoordinate.weakenFree SetSort.set ∈ₘ
        (left.weakenFree SetSort.set).weakenFree SetSort.set) ∧ₘ
      ((rightCoordinate ∈ₘ
          (right.weakenFree SetSort.set).weakenFree SetSort.set) ∧ₘ
        ((element.weakenFree SetSort.set).weakenFree SetSort.set ≐ₘ
          ⟨leftCoordinate.weakenFree SetSort.set, rightCoordinate⟩ₘ)))
    |>.existsFreeTop SetSort.set)
    |>.existsFreeTop SetSort.set

/-- `product` 恰由母集中满足坐标条件的元素组成。 -/
def cartesian_product_spec {bound free : SetContext}
    (left right product : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification product
    ((element ∈ₘ cartesian_product_bound_term
        (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)) ∧ₘ
      cartesian_product_member_condition
        (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set) element)

/-- 对固定两个集合断言满足笛卡尔积规格的结果存在。 -/
def cartesian_product_exists {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let product : SetTerm bound (SetSort.set :: free) := .fvar .here
  (cartesian_product_spec
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) product)
    |>.existsFreeTop SetSort.set

/-! ## 参数化分离实例与理论 -/

/-- 以 `left`、`right` 为参数的笛卡尔积筛选谓词。 -/
def cartesian_product_predicate {free : SetContext}
    (left right : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (cartesian_product_member_condition
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) element).abstractFreeTop

/-- 复合母集与规范有序对所需的最小描述符理论。 -/
def cartesian_product_base_theory : SetTheory :=
  Theory.union ordered_pair_operator_theory
    (Theory.union power_set_operator_theory
      binary_union_operator_theory)

/-- 在复合项基础上加入全部类型化笛卡尔积分离实例。 -/
def cartesian_product_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (left right : SetOpenTerm free),
      sentence = (cartesian_product_predicate left right).separation_axiom) ∨
    cartesian_product_base_theory sentence

/-- 笛卡尔积函数符号的开放定义实例。 -/
def cartesian_product_definition_instance {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ (left ×ₘ right)) ↔ₘ
    cartesian_product_spec left right candidate

/-- 笛卡尔积函数符号的闭定义公理。 -/
def cartesian_product_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (cartesian_product_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-- 在笛卡尔积存在理论上加入二元函数符号。 -/
def cartesian_product_operator_theory : SetTheory :=
  Theory.insert cartesian_product_definition_axiom cartesian_product_theory

/-! ## 结构自然性 -/

/-- 笛卡尔积成员条件与 free 重命名自然交换。 -/
@[simp] theorem cartesian_product_member_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (left right element : SetTerm bound sourceFree) :
    (cartesian_product_member_condition left right element).renameMapped
        VariableRenaming.id ρ =
      cartesian_product_member_condition
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ)
        (element.renameMapped VariableRenaming.id ρ) := by
  unfold cartesian_product_member_condition
  rw [Formula.renameMapped_existsFreeTop,
    Formula.renameMapped_existsFreeTop]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [ordered_pair_term_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 笛卡尔积规格与 free 重命名自然交换。 -/
@[simp] theorem cartesian_product_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (left right product : SetTerm bound sourceFree) :
    (cartesian_product_spec left right product).renameMapped
        VariableRenaming.id ρ =
      cartesian_product_spec
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ)
        (product.renameMapped VariableRenaming.id ρ) := by
  unfold cartesian_product_spec
  rw [membership_specification_renameMapped]
  simp only [Formula.renameMapped, Arguments.renameMapped,
    Term.renameMapped, power_set_binary_union_term,
    cartesian_product_bound_term]
  rw [cartesian_product_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  simp [Term.renameMapped, VariableRenaming.lift]

/-- 笛卡尔积规格与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem cartesian_product_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (left right product : SetTerm bound free) :
    (cartesian_product_spec left right product).weakenFree introduced =
      cartesian_product_spec
        (left.weakenFree introduced)
        (right.weakenFree introduced)
        (product.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact cartesian_product_spec_renameMapped
    (VariableRenaming.weaken introduced) left right product

/-- 笛卡尔积存在式与 free 重命名自然交换。 -/
@[simp] theorem cartesian_product_exists_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (left right : SetTerm bound sourceFree) :
    (cartesian_product_exists left right).renameMapped
        VariableRenaming.id ρ =
      cartesian_product_exists
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ) := by
  unfold cartesian_product_exists
  rw [Formula.renameMapped_existsFreeTop]
  rw [cartesian_product_spec_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 笛卡尔积存在式与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem cartesian_product_exists_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (left right : SetTerm bound free) :
    (cartesian_product_exists left right).weakenFree introduced =
      cartesian_product_exists
        (left.weakenFree introduced)
        (right.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact cartesian_product_exists_renameMapped
    (VariableRenaming.weaken introduced) left right

/-- 参数化笛卡尔积谓词在规范 fresh 元素处恢复成员条件。 -/
@[simp] theorem cartesian_product_predicate_atNewest
    {free : SetContext} (left right : SetOpenTerm free) :
    (cartesian_product_predicate left right).atNewest =
      cartesian_product_member_condition
        (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set) := by
  simp [SetPredicate.atNewest, cartesian_product_predicate,
    cartesian_product_member_condition, FreshVariable.newest]

/-- 谓词参数扩张后在下一规范 fresh 元素处仍命中同一快路径。 -/
@[simp] theorem cartesian_product_predicate_weakenFree_atNewest
    {free : SetContext} (left right : SetOpenTerm free) :
    ((cartesian_product_predicate left right).weakenFree).atNewest =
      cartesian_product_member_condition
        ((left.weakenFree SetSort.set).weakenFree SetSort.set)
        ((right.weakenFree SetSort.set).weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := SetSort.set :: free) SetSort.set) := by
  unfold SetPredicate.atNewest SetPredicate.weakenFree
    cartesian_product_predicate
  dsimp
  simp only [FreshVariable.newest]
  rw [Formula.instantiateTop_two_weakenings_abstractFreeTop_newest]
  change
    (cartesian_product_member_condition
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set)
      (Term.newestFree
        (σ := signature) (free := free) SetSort.set)).renameMapped
        VariableRenaming.id
        (VariableRenaming.lift (introduced := SetSort.set)
          (VariableRenaming.weaken SetSort.set)) =
      cartesian_product_member_condition
        ((left.weakenFree SetSort.set).weakenFree SetSort.set)
        ((right.weakenFree SetSort.set).weakenFree SetSort.set)
        (Term.newestFree
          (σ := signature) (free := SetSort.set :: free) SetSort.set)
  rw [cartesian_product_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-! ## 理论嵌入 -/

derive_theory_subset ordered_pair_operator_theory ⊆ cartesian_product_base_theory

derive_theory_subset power_set_operator_theory ⊆ cartesian_product_base_theory

derive_theory_subset binary_union_operator_theory ⊆ cartesian_product_base_theory

derive_theory_subset cartesian_product_base_theory ⊆ cartesian_product_theory

derive_theory_subset cartesian_product_theory ⊆ cartesian_product_operator_theory

derive_theory_subset cartesian_product_base_theory ⊆ cartesian_product_operator_theory

derive_theory_subset extensionality_theory ⊆ cartesian_product_base_theory

/-! ## 复合母集合同 -/

/-- 文献三重复合项满足幂集规格。 -/
theorem power_set_binary_union_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_base_theory]
      power_set_spec (left ∪ₘ right)
        (power_set_binary_union_term left right) :=
  FirstOrder.Derives.theory_weaken
    power_set_operator_theory_subset_cartesian_product_base_theory
    (power_set_term_spec_derives (Γ := Γ) (left ∪ₘ right))

/-- 文献四重复合母集满足外层幂集规格。 -/
theorem cartesian_product_bound_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_base_theory]
      power_set_spec (power_set_binary_union_term left right)
        (cartesian_product_bound_term left right) :=
  FirstOrder.Derives.theory_weaken
    power_set_operator_theory_subset_cartesian_product_base_theory
    (power_set_term_spec_derives (Γ := Γ)
      (power_set_binary_union_term left right))

/-- 三重复合项的成员关系等价于对子集条件。 -/
theorem mem_power_set_binary_union_term_iff_subset
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_base_theory]
      (element ∈ₘ power_set_binary_union_term left right) ↔ₘ
        (element ⊆ₘ (left ∪ₘ right)) :=
  FirstOrder.Derives.theory_weaken
    power_set_operator_theory_subset_cartesian_product_base_theory
    (mem_power_set_term_iff_subset (Γ := Γ) (left ∪ₘ right) element)

/-- 四重复合母集的成员关系等价于对三重复合项的子集条件。 -/
theorem mem_cartesian_product_bound_term_iff_subset
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_base_theory]
      (element ∈ₘ cartesian_product_bound_term left right) ↔ₘ
        (element ⊆ₘ power_set_binary_union_term left right) :=
  FirstOrder.Derives.theory_weaken
    power_set_operator_theory_subset_cartesian_product_base_theory
    (mem_power_set_term_iff_subset (Γ := Γ)
      (power_set_binary_union_term left right) element)

/-! ## 分离存在性、实例化与唯一性 -/

/-- 笛卡尔积分离 schema 可直接消费任意两个因子。 -/
theorem cartesian_product_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_theory]
      cartesian_product_exists left right := by
  have hGeneric := SetPredicate.separation_exists_derives
    (Γ := Γ) (cartesian_product_predicate left right)
    (cartesian_product_bound_term left right)
  have hLifted := FirstOrder.Derives.theory_weaken
    (T := (cartesian_product_predicate left right).separation_theory)
    (U := cartesian_product_theory)
    (by
      intro sentence hSentence
      rcases hSentence with rfl | hExtensionality
      · exact Or.inl ⟨free, left, right, rfl⟩
      · exact Or.inr
          (extensionality_theory_subset_cartesian_product_base_theory
            hExtensionality))
    hGeneric
  simpa only [cartesian_product_exists, cartesian_product_spec,
    SetPredicate.separation_exists, SetPredicate.separation_spec,
    SetPredicate.separation_condition,
    cartesian_product_predicate_weakenFree_atNewest,
    FreshVariable.newest] using! hLifted

/-- 笛卡尔积函数符号定义公理可在任意三个集合项处实例化。 -/
theorem cartesian_product_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_operator_theory]
      cartesian_product_definition_instance left right candidate := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    cartesian_product_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons right
        (VariableSubstitution.cons left VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[cartesian_product_operator_theory]
        Formula.fromSentence cartesian_product_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, cartesian_product_definition_axiom,
    cartesian_product_definition_instance, cartesian_product_spec,
    cartesian_product_member_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 笛卡尔积规格在任意元素处的点态实例。 -/
theorem cartesian_product_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right product element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] cartesian_product_spec left right product) :
    Γ ⊢ₘ[T]
      (element ∈ₘ product) ↔ₘ
        ((element ∈ₘ cartesian_product_bound_term left right) ∧ₘ
          cartesian_product_member_condition left right element) := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  simpa [cartesian_product_spec, membership_specification,
    cartesian_product_member_condition,
    Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hAt

/-- 同一对参数的两个笛卡尔积候选必相等。 -/
theorem cartesian_product_unique
    {free : SetContext} {Γ : Context signature free}
    (left right first second : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_base_theory]
      cartesian_product_spec left right first ⟶ₘ
        cartesian_product_spec left right second ⟶ₘ
          (first ≐ₘ second) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    (element ∈ₘ cartesian_product_bound_term
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set)) ∧ₘ
    cartesian_product_member_condition
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) element
  have hUnique := membership_specification_unique
    (Γ := Γ) first second condition
  exact FirstOrder.Derives.theory_weaken
    extensionality_theory_subset_cartesian_product_base_theory
    (by simpa [cartesian_product_spec, condition, element] using hUnique)

/-- 定义扩张中的规范笛卡尔积项满足其成员规格。 -/
theorem cartesian_product_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_operator_theory]
      cartesian_product_spec left right (left ×ₘ right) := by
  have hDefinition := cartesian_product_definition_instance_derives
    (Γ := Γ) left right (left ×ₘ right)
  exact FirstOrder.Derives.iff_elim_left hDefinition
    (Metatheory.Derives.equality_refl
      (T := cartesian_product_operator_theory) (Γ := Γ)
      (left ×ₘ right))

/-- 一个候选项等于规范笛卡尔积，当且仅当它满足笛卡尔积规格。 -/
theorem cartesian_product_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[cartesian_product_operator_theory]
      (candidate ≐ₘ (left ×ₘ right)) ↔ₘ
        cartesian_product_spec left right candidate :=
  cartesian_product_definition_instance_derives
    (Γ := Γ) left right candidate

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
