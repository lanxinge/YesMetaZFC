import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties

/-!
# 关系逆与关系复合：核心

关系逆与复合都采用“笛卡尔积母集 + 最小图条件”的参数化分离规格。母集成员已经
保证候选元素是有序对，因此核心规格不重复携带有序对谓词证明义务。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 关系逆 -/

/-- 关系逆候选由原关系中的某个成员反转得到。 -/
def relation_converse_graph_condition {bound free : SetContext}
    (relation element : SetTerm bound free) : SetFormula bound free :=
  let original : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((original ∈ₘ relation.weakenFree SetSort.set) ∧ₘ
    (element.weakenFree SetSort.set ≐ₘ original⁻¹ₘ))
    |>.existsFreeTop SetSort.set

/-- 关系逆的标准笛卡尔积母集。 -/
abbrev relation_converse_bound_term {bound free : SetContext}
    (relation : SetTerm bound free) : SetTerm bound free :=
  ranₘ(relation) ×ₘ domₘ(relation)

/-- 关系逆规格的点态成员条件。 -/
def relation_converse_member_condition {bound free : SetContext}
    (relation element : SetTerm bound free) : SetFormula bound free :=
  (element ∈ₘ relation_converse_bound_term relation) ∧ₘ
    relation_converse_graph_condition relation element

/-- candidate 是 relation 的关系逆。 -/
def relation_converse_spec {bound free : SetContext}
    (relation candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (relation_converse_member_condition
      (relation.weakenFree SetSort.set) element)

/-- 对固定关系断言一个关系逆候选存在。 -/
def relation_converse_exists {bound free : SetContext}
    (relation : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (relation_converse_spec
    (relation.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 从任意母集中分离关系逆元素。 -/
def relation_converse_separation_spec {bound free : SetContext}
    (relation source candidate : SetTerm bound free) :
    SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ source.weakenFree SetSort.set) ∧ₘ
      relation_converse_graph_condition
        (relation.weakenFree SetSort.set) element)

/-- 对固定关系与母集断言关系逆分离结果存在。 -/
def relation_converse_separation_exists {bound free : SetContext}
    (relation source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (relation_converse_separation_spec
    (relation.weakenFree SetSort.set)
    (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 关系逆图条件作为公共分离谓词。 -/
def relation_converse_predicate {free : SetContext}
    (relation : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (relation_converse_graph_condition
      (relation.weakenFree SetSort.set) element).abstractFreeTop

/-- 关系逆函数符号的开放定义实例。 -/
def relation_converse_definition_instance {bound free : SetContext}
    (relation candidate : SetTerm bound free) : SetFormula bound free :=
  is_relation_formula relation ⟶ₘ
    ((candidate ≐ₘ converseₘ(relation)) ↔ₘ
      relation_converse_spec relation candidate)

/-- 关系逆函数符号的闭定义公理。 -/
def relation_converse_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (relation_converse_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-! ## 关系复合 -/

/-- 存在一个中间点连接第一条关系与第二条关系。 -/
def relation_composition_graph_condition {bound free : SetContext}
    (first second element : SetTerm bound free) : SetFormula bound free :=
  let middle : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((⟨(element.weakenFree SetSort.set)₀ₘ, middle⟩ₘ ∈ₘ
      first.weakenFree SetSort.set) ∧ₘ
    (⟨middle, (element.weakenFree SetSort.set)₁ₘ⟩ₘ ∈ₘ
      second.weakenFree SetSort.set))
    |>.existsFreeTop SetSort.set

/-- 关系复合的标准笛卡尔积母集。 -/
abbrev relation_composition_bound_term {bound free : SetContext}
    (first second : SetTerm bound free) : SetTerm bound free :=
  domₘ(first) ×ₘ ranₘ(second)

/-- 关系复合规格的点态成员条件。 -/
def relation_composition_member_condition {bound free : SetContext}
    (first second element : SetTerm bound free) : SetFormula bound free :=
  (element ∈ₘ relation_composition_bound_term first second) ∧ₘ
    relation_composition_graph_condition first second element

/-- candidate 是 second ∘ first。 -/
def relation_composition_spec {bound free : SetContext}
    (first second candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (relation_composition_member_condition
      (first.weakenFree SetSort.set)
      (second.weakenFree SetSort.set) element)

/-- 对固定两个关系断言一个复合候选存在。 -/
def relation_composition_exists {bound free : SetContext}
    (first second : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (relation_composition_spec
    (first.weakenFree SetSort.set)
    (second.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 从任意母集中分离关系复合元素。 -/
def relation_composition_separation_spec {bound free : SetContext}
    (first second source candidate : SetTerm bound free) :
    SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ source.weakenFree SetSort.set) ∧ₘ
      relation_composition_graph_condition
        (first.weakenFree SetSort.set)
        (second.weakenFree SetSort.set) element)

/-- 对固定关系与母集断言关系复合分离结果存在。 -/
def relation_composition_separation_exists {bound free : SetContext}
    (first second source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (relation_composition_separation_spec
    (first.weakenFree SetSort.set)
    (second.weakenFree SetSort.set)
    (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 关系复合图条件作为公共分离谓词。 -/
def relation_composition_predicate {free : SetContext}
    (first second : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (relation_composition_graph_condition
      (first.weakenFree SetSort.set)
      (second.weakenFree SetSort.set) element).abstractFreeTop

/-- 关系复合函数符号的开放定义实例。 -/
def relation_composition_definition_instance {bound free : SetContext}
    (first second candidate : SetTerm bound free) : SetFormula bound free :=
  (is_relation_formula first ∧ₘ is_relation_formula second) ⟶ₘ
    ((candidate ≐ₘ (second ∘ₘ first)) ↔ₘ
      relation_composition_spec first second candidate)

/-- 关系复合函数符号的闭定义公理。 -/
def relation_composition_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (relation_composition_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-! ## 理论边界 -/

/-- 关系平面上加入全部类型化关系逆分离实例。 -/
def relation_converse_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (relation : SetOpenTerm free),
      sentence = (relation_converse_predicate relation).separation_axiom) ∨
    relation_plane_theory sentence

/-- 加入关系逆函数符号。 -/
def relation_converse_operator_theory : SetTheory :=
  Theory.insert relation_converse_definition_axiom relation_converse_theory

/-- 关系逆层上加入全部类型化关系复合分离实例。 -/
def relation_composition_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (first second : SetOpenTerm free),
      sentence =
        (relation_composition_predicate first second).separation_axiom) ∨
    relation_converse_operator_theory sentence

/-- 加入关系复合函数符号。 -/
def relation_composition_operator_theory : SetTheory :=
  Theory.insert relation_composition_definition_axiom
    relation_composition_theory

/-! ## 结构自然性 -/

/-- 关系逆图条件与 free 重命名自然交换。 -/
@[simp] theorem relation_converse_graph_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (relation element : SetTerm bound sourceFree) :
    (relation_converse_graph_condition relation element).renameMapped
        VariableRenaming.id ρ =
      relation_converse_graph_condition
        (relation.renameMapped VariableRenaming.id ρ)
        (element.renameMapped VariableRenaming.id ρ) := by
  unfold relation_converse_graph_condition
  rw [Formula.renameMapped_existsFreeTop]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 关系复合图条件与 free 重命名自然交换。 -/
@[simp] theorem relation_composition_graph_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (first second element : SetTerm bound sourceFree) :
    (relation_composition_graph_condition first second element).renameMapped
        VariableRenaming.id ρ =
      relation_composition_graph_condition
        (first.renameMapped VariableRenaming.id ρ)
        (second.renameMapped VariableRenaming.id ρ)
        (element.renameMapped VariableRenaming.id ρ) := by
  unfold relation_composition_graph_condition
  rw [Formula.renameMapped_existsFreeTop]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [ordered_pair_term_renameMapped,
    ordered_pair_term_renameMapped]
  rw [left_projection_term_renameMapped,
    right_projection_term_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 参数化关系逆谓词在规范 fresh 元素处恢复图条件。 -/
@[simp] theorem relation_converse_predicate_atNewest
    {free : SetContext} (relation : SetOpenTerm free) :
    (relation_converse_predicate relation).atNewest =
      relation_converse_graph_condition
        (relation.weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set) := by
  simp [SetPredicate.atNewest, relation_converse_predicate,
    relation_converse_graph_condition, FreshVariable.newest]

/-- 关系逆谓词参数扩张后仍命中规范 fresh 快路径。 -/
@[simp] theorem relation_converse_predicate_weakenFree_atNewest
    {free : SetContext} (relation : SetOpenTerm free) :
    ((relation_converse_predicate relation).weakenFree).atNewest =
      relation_converse_graph_condition
        ((relation.weakenFree SetSort.set).weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := SetSort.set :: free) SetSort.set) := by
  unfold SetPredicate.atNewest SetPredicate.weakenFree
    relation_converse_predicate
  dsimp
  simp only [FreshVariable.newest]
  rw [Formula.instantiateTop_two_weakenings_abstractFreeTop_newest]
  change
    (relation_converse_graph_condition
      (relation.weakenFree SetSort.set)
      (Term.newestFree
        (σ := signature) (free := free) SetSort.set)).renameMapped
        VariableRenaming.id
        (VariableRenaming.lift (introduced := SetSort.set)
          (VariableRenaming.weaken SetSort.set)) =
      relation_converse_graph_condition
        ((relation.weakenFree SetSort.set).weakenFree SetSort.set)
        (Term.newestFree
          (σ := signature) (free := SetSort.set :: free) SetSort.set)
  rw [relation_converse_graph_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 参数化关系复合谓词在规范 fresh 元素处恢复图条件。 -/
@[simp] theorem relation_composition_predicate_atNewest
    {free : SetContext} (first second : SetOpenTerm free) :
    (relation_composition_predicate first second).atNewest =
      relation_composition_graph_condition
        (first.weakenFree SetSort.set)
        (second.weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set) := by
  simp [SetPredicate.atNewest, relation_composition_predicate,
    relation_composition_graph_condition, FreshVariable.newest]

/-- 关系复合谓词参数扩张后仍命中规范 fresh 快路径。 -/
@[simp] theorem relation_composition_predicate_weakenFree_atNewest
    {free : SetContext} (first second : SetOpenTerm free) :
    ((relation_composition_predicate first second).weakenFree).atNewest =
      relation_composition_graph_condition
        ((first.weakenFree SetSort.set).weakenFree SetSort.set)
        ((second.weakenFree SetSort.set).weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := SetSort.set :: free) SetSort.set) := by
  unfold SetPredicate.atNewest SetPredicate.weakenFree
    relation_composition_predicate
  dsimp
  simp only [FreshVariable.newest]
  rw [Formula.instantiateTop_two_weakenings_abstractFreeTop_newest]
  change
    (relation_composition_graph_condition
      (first.weakenFree SetSort.set)
      (second.weakenFree SetSort.set)
      (Term.newestFree
        (σ := signature) (free := free) SetSort.set)).renameMapped
        VariableRenaming.id
        (VariableRenaming.lift (introduced := SetSort.set)
          (VariableRenaming.weaken SetSort.set)) =
      relation_composition_graph_condition
        ((first.weakenFree SetSort.set).weakenFree SetSort.set)
        ((second.weakenFree SetSort.set).weakenFree SetSort.set)
        (Term.newestFree
          (σ := signature) (free := SetSort.set :: free) SetSort.set)
  rw [relation_composition_graph_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

derive_theory_subset relation_plane_theory ⊆ relation_converse_theory

derive_theory_subset relation_converse_theory ⊆ relation_converse_operator_theory

derive_theory_subset relation_converse_operator_theory ⊆ relation_composition_theory

derive_theory_subset relation_plane_theory ⊆ relation_composition_theory

derive_theory_subset relation_composition_theory ⊆ relation_composition_operator_theory

derive_theory_subset relation_plane_theory ⊆ relation_composition_operator_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
