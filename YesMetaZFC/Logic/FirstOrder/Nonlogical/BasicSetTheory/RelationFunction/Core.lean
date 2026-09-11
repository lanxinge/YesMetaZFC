import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Reordering

/-!
# 关系与函数基础

本模块只保留关系/函数层的数学核心：Kuratowski 有序对、有序对谓词、左右投影与
反转。全部公式直接构造在内在类型语法上；量词由 free-top 抽象形成，因此不再携带
admissibility、闭性证书、自由变量编号或临时新鲜变量桥接。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## Kuratowski 有序对 -/

/-- Kuratowski 有序对的成员条件。 -/
def ordered_pair_member_condition {bound free : SetContext}
    (member left right : SetTerm bound free) : SetFormula bound free :=
  (member ≐ₘ {left}ₘ) ∨ₘ (member ≐ₘ {left, right}ₘ)

/-- 文献采用的经典蕴含写法。 -/
def ordered_pair_paper_condition {bound free : SetContext}
    (member left right : SetTerm bound free) : SetFormula bound free :=
  (¬ₘ (member ≐ₘ {left}ₘ)) ⟶ₘ (member ≐ₘ {left, right}ₘ)

/-- `pair` 是由 `left`、`right` 构成的 Kuratowski 有序对。 -/
def ordered_pair_spec {bound free : SetContext}
    (left right pair : SetTerm bound free) : SetFormula bound free :=
  pair_spec {left}ₘ {left, right}ₘ pair

/-- 文献蕴含写法下的 Kuratowski 有序对规格。 -/
def ordered_pair_paper_spec {bound free : SetContext}
    (left right pair : SetTerm bound free) : SetFormula bound free :=
  let member : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification pair
    (ordered_pair_paper_condition member
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set))

/-- 对固定坐标断言 Kuratowski 有序对存在。 -/
def ordered_pair_exists {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let pair : SetTerm bound (SetSort.set :: free) := .fvar .here
  (ordered_pair_spec
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) pair)
    |>.existsFreeTop SetSort.set

/-- 文献蕴含写法下的有序对存在公式。 -/
def ordered_pair_paper_exists {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let pair : SetTerm bound (SetSort.set :: free) := .fvar .here
  (ordered_pair_paper_spec
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) pair)
    |>.existsFreeTop SetSort.set

/-- 有序对函数符号的开放定义实例。 -/
def ordered_pair_definition_instance {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ ⟨left, right⟩ₘ) ↔ₘ
    ordered_pair_spec left right candidate

/-- 有序对函数符号的闭定义公理。 -/
def ordered_pair_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (ordered_pair_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-- 在单点集理论上加入有序对函数符号。 -/
def ordered_pair_operator_theory : SetTheory :=
  Theory.insert ordered_pair_definition_axiom singleton_operator_theory

/-! ## 有序对谓词与投影 -/

/-- 一个集合是有序对，当且仅当它等于某个规范有序对项。 -/
def is_ordered_pair_condition {bound free : SetContext}
    (pair : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: free) := .fvar .here
  let right : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar .here
  ((pair.weakenFree SetSort.set |>.weakenFree SetSort.set) ≐ₘ
      ⟨left.weakenFree SetSort.set, right⟩ₘ)
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 有序对谓词符号的开放定义实例。 -/
def is_ordered_pair_definition_instance {bound free : SetContext}
    (pair : SetTerm bound free) : SetFormula bound free :=
  is_ordered_pair_formula pair ↔ₘ is_ordered_pair_condition pair

/-- 有序对谓词符号的闭定义公理。 -/
def is_ordered_pair_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (is_ordered_pair_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-- 当前关系与函数层的首个理论。 -/
def relation_function_theory : SetTheory :=
  Theory.insert is_ordered_pair_definition_axiom ordered_pair_operator_theory

/-- `left` 满足 `pair` 的左投影规格。 -/
def left_projection_spec {bound free : SetContext}
    (pair left : SetTerm bound free) : SetFormula bound free :=
  let member : SetTerm bound (SetSort.set :: free) := .fvar .here
  (intersection_member_condition
      (pair.weakenFree SetSort.set) member ↔ₘ
      (member ≐ₘ left.weakenFree SetSort.set))
    |>.forallFreeTop SetSort.set

/-- 对固定有序对断言其左投影存在。 -/
def left_projection_exists {bound free : SetContext}
    (pair : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: free) := .fvar .here
  (left_projection_spec (pair.weakenFree SetSort.set) left)
    |>.existsFreeTop SetSort.set

/-- `right` 满足 `pair` 的右投影规格。 -/
def right_projection_spec {bound free : SetContext}
    (pair right : SetTerm bound free) : SetFormula bound free :=
  let left : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((pair.weakenFree SetSort.set) ≐ₘ
      ⟨left, right.weakenFree SetSort.set⟩ₘ)
    |>.existsFreeTop SetSort.set

/-- 对固定有序对断言其右投影存在。 -/
def right_projection_exists {bound free : SetContext}
    (pair : SetTerm bound free) : SetFormula bound free :=
  let right : SetTerm bound (SetSort.set :: free) := .fvar .here
  (right_projection_spec (pair.weakenFree SetSort.set) right)
    |>.existsFreeTop SetSort.set

/-! ## 投影与反转函数符号 -/

/-- 左投影函数符号的开放定义实例。 -/
def left_projection_definition_instance {bound free : SetContext}
    (pair candidate : SetTerm bound free) : SetFormula bound free :=
  is_ordered_pair_formula pair ⟶ₘ
    (((pair)₀ₘ ≐ₘ candidate) ↔ₘ left_projection_spec pair candidate)

/-- 左投影函数符号的闭定义公理。 -/
def left_projection_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (left_projection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 在有序对谓词理论上加入左投影函数符号。 -/
def left_projection_operator_theory : SetTheory :=
  Theory.insert left_projection_definition_axiom relation_function_theory

/-- 右投影函数符号的开放定义实例。 -/
def right_projection_definition_instance {bound free : SetContext}
    (pair candidate : SetTerm bound free) : SetFormula bound free :=
  is_ordered_pair_formula pair ⟶ₘ
    (((pair)₁ₘ ≐ₘ candidate) ↔ₘ right_projection_spec pair candidate)

/-- 右投影函数符号的闭定义公理。 -/
def right_projection_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (right_projection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 在左投影理论上加入右投影函数符号。 -/
def right_projection_operator_theory : SetTheory :=
  Theory.insert right_projection_definition_axiom left_projection_operator_theory

/-- `reverse` 是交换 `pair` 两个坐标得到的规范有序对。 -/
def ordered_pair_reverse_spec {bound free : SetContext}
    (pair reverse : SetTerm bound free) : SetFormula bound free :=
  reverse ≐ₘ ⟨(pair)₁ₘ, (pair)₀ₘ⟩ₘ

/-- 文献中的反转规格：结果是有序对，且两个投影交换。 -/
def ordered_pair_reverse_paper_spec {bound free : SetContext}
    (pair reverse : SetTerm bound free) : SetFormula bound free :=
  is_ordered_pair_formula reverse ∧ₘ
    (((reverse)₀ₘ ≐ₘ (pair)₁ₘ) ∧ₘ
      ((reverse)₁ₘ ≐ₘ (pair)₀ₘ))

/-- 对固定有序对断言一个满足文献规格的反转结果存在。 -/
def ordered_pair_reverse_exists {bound free : SetContext}
    (pair : SetTerm bound free) : SetFormula bound free :=
  let reverse : SetTerm bound (SetSort.set :: free) := .fvar .here
  (ordered_pair_reverse_paper_spec
      (pair.weakenFree SetSort.set) reverse)
    |>.existsFreeTop SetSort.set

/-- 有序对反转函数符号的开放定义实例。 -/
def ordered_pair_reverse_definition_instance {bound free : SetContext}
    (pair candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ pair⁻¹ₘ) ↔ₘ ordered_pair_reverse_spec pair candidate

/-- 有序对反转函数符号的闭定义公理。 -/
def ordered_pair_reverse_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (ordered_pair_reverse_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 在左右投影理论上加入有序对反转函数符号。 -/
def ordered_pair_reverse_operator_theory : SetTheory :=
  Theory.insert ordered_pair_reverse_definition_axiom
    right_projection_operator_theory

/-! ## 结构自然性 -/

@[simp] theorem ordered_pair_member_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (member left right : SetTerm bound sourceFree) :
    (ordered_pair_member_condition member left right).renameMapped
        VariableRenaming.id ρ =
      ordered_pair_member_condition
        (member.renameMapped VariableRenaming.id ρ)
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ) := by
  simp [ordered_pair_member_condition, singleton_term,
    unordered_pair_term, Term.renameMapped, Arguments.renameMapped,
    Formula.renameMapped]

/-- 有序对函数项与任意 bound/free 重命名严格交换。 -/
@[simp] theorem ordered_pair_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (left right : SetTerm sourceBound sourceFree) :
    (⟨left, right⟩ₘ).renameMapped boundRenaming freeRenaming =
      ⟨left.renameMapped boundRenaming freeRenaming,
        right.renameMapped boundRenaming freeRenaming⟩ₘ := by
  simp [ordered_pair_term, Term.renameMapped,
    Arguments.renameMapped]

/-- 左投影函数项与任意 bound/free 重命名严格交换。 -/
@[simp] theorem left_projection_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (pair : SetTerm sourceBound sourceFree) :
    ((pair)₀ₘ).renameMapped boundRenaming freeRenaming =
      (pair.renameMapped boundRenaming freeRenaming)₀ₘ := by
  simp [left_projection_term, Term.renameMapped,
    Arguments.renameMapped]

/-- 右投影函数项与任意 bound/free 重命名严格交换。 -/
@[simp] theorem right_projection_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (pair : SetTerm sourceBound sourceFree) :
    ((pair)₁ₘ).renameMapped boundRenaming freeRenaming =
      (pair.renameMapped boundRenaming freeRenaming)₁ₘ := by
  simp [right_projection_term, Term.renameMapped,
    Arguments.renameMapped]

/-- 有序对反转函数项与任意 bound/free 重命名严格交换。 -/
@[simp] theorem ordered_pair_reverse_term_renameMapped
    {sourceBound targetBound sourceFree targetFree : SetContext}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (pair : SetTerm sourceBound sourceFree) :
    pair⁻¹ₘ.renameMapped boundRenaming freeRenaming =
      (pair.renameMapped boundRenaming freeRenaming)⁻¹ₘ := by
  simp [ordered_pair_reverse_term, Term.renameMapped,
    Arguments.renameMapped]

@[simp] theorem ordered_pair_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (left right pair : SetTerm bound sourceFree) :
    (ordered_pair_spec left right pair).renameMapped
        VariableRenaming.id ρ =
      ordered_pair_spec
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ)
        (pair.renameMapped VariableRenaming.id ρ) := by
  unfold ordered_pair_spec
  rw [pair_spec_renameMapped]
  simp [singleton_term, unordered_pair_term,
    Term.renameMapped, Arguments.renameMapped]

@[simp] theorem ordered_pair_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (left right pair : SetTerm bound free) :
    (ordered_pair_spec left right pair).weakenFree introduced =
      ordered_pair_spec
        (left.weakenFree introduced)
        (right.weakenFree introduced)
        (pair.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact ordered_pair_spec_renameMapped
    (VariableRenaming.weaken introduced) left right pair

@[simp] theorem left_projection_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (pair left : SetTerm bound sourceFree) :
    (left_projection_spec pair left).renameMapped VariableRenaming.id ρ =
      left_projection_spec
        (pair.renameMapped VariableRenaming.id ρ)
        (left.renameMapped VariableRenaming.id ρ) := by
  unfold left_projection_spec
  rw [Formula.renameMapped_forallFreeTop]
  simp only [Formula.renameMapped]
  rw [intersection_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

@[simp] theorem left_projection_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (pair left : SetTerm bound free) :
    (left_projection_spec pair left).weakenFree introduced =
      left_projection_spec (pair.weakenFree introduced)
        (left.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact left_projection_spec_renameMapped
    (VariableRenaming.weaken introduced) pair left

/-- 左投影规格的顶部参数槽实例化后恢复原上下文规格。 -/
@[simp] theorem left_projection_spec_instantiateFreeTop_context
    {bound free : SetContext}
    (pair candidate : SetTerm bound free) :
    (left_projection_spec
        (pair.weakenFree SetSort.set)
        (.fvar .here : SetTerm bound (SetSort.set :: free))).instantiateFreeTop
          candidate =
        left_projection_spec pair candidate := by
  unfold left_projection_spec intersection_member_condition
  rw [Formula.instantiateFreeTop_forallFreeTop]
  simp [Formula.substituteFree,
    Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop]

/-- 右投影规格的顶部参数槽实例化后恢复原上下文规格。 -/
@[simp] theorem right_projection_spec_instantiateFreeTop_context
    {bound free : SetContext}
    (pair candidate : SetTerm bound free) :
    (right_projection_spec
        (pair.weakenFree SetSort.set)
        (.fvar .here : SetTerm bound (SetSort.set :: free))).instantiateFreeTop
          candidate =
        right_projection_spec pair candidate := by
  unfold right_projection_spec
  rw [Formula.instantiateFreeTop_existsFreeTop]
  simp [Formula.substituteFree,
    Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop]

/-- 右投影规格与 free 重命名自然交换。 -/
@[simp] theorem right_projection_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (pair right : SetTerm bound sourceFree) :
    (right_projection_spec pair right).renameMapped VariableRenaming.id ρ =
      right_projection_spec
        (pair.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ) := by
  unfold right_projection_spec
  rw [Formula.renameMapped_existsFreeTop]
  simp only [Formula.renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rw [ordered_pair_term_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 右投影规格与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem right_projection_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (pair right : SetTerm bound free) :
    (right_projection_spec pair right).weakenFree introduced =
      right_projection_spec (pair.weakenFree introduced)
        (right.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact right_projection_spec_renameMapped
    (VariableRenaming.weaken introduced) pair right

/-! ## 理论嵌入 -/

derive_theory_subset singleton_operator_theory ⊆ ordered_pair_operator_theory

derive_theory_subset ordered_pair_operator_theory ⊆ relation_function_theory

derive_theory_subset singleton_operator_theory ⊆ relation_function_theory

derive_theory_subset extensionality_theory ⊆ ordered_pair_operator_theory

derive_theory_subset relation_function_theory ⊆ left_projection_operator_theory

derive_theory_subset ordered_pair_operator_theory ⊆ left_projection_operator_theory

derive_theory_subset left_projection_operator_theory ⊆ right_projection_operator_theory

derive_theory_subset right_projection_operator_theory ⊆ ordered_pair_reverse_operator_theory

derive_theory_subset relation_function_theory ⊆ right_projection_operator_theory

derive_theory_subset ordered_pair_operator_theory ⊆ right_projection_operator_theory

derive_theory_subset relation_function_theory ⊆ ordered_pair_reverse_operator_theory

/-! ## 有序对存在、唯一性与定义合同 -/

theorem ordered_pair_paper_condition_iff_member_condition
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (member left right : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      ordered_pair_paper_condition member left right ↔ₘ
        ordered_pair_member_condition member left right := by
  simpa [ordered_pair_paper_condition,
    ordered_pair_member_condition] using
    (Metatheory.Derives.neg_imp_disj_iff_m
      (T := T) (Γ := Γ)
      (φ := member ≐ₘ {left}ₘ)
      (ψ := member ≐ₘ {left, right}ₘ))

theorem ordered_pair_paper_spec_iff_spec
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right pair : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      ordered_pair_paper_spec left right pair ↔ₘ
        ordered_pair_spec left right pair := by
  unfold ordered_pair_paper_spec ordered_pair_spec pair_spec
  apply Metatheory.Derives.forall_iff_mono
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  have hCondition := ordered_pair_paper_condition_iff_member_condition
    (T := T) (Γ := FreshVariable.extendContext SetSort.set Γ)
    member (left.weakenFree SetSort.set)
    (right.weakenFree SetSort.set)
  simpa [member, FreshVariable.newest,
    ordered_pair_member_condition] using!
    (Metatheory.Derives.iff_right_congr_m
      (φ := member ∈ₘ pair.weakenFree SetSort.set) hCondition)

theorem ordered_pair_paper_exists_iff_exists
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      ordered_pair_paper_exists left right ↔ₘ
        ordered_pair_exists left right := by
  unfold ordered_pair_paper_exists ordered_pair_exists
  apply Metatheory.Derives.exists_iff_mono
  let pair : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  simpa [pair, FreshVariable.newest] using!
    (ordered_pair_paper_spec_iff_spec
      (T := T) (Γ := FreshVariable.extendContext SetSort.set Γ)
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) pair)

theorem ordered_pair_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_theory] ordered_pair_exists left right := by
  simpa [ordered_pair_exists, ordered_pair_spec] using!
    (pair_exists_derives (Γ := Γ) {left}ₘ {left, right}ₘ)

theorem ordered_pair_paper_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_theory] ordered_pair_paper_exists left right := by
  exact FirstOrder.Derives.iff_elim_right
    (ordered_pair_paper_exists_iff_exists
      (T := pairing_theory) (Γ := Γ) left right)
    (ordered_pair_exists_derives (Γ := Γ) left right)

theorem ordered_pair_unique
    {free : SetContext} {Γ : Context signature free}
    (first second left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      ordered_pair_spec first second left ⟶ₘ
        ordered_pair_spec first second right ⟶ₘ (left ≐ₘ right) := by
  simpa [ordered_pair_spec] using
    (pair_unique (Γ := Γ) {first}ₘ {first, second}ₘ left right)

theorem ordered_pair_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_operator_theory]
      ordered_pair_definition_instance left right candidate := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    ordered_pair_definition_instance
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
      ([] : Context signature []) ⊢ₘ[ordered_pair_operator_theory]
        Formula.fromSentence ordered_pair_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, ordered_pair_definition_axiom,
    ordered_pair_definition_instance, ordered_pair_spec,
    pair_spec, pair_member_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

theorem ordered_pair_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_operator_theory]
      ordered_pair_spec left right ⟨left, right⟩ₘ := by
  have hDefinition := ordered_pair_definition_instance_derives
    (Γ := Γ) left right ⟨left, right⟩ₘ
  exact FirstOrder.Derives.iff_elim_left hDefinition
    (Metatheory.Derives.equality_refl
      (T := ordered_pair_operator_theory) (Γ := Γ) ⟨left, right⟩ₘ)

theorem ordered_pair_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_operator_theory]
      (candidate ≐ₘ ⟨left, right⟩ₘ) ↔ₘ
        ordered_pair_spec left right candidate :=
  ordered_pair_definition_instance_derives (Γ := Γ) left right candidate

theorem is_ordered_pair_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[relation_function_theory]
      is_ordered_pair_definition_instance pair := by
  let body : SetOpenFormula [SetSort.set] :=
    is_ordered_pair_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set])
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons pair VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[relation_function_theory]
        Formula.fromSentence is_ordered_pair_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, is_ordered_pair_definition_axiom,
    is_ordered_pair_definition_instance, is_ordered_pair_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-! ## 左投影的抽象性质 -/

theorem left_projection_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (pair left member : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] left_projection_spec pair left) :
    Γ ⊢ₘ[T]
      intersection_member_condition pair member ↔ₘ (member ≐ₘ left) := by
  have hAt := FirstOrder.Derives.forall_elim member hSpec
  simpa [left_projection_spec,
    intersection_member_condition, Formula.instantiateFreeTop,
    Formula.substituteFree, Substitution.free_map,
    Substitution.instantiateFreeTop, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hAt

theorem left_projection_unique
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (pair left right : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      left_projection_spec pair left ⟶ₘ
        left_projection_spec pair right ⟶ₘ (left ≐ₘ right) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    left_projection_spec pair right ::
      left_projection_spec pair left :: Γ
  have hLeftSpec : Δ ⊢ₘ[T] left_projection_spec pair left :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hRightSpec : Δ ⊢ₘ[T] left_projection_spec pair right :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hLeftAtLeft := left_projection_spec_membership_iff
    pair left left hLeftSpec
  have hRightAtLeft := left_projection_spec_membership_iff
    pair right left hRightSpec
  have hCommon : Δ ⊢ₘ[T] intersection_member_condition pair left :=
    FirstOrder.Derives.iff_elim_right hLeftAtLeft
      (Metatheory.Derives.equality_refl (T := T) (Γ := Δ) left)
  exact FirstOrder.Derives.iff_elim_left hRightAtLeft hCommon

/-- 规范 Kuratowski 有序对的左投影是第一坐标。 -/
theorem ordered_pair_term_left_projection_spec
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_operator_theory]
      left_projection_spec ⟨left, right⟩ₘ left := by
  unfold left_projection_spec
  apply FirstOrder.Derives.forall_intro
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let left' := left.weakenFree SetSort.set
  let right' := right.weakenFree SetSort.set
  let singleton : SetOpenTerm (SetSort.set :: free) := {left'}ₘ
  let pair : SetOpenTerm (SetSort.set :: free) := {left', right'}ₘ
  let ordered : SetOpenTerm (SetSort.set :: free) := ⟨left', right'⟩ₘ
  let Θ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Γ
  have hOuterSpec :
      Θ ⊢ₘ[ordered_pair_operator_theory]
        pair_spec singleton pair ordered := by
    simpa [left', right', singleton, pair, ordered,
      ordered_pair_spec] using
      (ordered_pair_term_spec_derives
        (Γ := Θ) left' right')
  have hSingletonSpec :
      Θ ⊢ₘ[ordered_pair_operator_theory]
        singleton_spec left' singleton :=
    FirstOrder.Derives.theory_weaken
      singleton_operator_theory_subset_ordered_pair_operator_theory
      (by simpa [singleton] using
        (singleton_term_spec_derives (Γ := Θ) left'))
  have hPairSpec :
      Θ ⊢ₘ[ordered_pair_operator_theory]
        pair_spec left' right' pair :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence =>
        singleton_operator_theory_subset_ordered_pair_operator_theory
          (Or.inr hSentence))
      (by simpa [pair] using
        (unordered_pair_term_spec_derives (Γ := Θ) left' right'))
  have hCommonBridge := FirstOrder.Derives.imp_elim
    (pair_common_member_condition_iff
      (T := ordered_pair_operator_theory) (Γ := Θ)
      singleton pair ordered member)
    hOuterSpec
  have hSingletonAt := singleton_spec_membership_iff
    left' singleton member hSingletonSpec
  have hPairAt := pair_spec_membership_iff
    left' right' pair member hPairSpec
  apply FirstOrder.Derives.iff_intro
  · have hCommon :
        intersection_member_condition ordered member :: Θ
          ⊢ₘ[ordered_pair_operator_theory]
            intersection_member_condition ordered member :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hMemberships := FirstOrder.Derives.iff_elim_left
      (FirstOrder.Derives.context_weaken_cons hCommonBridge) hCommon
    have hSingletonMembership :=
      FirstOrder.Derives.conj_elim_left hMemberships
    exact FirstOrder.Derives.iff_elim_left
      (FirstOrder.Derives.context_weaken_cons hSingletonAt)
      hSingletonMembership
  · have hEquality :
        (member ≐ₘ left') :: Θ ⊢ₘ[ordered_pair_operator_theory]
          member ≐ₘ left' :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hSingletonMembership := FirstOrder.Derives.iff_elim_right
      (FirstOrder.Derives.context_weaken_cons hSingletonAt) hEquality
    have hPairMembership := FirstOrder.Derives.iff_elim_right
      (FirstOrder.Derives.context_weaken_cons hPairAt)
      (FirstOrder.Derives.disj_intro_left hEquality)
    exact FirstOrder.Derives.iff_elim_right
      (FirstOrder.Derives.context_weaken_cons hCommonBridge)
      (FirstOrder.Derives.conj_intro
        hSingletonMembership hPairMembership)

/-- 左投影规格的对象单孔模板在顶部实例化后恢复开放规格。 -/
@[simp] theorem left_projection_spec_instantiateTop_pair_context
    {free : SetContext}
    (left replacement : SetOpenTerm free) :
    (left_projection_spec
        (.bvar .here : SetTerm [SetSort.set] free)
        (left.weakenBound SetSort.set)).instantiateTop replacement =
      left_projection_spec replacement left := by
  unfold left_projection_spec intersection_member_condition
  rw [Formula.instantiateTop_forallFreeTop]
  simp
  rw [Term.instantiateTop_bvar_here]

/-- 有序对对象等式可反向运输左投影规格。 -/
theorem left_projection_spec_transport_pair_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (first second left : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] first ≐ₘ second)
    (hSpec : Γ ⊢ₘ[T] left_projection_spec second left) :
    Γ ⊢ₘ[T] left_projection_spec first left := by
  let body : SetFormula [SetSort.set] free :=
    left_projection_spec
      (.bvar .here : SetTerm [SetSort.set] free)
      (left.weakenBound SetSort.set)
  have hTransport := Metatheory.Derives.equality_iff_of_equality
    (T := T) (Γ := Γ) body hEquality
  dsimp [body] at hTransport
  rw [left_projection_spec_instantiateTop_pair_context,
    left_projection_spec_instantiateTop_pair_context] at hTransport
  exact FirstOrder.Derives.iff_elim_right hTransport hSpec

/-- 两个坐标等式可组合为有序对函数项等式。 -/
theorem ordered_pair_term_congr_of_equalities
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond : SetOpenTerm free)
    (hFirst : Γ ⊢ₘ[T] leftFirst ≐ₘ rightFirst)
    (hSecond : Γ ⊢ₘ[T] leftSecond ≐ₘ rightSecond) :
    Γ ⊢ₘ[T]
      ⟨leftFirst, leftSecond⟩ₘ ≐ₘ
        ⟨rightFirst, rightSecond⟩ₘ := by
  let firstContext : SetTerm [SetSort.set] free :=
    ⟨(.bvar .here : SetTerm [SetSort.set] free),
      leftSecond.weakenBound SetSort.set⟩ₘ
  let secondContext : SetTerm [SetSort.set] free :=
    ⟨rightFirst.weakenBound SetSort.set,
      (.bvar .here : SetTerm [SetSort.set] free)⟩ₘ
  have hFirstContext (first : SetOpenTerm free) :
      firstContext.instantiateTop first = ⟨first, leftSecond⟩ₘ := by
    change
      ⟨((Term.bvar .here : SetTerm [SetSort.set] free).instantiateTop first),
        ((leftSecond.weakenBound SetSort.set).instantiateTop first)⟩ₘ =
        ⟨first, leftSecond⟩ₘ
    rw [Term.instantiateTop_bvar_here,
      Term.instantiateTop_weakenBound]
  have hSecondContext (second : SetOpenTerm free) :
      secondContext.instantiateTop second =
        ⟨rightFirst, second⟩ₘ := by
    change
      ⟨((rightFirst.weakenBound SetSort.set).instantiateTop second),
        ((Term.bvar .here : SetTerm [SetSort.set] free).instantiateTop second)⟩ₘ =
        ⟨rightFirst, second⟩ₘ
    rw [Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here]
  have hMiddle :
      firstContext.instantiateTop rightFirst =
        secondContext.instantiateTop leftSecond :=
    (hFirstContext rightFirst).trans (hSecondContext leftSecond).symm
  have hResult :=
    Metatheory.Derives.term_context_pair_congr_of_equalities
      (T := T) (Γ := Γ) firstContext secondContext hMiddle
      hFirst hSecond
  rw [hFirstContext leftFirst, hSecondContext rightSecond] at hResult
  exact hResult

/-- Kuratowski 有序对函数项相等，当且仅当两坐标分别相等。 -/
theorem ordered_pair_term_eq_iff_coordinates
    {free : SetContext} {Γ : Context signature free}
    (left₁ right₁ left₂ right₂ : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_operator_theory]
      (⟨left₁, right₁⟩ₘ ≐ₘ ⟨left₂, right₂⟩ₘ) ↔ₘ
        ((left₁ ≐ₘ left₂) ∧ₘ (right₁ ≐ₘ right₂)) := by
  apply FirstOrder.Derives.iff_intro
  · let pairEquality : SetOpenFormula free :=
      ⟨left₁, right₁⟩ₘ ≐ₘ ⟨left₂, right₂⟩ₘ
    let Δ : Context signature free := pairEquality :: Γ
    have hPairEquality :
        Δ ⊢ₘ[ordered_pair_operator_theory] pairEquality :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hLeftSpec₁ := ordered_pair_term_left_projection_spec
      (Γ := Δ) left₁ right₁
    have hLeftSpec₂ := ordered_pair_term_left_projection_spec
      (Γ := Δ) left₂ right₂
    have hLeftSpec₂AtFirst :=
      left_projection_spec_transport_pair_of_equality
        (T := ordered_pair_operator_theory) (Γ := Δ)
        ⟨left₁, right₁⟩ₘ ⟨left₂, right₂⟩ₘ left₂
        hPairEquality hLeftSpec₂
    have hLeftEquality :
        Δ ⊢ₘ[ordered_pair_operator_theory] left₁ ≐ₘ left₂ :=
      FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim
          (left_projection_unique
            (T := ordered_pair_operator_theory) (Γ := Δ)
            ⟨left₁, right₁⟩ₘ left₁ left₂)
          hLeftSpec₁)
        hLeftSpec₂AtFirst
    let singletonContext : SetTerm [SetSort.set] free :=
      {(.bvar .here : SetTerm [SetSort.set] free)}ₘ
    have hSingletonEquality :
        Δ ⊢ₘ[ordered_pair_operator_theory] {left₁}ₘ ≐ₘ {left₂}ₘ := by
      have hCongruence :=
        Metatheory.Derives.term_context_congr_of_equality
          (T := ordered_pair_operator_theory) (Γ := Δ)
          singletonContext hLeftEquality
      simpa [singletonContext] using! hCongruence
    have hOuterSpec₁ :
        Δ ⊢ₘ[ordered_pair_operator_theory]
          pair_spec {left₁}ₘ {left₁, right₁}ₘ ⟨left₁, right₁⟩ₘ := by
      simpa [ordered_pair_spec] using
        (ordered_pair_term_spec_derives (Γ := Δ) left₁ right₁)
    have hOuterSpec₂ :
        Δ ⊢ₘ[ordered_pair_operator_theory]
          pair_spec {left₂}ₘ {left₂, right₂}ₘ ⟨left₂, right₂⟩ₘ := by
      simpa [ordered_pair_spec] using
        (ordered_pair_term_spec_derives (Γ := Δ) left₂ right₂)
    have hOuterSpec₂AtFirst := pair_spec_transport_first_of_equality
      {left₁}ₘ {left₂}ₘ {left₂, right₂}ₘ ⟨left₂, right₂⟩ₘ
      hSingletonEquality hOuterSpec₂
    have hInnerPairEquality :
        Δ ⊢ₘ[ordered_pair_operator_theory]
          {left₁, right₁}ₘ ≐ₘ {left₂, right₂}ₘ :=
      pair_spec_right_unique_of_pair_equality
        {left₁}ₘ {left₁, right₁}ₘ {left₂, right₂}ₘ
        ⟨left₁, right₁⟩ₘ ⟨left₂, right₂⟩ₘ
        hOuterSpec₁ hOuterSpec₂AtFirst hPairEquality
    have hInnerSpec₁ :
        Δ ⊢ₘ[ordered_pair_operator_theory]
          pair_spec left₁ right₁ {left₁, right₁}ₘ :=
      FirstOrder.Derives.theory_weaken
        (fun hSentence =>
          singleton_operator_theory_subset_ordered_pair_operator_theory
            (Or.inr hSentence))
        (unordered_pair_term_spec_derives (Γ := Δ) left₁ right₁)
    have hInnerSpec₂ :
        Δ ⊢ₘ[ordered_pair_operator_theory]
          pair_spec left₂ right₂ {left₂, right₂}ₘ :=
      FirstOrder.Derives.theory_weaken
        (fun hSentence =>
          singleton_operator_theory_subset_ordered_pair_operator_theory
            (Or.inr hSentence))
        (unordered_pair_term_spec_derives (Γ := Δ) left₂ right₂)
    have hInnerSpec₂AtFirst := pair_spec_transport_first_of_equality
      left₁ left₂ right₂ {left₂, right₂}ₘ
      hLeftEquality hInnerSpec₂
    have hRightEquality :
        Δ ⊢ₘ[ordered_pair_operator_theory] right₁ ≐ₘ right₂ :=
      pair_spec_right_unique_of_pair_equality
        left₁ right₁ right₂ {left₁, right₁}ₘ {left₂, right₂}ₘ
        hInnerSpec₁ hInnerSpec₂AtFirst hInnerPairEquality
    exact FirstOrder.Derives.conj_intro hLeftEquality hRightEquality
  · let coordinateEqualities : SetOpenFormula free :=
      (left₁ ≐ₘ left₂) ∧ₘ (right₁ ≐ₘ right₂)
    let Δ : Context signature free := coordinateEqualities :: Γ
    have hCoordinates :
        Δ ⊢ₘ[ordered_pair_operator_theory] coordinateEqualities :=
      FirstOrder.Derives.assumption List.mem_cons_self
    exact ordered_pair_term_congr_of_equalities
      left₁ left₂ right₁ right₂
      (FirstOrder.Derives.conj_elim_left hCoordinates)
      (FirstOrder.Derives.conj_elim_right hCoordinates)

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
