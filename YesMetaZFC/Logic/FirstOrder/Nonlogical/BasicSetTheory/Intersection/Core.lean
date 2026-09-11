import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.EmptySet
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Pairing

/-!
# 非空族交集核心

交集成员条件直接建立在内在类型语法上。存在性只复用一个参数化分离谓词：
先从非空族取得规范 fresh 成员，再在该成员中分离所有公共元素。整个构造不再
携带变量编号、admissibility、闭性证书或描述符兼容层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- `element` 属于 `family` 的每个成员。 -/
def intersection_member_condition {bound free : SetContext}
    (family element : SetTerm bound free) : SetFormula bound free :=
  let member : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((member ∈ₘ family.weakenFree SetSort.set) ⟶ₘ
    (element.weakenFree SetSort.set ∈ₘ member))
    |>.forallFreeTop SetSort.set

/-- `candidate` 恰由 `family` 的公共元素组成。 -/
def intersection_spec {bound free : SetContext}
    (family candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (intersection_member_condition
      (family.weakenFree SetSort.set) element)

/-- 对固定族断言一个交集候选存在。 -/
def intersection_exists {bound free : SetContext}
    (family : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (intersection_spec (family.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 公共成员条件与 free 重命名自然交换。 -/
@[simp] theorem intersection_member_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (family element : SetTerm bound sourceFree) :
    (intersection_member_condition family element).renameMapped
        VariableRenaming.id ρ =
      intersection_member_condition
        (family.renameMapped VariableRenaming.id ρ)
        (element.renameMapped VariableRenaming.id ρ) := by
  unfold intersection_member_condition
  rw [Formula.renameMapped_forallFreeTop]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 交集规格与 free 重命名自然交换。 -/
@[simp] theorem intersection_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (family candidate : SetTerm bound sourceFree) :
    (intersection_spec family candidate).renameMapped
        VariableRenaming.id ρ =
      intersection_spec
        (family.renameMapped VariableRenaming.id ρ)
        (candidate.renameMapped VariableRenaming.id ρ) := by
  unfold intersection_spec
  rw [membership_specification_renameMapped]
  rw [intersection_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 交集规格与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem intersection_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (family candidate : SetTerm bound free) :
    (intersection_spec family candidate).weakenFree introduced =
      intersection_spec (family.weakenFree introduced)
        (candidate.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact intersection_spec_renameMapped
    (VariableRenaming.weaken introduced) family candidate

/-- 交集存在式与 free 重命名自然交换。 -/
@[simp] theorem intersection_exists_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (family : SetTerm bound sourceFree) :
    (intersection_exists family).renameMapped VariableRenaming.id ρ =
      intersection_exists
        (family.renameMapped VariableRenaming.id ρ) := by
  unfold intersection_exists
  rw [Formula.renameMapped_existsFreeTop]
  rw [intersection_spec_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 以 `family` 为参数的公共元素分离谓词。 -/
def intersection_predicate {free : SetContext}
    (family : SetOpenTerm free) : SetPredicate free where
  body :=
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    (intersection_member_condition
      (family.weakenFree SetSort.set) element).abstractFreeTop

/-- 从 `source` 中分离 `family` 的公共元素。 -/
def intersection_separation_spec {bound free : SetContext}
    (family source candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ source.weakenFree SetSort.set) ∧ₘ
      intersection_member_condition
        (family.weakenFree SetSort.set) element)

/-- 对固定族与承载集合断言上述分离结果存在。 -/
def intersection_separation_exists {bound free : SetContext}
    (family source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (intersection_separation_spec
    (family.weakenFree SetSort.set)
    (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 在外延理论上加入公共元素分离公理。 -/
def intersection_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext) (family : SetOpenTerm free),
      sentence = (intersection_predicate family).separation_axiom) ∨
    extensionality_theory sentence

/-- 交集存在性所需的最弱基础理论。 -/
def intersection_base_theory : SetTheory :=
  Theory.union intersection_separation_theory empty_set_symbol_theory

/-- 一元交函数符号的开放定义实例。 -/
def intersection_definition_instance {bound free : SetContext}
    (family candidate : SetTerm bound free) : SetFormula bound free :=
  set_nonempty_condition family ⟶ₘ
    ((candidate ≐ₘ ⋂ₘ family) ↔ₘ intersection_spec family candidate)

/-- 一元交函数符号的闭定义公理。 -/
def intersection_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (intersection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 在交集存在理论上加入一元交函数符号。 -/
def intersection_operator_theory : SetTheory :=
  Theory.insert intersection_definition_axiom intersection_base_theory

/-- `candidate` 恰由同时属于 `left` 与 `right` 的元素组成。 -/
def binary_intersection_spec {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    ((element ∈ₘ left.weakenFree SetSort.set) ∧ₘ
      (element ∈ₘ right.weakenFree SetSort.set))

/-- 配对与一元交函数符号理论的合并。 -/
def binary_intersection_base_theory : SetTheory :=
  Theory.union pairing_operator_theory intersection_operator_theory

/-- 二元交函数符号的开放定义实例。 -/
def binary_intersection_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ∩ₘ right) ≐ₘ (⋂ₘ {left, right}ₘ)

/-- 二元交函数符号的闭定义公理。 -/
def binary_intersection_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (binary_intersection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 在配对与一元交函数符号理论上加入二元交函数符号。 -/
def binary_intersection_operator_theory : SetTheory :=
  Theory.insert binary_intersection_definition_axiom
    binary_intersection_base_theory

/-- 公共元素分离理论嵌入交集基础理论。 -/
derive_theory_subset intersection_separation_theory ⊆ intersection_base_theory

/-- 空集符号理论嵌入交集基础理论。 -/
derive_theory_subset empty_set_symbol_theory ⊆ intersection_base_theory

/-- 外延理论嵌入交集基础理论。 -/
derive_theory_subset extensionality_theory ⊆ intersection_base_theory

/-- 交集基础理论嵌入一元交函数符号理论。 -/
derive_theory_subset intersection_base_theory ⊆ intersection_operator_theory

/-- 配对函数符号理论嵌入二元交基础理论。 -/
derive_theory_subset pairing_operator_theory ⊆ binary_intersection_base_theory

/-- 一元交函数符号理论嵌入二元交基础理论。 -/
derive_theory_subset intersection_operator_theory ⊆ binary_intersection_base_theory

/-- 二元交基础理论嵌入二元交函数符号理论。 -/
derive_theory_subset binary_intersection_base_theory ⊆ binary_intersection_operator_theory

/-- 一元交函数符号理论嵌入二元交函数符号理论。 -/
derive_theory_subset intersection_operator_theory ⊆ binary_intersection_operator_theory

/-- 配对函数符号理论嵌入二元交函数符号理论。 -/
derive_theory_subset pairing_operator_theory ⊆ binary_intersection_operator_theory

/-- 外延理论嵌入二元交函数符号理论。 -/
derive_theory_subset extensionality_theory ⊆ binary_intersection_operator_theory

/-- 公共成员条件可在任意给定族成员处消去。 -/
theorem intersection_member_condition_elim
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (family member element : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      intersection_member_condition family element ⟶ₘ
        (member ∈ₘ family) ⟶ₘ (element ∈ₘ member) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  have hUniversal :
      ((member ∈ₘ family) ::
        intersection_member_condition family element :: Γ) ⊢ₘ[T]
          intersection_member_condition family element :=
    FirstOrder.Derives.assumption (by simp)
  have hAt := FirstOrder.Derives.forall_elim member hUniversal
  have hImplication :
      ((member ∈ₘ family) ::
        intersection_member_condition family element :: Γ) ⊢ₘ[T]
          (member ∈ₘ family) ⟶ₘ (element ∈ₘ member) := by
    simpa [intersection_member_condition] using! hAt
  exact FirstOrder.Derives.imp_elim hImplication
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 交集规格在任意元素处的点态实例。 -/
theorem intersection_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (family candidate element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] intersection_spec family candidate) :
    Γ ⊢ₘ[T]
      (element ∈ₘ candidate) ↔ₘ
        intersection_member_condition family element := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  simpa [intersection_spec, intersection_member_condition,
    membership_specification, Formula.instantiateFreeTop,
    Formula.substituteFree, Substitution.free_map,
    Substitution.instantiateFreeTop, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hAt

/-- 参数化公共元素谓词在规范 fresh 元素处直接恢复公共成员条件。 -/
@[simp] theorem intersection_predicate_atNewest
    {free : SetContext} (family : SetOpenTerm free) :
    (intersection_predicate family).atNewest =
      intersection_member_condition
        (family.weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set) := by
  simp [SetPredicate.atNewest, intersection_predicate,
    intersection_member_condition, FreshVariable.newest]

/-- 谓词参数扩张后在下一规范 fresh 元素处仍命中同一快路径。 -/
@[simp] theorem intersection_predicate_weakenFree_atNewest
    {free : SetContext} (family : SetOpenTerm free) :
    ((intersection_predicate family).weakenFree).atNewest =
      intersection_member_condition
        ((family.weakenFree SetSort.set).weakenFree SetSort.set)
        (FreshVariable.newest
          (σ := signature) (free := SetSort.set :: free) SetSort.set) := by
  unfold SetPredicate.atNewest SetPredicate.weakenFree
    intersection_predicate
  dsimp
  simp only [FreshVariable.newest]
  rw [Formula.instantiateTop_two_weakenings_abstractFreeTop_newest]
  change
    (intersection_member_condition
      (family.weakenFree SetSort.set)
      (Term.newestFree
        (σ := signature) (free := free) SetSort.set)).renameMapped
        VariableRenaming.id
        (VariableRenaming.lift (introduced := SetSort.set)
          (VariableRenaming.weaken SetSort.set)) =
      intersection_member_condition
        ((family.weakenFree SetSort.set).weakenFree SetSort.set)
        (Term.newestFree
          (σ := signature) (free := SetSort.set :: free) SetSort.set)
  rw [intersection_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 公共元素分离 schema 可直接消费任意族与承载集合。 -/
theorem intersection_separation_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (family source : SetOpenTerm free) :
    Γ ⊢ₘ[intersection_base_theory]
      intersection_separation_exists family source := by
  have hGeneric := SetPredicate.separation_exists_derives
    (Γ := Γ) (intersection_predicate family) source
  have hLifted := FirstOrder.Derives.theory_weaken
    (T := (intersection_predicate family).separation_theory)
    (U := intersection_base_theory)
    (by
      intro sentence hSentence
      rcases hSentence with rfl | hExtensionality
      · exact Or.inl (Or.inl ⟨free, family, rfl⟩)
      · exact Or.inl (Or.inr hExtensionality))
    hGeneric
  simpa [intersection_separation_exists,
    intersection_separation_spec,
    SetPredicate.separation_exists, SetPredicate.separation_spec,
    SetPredicate.separation_condition, membership_specification,
    FreshVariable.newest] using! hLifted

/-- 一元交定义公理可在任意族与候选项处实例化。 -/
theorem intersection_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (family candidate : SetOpenTerm free) :
    Γ ⊢ₘ[intersection_operator_theory]
      intersection_definition_instance family candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    intersection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons family VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[intersection_operator_theory]
        Formula.fromSentence intersection_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, intersection_definition_axiom,
    intersection_definition_instance, intersection_spec,
    intersection_member_condition, set_nonempty_condition,
    membership_specification, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 二元交定义公理可在任意两个集合项处实例化。 -/
theorem binary_intersection_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[binary_intersection_operator_theory]
      binary_intersection_definition_instance left right := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    binary_intersection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons right
      (VariableSubstitution.cons left VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[binary_intersection_operator_theory]
        Formula.fromSentence binary_intersection_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, binary_intersection_definition_axiom,
    binary_intersection_definition_instance,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 从族中一个成员分离公共元素，与直接交集规格等价。 -/
theorem intersection_separation_spec_iff_of_mem
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (family source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (source ∈ₘ family) ⟶ₘ
        (intersection_separation_spec family source candidate ↔ₘ
          intersection_spec family candidate) := by
  apply FirstOrder.Derives.imp_intro
  unfold intersection_separation_spec intersection_spec
  apply Metatheory.Derives.forall_iff_mono
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let common : SetOpenFormula (SetSort.set :: free) :=
    intersection_member_condition
      (family.weakenFree SetSort.set) element
  let sourceMember : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ source.weakenFree SetSort.set
  have hSourceMember :
      FreshVariable.extendContext SetSort.set
        ((source ∈ₘ family) :: Γ) ⊢ₘ[T]
          (source.weakenFree SetSort.set ∈ₘ
            family.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [FreshVariable.extendContext])
  have hCondition :
      FreshVariable.extendContext SetSort.set
        ((source ∈ₘ family) :: Γ) ⊢ₘ[T]
          (sourceMember ∧ₘ common) ↔ₘ common := by
    apply FirstOrder.Derives.iff_intro
    · exact FirstOrder.Derives.conj_elim_right
        (FirstOrder.Derives.assumption List.mem_cons_self)
    · have hCommon :
          common :: FreshVariable.extendContext SetSort.set
            ((source ∈ₘ family) :: Γ) ⊢ₘ[T] common :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hElementSource := FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim
          (intersection_member_condition_elim
            (T := T)
            (Γ := common :: FreshVariable.extendContext SetSort.set
              ((source ∈ₘ family) :: Γ))
            (family.weakenFree SetSort.set)
            (source.weakenFree SetSort.set) element)
          hCommon)
        (FirstOrder.Derives.context_weaken_cons hSourceMember)
      exact FirstOrder.Derives.conj_intro hElementSource hCommon
  have hCongruence := Metatheory.Derives.iff_right_congr_m
    (φ := element ∈ₘ candidate.weakenFree SetSort.set) hCondition
  simpa [intersection_member_condition, element, common, sourceMember,
    FreshVariable.newest] using! hCongruence

/-- 同一族的两个交集候选必相等。 -/
theorem intersection_unique
    {free : SetContext} {Γ : Context signature free}
    (family left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      intersection_spec family left ⟶ₘ
        intersection_spec family right ⟶ₘ (left ≐ₘ right) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    intersection_member_condition
      (family.weakenFree SetSort.set) element
  simpa [intersection_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) left right condition)

/-- 一个直接交集候选立即见证交集存在。 -/
theorem intersection_spec_implies_exists
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (family candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      intersection_spec family candidate ⟶ₘ
        intersection_exists family := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.exists_intro candidate
  simpa [intersection_exists, intersection_spec,
    intersection_member_condition, membership_specification,
    Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using
    (FirstOrder.Derives.assumption (T := T) List.mem_cons_self :
      intersection_spec family candidate :: Γ ⊢ₘ[T]
        intersection_spec family candidate)

/-- 交集存在式与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem intersection_exists_weakenFree
    {free : SetContext} (introduced : SetSort)
    (family : SetOpenTerm free) :
    (intersection_exists family).weakenFree introduced =
      intersection_exists (family.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact intersection_exists_renameMapped
    (VariableRenaming.weaken introduced) family

/-- 已知族中一个成员时，分离构造给出交集存在。 -/
theorem intersection_exists_of_member
    {free : SetContext} {Γ : Context signature free}
    (family source : SetOpenTerm free) :
    Γ ⊢ₘ[intersection_base_theory]
      (source ∈ₘ family) ⟶ₘ intersection_exists family := by
  apply FirstOrder.Derives.imp_intro
  have hSeparation :
      (source ∈ₘ family) :: Γ ⊢ₘ[intersection_base_theory]
        intersection_separation_exists family source :=
    FirstOrder.Derives.context_weaken_cons
      (intersection_separation_exists_derives
        (Γ := Γ) family source)
  apply FirstOrder.Derives.exists_elim (by
    simpa [intersection_separation_exists] using hSeparation)
  let candidate : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let separation : SetOpenFormula (SetSort.set :: free) :=
    intersection_separation_spec
      (family.weakenFree SetSort.set)
      (source.weakenFree SetSort.set) candidate
  let Δ : Context signature (SetSort.set :: free) :=
    separation :: FreshVariable.extendContext SetSort.set
      ((source ∈ₘ family) :: Γ)
  have hSourceMember : Δ ⊢ₘ[intersection_base_theory]
      source.weakenFree SetSort.set ∈ₘ family.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [Δ, FreshVariable.extendContext])
  have hSeparationSpec : Δ ⊢ₘ[intersection_base_theory]
      intersection_separation_spec
        (family.weakenFree SetSort.set)
        (source.weakenFree SetSort.set) candidate := by
    simpa [Δ, separation] using
      (FirstOrder.Derives.assumption
        (T := intersection_base_theory)
        (Γ := Δ) List.mem_cons_self)
  have hBridge := FirstOrder.Derives.imp_elim
    (intersection_separation_spec_iff_of_mem
      (T := intersection_base_theory) (Γ := Δ)
      (family.weakenFree SetSort.set)
      (source.weakenFree SetSort.set) candidate)
    hSourceMember
  have hDirect := FirstOrder.Derives.iff_elim_left hBridge hSeparationSpec
  have hExists := FirstOrder.Derives.exists_intro_newest hDirect
  simpa [intersection_exists, intersection_spec,
    intersection_member_condition, membership_specification,
    candidate, FreshVariable.newest] using! hExists

/-- 非空族的交集存在。 -/
theorem intersection_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (family : SetOpenTerm free) :
    Γ ⊢ₘ[intersection_base_theory]
      set_nonempty_condition family ⟶ₘ intersection_exists family := by
  apply FirstOrder.Derives.imp_intro
  have hNonempty :
      set_nonempty_condition family :: Γ ⊢ₘ[intersection_base_theory]
        set_nonempty_condition family :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hHasMemberImp :
      set_nonempty_condition family :: Γ ⊢ₘ[intersection_base_theory]
        set_nonempty_condition family ⟶ₘ set_has_member family :=
    FirstOrder.Derives.context_weaken_cons
      (FirstOrder.Derives.theory_weaken
        empty_set_symbol_theory_subset_intersection_base_theory
        (set_nonempty_implies_has_member (Γ := Γ) family))
  have hHasMember := FirstOrder.Derives.imp_elim hHasMemberImp hNonempty
  apply FirstOrder.Derives.exists_elim (by
    simpa [set_has_member] using hHasMember)
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let membership : SetOpenFormula (SetSort.set :: free) :=
    member ∈ₘ family.weakenFree SetSort.set
  let Δ : Context signature (SetSort.set :: free) :=
    membership :: FreshVariable.extendContext SetSort.set
      (set_nonempty_condition family :: Γ)
  have hMember : Δ ⊢ₘ[intersection_base_theory]
      member ∈ₘ family.weakenFree SetSort.set := by
    simpa [Δ, membership] using
      (FirstOrder.Derives.assumption
        (T := intersection_base_theory)
        (Γ := Δ) List.mem_cons_self)
  have hExists := FirstOrder.Derives.imp_elim
    (intersection_exists_of_member
      (Γ := Δ) (family.weakenFree SetSort.set) member)
    hMember
  rw [intersection_exists_weakenFree]
  exact hExists

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
