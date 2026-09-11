import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.CartesianProduct
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Relation

/-!
# 关系的平面性质：核心

本模块只保留关系平面层真正使用的数学合同。所有项与公式都由宿主类型保证良构；
量词证明统一使用规范 fresh 上下文，不再携带变量编号、开项等式或闭性证书。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 统一理论边界 -/

/-- 关系平面定理所需的最小显式组合理论。 -/
def relation_plane_theory : SetTheory :=
  Theory.union relation_range_operator_theory
    (Theory.union cartesian_product_operator_theory
      ordered_pair_reverse_operator_theory)

derive_theory_subset relation_range_operator_theory ⊆ relation_plane_theory

derive_theory_subset cartesian_product_operator_theory ⊆ relation_plane_theory

derive_theory_subset ordered_pair_reverse_operator_theory ⊆ relation_plane_theory

derive_theory_subset relation_predicate_theory ⊆ relation_plane_theory

derive_theory_subset relation_function_theory ⊆ relation_plane_theory

derive_theory_subset union_operator_theory ⊆ relation_plane_theory

derive_theory_subset right_projection_operator_theory ⊆ relation_plane_theory

derive_theory_subset subset_theory ⊆ relation_plane_theory

derive_theory_subset binary_union_operator_theory ⊆ relation_plane_theory

derive_theory_subset power_set_operator_theory ⊆ relation_plane_theory

derive_theory_subset ordered_pair_operator_theory ⊆ relation_plane_theory

derive_theory_subset pairing_operator_theory ⊆ relation_plane_theory

derive_theory_subset singleton_operator_theory ⊆ relation_plane_theory

derive_theory_subset extensionality_theory ⊆ relation_plane_theory

/-! ## 并集与子集 -/

/-- 集合族中的一个容器所含元素属于该集合族的并集。 -/
theorem mem_union_of_mem_of_mem
    {free : SetContext} {Γ : Context signature free}
    (source container element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (container ∈ₘ source) ⟶ₘ
        ((element ∈ₘ container) ⟶ₘ (element ∈ₘ ⋃ₘ source)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (element ∈ₘ container) :: (container ∈ₘ source) :: Γ
  have hSpec : Δ ⊢ₘ[relation_plane_theory]
      union_spec source (⋃ₘ source) :=
    FirstOrder.Derives.theory_weaken
      union_operator_theory_subset_relation_plane_theory
      (union_term_spec_derives (Γ := Δ) source)
  have hAt := union_spec_membership_iff
    source (⋃ₘ source) element hSpec
  apply FirstOrder.Derives.iff_elim_right hAt
  apply FirstOrder.Derives.exists_intro container
  rw [Formula.instantiateTop_abstractFreeTop]
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.assumption
        (T := relation_plane_theory) (Γ := Δ) (by simp [Δ]))
      (FirstOrder.Derives.assumption
        (T := relation_plane_theory) (Γ := Δ) (by simp [Δ]))

/-- 集合族的任意成员包含于该集合族的并集。 -/
theorem member_subset_union
    {free : SetContext} {Γ : Context signature free}
    (source member : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (member ∈ₘ source) ⟶ₘ (member ⊆ₘ ⋃ₘ source) := by
  apply FirstOrder.Derives.imp_intro
  apply subset_intro subset_theory_subset_relation_plane_theory
  apply FirstOrder.Derives.imp_intro
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Δ : Context signature (SetSort.set :: free) :=
    (element ∈ₘ member.weakenFree SetSort.set) ::
      FreshVariable.extendContext SetSort.set
        ((member ∈ₘ source) :: Γ)
  have hMemberSource : Δ ⊢ₘ[relation_plane_theory]
      member.weakenFree SetSort.set ∈ₘ source.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [Δ, FreshVariable.extendContext])
  have hElementMember : Δ ⊢ₘ[relation_plane_theory]
      element ∈ₘ member.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by simp [Δ])
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (mem_union_of_mem_of_mem
        (Γ := Δ) (source.weakenFree SetSort.set)
        (member.weakenFree SetSort.set) element)
      hMemberSource)
    hElementMember

/-- 并集运算保持子集关系。 -/
theorem union_mono
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (left ⊆ₘ right) ⟶ₘ ((⋃ₘ left) ⊆ₘ (⋃ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := (left ⊆ₘ right) :: Γ
  apply subset_intro subset_theory_subset_relation_plane_theory
  apply FirstOrder.Derives.imp_intro
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Θ : Context signature (SetSort.set :: free) :=
    (element ∈ₘ ⋃ₘ (left.weakenFree SetSort.set)) ::
      FreshVariable.extendContext SetSort.set Δ
  have hLeftSpec : Θ ⊢ₘ[relation_plane_theory]
      union_spec (left.weakenFree SetSort.set)
        (⋃ₘ (left.weakenFree SetSort.set)) :=
    FirstOrder.Derives.theory_weaken
      union_operator_theory_subset_relation_plane_theory
      (union_term_spec_derives
        (Γ := Θ) (left.weakenFree SetSort.set))
  have hLeftMember : Θ ⊢ₘ[relation_plane_theory]
      element ∈ₘ ⋃ₘ (left.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by simp [Θ])
  have hWitness := FirstOrder.Derives.iff_elim_left
    (union_spec_membership_iff
      (left.weakenFree SetSort.set)
      (⋃ₘ (left.weakenFree SetSort.set)) element hLeftSpec)
    hLeftMember
  unfold union_witness_condition at hWitness
  apply FirstOrder.Derives.exists_elim hWitness
  let witness : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := SetSort.set :: free) SetSort.set
  let element' : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    element.weakenFree SetSort.set
  let left' : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    (left.weakenFree SetSort.set).weakenFree SetSort.set
  let right' : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    (right.weakenFree SetSort.set).weakenFree SetSort.set
  let witnessBody : SetOpenFormula
      (SetSort.set :: SetSort.set :: free) :=
    (witness ∈ₘ left') ∧ₘ (element' ∈ₘ witness)
  let Ω : Context signature (SetSort.set :: SetSort.set :: free) :=
    witnessBody :: FreshVariable.extendContext SetSort.set Θ
  have hConjunction : Ω ⊢ₘ[relation_plane_theory] witnessBody :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hWitnessLeft : Ω ⊢ₘ[relation_plane_theory]
      witness ∈ₘ left' :=
    FirstOrder.Derives.conj_elim_left hConjunction
  have hElementWitness : Ω ⊢ₘ[relation_plane_theory]
      element' ∈ₘ witness :=
    FirstOrder.Derives.conj_elim_right hConjunction
  have hSubset : Ω ⊢ₘ[relation_plane_theory] left' ⊆ₘ right' :=
    FirstOrder.Derives.assumption (by
      simp [Ω, Θ, Δ, left', right', FreshVariable.extendContext])
  have hWitnessRight : Ω ⊢ₘ[relation_plane_theory]
      witness ∈ₘ right' :=
    subset_membership subset_theory_subset_relation_plane_theory
      left' right' witness hSubset hWitnessLeft
  have hResult := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (mem_union_of_mem_of_mem
        (Γ := Ω) right' witness element')
      hWitnessRight)
    hElementWitness
  simpa [element', right'] using! hResult

/-- 关系的任意子集仍是关系。 -/
theorem is_relation_of_subset
    {free : SetContext} {Γ : Context signature free}
    (relation candidate : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      is_relation_formula relation ⟶ₘ
        (candidate ⊆ₘ relation) ⟶ₘ
          is_relation_formula candidate := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let relationFormula : SetOpenFormula free :=
    is_relation_formula relation
  let subsetFormula : SetOpenFormula free := candidate ⊆ₘ relation
  let Δ : Context signature free := subsetFormula :: relationFormula :: Γ
  change Δ ⊢ₘ[relation_plane_theory] is_relation_formula candidate
  apply is_relation_intro
    relation_predicate_theory_subset_relation_plane_theory
  apply FirstOrder.Derives.imp_intro
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let membership : SetOpenFormula (SetSort.set :: free) :=
    member ∈ₘ candidate.weakenFree SetSort.set
  let Ω : Context signature (SetSort.set :: free) :=
    membership :: FreshVariable.extendContext SetSort.set Δ
  have hSubset : Ω ⊢ₘ[relation_plane_theory]
      candidate.weakenFree SetSort.set ⊆ₘ
        relation.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [Ω, Δ, subsetFormula, FreshVariable.extendContext])
  have hCandidateMember : Ω ⊢ₘ[relation_plane_theory]
      member ∈ₘ candidate.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hRelationMember : Ω ⊢ₘ[relation_plane_theory]
      member ∈ₘ relation.weakenFree SetSort.set :=
    subset_membership subset_theory_subset_relation_plane_theory
      (candidate.weakenFree SetSort.set)
      (relation.weakenFree SetSort.set) member
      hSubset hCandidateMember
  have hRelation : Ω ⊢ₘ[relation_plane_theory]
      is_relation_formula (relation.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Ω, Δ, relationFormula, FreshVariable.extendContext])
  have hOrdered := FirstOrder.Derives.theory_weaken
    relation_predicate_theory_subset_relation_plane_theory
    (is_relation_member_is_ordered_pair
      (Γ := Ω) (relation.weakenFree SetSort.set) member)
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim hOrdered hRelation)
    hRelationMember

/-- 左集合中的元素进入二元并。 -/
theorem mem_binary_union_left
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (element ∈ₘ left) ⟶ₘ (element ∈ₘ (left ∪ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := (element ∈ₘ left) :: Γ
  have hSpec : Δ ⊢ₘ[relation_plane_theory]
      binary_union_spec left right (left ∪ₘ right) :=
    FirstOrder.Derives.theory_weaken
      binary_union_operator_theory_subset_relation_plane_theory
      (binary_union_term_spec_derives (Γ := Δ) left right)
  apply FirstOrder.Derives.iff_elim_right
    (binary_union_spec_membership_iff
      left right (left ∪ₘ right) element hSpec)
  exact FirstOrder.Derives.disj_intro_left
    (FirstOrder.Derives.assumption (by simp [Δ]))

/-- 右集合中的元素进入二元并。 -/
theorem mem_binary_union_right
    {free : SetContext} {Γ : Context signature free}
    (left right element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (element ∈ₘ right) ⟶ₘ (element ∈ₘ (left ∪ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := (element ∈ₘ right) :: Γ
  have hSpec : Δ ⊢ₘ[relation_plane_theory]
      binary_union_spec left right (left ∪ₘ right) :=
    FirstOrder.Derives.theory_weaken
      binary_union_operator_theory_subset_relation_plane_theory
      (binary_union_term_spec_derives (Γ := Δ) left right)
  apply FirstOrder.Derives.iff_elim_right
    (binary_union_spec_membership_iff
      left right (left ∪ₘ right) element hSpec)
  exact FirstOrder.Derives.disj_intro_right
    (FirstOrder.Derives.assumption (by simp [Δ]))

/-- 若左集合包含于右集合，则二元并吸收到右集合。 -/
theorem binary_union_term_eq_right_of_subset
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (left ⊆ₘ right) ⟶ₘ ((left ∪ₘ right) ≐ₘ right) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := (left ⊆ₘ right) :: Γ
  have hUnionSpec : Δ ⊢ₘ[relation_plane_theory]
      binary_union_spec left right (left ∪ₘ right) :=
    FirstOrder.Derives.theory_weaken
      binary_union_operator_theory_subset_relation_plane_theory
      (binary_union_term_spec_derives (Γ := Δ) left right)
  have hRightSpec : Δ ⊢ₘ[relation_plane_theory]
      binary_union_spec left right right := by
    unfold binary_union_spec membership_specification
    apply FirstOrder.Derives.forall_intro
    let element : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    let Θ : Context signature (SetSort.set :: free) :=
      FreshVariable.extendContext SetSort.set Δ
    apply FirstOrder.Derives.iff_intro
    · exact FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.assumption List.mem_cons_self)
    · have hChoice := FirstOrder.Derives.assumption
        (T := relation_plane_theory)
        (Γ := ((element ∈ₘ left.weakenFree SetSort.set) ∨ₘ
          (element ∈ₘ right.weakenFree SetSort.set)) :: Θ)
        List.mem_cons_self
      apply FirstOrder.Derives.disj_elim hChoice
      · have hSubset :
            ((element ∈ₘ left.weakenFree SetSort.set) ::
              ((element ∈ₘ left.weakenFree SetSort.set) ∨ₘ
                (element ∈ₘ right.weakenFree SetSort.set)) :: Θ)
              ⊢ₘ[relation_plane_theory]
                left.weakenFree SetSort.set ⊆ₘ
                  right.weakenFree SetSort.set :=
          FirstOrder.Derives.assumption (by
            simp [Θ, Δ, FreshVariable.extendContext])
        exact subset_membership
          subset_theory_subset_relation_plane_theory
          (left.weakenFree SetSort.set)
          (right.weakenFree SetSort.set) element hSubset
          (FirstOrder.Derives.assumption List.mem_cons_self)
      · exact FirstOrder.Derives.assumption List.mem_cons_self
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let condition : SetOpenFormula (SetSort.set :: free) :=
    binary_union_member_condition
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) element
  have hUnique : Δ ⊢ₘ[relation_plane_theory]
      binary_union_spec left right (left ∪ₘ right) ⟶ₘ
        (binary_union_spec left right right ⟶ₘ
          ((left ∪ₘ right) ≐ₘ right)) := by
    simpa [binary_union_spec, condition] using!
      FirstOrder.Derives.theory_weaken
        extensionality_theory_subset_relation_plane_theory
        (membership_specification_unique
          (Γ := Δ) (left ∪ₘ right) right condition)
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim hUnique hUnionSpec) hRightSpec

/-! ## 配对规格与有限成员 -/

/-- 无序对规格对两个参数对称。 -/
theorem pair_spec_comm_iff
    {free : SetContext} {Γ : Context signature free}
    (left right pair : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      pair_spec left right pair ↔ₘ pair_spec right left pair := by
  unfold pair_spec membership_specification
  apply Metatheory.Derives.forall_iff_mono
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Δ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Γ
  let membership : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ pair.weakenFree SetSort.set
  let leftEquality : SetOpenFormula (SetSort.set :: free) :=
    element ≐ₘ left.weakenFree SetSort.set
  let rightEquality : SetOpenFormula (SetSort.set :: free) :=
    element ≐ₘ right.weakenFree SetSort.set
  change Δ ⊢ₘ[relation_plane_theory]
    (membership ↔ₘ (leftEquality ∨ₘ rightEquality)) ↔ₘ
      (membership ↔ₘ (rightEquality ∨ₘ leftEquality))
  have hDisjunction : Δ ⊢ₘ[relation_plane_theory]
      (leftEquality ∨ₘ rightEquality) ↔ₘ
        (rightEquality ∨ₘ leftEquality) := by
    apply FirstOrder.Derives.iff_intro
    · apply FirstOrder.Derives.disj_elim
        (FirstOrder.Derives.assumption List.mem_cons_self)
      · exact FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.assumption List.mem_cons_self)
      · exact FirstOrder.Derives.disj_intro_left
          (FirstOrder.Derives.assumption List.mem_cons_self)
    · apply FirstOrder.Derives.disj_elim
        (FirstOrder.Derives.assumption List.mem_cons_self)
      · exact FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.assumption List.mem_cons_self)
      · exact FirstOrder.Derives.disj_intro_left
          (FirstOrder.Derives.assumption List.mem_cons_self)
  exact Metatheory.Derives.iff_right_congr_m hDisjunction

/-- 无序对函数项满足交换律。 -/
theorem unordered_pair_term_comm
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      {left, right}ₘ ≐ₘ {right, left}ₘ := by
  have hLeft : Γ ⊢ₘ[relation_plane_theory]
      pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken
      pairing_operator_theory_subset_relation_plane_theory
      (unordered_pair_term_spec_derives (Γ := Γ) left right)
  have hRightRaw : Γ ⊢ₘ[relation_plane_theory]
      pair_spec right left {right, left}ₘ :=
    FirstOrder.Derives.theory_weaken
      pairing_operator_theory_subset_relation_plane_theory
      (unordered_pair_term_spec_derives (Γ := Γ) right left)
  have hRight : Γ ⊢ₘ[relation_plane_theory]
      pair_spec left right {right, left}ₘ :=
    FirstOrder.Derives.iff_elim_right
      (pair_spec_comm_iff left right {right, left}ₘ) hRightRaw
  have hUnique := FirstOrder.Derives.theory_weaken
    extensionality_theory_subset_relation_plane_theory
    (pair_unique (Γ := Γ) left right
      {left, right}ₘ {right, left}ₘ)
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim hUnique hLeft) hRight

/-- 配对候选的两个生成元都在某集合中时，该候选包含于该集合。 -/
theorem pair_spec_implies_subset_of_members
    {free : SetContext} {Γ : Context signature free}
    (left right pair source : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      pair_spec left right pair ⟶ₘ
        ((left ∈ₘ source) ⟶ₘ
          ((right ∈ₘ source) ⟶ₘ (pair ⊆ₘ source))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (right ∈ₘ source) :: (left ∈ₘ source) ::
      pair_spec left right pair :: Γ
  apply subset_intro subset_theory_subset_relation_plane_theory
  apply FirstOrder.Derives.imp_intro
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Θ : Context signature (SetSort.set :: free) :=
    (element ∈ₘ pair.weakenFree SetSort.set) ::
      FreshVariable.extendContext SetSort.set Δ
  have hSpec : Θ ⊢ₘ[relation_plane_theory]
      pair_spec (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set)
        (pair.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Θ, Δ, FreshVariable.extendContext])
  have hElementPair : Θ ⊢ₘ[relation_plane_theory]
      element ∈ₘ pair.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by simp [Θ])
  have hChoice := FirstOrder.Derives.iff_elim_left
    (pair_spec_membership_iff
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set)
      (pair.weakenFree SetSort.set) element hSpec)
    hElementPair
  apply FirstOrder.Derives.disj_elim hChoice
  · have hEquality :
        ((element ≐ₘ left.weakenFree SetSort.set) :: Θ)
          ⊢ₘ[relation_plane_theory]
            element ≐ₘ left.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hLeftMember :
        ((element ≐ₘ left.weakenFree SetSort.set) :: Θ)
          ⊢ₘ[relation_plane_theory]
            left.weakenFree SetSort.set ∈ₘ source.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption (by
        simp [Θ, Δ, FreshVariable.extendContext])
    exact FirstOrder.Derives.iff_elim_right
      (membership_left_iff_of_equality
        element (left.weakenFree SetSort.set)
        (source.weakenFree SetSort.set) hEquality)
      hLeftMember
  · have hEquality :
        ((element ≐ₘ right.weakenFree SetSort.set) :: Θ)
          ⊢ₘ[relation_plane_theory]
            element ≐ₘ right.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hRightMember :
        ((element ≐ₘ right.weakenFree SetSort.set) :: Θ)
          ⊢ₘ[relation_plane_theory]
            right.weakenFree SetSort.set ∈ₘ source.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption (by
        simp [Θ, Δ, FreshVariable.extendContext])
    exact FirstOrder.Derives.iff_elim_right
      (membership_left_iff_of_equality
        element (right.weakenFree SetSort.set)
        (source.weakenFree SetSort.set) hEquality)
      hRightMember

/-- 两个生成元都在某集合中时，它们的无序对包含于该集合。 -/
theorem unordered_pair_subset_of_members
    {free : SetContext} {Γ : Context signature free}
    (left right source : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (left ∈ₘ source) ⟶ₘ
        ((right ∈ₘ source) ⟶ₘ ({left, right}ₘ ⊆ₘ source)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (right ∈ₘ source) :: (left ∈ₘ source) :: Γ
  have hSpec : Δ ⊢ₘ[relation_plane_theory]
      pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken
      pairing_operator_theory_subset_relation_plane_theory
      (unordered_pair_term_spec_derives (Γ := Δ) left right)
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (pair_spec_implies_subset_of_members
          (Γ := Δ) left right {left, right}ₘ source)
        hSpec)
      (FirstOrder.Derives.assumption (by simp)))
    (FirstOrder.Derives.assumption (by simp))

/-- 一个元素属于某集合时，其单点集包含于该集合。 -/
theorem singleton_subset_of_mem
    {free : SetContext} {Γ : Context signature free}
    (element source : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (element ∈ₘ source) ⟶ₘ ({element}ₘ ⊆ₘ source) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := (element ∈ₘ source) :: Γ
  apply subset_intro subset_theory_subset_relation_plane_theory
  apply FirstOrder.Derives.imp_intro
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Θ : Context signature (SetSort.set :: free) :=
    (member ∈ₘ {element.weakenFree SetSort.set}ₘ) ::
      FreshVariable.extendContext SetSort.set Δ
  have hSpec : Θ ⊢ₘ[relation_plane_theory]
      singleton_spec (element.weakenFree SetSort.set)
        {element.weakenFree SetSort.set}ₘ :=
    FirstOrder.Derives.theory_weaken
      singleton_operator_theory_subset_relation_plane_theory
      (singleton_term_spec_derives
        (Γ := Θ) (element.weakenFree SetSort.set))
  have hMember : Θ ⊢ₘ[relation_plane_theory]
      member ∈ₘ {element.weakenFree SetSort.set}ₘ :=
    FirstOrder.Derives.assumption (by simp [Θ])
  have hEquality := FirstOrder.Derives.iff_elim_left
    (singleton_spec_membership_iff
      (element.weakenFree SetSort.set)
      {element.weakenFree SetSort.set}ₘ member hSpec)
    hMember
  have hElementSource : Θ ⊢ₘ[relation_plane_theory]
      element.weakenFree SetSort.set ∈ₘ source.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [Θ, Δ, FreshVariable.extendContext])
  exact FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality member
      (element.weakenFree SetSort.set)
      (source.weakenFree SetSort.set) hEquality)
    hElementSource

/-- 元素属于其规范单点集。 -/
theorem mem_singleton_self
    {free : SetContext} {Γ : Context signature free}
    (element : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory] element ∈ₘ {element}ₘ := by
  have hSpec : Γ ⊢ₘ[relation_plane_theory]
      singleton_spec element {element}ₘ :=
    FirstOrder.Derives.theory_weaken
      singleton_operator_theory_subset_relation_plane_theory
      (singleton_term_spec_derives (Γ := Γ) element)
  exact FirstOrder.Derives.iff_elim_right
    (singleton_spec_membership_iff element {element}ₘ element hSpec)
    (Metatheory.Derives.equality_refl
      (T := relation_plane_theory) (Γ := Γ) element)

/-- 左生成元属于其规范无序对。 -/
theorem mem_unordered_pair_left
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory] left ∈ₘ {left, right}ₘ := by
  have hSpec : Γ ⊢ₘ[relation_plane_theory]
      pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken
      pairing_operator_theory_subset_relation_plane_theory
      (unordered_pair_term_spec_derives (Γ := Γ) left right)
  exact FirstOrder.Derives.iff_elim_right
    (pair_spec_membership_iff left right {left, right}ₘ left hSpec)
    (FirstOrder.Derives.disj_intro_left
      (Metatheory.Derives.equality_refl
        (T := relation_plane_theory) (Γ := Γ) left))

/-- 右生成元属于其规范无序对。 -/
theorem mem_unordered_pair_right
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory] right ∈ₘ {left, right}ₘ := by
  have hSpec : Γ ⊢ₘ[relation_plane_theory]
      pair_spec left right {left, right}ₘ :=
    FirstOrder.Derives.theory_weaken
      pairing_operator_theory_subset_relation_plane_theory
      (unordered_pair_term_spec_derives (Γ := Γ) left right)
  exact FirstOrder.Derives.iff_elim_right
    (pair_spec_membership_iff left right {left, right}ₘ right hSpec)
    (FirstOrder.Derives.disj_intro_right
      (Metatheory.Derives.equality_refl
        (T := relation_plane_theory) (Γ := Γ) right))

/-- 左坐标单点集属于其 Kuratowski 有序对。 -/
theorem singleton_mem_ordered_pair
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory] {left}ₘ ∈ₘ ⟨left, right⟩ₘ := by
  have hSpec : Γ ⊢ₘ[relation_plane_theory]
      ordered_pair_spec left right ⟨left, right⟩ₘ :=
    FirstOrder.Derives.theory_weaken
      ordered_pair_operator_theory_subset_relation_plane_theory
      (ordered_pair_term_spec_derives (Γ := Γ) left right)
  exact FirstOrder.Derives.iff_elim_right
    (pair_spec_membership_iff {left}ₘ {left, right}ₘ
      ⟨left, right⟩ₘ {left}ₘ hSpec)
    (FirstOrder.Derives.disj_intro_left
      (Metatheory.Derives.equality_refl
        (T := relation_plane_theory) (Γ := Γ) {left}ₘ))

/-- 坐标无序对属于其 Kuratowski 有序对。 -/
theorem unordered_pair_mem_ordered_pair
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory] {left, right}ₘ ∈ₘ ⟨left, right⟩ₘ := by
  have hSpec : Γ ⊢ₘ[relation_plane_theory]
      ordered_pair_spec left right ⟨left, right⟩ₘ :=
    FirstOrder.Derives.theory_weaken
      ordered_pair_operator_theory_subset_relation_plane_theory
      (ordered_pair_term_spec_derives (Γ := Γ) left right)
  exact FirstOrder.Derives.iff_elim_right
    (pair_spec_membership_iff {left}ₘ {left, right}ₘ
      ⟨left, right⟩ₘ {left, right}ₘ hSpec)
    (FirstOrder.Derives.disj_intro_right
      (Metatheory.Derives.equality_refl
        (T := relation_plane_theory) (Γ := Γ) {left, right}ₘ))

/-! ## Kuratowski 有序对的并集 -/

/-- Kuratowski 有序对的一元并恰好是其两个坐标的无序对。 -/
theorem union_ordered_pair_term_eq_unordered_pair
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_plane_theory]
      (⋃ₘ ⟨left, right⟩ₘ) ≐ₘ {left, right}ₘ := by
  let singleton : SetOpenTerm free := {left}ₘ
  let pair : SetOpenTerm free := {left, right}ₘ
  let ordered : SetOpenTerm free := ⟨left, right⟩ₘ
  let kuratowski : SetOpenTerm free := {singleton, pair}ₘ
  let binary : SetOpenTerm free := singleton ∪ₘ pair
  have hOrderedSpec : Γ ⊢ₘ[relation_plane_theory]
      pair_spec singleton pair ordered := by
    simpa [singleton, pair, ordered, ordered_pair_spec] using
      FirstOrder.Derives.theory_weaken
        ordered_pair_operator_theory_subset_relation_plane_theory
        (ordered_pair_term_spec_derives (Γ := Γ) left right)
  have hOrderedEquality : Γ ⊢ₘ[relation_plane_theory]
      ordered ≐ₘ kuratowski := by
    have hDefinition := FirstOrder.Derives.theory_weaken
      pairing_operator_theory_subset_relation_plane_theory
      (unordered_pair_eq_iff_spec
        (Γ := Γ) singleton pair ordered)
    simpa [kuratowski] using
      FirstOrder.Derives.iff_elim_right hDefinition hOrderedSpec
  have hUnionCongruence : Γ ⊢ₘ[relation_plane_theory]
      (⋃ₘ ordered) ≐ₘ (⋃ₘ kuratowski) :=
    union_term_congr_of_equality ordered kuratowski hOrderedEquality
  have hUnionBinary : Γ ⊢ₘ[relation_plane_theory]
      (⋃ₘ kuratowski) ≐ₘ binary := by
    have hDefinition := FirstOrder.Derives.theory_weaken
      binary_union_operator_theory_subset_relation_plane_theory
      (binary_union_term_eq_union_pair_derives
        (Γ := Γ) singleton pair)
    simpa [kuratowski, binary] using
      Metatheory.Derives.equality_symm hDefinition
  have hLeftMember : Γ ⊢ₘ[relation_plane_theory]
      left ∈ₘ pair := by
    simpa [pair] using
      (mem_unordered_pair_left (Γ := Γ) left right)
  have hSingletonSubset : Γ ⊢ₘ[relation_plane_theory]
      singleton ⊆ₘ pair :=
    by
      simpa [singleton] using FirstOrder.Derives.imp_elim
        (singleton_subset_of_mem (Γ := Γ) left pair)
        hLeftMember
  have hAbsorption : Γ ⊢ₘ[relation_plane_theory]
      binary ≐ₘ pair := by
    simpa [binary] using FirstOrder.Derives.imp_elim
      (binary_union_term_eq_right_of_subset
        (Γ := Γ) singleton pair)
      hSingletonSubset
  have hToBinary := Metatheory.Derives.equality_trans
    hUnionCongruence hUnionBinary
  have hResult := Metatheory.Derives.equality_trans
    hToBinary hAbsorption
  simpa [ordered, pair] using hResult

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
