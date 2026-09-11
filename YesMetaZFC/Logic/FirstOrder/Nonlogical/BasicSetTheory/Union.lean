import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Pairing

/-!
# 并集与二元并

并集成员条件、存在公理与函数符号定义全部建立在内在类型语法上。二元并只保留
“无序对后取并集”的定义等式及成员析取规格；旧的变量编号、admissibility、闭性
旁证和文献描述子兼容层不再进入公共接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- `element` 属于 `source` 的某个成员。 -/
def union_witness_condition {bound free : SetContext}
    (source element : SetTerm bound free) : SetFormula bound free :=
  let witness : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((witness ∈ₘ source.weakenFree SetSort.set) ∧ₘ
    (element.weakenFree SetSort.set ∈ₘ witness))
    |>.existsFreeTop SetSort.set

/-- `union` 恰好由 `source` 的所有成员的成员组成。 -/
def union_spec {bound free : SetContext}
    (source union : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification union
    (union_witness_condition
      (source.weakenFree SetSort.set) element)

/-- 对固定集合断言其并集存在。 -/
def union_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let union : SetTerm bound (SetSort.set :: free) := .fvar .here
  (union_spec (source.weakenFree SetSort.set) union)
    |>.existsFreeTop SetSort.set

/-- 并集存在公理。 -/
def union_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (union_exists
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set))

/-- 只在外延理论上加入并集存在公理。 -/
def union_theory : SetTheory :=
  Theory.insert union_axiom extensionality_theory

/-- 一元并集函数符号的开放定义实例。 -/
def union_definition_instance {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  union_spec source (⋃ₘ source)

/-- 一元并集函数符号的定义公理。 -/
def union_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (union_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set))

/-- 在并集存在理论上加入一元并集函数符号定义。 -/
def union_operator_theory : SetTheory :=
  Theory.insert union_definition_axiom union_theory

/-- `element` 属于 `left` 或 `right`。 -/
def binary_union_member_condition {bound free : SetContext}
    (left right element : SetTerm bound free) : SetFormula bound free :=
  (element ∈ₘ left) ∨ₘ (element ∈ₘ right)

/-- `candidate` 是 `left` 与 `right` 的二元并。 -/
def binary_union_spec {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (binary_union_member_condition
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) element)

/-- 二元并成员条件与 free 重命名自然交换。 -/
@[simp] theorem binary_union_member_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (left right element : SetTerm bound sourceFree) :
    (binary_union_member_condition left right element).renameMapped
        VariableRenaming.id ρ =
      binary_union_member_condition
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ)
        (element.renameMapped VariableRenaming.id ρ) := by
  simp [binary_union_member_condition, Formula.renameMapped,
    Arguments.renameMapped]

/-- 二元并规格与 free 重命名自然交换。 -/
@[simp] theorem binary_union_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (left right union : SetTerm bound sourceFree) :
    (binary_union_spec left right union).renameMapped
        VariableRenaming.id ρ =
      binary_union_spec
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ)
        (union.renameMapped VariableRenaming.id ρ) := by
  unfold binary_union_spec
  rw [membership_specification_renameMapped]
  rw [binary_union_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 二元并规格与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem binary_union_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (left right union : SetTerm bound free) :
    (binary_union_spec left right union).weakenFree introduced =
      binary_union_spec (left.weakenFree introduced)
        (right.weakenFree introduced) (union.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact binary_union_spec_renameMapped
    (VariableRenaming.weaken introduced) left right union

/-- 配对与一元并函数符号理论的合并。 -/
def binary_union_base_theory : SetTheory :=
  Theory.union pairing_operator_theory union_operator_theory

/-- 二元并函数符号的开放定义实例。 -/
def binary_union_definition_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  (left ∪ₘ right) ≐ₘ (⋃ₘ {left, right}ₘ)

/-- 二元并函数符号的定义公理。 -/
def binary_union_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (binary_union_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 在配对与一元并函数符号理论上加入二元并函数符号。 -/
def binary_union_operator_theory : SetTheory :=
  Theory.insert
    binary_union_definition_axiom
    binary_union_base_theory

/-- 配对函数符号理论嵌入二元并函数符号理论。 -/
derive_theory_subset pairing_operator_theory ⊆ binary_union_operator_theory

/-- 一元并函数符号理论嵌入二元并函数符号理论。 -/
derive_theory_subset union_operator_theory ⊆ binary_union_operator_theory

/-- 并集存在公理可在任意集合项处实例化。 -/
theorem union_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[union_theory] union_exists source := by
  let body : SetOpenFormula [SetSort.set] :=
    union_exists
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons source VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[union_theory]
        Formula.fromSentence union_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, union_axiom, union_exists, union_spec,
    union_witness_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId,
    FreshVariable.newest] using! hInstance

/-- 一元并函数符号定义公理可在任意集合项处实例化。 -/
theorem union_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[union_operator_theory]
      union_definition_instance source := by
  let body : SetOpenFormula [SetSort.set] :=
    union_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons source VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[union_operator_theory]
        Formula.fromSentence union_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, union_definition_axiom,
    union_definition_instance, union_spec,
    union_witness_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId,
    FreshVariable.newest] using! hInstance

/-- 规范并集项满足并集规格。 -/
theorem union_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[union_operator_theory]
      union_spec source (⋃ₘ source) := by
  simpa [union_definition_instance] using
    (union_definition_instance_derives (Γ := Γ) source)

/-- 并集规格在任意元素处的点态实例。 -/
theorem union_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source union element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] union_spec source union) :
    Γ ⊢ₘ[T]
      (element ∈ₘ union) ↔ₘ
        union_witness_condition source element := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  simpa [union_spec, union_witness_condition,
    membership_specification, Formula.instantiateFreeTop,
    Formula.substituteFree, Substitution.free_map,
    Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hAt

/-- 同一集合的两个并集候选必相等。 -/
theorem union_unique
    {free : SetContext} {Γ : Context signature free}
    (source left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      union_spec source left ⟶ₘ
        union_spec source right ⟶ₘ (left ≐ₘ right) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    union_witness_condition
      (source.weakenFree SetSort.set) element
  simpa [union_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) left right condition)

/-- 一个集合等于规范并集项，当且仅当它满足并集规格。 -/
theorem union_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[union_operator_theory]
      (candidate ≐ₘ ⋃ₘ source) ↔ₘ union_spec source candidate := by
  let union : SetOpenTerm free := ⋃ₘ source
  apply FirstOrder.Derives.iff_intro
  · have hEquality :
        ((candidate ≐ₘ union) :: Γ) ⊢ₘ[union_operator_theory]
          candidate ≐ₘ union :=
      FirstOrder.Derives.assumption List.mem_cons_self
    let body : Formula signature [SetSort.set] free :=
      union_spec
        (source.weakenBound SetSort.set) (.bvar .here)
    have hCongruence := Metatheory.Derives.equality_iff_of_equality
      (T := union_operator_theory)
      (Γ := (candidate ≐ₘ union) :: Γ) body hEquality
    have hUnionSpec :
        ((candidate ≐ₘ union) :: Γ) ⊢ₘ[union_operator_theory]
          union_spec source union :=
      FirstOrder.Derives.context_weaken_cons
        (assumption := candidate ≐ₘ union)
        (by simpa [union] using
          (union_term_spec_derives (Γ := Γ) source))
    have hCongruence' :
        ((candidate ≐ₘ union) :: Γ) ⊢ₘ[union_operator_theory]
          union_spec source candidate ↔ₘ union_spec source union := by
      simpa [body, union_spec, union_witness_condition,
        membership_specification,
        Formula.instantiateFreeTop, Formula.substituteFree,
        Substitution.free_map,
        Substitution.instantiateFreeTop, Formula.substitute,
        Formula.substituteMapped, Term.substituteMapped,
        Arguments.substituteMapped,
        VariableSubstitution.liftFree,
        VariableSubstitution.instantiateFreeTop,
        VariableSubstitution.instantiateTop,
        VariableSubstitution.weakenBound,
        VariableSubstitution.boundId,
        VariableSubstitution.freeId] using! hCongruence
    simpa [union] using
      FirstOrder.Derives.iff_elim_right hCongruence' hUnionSpec
  · have hCandidateSpec :
        (union_spec source candidate :: Γ) ⊢ₘ[union_operator_theory]
          union_spec source candidate :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hUnionSpec :
        (union_spec source candidate :: Γ) ⊢ₘ[union_operator_theory]
          union_spec source union :=
      FirstOrder.Derives.context_weaken_cons
        (assumption := union_spec source candidate)
        (by simpa [union] using
          (union_term_spec_derives (Γ := Γ) source))
    have hUnique :
        (union_spec source candidate :: Γ) ⊢ₘ[union_operator_theory]
          union_spec source candidate ⟶ₘ
            union_spec source union ⟶ₘ (candidate ≐ₘ union) :=
      FirstOrder.Derives.context_weaken_cons
        (assumption := union_spec source candidate)
        (FirstOrder.Derives.theory_weaken (by
          intro sentence hSentence
          exact Or.inr (Or.inr hSentence))
          (union_unique (Γ := Γ) source candidate union))
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hUnique hCandidateSpec)
      hUnionSpec

/-- 已证明的集合等式可直接提升为一元并项等式。 -/
theorem union_term_congr_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (⋃ₘ left) ≐ₘ (⋃ₘ right) := by
  let termContext : SetTerm [SetSort.set] free :=
    ⋃ₘ (.bvar .here : SetTerm [SetSort.set] free)
  simpa [termContext] using!
    (Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ) termContext hEquality)

/-- 一元并项合同的蕴含形式。 -/
theorem union_term_congr
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ ((⋃ₘ left) ≐ₘ (⋃ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  exact union_term_congr_of_equality left right
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 等价的源集合可运输同一个候选对象的并集等式。 -/
theorem union_eq_transport
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ
        ((candidate ≐ₘ ⋃ₘ left) ⟶ₘ
          (candidate ≐ₘ ⋃ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (candidate ≐ₘ ⋃ₘ left) :: (left ≐ₘ right) :: Γ
  have hSourceEquality : Δ ⊢ₘ[T] left ≐ₘ right :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hCandidateEquality : Δ ⊢ₘ[T] candidate ≐ₘ ⋃ₘ left :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hUnionEquality := union_term_congr_of_equality
    (T := T) (Γ := Δ) left right hSourceEquality
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hUnionEquality

/-- 二元并定义公理可在任意两个集合项处实例化。 -/
theorem binary_union_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[binary_union_operator_theory]
      binary_union_definition_instance left right := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    binary_union_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons right
      (VariableSubstitution.cons left VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[binary_union_operator_theory]
        Formula.fromSentence binary_union_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, binary_union_definition_axiom,
    binary_union_definition_instance,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 定义扩张中的二元并项等于对应无序对的一元并。 -/
theorem binary_union_term_eq_union_pair_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[binary_union_operator_theory]
      (left ∪ₘ right) ≐ₘ (⋃ₘ {left, right}ₘ) := by
  simpa [binary_union_definition_instance] using
    (binary_union_definition_instance_derives (Γ := Γ) left right)

/-- 二元并规格在任意元素处的点态实例。 -/
theorem binary_union_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right union element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] binary_union_spec left right union) :
    Γ ⊢ₘ[T]
      (element ∈ₘ union) ↔ₘ
        ((element ∈ₘ left) ∨ₘ (element ∈ₘ right)) := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  simpa [binary_union_spec, binary_union_member_condition,
    membership_specification] using! hAt

/-- 无序对规格与一元并规格组合成二元并的成员析取规格。 -/
theorem pair_union_spec_implies_binary_union_spec
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right pair union : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      pair_spec left right pair ⟶ₘ
        union_spec pair union ⟶ₘ
          binary_union_spec left right union := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  unfold binary_union_spec membership_specification
  apply FirstOrder.Derives.forall_intro
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let Δ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set
      (union_spec pair union :: pair_spec left right pair :: Γ)
  have hPairWeak :
      Δ ⊢ₘ[T] (pair_spec left right pair).weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [Δ, FreshVariable.extendContext])
  have hUnionWeak :
      Δ ⊢ₘ[T] (union_spec pair union).weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [Δ, FreshVariable.extendContext])
  have hUnionAtRaw :=
    FirstOrder.Derives.forall_elim_newest_weakened hUnionWeak
  have hUnionAt :
      Δ ⊢ₘ[T]
        (element ∈ₘ union.weakenFree SetSort.set) ↔ₘ
          union_witness_condition
            (pair.weakenFree SetSort.set) element := by
    simpa [element, union_spec, union_witness_condition,
      membership_specification, Formula.instantiateFreeTop,
      Formula.substituteFree, Substitution.free_map,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteMapped, Arguments.substituteMapped,
      VariableSubstitution.liftFree,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId,
      VariableSubstitution.freeId,
      FreshVariable.newest] using hUnionAtRaw
  apply FirstOrder.Derives.iff_intro
  · have hUnionAt' := FirstOrder.Derives.context_weaken_cons
      (assumption := element ∈ₘ union.weakenFree SetSort.set) hUnionAt
    have hElementInUnion :
        ((element ∈ₘ union.weakenFree SetSort.set) :: Δ) ⊢ₘ[T]
          element ∈ₘ union.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hExists := FirstOrder.Derives.iff_elim_left
      hUnionAt' hElementInUnion
    apply FirstOrder.Derives.exists_elim hExists
    let witness : SetOpenTerm
        (SetSort.set :: SetSort.set :: free) := .fvar .here
    let element' : SetOpenTerm
        (SetSort.set :: SetSort.set :: free) :=
      element.weakenFree SetSort.set
    let Ω : Context signature
        (SetSort.set :: SetSort.set :: free) :=
      ((witness ∈ₘ (pair.weakenFree SetSort.set).weakenFree SetSort.set) ∧ₘ
          (element' ∈ₘ witness)) ::
        FreshVariable.extendContext SetSort.set
          ((element ∈ₘ union.weakenFree SetSort.set) :: Δ)
    have hConjunction :
        Ω ⊢ₘ[T]
          (witness ∈ₘ
              (pair.weakenFree SetSort.set).weakenFree SetSort.set) ∧ₘ
            (element' ∈ₘ witness) :=
      FirstOrder.Derives.assumption (by simp [Ω])
    have hWitnessInPair :=
      FirstOrder.Derives.conj_elim_left hConjunction
    have hElementInWitness :=
      FirstOrder.Derives.conj_elim_right hConjunction
    have hPairWeak' :
        Ω ⊢ₘ[T]
          ((pair_spec left right pair).weakenFree SetSort.set
            |>.weakenFree SetSort.set) :=
      FirstOrder.Derives.assumption (by
        simp [Ω, Δ, FreshVariable.extendContext])
    have hPairAt := pair_spec_membership_iff
      ((left.weakenFree SetSort.set).weakenFree SetSort.set)
      ((right.weakenFree SetSort.set).weakenFree SetSort.set)
      ((pair.weakenFree SetSort.set).weakenFree SetSort.set) witness (by
        have h := hPairWeak'
        change Ω ⊢ₘ[T] ((pair_spec left right pair).renameMapped
          VariableRenaming.id (VariableRenaming.weaken SetSort.set)).renameMapped
          VariableRenaming.id (VariableRenaming.weaken SetSort.set) at h
        rw [pair_spec_renameMapped, pair_spec_renameMapped] at h
        exact h)
    have hChoice := FirstOrder.Derives.iff_elim_left
      hPairAt hWitnessInPair
    apply FirstOrder.Derives.disj_elim hChoice
    · apply FirstOrder.Derives.disj_intro_left
      exact FirstOrder.Derives.iff_elim_left
        (membership_right_iff_of_equality _ _ _
          (FirstOrder.Derives.assumption List.mem_cons_self))
        (FirstOrder.Derives.context_weaken_cons hElementInWitness)
    · apply FirstOrder.Derives.disj_intro_right
      exact FirstOrder.Derives.iff_elim_left
        (membership_right_iff_of_equality _ _ _
          (FirstOrder.Derives.assumption List.mem_cons_self))
        (FirstOrder.Derives.context_weaken_cons hElementInWitness)
  · let choice : SetOpenFormula (SetSort.set :: free) :=
      (element ∈ₘ left.weakenFree SetSort.set) ∨ₘ
        (element ∈ₘ right.weakenFree SetSort.set)
    let Θ : Context signature (SetSort.set :: free) := choice :: Δ
    have hChoice : Θ ⊢ₘ[T] choice :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hUnionAt' :
        Θ ⊢ₘ[T]
          (element ∈ₘ union.weakenFree SetSort.set) ↔ₘ
            union_witness_condition
              (pair.weakenFree SetSort.set) element :=
      FirstOrder.Derives.context_weaken_cons hUnionAt
    have hPairSpec : Θ ⊢ₘ[T] pair_spec (left.weakenFree SetSort.set)
        (right.weakenFree SetSort.set) (pair.weakenFree SetSort.set) := by
      have h := FirstOrder.Derives.context_weaken_cons (assumption := choice) hPairWeak
      change Θ ⊢ₘ[T] (pair_spec left right pair).renameMapped
        VariableRenaming.id (VariableRenaming.weaken SetSort.set) at h
      rw [pair_spec_renameMapped] at h
      exact h
    have hLeftInPair := FirstOrder.Derives.iff_elim_right
      (pair_spec_membership_iff _ _ _ (left.weakenFree SetSort.set) hPairSpec)
      (FirstOrder.Derives.disj_intro_left (FirstOrder.Derives.eq_refl _))
    have hRightInPair := FirstOrder.Derives.iff_elim_right
      (pair_spec_membership_iff _ _ _ (right.weakenFree SetSort.set) hPairSpec)
      (FirstOrder.Derives.disj_intro_right (FirstOrder.Derives.eq_refl _))
    apply FirstOrder.Derives.iff_elim_right hUnionAt'
    apply FirstOrder.Derives.disj_elim hChoice
    · apply FirstOrder.Derives.exists_intro (left.weakenFree SetSort.set)
      simpa [union_witness_condition] using! FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.context_weaken_cons hLeftInPair)
        (FirstOrder.Derives.assumption List.mem_cons_self)
    · apply FirstOrder.Derives.exists_intro (right.weakenFree SetSort.set)
      simpa [union_witness_condition] using! FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.context_weaken_cons hRightInPair)
        (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 二元并项满足成员析取规格。 -/
theorem binary_union_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[binary_union_operator_theory]
      binary_union_spec left right (left ∪ₘ right) := by
  let pair : SetOpenTerm free := {left, right}ₘ
  let union : SetOpenTerm free := left ∪ₘ right
  have hPairSpec :
      Γ ⊢ₘ[binary_union_operator_theory]
        pair_spec left right pair :=
    FirstOrder.Derives.theory_weaken
      pairing_operator_theory_subset_binary_union_operator_theory
      (by simpa [pair] using
        (unordered_pair_term_spec_derives (Γ := Γ) left right))
  have hUnionEqSpec :
      Γ ⊢ₘ[binary_union_operator_theory]
        (union ≐ₘ ⋃ₘ pair) ↔ₘ union_spec pair union :=
    FirstOrder.Derives.theory_weaken
      union_operator_theory_subset_binary_union_operator_theory
      (union_eq_iff_spec (Γ := Γ) pair union)
  have hDefinition :
      Γ ⊢ₘ[binary_union_operator_theory]
        union ≐ₘ ⋃ₘ pair := by
    simpa [union, pair] using
      (binary_union_term_eq_union_pair_derives
        (Γ := Γ) left right)
  have hUnionSpec := FirstOrder.Derives.iff_elim_left
    hUnionEqSpec hDefinition
  have hBridge := pair_union_spec_implies_binary_union_spec
    (T := binary_union_operator_theory) (Γ := Γ)
    left right pair union
  simpa [union] using
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hBridge hPairSpec)
      hUnionSpec

/-- 两个参数的已证明等式可组合为二元并项等式。 -/
theorem binary_union_term_congr_of_equalities
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond : SetOpenTerm free)
    (hFirst : Γ ⊢ₘ[T] leftFirst ≐ₘ rightFirst)
    (hSecond : Γ ⊢ₘ[T] leftSecond ≐ₘ rightSecond) :
    Γ ⊢ₘ[T]
      (leftFirst ∪ₘ leftSecond) ≐ₘ
        (rightFirst ∪ₘ rightSecond) := by
  let firstContext : SetTerm [SetSort.set] free :=
    (.bvar .here : SetTerm [SetSort.set] free) ∪ₘ
      leftSecond.weakenBound SetSort.set
  let secondContext : SetTerm [SetSort.set] free :=
    rightFirst.weakenBound SetSort.set ∪ₘ
      (.bvar .here : SetTerm [SetSort.set] free)
  have hFirstContext (first : SetOpenTerm free) :
      firstContext.instantiateTop first = first ∪ₘ leftSecond := by
    change
      (((Term.bvar .here : SetTerm [SetSort.set] free)
          |>.instantiateTop first) ∪ₘ
        ((leftSecond.weakenBound SetSort.set).instantiateTop first)) =
          first ∪ₘ leftSecond
    rw [Term.instantiateTop_bvar_here,
      Term.instantiateTop_weakenBound]
  have hSecondContext (second : SetOpenTerm free) :
      secondContext.instantiateTop second = rightFirst ∪ₘ second := by
    change
      (((rightFirst.weakenBound SetSort.set).instantiateTop second) ∪ₘ
        ((Term.bvar .here : SetTerm [SetSort.set] free)
          |>.instantiateTop second)) = rightFirst ∪ₘ second
    rw [Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here]
  have hMiddle :
      firstContext.instantiateTop rightFirst =
        secondContext.instantiateTop leftSecond :=
    (hFirstContext rightFirst).trans
      (hSecondContext leftSecond).symm
  have hResult :=
    Metatheory.Derives.term_context_pair_congr_of_equalities
      (T := T) (Γ := Γ) firstContext secondContext hMiddle
      hFirst hSecond
  rw [hFirstContext leftFirst, hSecondContext rightSecond] at hResult
  exact hResult

/-- 两组参数等式推出对应二元并项相等。 -/
theorem binary_union_term_congr
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (leftFirst ≐ₘ rightFirst) ⟶ₘ
        ((leftSecond ≐ₘ rightSecond) ⟶ₘ
          ((leftFirst ∪ₘ leftSecond) ≐ₘ
            (rightFirst ∪ₘ rightSecond))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  exact binary_union_term_congr_of_equalities
    leftFirst rightFirst leftSecond rightSecond
    (FirstOrder.Derives.assumption (by simp))
    (FirstOrder.Derives.assumption List.mem_cons_self)

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
