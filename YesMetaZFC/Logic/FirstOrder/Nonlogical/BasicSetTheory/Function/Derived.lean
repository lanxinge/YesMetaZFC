import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Function.Core
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationProperties.Bounds

/-!
# 等价关系、函数与映射：导出定理

闭定义公理统一经 `forall_close_elim` 实例化；公开定理只保留数学前提，不再暴露
admissibility、作用域、变量编号或旧式全称闭包包装。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 理论嵌入 -/

derive_theory_subset relation_plane_theory ⊆ function_predicate_theory

derive_theory_subset relation_domain_operator_theory ⊆ function_predicate_theory

derive_theory_subset function_predicate_theory ⊆ function_application_theory

derive_theory_subset relation_plane_theory ⊆ function_application_theory

derive_theory_subset relation_domain_operator_theory ⊆ function_application_theory

derive_theory_subset extensionality_theory ⊆ function_application_theory

derive_theory_subset left_projection_operator_theory ⊆ function_predicate_theory

derive_theory_subset left_projection_operator_theory ⊆ function_application_theory

/-! ## 闭定义公理实例化 -/

theorem is_equivalence_relation_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[equivalence_relation_theory]
      is_equivalence_relation_definition_instance relation := by
  let body : SetOpenFormula [SetSort.set] :=
    is_equivalence_relation_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set])
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons relation VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[equivalence_relation_theory]
        Formula.fromSentence is_equivalence_relation_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, is_equivalence_relation_definition_axiom,
    is_equivalence_relation_definition_instance,
    is_equivalence_relation_condition,
    relation_reflexive_on_domain_condition,
    relation_symmetric_on_domain_condition,
    relation_transitive_on_domain_condition, set_has_member,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

theorem is_function_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (function : SetOpenTerm free) :
    Γ ⊢ₘ[function_predicate_theory]
      is_function_definition_instance function := by
  let body : SetOpenFormula [SetSort.set] :=
    is_function_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set])
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons function VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[function_predicate_theory]
        Formula.fromSentence is_function_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, is_function_definition_axiom,
    is_function_definition_instance, is_function_condition,
    function_single_valued_condition,
    function_single_valued_at_input,
    function_single_valued_at_left,
    function_single_valued_at_values,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

theorem is_mapping_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (function source target : SetOpenTerm free) :
    Γ ⊢ₘ[mapping_predicate_theory]
      is_mapping_definition_instance function source target := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    is_mapping_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons target
      (VariableSubstitution.cons source
        (VariableSubstitution.cons function VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[mapping_predicate_theory]
        Formula.fromSentence is_mapping_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, is_mapping_definition_axiom,
    is_mapping_definition_instance, is_mapping_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

theorem function_application_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (function argument value : SetOpenTerm free) :
    Γ ⊢ₘ[function_application_theory]
      function_application_definition_instance function argument value := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    function_application_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons value
      (VariableSubstitution.cons argument
        (VariableSubstitution.cons function VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[function_application_theory]
        Formula.fromSentence function_application_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, function_application_definition_axiom,
    function_application_definition_instance,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-! ## 公开定义合同 -/

theorem is_equivalence_relation_iff_condition
    {free : SetContext} {Γ : Context signature free}
    (relation : SetOpenTerm free) :
    Γ ⊢ₘ[equivalence_relation_theory]
      is_equivalence_relation_formula relation ↔ₘ
        is_equivalence_relation_condition relation :=
  is_equivalence_relation_definition_instance_derives (Γ := Γ) relation

theorem is_function_iff_condition
    {free : SetContext} {Γ : Context signature free}
    (function : SetOpenTerm free) :
    Γ ⊢ₘ[function_predicate_theory]
      is_function_formula function ↔ₘ is_function_condition function :=
  is_function_definition_instance_derives (Γ := Γ) function

theorem is_mapping_iff_condition
    {free : SetContext} {Γ : Context signature free}
    (function source target : SetOpenTerm free) :
    Γ ⊢ₘ[mapping_predicate_theory]
      is_mapping_formula function source target ↔ₘ
        is_mapping_condition function source target :=
  is_mapping_definition_instance_derives
    (Γ := Γ) function source target

theorem function_application_eq_iff_graph
    {free : SetContext} {Γ : Context signature free}
    (function argument value : SetOpenTerm free) :
    Γ ⊢ₘ[function_application_theory]
      (is_function_formula function ∧ₘ
        (argument ∈ₘ domₘ(function))) ⟶ₘ
      ((value ≐ₘ (function ·ₘ argument)) ↔ₘ
        (⟨argument, value⟩ₘ ∈ₘ function)) :=
  function_application_definition_instance_derives
    (Γ := Γ) function argument value

/-- 函数谓词蕴含关系性。 -/
theorem is_function_implies_is_relation
    {free : SetContext} {Γ : Context signature free}
    (function : SetOpenTerm free) :
    Γ ⊢ₘ[function_predicate_theory]
      is_function_formula function ⟶ₘ is_relation_formula function := by
  apply FirstOrder.Derives.imp_intro
  let predicate : SetOpenFormula free := is_function_formula function
  let Δ : Context signature free := predicate :: Γ
  have hCondition := FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.context_weaken_cons
      (is_function_iff_condition (Γ := Γ) function))
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.conj_elim_left hCondition

/-- 映射谓词蕴含其定义条件。 -/
theorem is_mapping_implies_condition
    {free : SetContext} {Γ : Context signature free}
    (function source target : SetOpenTerm free) :
    Γ ⊢ₘ[mapping_predicate_theory]
      is_mapping_formula function source target ⟶ₘ
        is_mapping_condition function source target := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.iff_elim_left
    (FirstOrder.Derives.context_weaken_cons
      (is_mapping_iff_condition (Γ := Γ) function source target))
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-! ## 关系成员的坐标合同 -/

/-- 关系图成员的第一坐标属于关系定义域。 -/
theorem relation_member_left_coordinate_mem_domain
    {free : SetContext} {Γ : Context signature free}
    (relation input value : SetOpenTerm free) :
    Γ ⊢ₘ[function_predicate_theory]
      is_relation_formula relation ⟶ₘ
        ((⟨input, value⟩ₘ ∈ₘ relation) ⟶ₘ
          (input ∈ₘ domₘ(relation))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let pair : SetOpenTerm free := ⟨input, value⟩ₘ
  let relationFormula : SetOpenFormula free :=
    is_relation_formula relation
  let membership : SetOpenFormula free := pair ∈ₘ relation
  let Δ : Context signature free :=
    membership :: relationFormula :: Γ
  have hRelation :
      Δ ⊢ₘ[function_predicate_theory]
        is_relation_formula relation := by
    simpa [Δ, relationFormula] using
      (FirstOrder.Derives.assumption
        (T := function_predicate_theory) (Γ := Δ)
        (by simp [Δ, relationFormula]))
  have hMembership :
      Δ ⊢ₘ[function_predicate_theory]
        pair ∈ₘ relation := by
    simpa [Δ, membership] using
      (FirstOrder.Derives.assumption
        (T := function_predicate_theory) (Γ := Δ)
        (by simp [Δ, membership]))
  have hDomainIff :
      Δ ⊢ₘ[function_predicate_theory]
        (input ∈ₘ domₘ(relation)) ↔ₘ
          ((input ∈ₘ double_union_term relation) ∧ₘ
            relation_domain_member_condition relation input) := by
    have hIff := FirstOrder.Derives.context_weaken_cons
      (assumption := membership)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := relationFormula)
        (FirstOrder.Derives.theory_weaken
          relation_domain_operator_theory_subset_function_predicate_theory
          (is_relation_domain_member_iff
            (Γ := Γ) relation input)))
    exact FirstOrder.Derives.imp_elim hIff hRelation
  have hCoordinates :
      Δ ⊢ₘ[function_predicate_theory]
        input ∈ₘ double_union_term relation := by
    have hCoordinateIff := FirstOrder.Derives.theory_weaken
      relation_plane_theory_subset_function_predicate_theory
      (ordered_pair_coordinates_mem_double_union
        (Γ := Γ) relation pair input value)
    have hRepresentation :
        Δ ⊢ₘ[function_predicate_theory]
          pair ≐ₘ ⟨input, value⟩ₘ := by
      simpa [pair] using
        (Metatheory.Derives.equality_refl
          (T := function_predicate_theory) (Γ := Δ) pair)
    have hAt := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hCoordinateIff))
        hMembership)
      hRepresentation
    exact FirstOrder.Derives.conj_elim_left hAt
  have hDomainCondition :
      Δ ⊢ₘ[function_predicate_theory]
        relation_domain_member_condition relation input := by
    unfold relation_domain_member_condition
      relation_coordinate_member_condition
    apply FirstOrder.Derives.exists_intro pair
    rw [Formula.instantiateTop_abstractFreeTop]
    apply FirstOrder.Derives.conj_intro
    · simpa [pair, Formula.instantiateFreeTop, Formula.substituteFree,
        Substitution.free_map, Substitution.instantiateFreeTop,
        Formula.substitute, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.liftFree,
        VariableSubstitution.instantiateFreeTop,
        VariableSubstitution.weakenBound,
        VariableSubstitution.boundId,
        VariableSubstitution.freeId] using hMembership
    · have hProjection := FirstOrder.Derives.theory_weaken
        left_projection_operator_theory_subset_function_predicate_theory
        (ordered_pair_term_left_projection_eq
          (Γ := Δ) input value)
      exact Metatheory.Derives.equality_symm
        (by simpa [pair, relation_coordinate_projection_term,
          Formula.instantiateFreeTop, Formula.substituteFree,
          Substitution.free_map, Substitution.instantiateFreeTop,
          Formula.substitute, Formula.substituteMapped,
          Term.substituteMapped, Arguments.substituteMapped,
          VariableSubstitution.liftFree,
          VariableSubstitution.instantiateFreeTop,
          VariableSubstitution.weakenBound,
          VariableSubstitution.boundId,
          VariableSubstitution.freeId] using hProjection)
  have hAt := FirstOrder.Derives.iff_elim_right
    hDomainIff (FirstOrder.Derives.conj_intro
      hCoordinates hDomainCondition)
  simpa [Δ, pair, membership, relationFormula] using hAt

/-- 关系图成员的第二坐标属于关系值域。 -/
theorem relation_member_right_coordinate_mem_range
    {free : SetContext} {Γ : Context signature free}
    (relation input value : SetOpenTerm free) :
    Γ ⊢ₘ[function_predicate_theory]
      is_relation_formula relation ⟶ₘ
        ((⟨input, value⟩ₘ ∈ₘ relation) ⟶ₘ
          (value ∈ₘ ranₘ(relation))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let pair : SetOpenTerm free := ⟨input, value⟩ₘ
  let relationFormula : SetOpenFormula free :=
    is_relation_formula relation
  let membership : SetOpenFormula free := pair ∈ₘ relation
  let Δ : Context signature free :=
    membership :: relationFormula :: Γ
  have hRelation :
      Δ ⊢ₘ[function_predicate_theory]
        is_relation_formula relation := by
    simpa [Δ, relationFormula] using
      (FirstOrder.Derives.assumption
        (T := function_predicate_theory) (Γ := Δ)
        (by simp [Δ, relationFormula]))
  have hMembership :
      Δ ⊢ₘ[function_predicate_theory]
        pair ∈ₘ relation := by
    simpa [Δ, membership] using
      (FirstOrder.Derives.assumption
        (T := function_predicate_theory) (Γ := Δ)
        (by simp [Δ, membership]))
  have hRangeIff :
      Δ ⊢ₘ[function_predicate_theory]
        (value ∈ₘ ranₘ(relation)) ↔ₘ
          ((value ∈ₘ double_union_term relation) ∧ₘ
            relation_range_member_condition relation value) := by
    have hIff := FirstOrder.Derives.context_weaken_cons
      (assumption := membership)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := relationFormula)
        (FirstOrder.Derives.theory_weaken
          (show Theory.Extends function_predicate_theory relation_range_operator_theory from by theory_inclusion)
          (is_relation_range_member_iff
            (Γ := Γ) relation value)))
    exact FirstOrder.Derives.imp_elim hIff hRelation
  have hCoordinates :
      Δ ⊢ₘ[function_predicate_theory]
        value ∈ₘ double_union_term relation := by
    have hCoordinateIff := FirstOrder.Derives.theory_weaken
      relation_plane_theory_subset_function_predicate_theory
      (ordered_pair_coordinates_mem_double_union
        (Γ := Γ) relation pair input value)
    have hRepresentation :
        Δ ⊢ₘ[function_predicate_theory]
          pair ≐ₘ ⟨input, value⟩ₘ := by
      simpa [pair] using
        (Metatheory.Derives.equality_refl
          (T := function_predicate_theory) (Γ := Δ) pair)
    have hAt := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.context_weaken_cons
          (assumption := membership)
          (FirstOrder.Derives.context_weaken_cons
            (assumption := relationFormula) hCoordinateIff))
        hMembership)
      hRepresentation
    exact FirstOrder.Derives.conj_elim_right hAt
  have hRangeCondition :
      Δ ⊢ₘ[function_predicate_theory]
        relation_range_member_condition relation value := by
    unfold relation_range_member_condition
      relation_coordinate_member_condition
    apply FirstOrder.Derives.exists_intro pair
    rw [Formula.instantiateTop_abstractFreeTop]
    apply FirstOrder.Derives.conj_intro
    · simpa [pair, Formula.instantiateFreeTop, Formula.substituteFree,
        Substitution.free_map, Substitution.instantiateFreeTop,
        Formula.substitute, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.liftFree,
        VariableSubstitution.instantiateFreeTop,
        VariableSubstitution.weakenBound,
        VariableSubstitution.boundId,
        VariableSubstitution.freeId] using hMembership
    · have hProjection := FirstOrder.Derives.theory_weaken
        (show Theory.Extends function_predicate_theory right_projection_operator_theory from by theory_inclusion)
        (ordered_pair_term_right_projection_eq
          (Γ := Δ) input value)
      exact Metatheory.Derives.equality_symm
        (by simpa [pair, relation_coordinate_projection_term,
          Formula.instantiateFreeTop, Formula.substituteFree,
          Substitution.free_map, Substitution.instantiateFreeTop,
          Formula.substitute, Formula.substituteMapped,
          Term.substituteMapped, Arguments.substituteMapped,
          VariableSubstitution.liftFree,
          VariableSubstitution.instantiateFreeTop,
          VariableSubstitution.weakenBound,
          VariableSubstitution.boundId,
          VariableSubstitution.freeId] using hProjection)
  have hAt := FirstOrder.Derives.iff_elim_right
    hRangeIff (FirstOrder.Derives.conj_intro
      hCoordinates hRangeCondition)
  simpa [Δ, pair, membership, relationFormula] using hAt



/-- 函数图在同一输入处的两个值相等。 -/
theorem is_function_single_valued
    {free : SetContext} {Γ : Context signature free}
    (function input left right : SetOpenTerm free) :
    Γ ⊢ₘ[function_predicate_theory]
      is_function_formula function ⟶ₘ
        (⟨input, left⟩ₘ ∈ₘ function) ⟶ₘ
          (⟨input, right⟩ₘ ∈ₘ function) ⟶ₘ
            (left ≐ₘ right) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let rightMembership : SetOpenFormula free :=
    ⟨input, right⟩ₘ ∈ₘ function
  let leftMembership : SetOpenFormula free :=
    ⟨input, left⟩ₘ ∈ₘ function
  let predicate : SetOpenFormula free := is_function_formula function
  let Δ : Context signature free :=
    rightMembership :: leftMembership :: predicate :: Γ
  have hPredicate : Δ ⊢ₘ[function_predicate_theory] predicate :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hDefinition : Δ ⊢ₘ[function_predicate_theory]
      is_function_definition_instance function :=
    FirstOrder.Derives.context_weaken_cons
      (assumption := rightMembership)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := leftMembership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate)
          (is_function_definition_instance_derives
            (Γ := Γ) function)))
  have hCondition := FirstOrder.Derives.iff_elim_left
    hDefinition hPredicate
  have hSingle := FirstOrder.Derives.conj_elim_right hCondition
  unfold function_single_valued_condition at hSingle
  have hInput := FirstOrder.Derives.forall_elim input hSingle
  rw [Formula.instantiateTop_abstractFreeTop] at hInput
  rw [function_single_valued_at_input_instantiateFreeTop_context]
    at hInput
  unfold function_single_valued_at_input at hInput
  have hLeft := FirstOrder.Derives.forall_elim left hInput
  rw [Formula.instantiateTop_abstractFreeTop] at hLeft
  rw [function_single_valued_at_left_instantiateFreeTop_context]
    at hLeft
  unfold function_single_valued_at_left at hLeft
  have hRight := FirstOrder.Derives.forall_elim right hLeft
  rw [Formula.instantiateTop_abstractFreeTop] at hRight
  rw [function_single_valued_at_values_instantiateFreeTop_context]
    at hRight
  have hRule : Δ ⊢ₘ[function_predicate_theory]
      ((⟨input, left⟩ₘ ∈ₘ function) ∧ₘ
        (⟨input, right⟩ₘ ∈ₘ function)) ⟶ₘ
          (left ≐ₘ right) := by
    simpa [function_single_valued_at_values] using hRight
  exact FirstOrder.Derives.imp_elim hRule
    (FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.assumption (by simp))
      (FirstOrder.Derives.assumption (by simp)))

/-- 函数在定义域参数处的规范求值有序对属于其图。 -/
theorem function_application_graph_mem
    {free : SetContext} {Γ : Context signature free}
    (function argument : SetOpenTerm free) :
    Γ ⊢ₘ[function_application_theory]
      is_function_formula function ⟶ₘ
        (argument ∈ₘ domₘ(function)) ⟶ₘ
          (⟨argument, function ·ₘ argument⟩ₘ ∈ₘ function) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let domainMembership : SetOpenFormula free :=
    argument ∈ₘ domₘ(function)
  let predicate : SetOpenFormula free := is_function_formula function
  let Δ : Context signature free := domainMembership :: predicate :: Γ
  have hDefinition := FirstOrder.Derives.context_weaken_cons
    (assumption := domainMembership)
    (FirstOrder.Derives.context_weaken_cons
      (assumption := predicate)
      (function_application_eq_iff_graph
        (Γ := Γ) function argument (function ·ₘ argument)))
  have hGuard : Δ ⊢ₘ[function_application_theory]
      is_function_formula function ∧ₘ
        (argument ∈ₘ domₘ(function)) :=
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.assumption (by simp [Δ, predicate]))
      (FirstOrder.Derives.assumption (by simp [Δ, domainMembership]))
  have hGraph := FirstOrder.Derives.imp_elim hDefinition hGuard
  exact FirstOrder.Derives.iff_elim_left hGraph
    (Metatheory.Derives.equality_refl
      (T := function_application_theory) (Γ := Δ)
      (function ·ₘ argument))

/-! ## 图成员的函数值合同 -/

/-- 在函数与定义域 guard 下，图成员给出规范函数值。 -/
theorem function_application_eq_of_graph
    {free : SetContext} {Γ : Context signature free}
    (function argument value : SetOpenTerm free) :
    Γ ⊢ₘ[function_application_theory]
      (is_function_formula function ∧ₘ
        (argument ∈ₘ domₘ(function))) ⟶ₘ
          ((⟨argument, value⟩ₘ ∈ₘ function) ⟶ₘ
            (value ≐ₘ (function ·ₘ argument))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let guard : SetOpenFormula free :=
    is_function_formula function ∧ₘ
      (argument ∈ₘ domₘ(function))
  let membership : SetOpenFormula free :=
    ⟨argument, value⟩ₘ ∈ₘ function
  let Δ : Context signature free :=
    membership :: guard :: Γ
  have hGuard : Δ ⊢ₘ[function_application_theory] guard :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hMembership :
      Δ ⊢ₘ[function_application_theory] membership :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hContract :
      Δ ⊢ₘ[function_application_theory]
        ((value ≐ₘ (function ·ₘ argument)) ↔ₘ membership) := by
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (assumption := membership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := guard)
          (function_application_eq_iff_graph
            (Γ := Γ) function argument value)))
      hGuard
  simpa [guard, membership, Δ] using
    (FirstOrder.Derives.iff_elim_right hContract hMembership)

/-- 映射在定义域内的规范函数值落入目标集。 -/
theorem is_mapping_application_mem_target
    {free : SetContext} {Γ : Context signature free}
    (function source target argument : SetOpenTerm free) :
    Γ ⊢ₘ[function_application_theory]
      is_mapping_formula function source target ⟶ₘ
        ((argument ∈ₘ domₘ(function)) ⟶ₘ
          ((function ·ₘ argument) ∈ₘ target)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let mapping : SetOpenFormula free :=
    is_mapping_formula function source target
  let domainMembership : SetOpenFormula free :=
    argument ∈ₘ domₘ(function)
  let Δ : Context signature free :=
    domainMembership :: mapping :: Γ
  have hMapping :
      Δ ⊢ₘ[function_application_theory] mapping :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hDomain :
      Δ ⊢ₘ[function_application_theory] domainMembership :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hCondition :
      Δ ⊢ₘ[function_application_theory]
        is_mapping_condition function source target := by
    have hImp := FirstOrder.Derives.theory_weaken
      mapping_predicate_theory_subset_function_application_theory
      (is_mapping_implies_condition
        (Γ := Γ) function source target)
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (assumption := domainMembership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := mapping) hImp))
      (by simpa [mapping] using hMapping)
  have hFunction :
      Δ ⊢ₘ[function_application_theory]
        is_function_formula function :=
    FirstOrder.Derives.conj_elim_left hCondition
  have hRelation :
      Δ ⊢ₘ[function_application_theory]
        is_relation_formula function := by
    have hImp := FirstOrder.Derives.theory_weaken
      function_predicate_theory_subset_function_application_theory
      (is_function_implies_is_relation
        (Γ := Γ) function)
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (assumption := domainMembership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := mapping) hImp))
      (by simpa [mapping] using hFunction)
  have hRangeSubset :
      Δ ⊢ₘ[function_application_theory]
        ranₘ(function) ⊆ₘ target := by
    exact FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_right hCondition)
  have hGraphMembership :
      Δ ⊢ₘ[function_application_theory]
        (⟨argument, function ·ₘ argument⟩ₘ ∈ₘ function) := by
    have hImp := FirstOrder.Derives.context_weaken_cons
      (assumption := domainMembership)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := mapping)
        (function_application_graph_mem
          (Γ := Γ) function argument))
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hImp
        (by simpa [mapping] using hFunction))
      (by simpa [domainMembership] using hDomain)
  have hRangeMembership :
      Δ ⊢ₘ[function_application_theory]
        (function ·ₘ argument) ∈ₘ ranₘ(function) := by
    have hImp := FirstOrder.Derives.theory_weaken
      function_predicate_theory_subset_function_application_theory
      (relation_member_right_coordinate_mem_range
        (Γ := Γ) function argument (function ·ₘ argument))
    have hImp' := FirstOrder.Derives.context_weaken_cons
      (assumption := domainMembership)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := mapping) hImp)
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hImp'
        hRelation)
      (by simpa [domainMembership, mapping] using hGraphMembership)
  have hTarget :
      Δ ⊢ₘ[function_application_theory]
        (function ·ₘ argument) ∈ₘ target :=
    subset_membership
      (show Theory.Extends function_application_theory subset_theory from by theory_inclusion)
      (ranₘ(function)) target (function ·ₘ argument)
      hRangeSubset hRangeMembership
  simpa [mapping, domainMembership, Δ] using hTarget

/-- 函数成员的规范坐标刻画。 -/
theorem is_function_member_iff_coordinates
    {free : SetContext} {Γ : Context signature free}
    (function member : SetOpenTerm free) :
    Γ ⊢ₘ[function_application_theory]
      is_function_formula function ⟶ₘ
        ((member ∈ₘ function) ↔ₘ
          function_graph_member_condition function member) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.iff_intro
  · let predicate : SetOpenFormula free :=
      is_function_formula function
    let membership : SetOpenFormula free :=
      member ∈ₘ function
    let Δ : Context signature free :=
      membership :: predicate :: Γ
    have hFunction :
        Δ ⊢ₘ[function_application_theory] predicate :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hMembership :
        Δ ⊢ₘ[function_application_theory] membership :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hRelation :
        Δ ⊢ₘ[function_application_theory]
          is_relation_formula function := by
      have hImp := FirstOrder.Derives.theory_weaken
        function_predicate_theory_subset_function_application_theory
        (is_function_implies_is_relation
          (Γ := Γ) function)
      have hImp' := FirstOrder.Derives.context_weaken_cons
        (assumption := membership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate) hImp)
      exact FirstOrder.Derives.imp_elim hImp'
        (by simpa [predicate] using hFunction)
    have hOrdered :
        Δ ⊢ₘ[function_application_theory]
          is_ordered_pair_formula member := by
      have hImp := FirstOrder.Derives.theory_weaken
        (show Theory.Extends function_application_theory relation_predicate_theory from by theory_inclusion)
        (is_relation_member_is_ordered_pair
          (Γ := Γ) function member)
      have hImp' := FirstOrder.Derives.context_weaken_cons
        (assumption := membership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate) hImp)
      exact FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim hImp'
          (by simpa [predicate] using hRelation))
        (by simpa [membership] using hMembership)
    let left : SetOpenTerm free := (member)₀ₘ
    let right : SetOpenTerm free := (member)₁ₘ
    let represented : SetOpenTerm free := ⟨left, right⟩ₘ
    have hRepresentation :
        Δ ⊢ₘ[function_application_theory]
          member ≐ₘ represented := by
      have hImp := FirstOrder.Derives.theory_weaken
        relation_plane_theory_subset_function_application_theory
        (is_relation_member_eq_ordered_pair_projections
          (Γ := Γ) function member)
      have hImp' := FirstOrder.Derives.context_weaken_cons
        (assumption := membership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate) hImp)
      have hAt := FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim hImp'
          (by simpa [predicate] using hRelation))
        (by simpa [membership] using hMembership)
      simpa [left, right, represented] using hAt
    have hRepresentedMembership :
        Δ ⊢ₘ[function_application_theory]
          represented ∈ₘ function := by
      have hTransport := membership_left_iff_of_equality
        (T := function_application_theory) (Γ := Δ)
        member represented function hRepresentation
      exact FirstOrder.Derives.iff_elim_left hTransport hMembership
    have hDomain :
        Δ ⊢ₘ[function_application_theory]
          left ∈ₘ domₘ(function) := by
      have hImp := FirstOrder.Derives.theory_weaken
        function_predicate_theory_subset_function_application_theory
        (relation_member_left_coordinate_mem_domain
          (Γ := Γ) function left right)
      have hImp' := FirstOrder.Derives.context_weaken_cons
        (assumption := membership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate) hImp)
      exact FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim hImp'
          (by simpa [predicate] using hRelation))
        (by simpa [left, right, represented] using hRepresentedMembership)
    have hValue :
        Δ ⊢ₘ[function_application_theory]
          right ≐ₘ (function ·ₘ left) := by
      have hImp := function_application_eq_of_graph
        (Γ := Γ) function left right
      have hImp' := FirstOrder.Derives.context_weaken_cons
        (assumption := membership)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate) hImp)
      have hGuard := FirstOrder.Derives.conj_intro
        (by simpa [predicate] using hFunction) hDomain
      exact FirstOrder.Derives.imp_elim
        (FirstOrder.Derives.imp_elim hImp' hGuard)
        (by simpa [left, right, represented] using hRepresentedMembership)
    simpa [predicate, membership, function_graph_member_condition,
      left, right, represented] using
      (FirstOrder.Derives.conj_intro hOrdered
        (FirstOrder.Derives.conj_intro hDomain hValue))
  · let condition : SetOpenFormula free :=
      function_graph_member_condition function member
    let predicate : SetOpenFormula free :=
      is_function_formula function
    let Δ : Context signature free :=
      condition :: predicate :: Γ
    have hFunction :
        Δ ⊢ₘ[function_application_theory] predicate :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hCondition :
        Δ ⊢ₘ[function_application_theory] condition :=
      FirstOrder.Derives.assumption (by simp [Δ])
    let left : SetOpenTerm free := (member)₀ₘ
    let right : SetOpenTerm free := (member)₁ₘ
    let represented : SetOpenTerm free := ⟨left, right⟩ₘ
    have hOrdered :
        Δ ⊢ₘ[function_application_theory]
          is_ordered_pair_formula member := by
      simpa [condition] using
        (FirstOrder.Derives.conj_elim_left hCondition)
    have hDomain :
        Δ ⊢ₘ[function_application_theory]
          left ∈ₘ domₘ(function) := by
      simpa [condition, left] using
        (FirstOrder.Derives.conj_elim_left
          (FirstOrder.Derives.conj_elim_right hCondition))
    have hValue :
        Δ ⊢ₘ[function_application_theory]
          right ≐ₘ (function ·ₘ left) := by
      simpa [condition, left, right] using
        (FirstOrder.Derives.conj_elim_right
          (FirstOrder.Derives.conj_elim_right hCondition))
    have hRepresentation :
        Δ ⊢ₘ[function_application_theory]
          member ≐ₘ represented := by
      have hImp := FirstOrder.Derives.theory_weaken
        (show Theory.Extends function_application_theory right_projection_operator_theory from by theory_inclusion)
        (is_ordered_pair_eq_ordered_pair_projections
          (Γ := Γ) member)
      have hImp' := FirstOrder.Derives.context_weaken_cons
        (assumption := condition)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate) hImp)
      have hAt := FirstOrder.Derives.imp_elim hImp' hOrdered
      simpa [left, right, represented] using hAt
    have hRepresentedMembership :
        Δ ⊢ₘ[function_application_theory]
          represented ∈ₘ function := by
      have hContract := FirstOrder.Derives.context_weaken_cons
        (assumption := condition)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := predicate)
          (function_application_eq_iff_graph
            (Γ := Γ) function left right))
      have hGuard := FirstOrder.Derives.conj_intro
        (by simpa [predicate] using hFunction) hDomain
      have hIff := FirstOrder.Derives.imp_elim hContract hGuard
      exact FirstOrder.Derives.iff_elim_left hIff hValue
    have hMembership :
        Δ ⊢ₘ[function_application_theory]
          member ∈ₘ function := by
      have hTransport := membership_left_iff_of_equality
        (T := function_application_theory) (Γ := Δ)
        member represented function hRepresentation
      exact FirstOrder.Derives.iff_elim_right hTransport
        hRepresentedMembership
    simpa [condition, predicate] using hMembership

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
