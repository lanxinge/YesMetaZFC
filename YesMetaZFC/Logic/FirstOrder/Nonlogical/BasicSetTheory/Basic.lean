import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality.Basic
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Axioms

/-!
# 基本集合论的首批具体非逻辑定理

所有接口直接接收内在类型集合项。成员规格的条件位于规范 fresh free 槽中；外延与
子集公理从闭理论公理逐层实例化，不再携带变量编号、admissibility、scope 或
freshness 旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- 第一存在性：存在一个等于自身的集合。 -/
theorem first_existence :
    ([] : Context signature []) ⊢ₘ[(Theory.empty : SetTheory)]
      ((Term.newestFree (σ := signature) (bound := []) (free := [])
          SetSort.set ≐ₘ
        Term.newestFree (σ := signature) (bound := []) (free := [])
          SetSort.set).existsFreeTop SetSort.set) := by
  apply FirstOrder.Derives.free_strengthening
  exact FirstOrder.Derives.exists_intro_newest
    (Metatheory.Derives.equality_refl
      (T := (Theory.empty : SetTheory))
      (Γ := ([] : Context signature [SetSort.set]))
      (Term.newestFree (σ := signature) (bound := []) (free := [])
        SetSort.set))

/-- 相等集合具有完全相同的元素。 -/
theorem equality_implies_membership_agreement
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[T] equality_to_agreement left right := by
  unfold equality_to_agreement
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.forall_intro
  have hEquality :
      FreshVariable.extendContext SetSort.set ((left ≐ₘ right) :: Γ) ⊢ₘ[T]
        left.weakenFree SetSort.set ≐ₘ right.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [FreshVariable.extendContext])
  let element : SetOpenTerm (SetSort.set :: free) :=
    Term.newestFree (σ := signature) (bound := []) (free := free)
      SetSort.set
  let body : Formula signature [SetSort.set] (SetSort.set :: free) :=
    element.weakenBound SetSort.set ∈ₘ (.bvar .here)
  have hAgreement :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T)
      (Γ := FreshVariable.extendContext SetSort.set
        ((left ≐ₘ right) :: Γ))
      body hEquality
  simpa [membership_agreement, element, body] using! hAgreement

/-- 容器等式可运输任意固定项的成员关系。 -/
theorem membership_right_iff_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (element left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (element ∈ₘ left) ↔ₘ (element ∈ₘ right) := by
  let body : Formula signature [SetSort.set] free :=
    element.weakenBound SetSort.set ∈ₘ (.bvar .here)
  simpa [body] using!
    (Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) body hEquality)

/-- 元素等式可运输其在任意固定容器中的成员关系。 -/
theorem membership_left_iff_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right set : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (left ∈ₘ set) ↔ₘ (right ∈ₘ set) := by
  let body : Formula signature [SetSort.set] free :=
    (.bvar .here) ∈ₘ set.weakenBound SetSort.set
  simpa [body] using!
    (Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) body hEquality)

/-- 左端集合等式可运输子集关系。 -/
theorem subset_left_iff_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right set : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (left ⊆ₘ set) ↔ₘ (right ⊆ₘ set) := by
  let body : Formula signature [SetSort.set] free :=
    (.bvar .here) ⊆ₘ set.weakenBound SetSort.set
  simpa [body] using!
    (Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) body hEquality)

/-- 外延理论可在任意两个集合项处实例化外延公理。 -/
theorem extensionality_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      extensionality_instance left right := by
  have hAxiom :
      ([] : Context signature []) ⊢ₘ[extensionality_theory]
        extensionality_axiom := by
    simpa [Formula.fromSentence, Renaming.emptyFree] using
      (FirstOrder.Derives.theory_axiom
        (free := []) (Γ := ([] : Context signature [])) (by rfl))
  simp only [extensionality_axiom,
    Metatheory.Formula.forall_close_cons,
    Metatheory.Formula.forall_close_nil] at hAxiom
  have hFirst := FirstOrder.Derives.forall_elim_newest hAxiom
  have hBody := FirstOrder.Derives.forall_elim_newest hFirst
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons right
      (VariableSubstitution.cons left VariableSubstitution.empty)
  have hInstance := FirstOrder.Derives.free_substitution τ hBody
  have hInstanceInContext :=
    FirstOrder.Derives.context_weaken (Δ := Γ)
      (by
        intro candidate hMember
        cases hMember)
      hInstance
  simpa [τ, extensionality_instance, agreement_to_equality,
    membership_agreement, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.freeId,
    VariableSubstitution.boundId,
    VariableSubstitution.weakenBound, VariableSubstitution.liftFree,
    Context.substituteFree, FreshVariable.extendContext] using hInstanceInContext

/-- 以一个规范 fresh 元素描述集合的通用成员规格。 -/
def membership_specification {bound free : SetContext}
    (candidate : SetTerm bound free)
    (condition : SetFormula bound (SetSort.set :: free)) :
    SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) :=
    .fvar .here
  ((element ∈ₘ candidate.weakenFree SetSort.set) ↔ₘ condition)
    |>.forallFreeTop SetSort.set

/-- 通用成员规格与 free 重命名自然交换。 -/
@[simp] theorem membership_specification_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (candidate : SetTerm bound sourceFree)
    (condition : SetFormula bound (SetSort.set :: sourceFree)) :
    (membership_specification candidate condition).renameMapped
        VariableRenaming.id ρ =
      membership_specification
        (candidate.renameMapped VariableRenaming.id ρ)
        (condition.renameMapped VariableRenaming.id
          (VariableRenaming.lift (introduced := SetSort.set) ρ)) := by
  unfold membership_specification
  rw [Formula.renameMapped_forallFreeTop]
  simp only [Formula.renameMapped, Arguments.renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 通用成员规格与 bound 顶部实例化自然交换。 -/
@[simp] theorem membership_specification_instantiateTop
    {bound free : SetContext}
    (replacement : SetTerm bound free)
    (candidate : SetTerm (SetSort.set :: bound) free)
    (condition : SetFormula (SetSort.set :: bound)
      (SetSort.set :: free)) :
    (membership_specification candidate condition).instantiateTop replacement =
      membership_specification
        (candidate.instantiateTop replacement)
        (condition.instantiateTop
          (replacement.weakenFree SetSort.set)) := by
  unfold membership_specification
  rw [Formula.instantiateTop_forallFreeTop]
  exact congrArg
    (fun currentCandidate : SetTerm bound (SetSort.set :: free) =>
      Formula.forallFreeTop SetSort.set
        (((.fvar .here : SetTerm bound (SetSort.set :: free)) ∈ₘ
          currentCandidate) ↔ₘ
          condition.instantiateTop (replacement.weakenFree SetSort.set)))
    (Term.instantiateTop_weakenFree
      (introduced := SetSort.set) replacement candidate)

/-- 两个集合满足同一个成员规格时相等。 -/
theorem membership_specification_unique
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (condition : SetOpenFormula (SetSort.set :: free)) :
    Γ ⊢ₘ[extensionality_theory]
      membership_specification left condition ⟶ₘ
        membership_specification right condition ⟶ₘ (left ≐ₘ right) := by
  let leftSpecification := membership_specification left condition
  let rightSpecification := membership_specification right condition
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  have hAgreement :
      (rightSpecification :: leftSpecification :: Γ) ⊢ₘ[extensionality_theory]
        membership_agreement left right := by
    apply FirstOrder.Derives.forall_intro
    have hLeftUniversal :
        FreshVariable.extendContext SetSort.set
          (rightSpecification :: leftSpecification :: Γ) ⊢ₘ[extensionality_theory]
          leftSpecification.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption (.tail _ (.head _))
    have hRightUniversal :
        FreshVariable.extendContext SetSort.set
          (rightSpecification :: leftSpecification :: Γ) ⊢ₘ[extensionality_theory]
          rightSpecification.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption (.head _)
    have hLeftAt :=
      FirstOrder.Derives.forall_elim_newest_weakened hLeftUniversal
    have hRightAt :=
      FirstOrder.Derives.forall_elim_newest_weakened hRightUniversal
    exact Metatheory.Derives.iff_trans
      (by simpa [leftSpecification, membership_specification] using hLeftAt)
      (Metatheory.Derives.iff_symm
        (by simpa [rightSpecification, membership_specification] using hRightAt))
  have hExtensionality :=
    extensionality_instance_derives
      (Γ := rightSpecification :: leftSpecification :: Γ) left right
  exact FirstOrder.Derives.imp_elim hExtensionality hAgreement

/-- 子集理论可在任意两个集合项处实例化子集定义公理。 -/
theorem subset_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[subset_theory] subset_definition_instance left right := by
  have hAxiom :
      ([] : Context signature []) ⊢ₘ[subset_theory]
        subset_definition_axiom := by
    simpa [Formula.fromSentence, Renaming.emptyFree] using
      (FirstOrder.Derives.theory_axiom
        (free := []) (Γ := ([] : Context signature []))
        (by exact Or.inl rfl))
  simp only [subset_definition_axiom,
    Metatheory.Formula.forall_close_cons,
    Metatheory.Formula.forall_close_nil] at hAxiom
  have hFirst := FirstOrder.Derives.forall_elim_newest hAxiom
  have hBody := FirstOrder.Derives.forall_elim_newest hFirst
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons right
      (VariableSubstitution.cons left VariableSubstitution.empty)
  have hInstance := FirstOrder.Derives.free_substitution τ hBody
  have hInstanceInContext :=
    FirstOrder.Derives.context_weaken (Δ := Γ)
      (by
        intro candidate hMember
        cases hMember)
      hInstance
  simpa [τ, subset_definition_instance, subset_condition,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.freeId, VariableSubstitution.boundId,
    VariableSubstitution.weakenBound, VariableSubstitution.liftFree,
    Context.substituteFree, FreshVariable.extendContext] using hInstanceInContext

/-- 在包含子集定义的任意理论中，由规范 fresh 元素上的点态蕴含引入子集关系。 -/
theorem subset_intro
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (hSubsetTheory : ∀ {sentence : SetSentence},
      subset_theory sentence → T sentence)
    (left right : SetOpenTerm free)
    (hPoint : FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
      (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set ∈ₘ
        left.weakenFree SetSort.set) ⟶ₘ
      (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set ∈ₘ
        right.weakenFree SetSort.set)) :
    Γ ⊢ₘ[T] left ⊆ₘ right := by
  have hCondition : Γ ⊢ₘ[T] subset_condition left right := by
    unfold subset_condition
    exact FirstOrder.Derives.forall_intro hPoint
  have hDefinition := FirstOrder.Derives.theory_weaken
    hSubsetTheory (subset_definition_instance_derives (Γ := Γ) left right)
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

/-- 子集关系可在任意元素处消去为成员蕴含。 -/
theorem subset_membership
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (hSubsetTheory : ∀ {sentence : SetSentence},
      subset_theory sentence → T sentence)
    (left right element : SetOpenTerm free)
    (hSubset : Γ ⊢ₘ[T] left ⊆ₘ right)
    (hMember : Γ ⊢ₘ[T] element ∈ₘ left) :
    Γ ⊢ₘ[T] element ∈ₘ right := by
  have hDefinition := FirstOrder.Derives.theory_weaken
    hSubsetTheory (subset_definition_instance_derives (Γ := Γ) left right)
  have hCondition := FirstOrder.Derives.iff_elim_left
    hDefinition hSubset
  have hAt := FirstOrder.Derives.forall_elim element hCondition
  exact FirstOrder.Derives.imp_elim
    (by simpa [subset_condition] using! hAt) hMember

/-- 成员规格由母集成员条件合取给出时，候选集合包含于母集。 -/
theorem membership_specification_subset_source
    {free : SetContext} {Γ : Context signature free}
    (candidate source : SetOpenTerm free)
    (condition : SetOpenFormula (SetSort.set :: free)) :
    let element : SetOpenTerm (SetSort.set :: free) :=
      Term.newestFree (σ := signature) (bound := []) (free := free)
        SetSort.set
    Γ ⊢ₘ[subset_theory]
      membership_specification candidate
          ((element ∈ₘ source.weakenFree SetSort.set) ∧ₘ condition) ⟶ₘ
        (candidate ⊆ₘ source) := by
  dsimp
  let element : SetOpenTerm (SetSort.set :: free) :=
    Term.newestFree (σ := signature) (bound := []) (free := free)
      SetSort.set
  let specification := membership_specification candidate
    ((element ∈ₘ source.weakenFree SetSort.set) ∧ₘ condition)
  apply FirstOrder.Derives.imp_intro
  have hSubsetCondition :
      (specification :: Γ) ⊢ₘ[subset_theory]
        subset_condition candidate source := by
    apply FirstOrder.Derives.forall_intro
    have hUniversal :
        FreshVariable.extendContext SetSort.set (specification :: Γ) ⊢ₘ[subset_theory]
          specification.weakenFree SetSort.set :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hAt := FirstOrder.Derives.forall_elim_newest_weakened hUniversal
    apply FirstOrder.Derives.imp_intro
    have hAt' := FirstOrder.Derives.context_weaken_cons
      (assumption := element ∈ₘ candidate.weakenFree SetSort.set) hAt
    have hConjunction := FirstOrder.Derives.iff_elim_left hAt'
      (FirstOrder.Derives.assumption List.mem_cons_self)
    exact FirstOrder.Derives.conj_elim_left hConjunction
  have hDefinition := subset_definition_instance_derives
    (Γ := specification :: Γ) candidate source
  exact FirstOrder.Derives.iff_elim_right hDefinition hSubsetCondition

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
