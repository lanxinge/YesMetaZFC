import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.PowerSet

/-!
# 配对与单点集

配对规格统一采用析取式成员条件。无序对与单点集是具体语言中的真实函数项；
存在公理、定义合同、唯一性与等式运输全部建立在内在类型语法上，不再保留
文献排版编码、admissibility、自由变量编号或闭性旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- `element` 是 `left` 或 `right`。 -/
def pair_member_condition {bound free : SetContext}
    (element left right : SetTerm bound free) : SetFormula bound free :=
  (element ≐ₘ left) ∨ₘ (element ≐ₘ right)

/-- `pair` 恰好含有 `left` 与 `right`。 -/
def pair_spec {bound free : SetContext}
    (left right pair : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification pair
    (pair_member_condition element
      (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set))

/-- 配对成员条件与 free 重命名自然交换。 -/
@[simp] theorem pair_member_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (element left right : SetTerm bound sourceFree) :
    (pair_member_condition element left right).renameMapped
        VariableRenaming.id ρ =
      pair_member_condition
        (element.renameMapped VariableRenaming.id ρ)
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ) := by
  rfl

/-- 配对规格与 free 重命名自然交换。 -/
@[simp] theorem pair_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (left right pair : SetTerm bound sourceFree) :
    (pair_spec left right pair).renameMapped VariableRenaming.id ρ =
      pair_spec
        (left.renameMapped VariableRenaming.id ρ)
        (right.renameMapped VariableRenaming.id ρ)
        (pair.renameMapped VariableRenaming.id ρ) := by
  unfold pair_spec
  rw [membership_specification_renameMapped]
  rw [pair_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift,
    Term.renameMapped_weakenFree_lift]
  rfl

/-- 配对规格与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem pair_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (left right pair : SetTerm bound free) :
    (pair_spec left right pair).weakenFree introduced =
      pair_spec (left.weakenFree introduced)
        (right.weakenFree introduced) (pair.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact pair_spec_renameMapped
    (VariableRenaming.weaken introduced) left right pair

/-- 对固定的两个集合断言其无序对存在。 -/
def pair_exists {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  let pair : SetTerm bound (SetSort.set :: free) := .fvar .here
  (pair_spec (left.weakenFree SetSort.set)
      (right.weakenFree SetSort.set) pair)
    |>.existsFreeTop SetSort.set

/-- 配对存在公理。 -/
def pairing_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (pair_exists
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set]))

/-- 只在外延理论上加入配对存在公理。 -/
def pairing_theory : SetTheory :=
  Theory.insert pairing_axiom extensionality_theory

/-- 无序对函数符号的开放定义实例。 -/
def pair_definition_instance {bound free : SetContext}
    (left right candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ {left, right}ₘ) ↔ₘ pair_spec left right candidate

/-- 无序对函数符号的定义公理。 -/
def pair_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (pair_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

/-- 在配对存在理论上加入无序对函数符号定义。 -/
def pairing_operator_theory : SetTheory :=
  Theory.insert pair_definition_axiom pairing_theory

/-- `singleton` 恰好只含有 `element`。 -/
def singleton_spec {bound free : SetContext}
    (element singleton : SetTerm bound free) : SetFormula bound free :=
  let member : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification singleton
    (member ≐ₘ element.weakenFree SetSort.set)

/-- 单点集规格与 free 重命名自然交换。 -/
@[simp] theorem singleton_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (element singleton : SetTerm bound sourceFree) :
    (singleton_spec element singleton).renameMapped VariableRenaming.id ρ =
      singleton_spec
        (element.renameMapped VariableRenaming.id ρ)
        (singleton.renameMapped VariableRenaming.id ρ) := by
  unfold singleton_spec
  rw [membership_specification_renameMapped]
  simp only [Formula.renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 单点集规格与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem singleton_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (element singleton : SetTerm bound free) :
    (singleton_spec element singleton).weakenFree introduced =
      singleton_spec (element.weakenFree introduced)
        (singleton.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact singleton_spec_renameMapped
    (VariableRenaming.weaken introduced) element singleton

/-- 对固定集合断言其单点集存在。 -/
def singleton_exists {bound free : SetContext}
    (element : SetTerm bound free) : SetFormula bound free :=
  let singleton : SetTerm bound (SetSort.set :: free) := .fvar .here
  (singleton_spec (element.weakenFree SetSort.set) singleton)
    |>.existsFreeTop SetSort.set

/-- 单点集函数符号的开放定义实例。 -/
def singleton_definition_instance {bound free : SetContext}
    (element : SetTerm bound free) : SetFormula bound free :=
  {element}ₘ ≐ₘ {element, element}ₘ

/-- 单点集函数符号的定义公理。 -/
def singleton_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (singleton_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set))

/-- 在无序对函数符号理论上加入单点集函数符号定义。 -/
def singleton_operator_theory : SetTheory :=
  Theory.insert singleton_definition_axiom pairing_operator_theory

/-- 配对存在公理可在任意两个集合项处实例化。 -/
theorem pair_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_theory] pair_exists left right := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    pair_exists
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons right
      (VariableSubstitution.cons left VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[pairing_theory]
        Formula.fromSentence pairing_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, pairing_axiom, pair_exists, pair_spec,
    pair_member_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 同一对元素的两个配对候选必相等。 -/
theorem pair_unique
    {free : SetContext} {Γ : Context signature free}
    (first second left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      pair_spec first second left ⟶ₘ
        pair_spec first second right ⟶ₘ (left ≐ₘ right) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    pair_member_condition element
      (first.weakenFree SetSort.set)
      (second.weakenFree SetSort.set)
  simpa [pair_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) left right condition)

/-- 重复元素的配对规格恰好就是单点集规格。 -/
theorem pair_repeated_spec_iff_singleton_spec
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (element candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      pair_spec element element candidate ↔ₘ
        singleton_spec element candidate := by
  unfold pair_spec singleton_spec
  apply Metatheory.Derives.forall_iff_mono
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let equality : SetOpenFormula (SetSort.set :: free) :=
    member ≐ₘ element.weakenFree SetSort.set
  have hIdempotent :
      FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
        (equality ∨ₘ equality) ↔ₘ equality :=
    Metatheory.Derives.disj_idem_m
  have hCongruence := Metatheory.Derives.iff_right_congr_m
    (φ := member ∈ₘ candidate.weakenFree SetSort.set) hIdempotent
  simpa [pair_member_condition, member, equality,
    FreshVariable.newest] using! hCongruence

/-- 配对存在公理推出任意集合的单点集存在。 -/
theorem singleton_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (element : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_theory] singleton_exists element := by
  have hPair := pair_exists_derives (Γ := Γ) element element
  have hBridge :
      Γ ⊢ₘ[pairing_theory]
        pair_exists element element ↔ₘ singleton_exists element := by
    unfold pair_exists singleton_exists
    apply Metatheory.Derives.exists_iff_mono
    let candidate : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    simpa [candidate, FreshVariable.newest] using!
      (pair_repeated_spec_iff_singleton_spec
        (T := pairing_theory)
        (Γ := FreshVariable.extendContext SetSort.set Γ)
        (element.weakenFree SetSort.set) candidate)
  exact FirstOrder.Derives.iff_elim_left hBridge hPair

/-- 无序对定义公理可在任意三个集合项处实例化。 -/
theorem pair_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_operator_theory]
      pair_definition_instance left right candidate := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    pair_definition_instance
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
      ([] : Context signature []) ⊢ₘ[pairing_operator_theory]
        Formula.fromSentence pair_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, pair_definition_axiom,
    pair_definition_instance, pair_spec,
    pair_member_condition, membership_specification,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 定义扩张中的无序对项满足配对规格。 -/
theorem unordered_pair_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_operator_theory]
      pair_spec left right {left, right}ₘ := by
  have hDefinition := pair_definition_instance_derives
    (Γ := Γ) left right {left, right}ₘ
  exact FirstOrder.Derives.iff_elim_left hDefinition
    (Metatheory.Derives.equality_refl
      (T := pairing_operator_theory) (Γ := Γ) {left, right}ₘ)

/-- 一个候选项等于规范无序对，当且仅当它满足对应规格。 -/
theorem unordered_pair_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[pairing_operator_theory]
      (candidate ≐ₘ {left, right}ₘ) ↔ₘ
        pair_spec left right candidate :=
  pair_definition_instance_derives (Γ := Γ) left right candidate

/-- 两个参数的已证明等式可组合为无序对项等式。 -/
theorem unordered_pair_term_congr_of_equalities
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond : SetOpenTerm free)
    (hFirst : Γ ⊢ₘ[T] leftFirst ≐ₘ rightFirst)
    (hSecond : Γ ⊢ₘ[T] leftSecond ≐ₘ rightSecond) :
    Γ ⊢ₘ[T]
      {leftFirst, leftSecond}ₘ ≐ₘ {rightFirst, rightSecond}ₘ := by
  let firstContext : SetTerm [SetSort.set] free :=
    {(.bvar .here : SetTerm [SetSort.set] free),
      leftSecond.weakenBound SetSort.set}ₘ
  let secondContext : SetTerm [SetSort.set] free :=
    {rightFirst.weakenBound SetSort.set,
      (.bvar .here : SetTerm [SetSort.set] free)}ₘ
  have hFirstContext (first : SetOpenTerm free) :
      firstContext.instantiateTop first = {first, leftSecond}ₘ := by
    change
      {((Term.bvar .here : SetTerm [SetSort.set] free).instantiateTop first),
        ((leftSecond.weakenBound SetSort.set).instantiateTop first)}ₘ =
        {first, leftSecond}ₘ
    rw [Term.instantiateTop_bvar_here,
      Term.instantiateTop_weakenBound]
  have hSecondContext (second : SetOpenTerm free) :
      secondContext.instantiateTop second = {rightFirst, second}ₘ := by
    change
      {((rightFirst.weakenBound SetSort.set).instantiateTop second),
        ((Term.bvar .here : SetTerm [SetSort.set] free).instantiateTop second)}ₘ =
        {rightFirst, second}ₘ
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

/-- 两组参数等式推出对应无序对项相等。 -/
theorem unordered_pair_term_congr
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (leftFirst ≐ₘ rightFirst) ⟶ₘ
        ((leftSecond ≐ₘ rightSecond) ⟶ₘ
          ({leftFirst, leftSecond}ₘ ≐ₘ
            {rightFirst, rightSecond}ₘ)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  exact unordered_pair_term_congr_of_equalities
    leftFirst rightFirst leftSecond rightSecond
    (FirstOrder.Derives.assumption (by simp))
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 两组参数等式可运输同一个候选对象的无序对等式。 -/
theorem unordered_pair_eq_transport
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (leftFirst rightFirst leftSecond rightSecond candidate :
      SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (leftFirst ≐ₘ rightFirst) ⟶ₘ
        ((leftSecond ≐ₘ rightSecond) ⟶ₘ
          ((candidate ≐ₘ {leftFirst, leftSecond}ₘ) ⟶ₘ
            (candidate ≐ₘ {rightFirst, rightSecond}ₘ))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    (candidate ≐ₘ {leftFirst, leftSecond}ₘ) ::
      (leftSecond ≐ₘ rightSecond) ::
        (leftFirst ≐ₘ rightFirst) :: Γ
  have hPairEquality :
      Δ ⊢ₘ[T] {leftFirst, leftSecond}ₘ ≐ₘ
        {rightFirst, rightSecond}ₘ :=
    unordered_pair_term_congr_of_equalities
      leftFirst rightFirst leftSecond rightSecond
      (FirstOrder.Derives.assumption (by simp [Δ]))
      (FirstOrder.Derives.assumption (by simp [Δ]))
  have hCandidateEquality :
      Δ ⊢ₘ[T] candidate ≐ₘ {leftFirst, leftSecond}ₘ :=
    FirstOrder.Derives.assumption (by simp [Δ])
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hPairEquality

/-- 单点集定义公理可在任意集合项处实例化。 -/
theorem singleton_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (element : SetOpenTerm free) :
    Γ ⊢ₘ[singleton_operator_theory]
      singleton_definition_instance element := by
  let body : SetOpenFormula [SetSort.set] :=
    singleton_definition_instance
      (FreshVariable.newest
        (σ := signature) (free := []) SetSort.set)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons element VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[singleton_operator_theory]
        Formula.fromSentence singleton_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, singleton_definition_axiom,
    singleton_definition_instance, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId,
    FreshVariable.newest] using! hInstance

/-- 定义扩张中的单点集项等于对应的重复无序对项。 -/
theorem singleton_term_eq_pair_derives
    {free : SetContext} {Γ : Context signature free}
    (element : SetOpenTerm free) :
    Γ ⊢ₘ[singleton_operator_theory]
      {element}ₘ ≐ₘ {element, element}ₘ := by
  simpa [singleton_definition_instance] using
    (singleton_definition_instance_derives (Γ := Γ) element)

/-- 定义扩张中的单点集项满足单点集规格。 -/
theorem singleton_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (element : SetOpenTerm free) :
    Γ ⊢ₘ[singleton_operator_theory]
      singleton_spec element {element}ₘ := by
  let singleton : SetOpenTerm free := {element}ₘ
  let repeatedPair : SetOpenTerm free := {element, element}ₘ
  have hEquality :
      Γ ⊢ₘ[singleton_operator_theory] singleton ≐ₘ repeatedPair := by
    simpa [singleton, repeatedPair] using
      (singleton_term_eq_pair_derives (Γ := Γ) element)
  let body : Formula signature [SetSort.set] free :=
    singleton_spec (element.weakenBound SetSort.set) (.bvar .here)
  have hCongruence := Metatheory.Derives.equality_iff_of_equality
    (T := singleton_operator_theory) (Γ := Γ) body hEquality
  have hCongruence' :
      Γ ⊢ₘ[singleton_operator_theory]
        singleton_spec element singleton ↔ₘ
          singleton_spec element repeatedPair := by
    simpa [body, singleton_spec, membership_specification] using! hCongruence
  have hPairSpec :
      Γ ⊢ₘ[singleton_operator_theory]
        pair_spec element element repeatedPair :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => Or.inr hSentence)
      (by simpa [repeatedPair] using
        (unordered_pair_term_spec_derives (Γ := Γ) element element))
  have hRepeatedSpec := FirstOrder.Derives.iff_elim_left
    (pair_repeated_spec_iff_singleton_spec
      (T := singleton_operator_theory) (Γ := Γ) element repeatedPair)
    hPairSpec
  simpa [singleton] using
    FirstOrder.Derives.iff_elim_right hCongruence' hRepeatedSpec

/-- 配对规格在任意成员项处的点态实例。 -/
theorem pair_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right pair member : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] pair_spec left right pair) :
    Γ ⊢ₘ[T]
      (member ∈ₘ pair) ↔ₘ
        ((member ≐ₘ left) ∨ₘ (member ≐ₘ right)) := by
  have hAt := FirstOrder.Derives.forall_elim member hSpec
  simpa [pair_spec, pair_member_condition,
    membership_specification] using! hAt

/-- 单点集规格在任意成员项处的点态实例。 -/
theorem singleton_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (element singleton member : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] singleton_spec element singleton) :
    Γ ⊢ₘ[T] (member ∈ₘ singleton) ↔ₘ (member ≐ₘ element) := by
  have hAt := FirstOrder.Derives.forall_elim member hSpec
  simpa [singleton_spec, membership_specification] using! hAt

/-- 同一个配对候选在首项固定时，第二项唯一。 -/
theorem pair_spec_right_unique
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (first left right pair : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      pair_spec first left pair ⟶ₘ
        pair_spec first right pair ⟶ₘ (left ≐ₘ right) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    pair_spec first right pair :: pair_spec first left pair :: Γ
  have hLeftSpec : Δ ⊢ₘ[T] pair_spec first left pair :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hRightSpec : Δ ⊢ₘ[T] pair_spec first right pair :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hLeftAtLeft := pair_spec_membership_iff
    first left pair left hLeftSpec
  have hRightAtLeft := pair_spec_membership_iff
    first right pair left hRightSpec
  have hLeftMem : Δ ⊢ₘ[T] left ∈ₘ pair :=
    FirstOrder.Derives.iff_elim_right hLeftAtLeft
      (FirstOrder.Derives.disj_intro_right
        (Metatheory.Derives.equality_refl
          (T := T) (Γ := Δ) left))
  have hLeftCases :
      Δ ⊢ₘ[T] (left ≐ₘ first) ∨ₘ (left ≐ₘ right) :=
    FirstOrder.Derives.iff_elim_left hRightAtLeft hLeftMem
  have hRightAtRight := pair_spec_membership_iff
    first right pair right hRightSpec
  have hLeftAtRight := pair_spec_membership_iff
    first left pair right hLeftSpec
  have hRightMem : Δ ⊢ₘ[T] right ∈ₘ pair :=
    FirstOrder.Derives.iff_elim_right hRightAtRight
      (FirstOrder.Derives.disj_intro_right
        (Metatheory.Derives.equality_refl
          (T := T) (Γ := Δ) right))
  have hRightCases :
      Δ ⊢ₘ[T] (right ≐ₘ first) ∨ₘ (right ≐ₘ left) :=
    FirstOrder.Derives.iff_elim_left hLeftAtRight hRightMem
  apply FirstOrder.Derives.disj_elim hLeftCases
  · have hRightCases' := FirstOrder.Derives.context_weaken_cons
      (assumption := left ≐ₘ first) hRightCases
    apply FirstOrder.Derives.disj_elim hRightCases'
    · exact Metatheory.Derives.equality_trans
        (FirstOrder.Derives.assumption (by simp))
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.assumption List.mem_cons_self))
    · exact Metatheory.Derives.equality_symm
        (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.assumption List.mem_cons_self

/-- 相等的两个配对候选在首项固定时具有相同的第二项。 -/
theorem pair_spec_right_unique_of_pair_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (first left right pairLeft pairRight : SetOpenTerm free)
    (hLeftSpec : Γ ⊢ₘ[T] pair_spec first left pairLeft)
    (hRightSpec : Γ ⊢ₘ[T] pair_spec first right pairRight)
    (hPairEquality : Γ ⊢ₘ[T] pairLeft ≐ₘ pairRight) :
    Γ ⊢ₘ[T] left ≐ₘ right := by
  let body : Formula signature [SetSort.set] free :=
    pair_spec (first.weakenBound SetSort.set)
      (right.weakenBound SetSort.set) (.bvar .here)
  have hTransport := Metatheory.Derives.equality_iff_of_equality
    (T := T) (Γ := Γ) body hPairEquality
  have hTransport' :
      Γ ⊢ₘ[T]
        pair_spec first right pairLeft ↔ₘ
          pair_spec first right pairRight := by
    simpa [body, pair_spec, pair_member_condition,
      membership_specification] using! hTransport
  have hRightSpecLeft :=
    FirstOrder.Derives.iff_elim_right hTransport' hRightSpec
  have hUnique := pair_spec_right_unique
    (T := T) (Γ := Γ) first left right pairLeft
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim hUnique hLeftSpec)
    hRightSpecLeft

/-- 配对规格的首元素可沿已证明的等式反向运输。 -/
theorem pair_spec_transport_first_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (first second fixed pair : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] first ≐ₘ second)
    (hSpec : Γ ⊢ₘ[T] pair_spec second fixed pair) :
    Γ ⊢ₘ[T] pair_spec first fixed pair := by
  let body : SetFormula [SetSort.set] free :=
    pair_spec (.bvar .here : SetTerm [SetSort.set] free)
      (fixed.weakenBound SetSort.set)
      (pair.weakenBound SetSort.set)
  have hTransport := Metatheory.Derives.equality_iff_of_equality
    (T := T) (Γ := Γ) body hEquality
  have hTransport' :
      Γ ⊢ₘ[T]
        pair_spec first fixed pair ↔ₘ pair_spec second fixed pair := by
    simpa [body, pair_spec, pair_member_condition,
      membership_specification] using! hTransport
  exact FirstOrder.Derives.iff_elim_right hTransport' hSpec

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
