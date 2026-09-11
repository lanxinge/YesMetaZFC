import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union

/-!
# 后继

后继的核心成员条件采用 `z = x ∨ z ∈ x`。文献中的 `¬(z = x) → z ∈ x`
作为对象经典逻辑下的等价接口保留。存在性由规范见证 `x ∪ {x, x}` 构造，
后继函数符号仅是这一既有构造的定义扩张。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- `element` 等于 `source` 或属于 `source`。 -/
def successor_member_condition {bound free : SetContext}
    (element source : SetTerm bound free) : SetFormula bound free :=
  (element ≐ₘ source) ∨ₘ (element ∈ₘ source)

/-- 文献采用的后继成员条件。 -/
def successor_paper_condition {bound free : SetContext}
    (element source : SetTerm bound free) : SetFormula bound free :=
  (¬ₘ (element ≐ₘ source)) ⟶ₘ (element ∈ₘ source)

/-- `candidate` 正好是 `source` 的后继。 -/
def successor_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (successor_member_condition element
      (source.weakenFree SetSort.set))

/-- 文献蕴含写法下的后继规格。 -/
def successor_paper_spec {bound free : SetContext}
    (source candidate : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  membership_specification candidate
    (successor_paper_condition element
      (source.weakenFree SetSort.set))

/-- 对固定集合断言其后继存在。 -/
def successor_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (successor_spec (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 文献蕴含写法下的后继存在公式。 -/
def successor_paper_exists {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (successor_paper_spec (source.weakenFree SetSort.set) candidate)
    |>.existsFreeTop SetSort.set

/-- 由配对与二元并给出的规范后继见证。 -/
abbrev successor_witness_term {bound free : SetContext}
    (source : SetTerm bound free) : SetTerm bound free :=
  source ∪ₘ {source, source}ₘ

/-- 后继存在性所需的最弱既有理论。 -/
def successor_base_theory : SetTheory :=
  binary_union_operator_theory

/-- 后继函数符号的开放定义实例。 -/
def successor_definition_instance {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  Sₘ(source) ≐ₘ successor_witness_term source

/-- 后继函数符号的闭定义公理。 -/
def successor_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (successor_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set]))

/-- 在既有后继构造理论上加入后继函数符号。 -/
def successor_operator_theory : SetTheory :=
  Theory.insert successor_definition_axiom successor_base_theory

/-- 二元并函数符号理论嵌入后继函数符号理论。 -/
derive_theory_subset binary_union_operator_theory ⊆ successor_operator_theory

/-- 外延理论嵌入后继函数符号理论。 -/
derive_theory_subset extensionality_theory ⊆ successor_operator_theory

/-- 后继成员条件与 free 重命名自然交换。 -/
@[simp] theorem successor_member_condition_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (element source : SetTerm bound sourceFree) :
    (successor_member_condition element source).renameMapped
        VariableRenaming.id ρ =
      successor_member_condition
        (element.renameMapped VariableRenaming.id ρ)
        (source.renameMapped VariableRenaming.id ρ) := by
  simp [successor_member_condition, Formula.renameMapped,
    Arguments.renameMapped]

/-- 后继规格与 free 重命名自然交换。 -/
@[simp] theorem successor_spec_renameMapped
    {bound sourceFree targetFree : SetContext}
    (ρ : VariableRenaming sourceFree targetFree)
    (source candidate : SetTerm bound sourceFree) :
    (successor_spec source candidate).renameMapped VariableRenaming.id ρ =
      successor_spec
        (source.renameMapped VariableRenaming.id ρ)
        (candidate.renameMapped VariableRenaming.id ρ) := by
  unfold successor_spec
  rw [membership_specification_renameMapped]
  rw [successor_member_condition_renameMapped]
  rw [Term.renameMapped_weakenFree_lift]
  rfl

/-- 后继规格与任意新 free 参数槽的 weakening 严格交换。 -/
@[simp] theorem successor_spec_weakenFree
    {bound free : SetContext} (introduced : SetSort)
    (source candidate : SetTerm bound free) :
    (successor_spec source candidate).weakenFree introduced =
      successor_spec (source.weakenFree introduced)
        (candidate.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  exact successor_spec_renameMapped
    (VariableRenaming.weaken introduced) source candidate

/-- 文献后继成员条件与现代析取条件在对象经典逻辑中等价。 -/
theorem successor_paper_condition_iff_member_condition
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (element source : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      successor_paper_condition element source ↔ₘ
        successor_member_condition element source := by
  simpa [successor_paper_condition, successor_member_condition] using
    (Metatheory.Derives.neg_imp_disj_iff_m
      (T := T) (Γ := Γ)
      (φ := element ≐ₘ source) (ψ := element ∈ₘ source))

/-- 文献后继规格与现代后继规格等价。 -/
theorem successor_paper_spec_iff_spec
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      successor_paper_spec source candidate ↔ₘ
        successor_spec source candidate := by
  unfold successor_paper_spec successor_spec membership_specification
  apply Metatheory.Derives.forall_iff_mono
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  have hCondition := successor_paper_condition_iff_member_condition
    (T := T) (Γ := FreshVariable.extendContext SetSort.set Γ)
    element (source.weakenFree SetSort.set)
  simpa [element, FreshVariable.newest] using!
    (Metatheory.Derives.iff_right_congr_m
      (φ := element ∈ₘ candidate.weakenFree SetSort.set) hCondition)

/-- 单点集规格把二元并成员条件化为后继成员条件。 -/
theorem binary_union_singleton_condition_iff_successor_condition
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source singleton element : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      singleton_spec source singleton ⟶ₘ
        (binary_union_member_condition source singleton element ↔ₘ
          successor_member_condition element source) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := singleton_spec source singleton :: Γ
  have hSingleton : Δ ⊢ₘ[T] singleton_spec source singleton :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hSingletonAt := singleton_spec_membership_iff
    source singleton element hSingleton
  apply FirstOrder.Derives.iff_intro
  · have hCases :
        binary_union_member_condition source singleton element :: Δ ⊢ₘ[T]
          (element ∈ₘ source) ∨ₘ (element ∈ₘ singleton) := by
      simpa [binary_union_member_condition] using
        (FirstOrder.Derives.assumption List.mem_cons_self)
    apply FirstOrder.Derives.disj_elim hCases
    · exact FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.assumption List.mem_cons_self)
    · have hSingletonAt' := FirstOrder.Derives.context_weaken_cons
        (assumption := element ∈ₘ singleton)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := binary_union_member_condition
            source singleton element)
          hSingletonAt)
      exact FirstOrder.Derives.disj_intro_left
        (FirstOrder.Derives.iff_elim_left hSingletonAt'
          (FirstOrder.Derives.assumption List.mem_cons_self))
  · have hCases :
        successor_member_condition element source :: Δ ⊢ₘ[T]
          (element ≐ₘ source) ∨ₘ (element ∈ₘ source) := by
      simpa [successor_member_condition] using
        (FirstOrder.Derives.assumption List.mem_cons_self)
    apply FirstOrder.Derives.disj_elim hCases
    · have hSingletonAt' := FirstOrder.Derives.context_weaken_cons
        (assumption := element ≐ₘ source)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := successor_member_condition element source)
          hSingletonAt)
      exact FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.iff_elim_right hSingletonAt'
          (FirstOrder.Derives.assumption List.mem_cons_self))
    · exact FirstOrder.Derives.disj_intro_left
        (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 单点集规格与二元并规格组合成后继规格。 -/
theorem binary_union_singleton_spec_implies_successor_spec
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source singleton candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      singleton_spec source singleton ⟶ₘ
        (binary_union_spec source singleton candidate ⟶ₘ
          successor_spec source candidate) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  unfold successor_spec membership_specification
  apply FirstOrder.Derives.forall_intro
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let Δ : Context signature free :=
    binary_union_spec source singleton candidate ::
      singleton_spec source singleton :: Γ
  let Θ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Δ
  have hSingleton : Θ ⊢ₘ[T]
      singleton_spec (source.weakenFree SetSort.set)
        (singleton.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Θ, Δ, FreshVariable.extendContext])
  have hUnion : Θ ⊢ₘ[T]
      binary_union_spec (source.weakenFree SetSort.set)
        (singleton.weakenFree SetSort.set)
        (candidate.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Θ, Δ, FreshVariable.extendContext])
  have hUnionAt := binary_union_spec_membership_iff
    (source.weakenFree SetSort.set)
    (singleton.weakenFree SetSort.set)
    (candidate.weakenFree SetSort.set) member hUnion
  have hCondition := FirstOrder.Derives.imp_elim
    (binary_union_singleton_condition_iff_successor_condition
      (T := T) (Γ := Θ)
      (source.weakenFree SetSort.set)
      (singleton.weakenFree SetSort.set) member)
    hSingleton
  simpa [member, Θ, Δ, FreshVariable.newest] using!
    (Metatheory.Derives.iff_trans hUnionAt hCondition)

/-- 规范见证满足现代后继规格。 -/
theorem successor_witness_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[successor_base_theory]
      successor_spec source (successor_witness_term source) := by
  let singleton : SetOpenTerm free := {source, source}ₘ
  let witness : SetOpenTerm free := source ∪ₘ singleton
  have hPair := FirstOrder.Derives.theory_weaken
    pairing_operator_theory_subset_binary_union_operator_theory
    (unordered_pair_term_spec_derives (Γ := Γ) source source)
  have hSingleton := FirstOrder.Derives.iff_elim_left
    (pair_repeated_spec_iff_singleton_spec
      (T := successor_base_theory) (Γ := Γ) source singleton)
    (by simpa [singleton] using! hPair)
  have hUnion := binary_union_term_spec_derives
    (Γ := Γ) source singleton
  have hBridge := binary_union_singleton_spec_implies_successor_spec
    (T := successor_base_theory) (Γ := Γ)
    source singleton witness
  simpa [witness, singleton] using
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hBridge hSingleton) hUnion

/-- 后继规格的规范候选参数经顶部 free 实例化后直接恢复开放规格。 -/
@[simp] theorem successor_spec_instantiateFreeTop_context
    {free : SetContext}
    (source replacement : SetOpenTerm free) :
    (successor_spec (source.weakenFree SetSort.set)
        (.fvar .here : SetOpenTerm (SetSort.set :: free))).instantiateFreeTop
          replacement =
      successor_spec source replacement := by
  unfold successor_spec membership_specification
  rw [Formula.instantiateFreeTop_forallFreeTop]
  simp [successor_member_condition, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop]

/-- 每个集合都有一个由既有配对与二元并构造出的后继。 -/
theorem successor_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[successor_base_theory] successor_exists source := by
  unfold successor_exists
  apply FirstOrder.Derives.exists_intro (successor_witness_term source)
  rw [Formula.instantiateTop_abstractFreeTop,
    successor_spec_instantiateFreeTop_context]
  exact successor_witness_spec_derives (Γ := Γ) source

/-- 同一源集合的两个现代后继候选必相等。 -/
theorem successor_unique
    {free : SetContext} {Γ : Context signature free}
    (source left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      successor_spec source left ⟶ₘ
        (successor_spec source right ⟶ₘ (left ≐ₘ right)) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    successor_member_condition element
      (source.weakenFree SetSort.set)
  simpa [successor_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) left right condition)

/-- 文献后继存在式与现代后继存在式等价。 -/
theorem successor_paper_exists_iff_exists
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      successor_paper_exists source ↔ₘ successor_exists source := by
  unfold successor_paper_exists successor_exists
  apply Metatheory.Derives.exists_iff_mono
  let candidate : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  simpa [candidate, FreshVariable.newest] using!
    (successor_paper_spec_iff_spec
      (T := T) (Γ := FreshVariable.extendContext SetSort.set Γ)
      (source.weakenFree SetSort.set) candidate)

/-- 文献写法的后继存在式同样由规范见证导出。 -/
theorem successor_paper_exists_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[successor_base_theory] successor_paper_exists source :=
  FirstOrder.Derives.iff_elim_right
    (successor_paper_exists_iff_exists
      (T := successor_base_theory) (Γ := Γ) source)
    (successor_exists_derives (Γ := Γ) source)

/-- 同一源集合的两个文献后继候选必相等。 -/
theorem successor_paper_unique
    {free : SetContext} {Γ : Context signature free}
    (source left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      successor_paper_spec source left ⟶ₘ
        (successor_paper_spec source right ⟶ₘ (left ≐ₘ right)) := by
  let element : SetOpenTerm (SetSort.set :: free) := .fvar .here
  let condition : SetOpenFormula (SetSort.set :: free) :=
    successor_paper_condition element
      (source.weakenFree SetSort.set)
  simpa [successor_paper_spec, condition, element] using
    (membership_specification_unique
      (Γ := Γ) left right condition)

/-- 后继函数符号定义公理可在任意集合项处实例化。 -/
theorem successor_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory]
      successor_definition_instance source := by
  let body : SetOpenFormula [SetSort.set] :=
    successor_definition_instance
      (.fvar .here : SetOpenTerm [SetSort.set])
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons source VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[successor_operator_theory]
        Formula.fromSentence successor_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, successor_definition_axiom,
    successor_definition_instance, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-- 后继函数项按定义等于规范见证。 -/
theorem successor_term_eq_witness_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory]
      Sₘ(source) ≐ₘ successor_witness_term source := by
  simpa [successor_definition_instance] using
    (successor_definition_instance_derives (Γ := Γ) source)

/-- 后继规格的候选单孔模板在顶部实例化后恢复开放规格。 -/
@[simp] theorem successor_spec_instantiateTop_context
    {free : SetContext}
    (source replacement : SetOpenTerm free) :
    (successor_spec
        (source.weakenBound SetSort.set)
        (.bvar .here : SetTerm [SetSort.set] free)).instantiateTop replacement =
      successor_spec source replacement := by
  unfold successor_spec
  rw [membership_specification_instantiateTop]
  rw [Term.instantiateTop_bvar_here]
  simp [successor_member_condition]

/-- 规范后继函数项满足现代后继规格。 -/
theorem successor_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory]
      successor_spec source Sₘ(source) := by
  have hWitness := FirstOrder.Derives.theory_weaken
    binary_union_operator_theory_subset_successor_operator_theory
    (successor_witness_spec_derives (Γ := Γ) source)
  have hEquality := successor_term_eq_witness_derives
    (Γ := Γ) source
  let body : SetFormula [SetSort.set] free :=
    successor_spec (source.weakenBound SetSort.set)
      (.bvar .here : SetTerm [SetSort.set] free)
  have hTransport := Metatheory.Derives.equality_iff_of_equality
    (T := successor_operator_theory) (Γ := Γ) body hEquality
  dsimp [body] at hTransport
  rw [successor_spec_instantiateTop_context,
    successor_spec_instantiateTop_context] at hTransport
  exact FirstOrder.Derives.iff_elim_right hTransport hWitness

/-- 后继规格在任意元素处的点态实例。 -/
theorem successor_spec_membership_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source candidate element : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] successor_spec source candidate) :
    Γ ⊢ₘ[T]
      (element ∈ₘ candidate) ↔ₘ
        successor_member_condition element source := by
  have hAt := FirstOrder.Derives.forall_elim element hSpec
  simpa [successor_spec, successor_member_condition,
    membership_specification] using! hAt

/-- 规范后继函数项的点态成员刻画。 -/
theorem successor_term_membership_iff
    {free : SetContext} {Γ : Context signature free}
    (source element : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory]
      (element ∈ₘ Sₘ(source)) ↔ₘ
        successor_member_condition element source :=
  successor_spec_membership_iff source Sₘ(source) element
    (successor_term_spec_derives (Γ := Γ) source)

/-- 每个集合属于自己的后继。 -/
theorem mem_successor_self
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory] source ∈ₘ Sₘ(source) :=
  FirstOrder.Derives.iff_elim_right
    (successor_term_membership_iff (Γ := Γ) source source)
    (FirstOrder.Derives.disj_intro_left
      (Metatheory.Derives.equality_refl
        (T := successor_operator_theory) (Γ := Γ) source))

/-- `source` 的每个成员也属于其后继。 -/
theorem mem_successor_of_mem
    {free : SetContext} {Γ : Context signature free}
    (source element : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory]
      (element ∈ₘ source) ⟶ₘ (element ∈ₘ Sₘ(source)) := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.iff_elim_right
    (FirstOrder.Derives.context_weaken_cons
      (assumption := element ∈ₘ source)
      (successor_term_membership_iff (Γ := Γ) source element))
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.assumption List.mem_cons_self))

/-- 候选项等于规范后继，当且仅当它满足现代后继规格。 -/
theorem successor_eq_iff_spec
    {free : SetContext} {Γ : Context signature free}
    (source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory]
      (candidate ≐ₘ Sₘ(source)) ↔ₘ successor_spec source candidate := by
  apply FirstOrder.Derives.iff_intro
  · let Δ : Context signature free :=
      (candidate ≐ₘ Sₘ(source)) :: Γ
    have hEquality : Δ ⊢ₘ[successor_operator_theory]
        candidate ≐ₘ Sₘ(source) :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hTermSpec := FirstOrder.Derives.context_weaken_cons
      (assumption := candidate ≐ₘ Sₘ(source))
      (successor_term_spec_derives (Γ := Γ) source)
    let body : SetFormula [SetSort.set] free :=
      successor_spec (source.weakenBound SetSort.set)
        (.bvar .here : SetTerm [SetSort.set] free)
    have hTransport := Metatheory.Derives.equality_iff_of_equality
      (T := successor_operator_theory) (Γ := Δ) body hEquality
    dsimp [body] at hTransport
    rw [successor_spec_instantiateTop_context,
      successor_spec_instantiateTop_context] at hTransport
    exact FirstOrder.Derives.iff_elim_right hTransport hTermSpec
  · let Δ : Context signature free := successor_spec source candidate :: Γ
    have hCandidate : Δ ⊢ₘ[successor_operator_theory]
        successor_spec source candidate :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hTermSpec := FirstOrder.Derives.context_weaken_cons
      (assumption := successor_spec source candidate)
      (successor_term_spec_derives (Γ := Γ) source)
    have hUnique := FirstOrder.Derives.theory_weaken
      extensionality_theory_subset_successor_operator_theory
      (successor_unique (Γ := Δ) source candidate Sₘ(source))
    exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hUnique hCandidate) hTermSpec

/-- 候选项等于规范后继，当且仅当它满足文献后继规格。 -/
theorem successor_eq_iff_paper_spec
    {free : SetContext} {Γ : Context signature free}
    (source candidate : SetOpenTerm free) :
    Γ ⊢ₘ[successor_operator_theory]
      (candidate ≐ₘ Sₘ(source)) ↔ₘ
        successor_paper_spec source candidate := by
  have hModern := successor_eq_iff_spec (Γ := Γ) source candidate
  have hPaperModern := successor_paper_spec_iff_spec
    (T := successor_operator_theory) (Γ := Γ) source candidate
  exact Metatheory.Derives.iff_trans hModern
    (Metatheory.Derives.iff_symm hPaperModern)

/-- 已证明的集合等式可直接提升为后继函数项等式。 -/
theorem successor_term_congr_of_equality
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] Sₘ(left) ≐ₘ Sₘ(right) := by
  let context : SetTerm [SetSort.set] free :=
    Sₘ((.bvar .here : SetTerm [SetSort.set] free))
  simpa [context] using!
    (Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ) context hEquality)

/-- 后继函数项保持任意已证明的参数等式。 -/
theorem successor_term_congr
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[T] (left ≐ₘ right) ⟶ₘ (Sₘ(left) ≐ₘ Sₘ(right)) := by
  apply FirstOrder.Derives.imp_intro
  exact successor_term_congr_of_equality left right
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 源集合等式可运输同一个候选对象的后继等式。 -/
theorem successor_eq_transport
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (left ≐ₘ right) ⟶ₘ
        ((candidate ≐ₘ Sₘ(left)) ⟶ₘ
          (candidate ≐ₘ Sₘ(right))) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  exact Metatheory.Derives.equality_trans
    (FirstOrder.Derives.assumption List.mem_cons_self)
    (successor_term_congr_of_equality left right
      (FirstOrder.Derives.assumption (by simp)))

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
