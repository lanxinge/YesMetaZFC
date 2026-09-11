import YesMetaZFC.Model.ZFC.Pure.PureFiniteUniverseStage

/-! # 截断自然减法的内部存在性

有限序数取并集就是截断前驱。将内部 ω 并集迭代限制到右参数的后继，
得到原减法规格要求的有限映射；唯一性由内部有限递推外延性给出。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalDifference
open PureModel PureNaturalInduction PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

def Step (hℳ : Theory.Models ℳ theory) (current next : Carrier ℳ) : Prop :=
  (current = zero hℳ ∧ next = zero hℳ) ∨ ∃ previous, current = succ hℳ previous ∧ next = previous

theorem union_zero (hℳ : Theory.Models ℳ theory) : PureSetIterations.Union (zero hℳ) (zero hℳ) := by
  intro element
  exact iff_of_false (zero_spec hℳ element) (fun ⟨member,hMember,_⟩ => zero_spec hℳ member hMember)

theorem union_successor (hℳ : Theory.Models ℳ theory) {previous : Carrier ℳ}
    (hPrevious : membership ℳ previous (omega hℳ)) : PureSetIterations.Union (succ hℳ previous) previous := by
  have hOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) previous hPrevious
  intro element
  constructor
  · intro hElement
    exact ⟨previous,(succ_spec hℳ previous previous).mpr (Or.inr rfl),hElement⟩
  · rintro ⟨member,hMember,hElement⟩
    rcases (succ_spec hℳ previous member).mp hMember with hLess | rfl
    · exact hOrdinal.transitive member hLess element hElement
    · exact hElement

theorem step_exists (hℳ : Theory.Models ℳ theory) {current : Carrier ℳ}
    (hCurrent : membership ℳ current (omega hℳ)) :
    ∃ next, membership ℳ next (omega hℳ) ∧ Step hℳ current next ∧ PureSetIterations.Union current next := by
  classical
  by_cases hZero : current = zero hℳ
  · subst current
    exact ⟨zero hℳ,zero_mem hℳ,Or.inl ⟨rfl,rfl⟩,union_zero hℳ⟩
  · have hNonempty : ∃ member, membership ℳ member current := by
      by_cases h : ∃ member, membership ℳ member current
      · exact h
      · exact False.elim (hZero (extensionality hℳ current (zero hℳ)
          (fun member => iff_of_false (fun hMember => h ⟨member,hMember⟩) (zero_spec hℳ member))))
    obtain ⟨previous,hPrevious,hSuccessor⟩ := (omega_project hℳ).exists_predecessor_of_mem_of_nonempty (project_modelsZF hℳ) hCurrent hNonempty
    have hEqual := _root_.YesMetaZFC.SetTheory.Structure.SuccessorOf.eq (project_models hℳ).1 hSuccessor (succ_project hℳ previous)
    exact ⟨previous,hPrevious,Or.inr ⟨previous,hEqual,rfl⟩,hEqual.symm ▸ union_successor hℳ hPrevious⟩

theorem step_union (hℳ : Theory.Models ℳ theory) {current next : Carrier ℳ}
    (hCurrent : membership ℳ current (omega hℳ)) (hStep : Step hℳ current next) : PureSetIterations.Union current next := by
  rcases hStep with ⟨hCurrentZero,hNextZero⟩ | ⟨previous,hSuccessor,hNext⟩
  · rw [hCurrentZero,hNextZero]
    exact union_zero hℳ
  · rw [hSuccessor] at hCurrent
    rw [hSuccessor,hNext]
    exact union_successor hℳ ((omega_project hℳ).transitive (project_modelsZF hℳ) _ hCurrent previous
      ((succ_spec hℳ previous previous).mpr (Or.inr rfl)))

theorem union_step (hℳ : Theory.Models ℳ theory) {current next : Carrier ℳ}
    (hCurrent : membership ℳ current (omega hℳ)) (hUnion : PureSetIterations.Union current next) :
    membership ℳ next (omega hℳ) ∧ Step hℳ current next := by
  obtain ⟨previous,hPrevious,hStep,hPreviousUnion⟩ := step_exists hℳ hCurrent
  have hEqual := extensionality hℳ next previous (fun element => (hUnion element).trans (hPreviousUnion element).symm)
  exact hEqual.symm ▸ ⟨hPrevious,hStep⟩

def naturalValues : Formula S [] [s,s] :=
  Nonlogical.BasicSetTheory.membership_formula
    (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there .here)) (.fvar .here)) Nonlogical.BasicSetTheory.omega_term

theorem iteration_natural (hℳ : Theory.Models ℳ theory) {sequence initial : Carrier ℳ}
    (hIteration : PureOmegaIteration.Iterates hℳ PureSetIterations.Union sequence initial)
    (hInitial : membership ℳ initial (omega hℳ)) :
    ∀ index, membership ℳ index (omega hℳ) → membership ℳ (value hℳ sequence index) (omega hℳ) := by
  apply source_induction hℳ naturalValues (.cons sequence .nil)
  · change membership ℳ (value hℳ sequence (zero hℳ)) (omega hℳ)
    rw [hIteration.2.2.1]
    exact hInitial
  · intro index hIndex hPrevious
    exact (union_step hℳ hPrevious (hIteration.2.2.2 index hIndex)).1

def Iteration (hℳ : Theory.Models ℳ theory) (left right sequence output : Carrier ℳ) : Prop :=
  PureMappingDefinitions.IsMapping ℳ sequence (succ hℳ right) (omega hℳ) ∧
    value hℳ sequence (zero hℳ) = left ∧
      (∀ index, membership ℳ index right → Step hℳ (value hℳ sequence index) (value hℳ sequence (succ hℳ index))) ∧
        value hℳ sequence right = output

theorem iteration_exists (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    ∃ output sequence, membership ℳ output (omega hℳ) ∧ Iteration hℳ left right sequence output := by
  obtain ⟨whole,hWhole,_⟩ := PureOmegaIteration.functional hℳ PureSetIterations.union_rep (PureSetIterations.union_total hℳ) left
  have hIteration := PureOmegaIteration.iterates_of_graph hℳ PureSetIterations.union_rep (PureSetIterations.union_total hℳ) hWhole
  have hNatural := iteration_natural hℳ hIteration hLeft
  have hWholeMap : PureMappingDefinitions.IsMapping ℳ whole (omega hℳ) (omega hℳ) := by
    refine ⟨hIteration.1,hIteration.2.1,?_⟩
    intro input hInput
    have hValue := (PureRelationFunctions.application_spec hIteration.1 ((hIteration.2.1 input).mp hInput) _).mp
      (((PureDifferenceStage.realizes hℳ).function .application (.cons whole (.cons input .nil)) _).mpr rfl)
    exact ⟨value hℳ whole input,hNatural input hInput,hValue⟩
  obtain ⟨sequence,hSequence⟩ := PureMappingOperations.exists_output hℳ .restriction (.cons whole (.cons (succ hℳ right) .nil))
  have hRestriction := PureMappingOperations.restriction_project hℳ sequence whole (succ hℳ right) hSequence
  have hMap : PureMappingDefinitions.IsMapping ℳ sequence (succ hℳ right) (omega hℳ) := by
    exact PureMappingOperations.restriction_mapping hℳ sequence whole (omega hℳ) (omega hℳ) (succ hℳ right)
      hSequence hWholeMap (fun input hInput => input_mem_omega hℳ hRight hInput)
  have hValues {input : Carrier ℳ} (hInput : membership ℳ input (succ hℳ right)) :
      value hℳ sequence input = value hℳ whole input := by
    have hPair := application_member hℳ hMap hInput
    have hWholePair := (hRestriction.2 input _).mp hPair |>.2
    exact hIteration.1.2 input _ _ hWholePair (application_member hℳ hWholeMap (input_mem_omega hℳ hRight hInput))
  refine ⟨value hℳ whole right,sequence,hNatural right hRight,hMap,?_,?_,hValues ((succ_spec hℳ right right).mpr (Or.inr rfl))⟩
  · exact (hValues (zero_mem_successor hℳ hRight)).trans hIteration.2.2.1
  · intro index hIndex
    have hIndexSucc := (succ_spec hℳ right index).mpr (Or.inl hIndex)
    rw [hValues hIndexSucc,hValues (successor_mem_successor hℳ hRight hIndex)]
    exact (union_step hℳ (hNatural index (input_mem_omega hℳ hRight hIndexSucc))
      (hIteration.2.2.2 index (input_mem_omega hℳ hRight hIndexSucc))).2

theorem iteration_unique (hℳ : Theory.Models ℳ theory) {left right first second outFirst outSecond : Carrier ℳ}
    (hRight : membership ℳ right (omega hℳ)) (hFirst : Iteration hℳ left right first outFirst)
    (hSecond : Iteration hℳ left right second outSecond) : outFirst = outSecond := by
  have hEqual := finite_recurrence_ext hℳ hRight hFirst.1 hSecond.1 (hFirst.2.1.trans hSecond.2.1.symm) (fun index hIndex hCurrent => by
    have hInput := (succ_spec hℳ right index).mpr (Or.inl hIndex)
    obtain ⟨vF,hVF,hPF⟩ := hFirst.1.2.2 index hInput
    obtain ⟨vS,hVS,hPS⟩ := hSecond.1.2.2 index hInput
    have hNaturalFirst := (hFirst.1.1.2 index vF _ hPF (application_member hℳ hFirst.1 hInput)) ▸ hVF
    have hNaturalSecond := (hSecond.1.1.2 index vS _ hPS (application_member hℳ hSecond.1 hInput)) ▸ hVS
    have hUF := step_union hℳ hNaturalFirst (hFirst.2.2.1 index hIndex)
    have hUS := step_union hℳ hNaturalSecond (hSecond.2.2.1 index hIndex)
    rw [hCurrent] at hUF
    exact extensionality hℳ _ _ (fun element => (hUF element).trans (hUS element).symm))
  exact hFirst.2.2.2.symm.trans (hEqual ▸ hSecond.2.2.2)

def specification : Formula S [] [s,s,s] := Nonlogical.BasicSetTheory.natural_difference_spec
  (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

theorem specification_correct (hℳ : Theory.Models ℳ theory) (left right output : Carrier ℳ) :
    specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (PureArithmeticStage.expansion hℳ).model [] [s,s,s]) ↔
      membership ℳ output (omega hℳ) ∧ ∃ sequence, Iteration hℳ left right sequence output := by
  simp only [specification,Nonlogical.BasicSetTheory.natural_difference_spec,
    Nonlogical.BasicSetTheory.natural_difference_graph_condition,Nonlogical.BasicSetTheory.natural_difference_step_condition,
    Formula.satisfies_existsFreeTop,Formula.satisfies_forallFreeTop,Formula.satisfies,
    Nonlogical.BasicSetTheory.membership_formula,Nonlogical.BasicSetTheory.is_mapping_formula,
    Nonlogical.BasicSetTheory.function_application_term,Nonlogical.BasicSetTheory.successor_term,
    Nonlogical.BasicSetTheory.empty_set_term,Nonlogical.BasicSetTheory.omega_term,
    Term.eval,Arguments.eval,Term.eval_weakenFree,Expansion.model,
    PureArithmeticStage.omega_eq hℳ,PureArithmeticStage.zero_eq hℳ,PureArithmeticStage.succ_eq hℳ,
    PureArithmeticStage.value_eq hℳ,PureArithmeticStage.membership_correct hℳ,PureArithmeticStage.mapping_correct hℳ]
  rfl

def body : Formula ℒ [] [setSort,setSort,setSort] :=
  .conj PureOrdinalArithmetic.naturalGuard (openFormula PureArithmeticStage.interpretation specification)
def graph : Formula ℒ [] [setSort,setSort,setSort] :=
  _root_.YesMetaZFC.Automation.TotalizedGraph.formula body PureRelationFunctions.emptyFallback

theorem body_correct (hℳ : Theory.Models ℳ theory) (left right output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      (membership ℳ left (omega hℳ) ∧ membership ℳ right (omega hℳ)) ∧
        membership ℳ output (omega hℳ) ∧ ∃ sequence, Iteration hℳ left right sequence output :=
  and_congr (PureOrdinalArithmetic.guard_correct hℳ output left right)
    ((openFormula_correct (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ) specification
      (.cons output (.cons left (.cons right .nil)))).trans (specification_correct hℳ left right output))

theorem exists_body (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    ∃ output, body.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) := by
  obtain ⟨output,sequence,hOutput,hSequence⟩ := iteration_exists hℳ hLeft hRight
  exact ⟨output,(body_correct hℳ left right output).mpr ⟨⟨hLeft,hRight⟩,hOutput,sequence,hSequence⟩⟩

theorem functional (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons left (.cons right .nil)))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ body (.cons left (.cons right .nil))
  intro first second hFirst hSecond
  obtain ⟨⟨_,hRight⟩,_,firstSequence,hF⟩ := (body_correct hℳ left right first).mp hFirst
  obtain ⟨_,_,secondSequence,hS⟩ := (body_correct hℳ left right second).mp hSecond
  exact iteration_unique hℳ hRight hF hS

theorem agrees (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (PureArithmeticStage.expansion hℳ).model [] [s,s,s]) := by
  apply (PureRelationFunctions.totalized_agrees body (.cons left (.cons right .nil)) (exists_body hℳ hLeft hRight) output).trans
  exact (body_correct hℳ left right output).trans
    (Iff.trans ⟨And.right,fun h => ⟨⟨hLeft,hRight⟩,h⟩⟩ (specification_correct hℳ left right output).symm)

theorem dependencies_covered : formulaCovered PureArithmeticStage.functionCovered
    PureNaturalRelations.relationCovered specification = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalDifference
