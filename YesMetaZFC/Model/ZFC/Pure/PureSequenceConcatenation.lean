import YesMetaZFC.Model.ZFC.Pure.PureFiniteSequenceCore
import YesMetaZFC.Model.ZFC.Pure.PureReplacement

/-! # 有限序列拼接的内部函数图

加法把和长度分成不相交的前段与移位后段；替换直接收集对应值。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceConcatenation
open PureModel PureNaturalInduction PureOrderSemantics PureFiniteSequenceCore
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def selector : Formula S [] [s,s,s,s] :=
  let output : Term S [] [s,s,s,s] s := .fvar .here
  let input : Term S [] [s,s,s,s] s := .fvar (.there .here)
  let left : Term S [] [s,s,s,s] s := .fvar (.there (.there .here))
  let right : Term S [] [s,s,s,s] s := .fvar (.there (.there (.there .here)))
  let index : Term S [] [s,s,s,s,s] s := .fvar .here
  .disj (.conj (Nonlogical.BasicSetTheory.membership_formula input (Nonlogical.BasicSetTheory.domain_term left))
    (.equal output (Nonlogical.BasicSetTheory.function_application_term left input)))
    ((Formula.conj (Nonlogical.BasicSetTheory.membership_formula index (Nonlogical.BasicSetTheory.domain_term (right.weakenFree s)))
      (.conj (.equal (input.weakenFree s) (Nonlogical.BasicSetTheory.natural_addition_term (Nonlogical.BasicSetTheory.domain_term (left.weakenFree s)) index))
        (.equal (output.weakenFree s) (Nonlogical.BasicSetTheory.function_application_term (right.weakenFree s) index)))).existsFreeTop s)

def Choice (hℳ : Theory.Models ℳ theory) (left right input output : Carrier ℳ) : Prop :=
  (membership ℳ input (domain hℳ left) ∧ output = value hℳ left input) ∨
    ∃ index, membership ℳ index (domain hℳ right) ∧ input = add hℳ (domain hℳ left) index ∧ output = value hℳ right index

def selectorPure : Formula ℒ [] [setSort,setSort,setSort,setSort] := openFormula PureNaturalDifferenceStage.interpretation selector

theorem selector_correct (hℳ : Theory.Models ℳ theory) (left right input output : Carrier ℳ) :
    selectorPure.satisfies (templateEnv (.cons output (.cons input (.cons left (.cons right .nil))))) ↔ Choice hℳ left right input output := by
  apply (openFormula_correct (E hℳ) (PureNaturalDifferenceStage.realizes hℳ) selector (.cons output (.cons input (.cons left (.cons right .nil))))).trans
  simp only [selector,Formula.satisfies_existsFreeTop,Formula.satisfies,
    Nonlogical.BasicSetTheory.membership_formula,Nonlogical.BasicSetTheory.domain_term,
    Nonlogical.BasicSetTheory.natural_addition_term,Nonlogical.BasicSetTheory.function_application_term,
    Term.eval,Arguments.eval,Term.eval_weakenFree,Expansion.model]
  change (membership ℳ input (domain hℳ left) ∧ output = (E hℳ).function .application (.cons left (.cons input .nil))) ∨
    (∃ index, membership ℳ index (domain hℳ right) ∧ input = add hℳ (domain hℳ left) index ∧
      output = (E hℳ).function .application (.cons right (.cons index .nil))) ↔ _
  simp only [value_eq hℳ]
  rfl

theorem choice_unique (hℳ : Theory.Models ℳ theory) {left right input first second : Carrier ℳ}
    (hLeft : Finite hℳ left) (hRight : Finite hℳ right)
    (hFirst : Choice hℳ left right input first) (hSecond : Choice hℳ left right input second) : first = second := by
  rcases hFirst with ⟨hInput,hFirst⟩ | ⟨i,hi,hInput,hFirst⟩
  · rcases hSecond with ⟨_,hSecond⟩ | ⟨j,hj,hIndex,hSecond⟩
    · exact hFirst.trans hSecond.symm
    · exact False.elim (add_not_mem_left hℳ hLeft.2 ((omega_project hℳ).transitive (project_modelsZF hℳ) _ hRight.2 j hj) (hIndex ▸ hInput))
  · rcases hSecond with ⟨hIndex,hSecond⟩ | ⟨j,hj,hIndex,hSecond⟩
    · exact False.elim (add_not_mem_left hℳ hLeft.2 ((omega_project hℳ).transitive (project_modelsZF hℳ) _ hRight.2 i hi) (hInput ▸ hIndex))
    · have hEqual := add_injective hℳ hLeft.2
        ((omega_project hℳ).transitive (project_modelsZF hℳ) _ hRight.2 i hi)
        ((omega_project hℳ).transitive (project_modelsZF hℳ) _ hRight.2 j hj) (hInput.symm.trans hIndex)
      exact hFirst.trans ((congrArg (value hℳ right) hEqual).trans hSecond.symm)

def Concats (hℳ : Theory.Models ℳ theory) (left right output : Carrier ℳ) : Prop :=
  Finite hℳ output ∧ domain hℳ output = add hℳ (domain hℳ left) (domain hℳ right) ∧
    (∀ input, membership ℳ input (domain hℳ left) → value hℳ output input = value hℳ left input) ∧
      ∀ input, membership ℳ input (domain hℳ right) → value hℳ output (add hℳ (domain hℳ left) input) = value hℳ right input

theorem exists_concatenation (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : Finite hℳ left) (hRight : Finite hℳ right) : ∃ output, Concats hℳ left right output := by
  let length := add hℳ (domain hℳ left) (domain hℳ right)
  let target := (E hℳ).function .binaryUnion (.cons (range hℳ left) (.cons (range hℳ right) .nil))
  have hTarget := (PureRelationSetOperations.binaryUnion_correct hℳ target (range hℳ left) (range hℳ right)).mp
    (((PureNaturalDifferenceStage.realizes hℳ).function .binaryUnion (.cons (range hℳ left) (.cons (range hℳ right) .nil)) target).mpr rfl)
  obtain ⟨output,hMap,hValues⟩ := PureReplacement.mapping_exists hℳ selectorPure (.cons left (.cons right .nil)) length target
    (fun input hInput => by
      rcases (add_parts hℳ hLeft.2 hRight.2 input).mp hInput with hFirst | ⟨index,hIndex,hEqual⟩
      · exact ⟨value hℳ left input,(selector_correct hℳ left right input _).mpr (Or.inl ⟨hFirst,rfl⟩)⟩
      · exact ⟨value hℳ right index,(selector_correct hℳ left right input _).mpr (Or.inr ⟨index,hIndex,hEqual,rfl⟩)⟩)
    (fun input _ first second hFirst hSecond => choice_unique hℳ hLeft hRight
      ((selector_correct hℳ left right input first).mp hFirst) ((selector_correct hℳ left right input second).mp hSecond))
    (fun input _ output hOutput => by
      rcases (selector_correct hℳ left right input output).mp hOutput with ⟨hInput,rfl⟩ | ⟨index,hIndex,_,rfl⟩
      · exact (hTarget _).mpr (Or.inl (value_mem hℳ (mapping_self hℳ hLeft.1) hInput))
      · exact (hTarget _).mpr (Or.inr (value_mem hℳ (mapping_self hℳ hRight.1) hIndex)))
  have hDomain := mapping_domain hℳ hMap
  refine ⟨output,⟨hMap.1,hDomain.symm ▸ add_mem hℳ hLeft.2 hRight.2⟩,hDomain,?_,?_⟩
  · intro input hInput
    have hInLength := (add_parts hℳ hLeft.2 hRight.2 input).mpr (Or.inl hInput)
    have hPair := (hValues input (value hℳ left input)).mpr ⟨hInLength,(selector_correct hℳ left right input _).mpr (Or.inl ⟨hInput,rfl⟩)⟩
    exact (hMap.1.2 input _ _ hPair (application_member hℳ hMap hInLength)).symm
  · intro index hIndex
    have hInLength := (add_parts hℳ hLeft.2 hRight.2 _).mpr (Or.inr ⟨index,hIndex,rfl⟩)
    have hPair := (hValues _ (value hℳ right index)).mpr ⟨hInLength,(selector_correct hℳ left right _ _).mpr (Or.inr ⟨index,hIndex,rfl,rfl⟩)⟩
    exact (hMap.1.2 _ _ _ hPair (application_member hℳ hMap hInLength)).symm

theorem unique (hℳ : Theory.Models ℳ theory) {left right first second : Carrier ℳ}
    (hLeft : Finite hℳ left) (hRight : Finite hℳ right)
    (hFirst : Concats hℳ left right first) (hSecond : Concats hℳ left right second) : first = second := by
  apply function_ext hℳ hFirst.1.1 hSecond.1.1 (hFirst.2.1.trans hSecond.2.1.symm)
  intro input hInput
  have hInLength := hFirst.2.1 ▸ hInput
  rcases (add_parts hℳ hLeft.2 hRight.2 input).mp hInLength with hFirstPart | ⟨index,hIndex,rfl⟩
  · exact (hFirst.2.2.1 input hFirstPart).trans (hSecond.2.2.1 input hFirstPart).symm
  · exact (hFirst.2.2.2 index hIndex).trans (hSecond.2.2.2 index hIndex).symm

def guard : Formula S [] [s,s,s] := .conj (FormalSystem.finite_sequence_condition (.fvar (.there .here)))
  (FormalSystem.finite_sequence_condition (.fvar (.there (.there .here))))
def specification : Formula S [] [s,s,s] := FormalSystem.finite_sequence_concatenation_spec
  (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
def body : Formula ℒ [] [setSort,setSort,setSort] := openFormula PureNaturalDifferenceStage.interpretation (.conj guard specification)
def graph : Formula ℒ [] [setSort,setSort,setSort] := _root_.YesMetaZFC.Automation.TotalizedGraph.formula body PureRelationFunctions.emptyFallback

theorem specification_correct (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : Finite hℳ left) (hRight : Finite hℳ right) (output : Carrier ℳ) :
    specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (E hℳ).model [] [s,s,s]) ↔ Concats hℳ left right output := by
  simp only [specification,FormalSystem.finite_sequence_concatenation_spec,
    FormalSystem.finite_sequence_concatenation_left_condition,FormalSystem.finite_sequence_concatenation_right_condition,
    Formula.satisfies_forallFreeTop,Formula.satisfies,finite_correct hℳ]
  change (Finite hℳ output ∧ domain hℳ output = add hℳ (domain hℳ left) (domain hℳ right) ∧
    (∀ input, membership ℳ input (domain hℳ left) → membership ℳ input (domain hℳ output) ∧
      (E hℳ).function .application (.cons output (.cons input .nil)) = (E hℳ).function .application (.cons left (.cons input .nil))) ∧
    (∀ input, membership ℳ input (domain hℳ right) → membership ℳ (add hℳ (domain hℳ left) input) (domain hℳ output) ∧
      (E hℳ).function .application (.cons output (.cons (add hℳ (domain hℳ left) input) .nil)) = (E hℳ).function .application (.cons right (.cons input .nil)))) ↔ _
  simp only [value_eq hℳ]
  constructor
  · rintro ⟨hFinite,hDomain,hF,hS⟩
    exact ⟨hFinite,hDomain,fun input hInput => (hF input hInput).2,fun input hInput => (hS input hInput).2⟩
  · rintro ⟨hFinite,hDomain,hF,hS⟩
    refine ⟨hFinite,hDomain,?_,?_⟩
    · intro input hInput
      exact ⟨hDomain.symm ▸ (add_parts hℳ hLeft.2 hRight.2 input).mpr (Or.inl hInput),hF input hInput⟩
    · intro input hInput
      exact ⟨hDomain.symm ▸ (add_parts hℳ hLeft.2 hRight.2 _).mpr (Or.inr ⟨input,hInput,rfl⟩),hS input hInput⟩

theorem body_correct (hℳ : Theory.Models ℳ theory) (left right output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      (Finite hℳ left ∧ Finite hℳ right) ∧ Concats hℳ left right output := by
  apply (openFormula_correct (E hℳ) (PureNaturalDifferenceStage.realizes hℳ) (.conj guard specification) (.cons output (.cons left (.cons right .nil)))).trans
  have hGuard : guard.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (E hℳ).model [] [s,s,s]) ↔ Finite hℳ left ∧ Finite hℳ right :=
    and_congr (finite_correct hℳ _ _) (finite_correct hℳ _ _)
  constructor
  · rintro ⟨hGuardSource,hSpec⟩
    have hG := hGuard.mp hGuardSource
    exact ⟨hG,(specification_correct hℳ hG.1 hG.2 output).mp hSpec⟩
  · rintro ⟨hG,hSpec⟩
    exact ⟨hGuard.mpr hG,(specification_correct hℳ hG.1 hG.2 output).mpr hSpec⟩

theorem exists_body (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ} (hLeft : Finite hℳ left) (hRight : Finite hℳ right) :
    ∃ output, body.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) := by
  obtain ⟨output,hOutput⟩ := exists_concatenation hℳ hLeft hRight
  exact ⟨output,(body_correct hℳ left right output).mpr ⟨⟨hLeft,hRight⟩,hOutput⟩⟩

theorem functional (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons left (.cons right .nil)))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ body (.cons left (.cons right .nil))
  intro first second hFirst hSecond
  have hF := (body_correct hℳ left right first).mp hFirst
  have hS := (body_correct hℳ left right second).mp hSecond
  exact unique hℳ hF.1.1 hF.1.2 hF.2 hS.2

theorem agrees (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ} (hLeft : Finite hℳ left) (hRight : Finite hℳ right) (output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (E hℳ).model [] [s,s,s]) :=
  (PureRelationFunctions.totalized_agrees body (.cons left (.cons right .nil)) (exists_body hℳ hLeft hRight) output).trans
    ((body_correct hℳ left right output).trans (Iff.trans ⟨And.right,fun h => ⟨⟨hLeft,hRight⟩,h⟩⟩ (specification_correct hℳ hLeft hRight output).symm))

theorem dependencies_covered : formulaCovered PureNaturalDifferenceStage.functionCovered PureNaturalDifferenceStage.relationCovered (.conj guard specification) = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSequenceConcatenation
