import YesMetaZFC.Model.ZFC.Pure.PureRoundOneRelations

/-! # 阶段扩张中的归纳集语义

原谓词中的空集常元和后继函数与 Project 的见证式归纳性逐对象对应。
这把本轮关系定义接到 ω、归纳核以及下一轮的自然数构造。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageSemantics
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion PureRoundOneRelations.interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (PureRoundOneRelations.functional hℳ)

theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) :=
  expansion_realizes (PureRoundOneRelations.functional hℳ)

theorem membership_correct (hℳ : Theory.Models ℳ theory) (element set : Carrier ℳ) :
    (expansion hℳ).relation .membership (.cons element (.cons set .nil)) ↔ membership ℳ element set := by
  rfl

theorem empty_spec (hℳ : Theory.Models ℳ theory) :
    ∀ element, ¬ membership ℳ element ((expansion hℳ).function .emptySet .nil) :=
  (PureFunctionDefinitions.empty_correct _).mp ((realizes hℳ).function .emptySet .nil _ |>.mpr rfl)

theorem successor_spec (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    ∀ element, membership ℳ element ((expansion hℳ).function .successor (.cons input .nil)) ↔
      membership ℳ element input ∨ element = input :=
  (PureFunctionDefinitions.successor_correct _ input).mp
    ((realizes hℳ).function .successor (.cons input .nil) _ |>.mpr rfl)

theorem same_members_iff (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :
    (Project.FirstOrderSemantics.reduct ℳ).SameMembers left right ↔ left = right :=
  ⟨(project_models hℳ).1.eq_of_same_members left right, fun h => h ▸ (fun _ => Iff.rfl)⟩

theorem successor_project (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    (Project.FirstOrderSemantics.reduct ℳ).SuccessorOf
      ((expansion hℳ).function .successor (.cons input .nil)) input :=
  fun element => (successor_spec hℳ input element).trans
    (or_congr Iff.rfl (same_members_iff hℳ element input).symm)

/-- 原定义公式中的归纳性与见证式集合论归纳性完全一致。 -/
theorem inductive_condition_correct (hℳ : Theory.Models ℳ theory) (set : Carrier ℳ) :
    (PureRoundOneRelations.condition .isInductiveSet).satisfies
        (templateEnv (.cons set .nil) : Env (expansion hℳ).model [] [Nonlogical.BasicSetTheory.SetSort.set]) ↔
      membership ℳ ((expansion hℳ).function .emptySet .nil) set ∧
        ∀ input, membership ℳ input set → membership ℳ ((expansion hℳ).function .successor (.cons input .nil)) set := by
  simp only [PureRoundOneRelations.condition, Nonlogical.BasicSetTheory.is_inductive_set_condition,
    Nonlogical.BasicSetTheory.infinity_condition, Formula.satisfies_forallFreeTop,
    Formula.satisfies]
  rfl

theorem inductive_correct (hℳ : Theory.Models ℳ theory) (set : Carrier ℳ) :
    (PureRoundOneRelations.graph .isInductiveSet).satisfies (templateEnv (.cons set .nil)) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsInductive set := by
  have hDefinition := PureRoundOneRelations.definition_correct hℳ .isInductiveSet (.cons set .nil)
  change (expansion hℳ).relation .isInductiveSet (.cons set .nil) ↔ _
  apply hDefinition.trans
  apply (inductive_condition_correct hℳ set).trans
  constructor
  · rintro ⟨hEmpty, hSuccessors⟩
    exact ⟨⟨(expansion hℳ).function .emptySet .nil, empty_spec hℳ, hEmpty⟩,
      fun input hInput => ⟨(expansion hℳ).function .successor (.cons input .nil),
        successor_project hℳ input, hSuccessors input hInput⟩⟩
  · rintro ⟨⟨empty, hEmpty, hEmptySet⟩, hSuccessors⟩
    have hEmptyEq : empty = (expansion hℳ).function .emptySet .nil :=
      extensionality hℳ _ _ (fun element => iff_of_false (hEmpty element) (empty_spec hℳ element))
    refine ⟨hEmptyEq ▸ hEmptySet, ?_⟩
    intro input hInput
    obtain ⟨successor, hSuccessor, hSuccessorSet⟩ := hSuccessors input hInput
    have hEq : successor = (expansion hℳ).function .successor (.cons input .nil) :=
      extensionality hℳ _ _ (fun element => ((hSuccessor element).trans (or_congr Iff.rfl (same_members_iff hℳ element input))).trans
        (successor_spec hℳ input element).symm)
    exact hEq ▸ hSuccessorSet

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageSemantics
