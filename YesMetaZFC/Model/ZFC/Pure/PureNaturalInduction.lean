import YesMetaZFC.Model.ZFC.Pure.PureDifferenceStage

/-! # 当前扩张中的内部自然数归纳与递推唯一性

归纳性质始终由实际纯公式给出；分离构造性质集后消费模型内部的最小归纳集。
不假定模型的自然数在外部标准，也不对任意外部谓词声称归纳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalInduction
open PureModel
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable abbrev omega (hℳ : Theory.Models ℳ theory) : Carrier ℳ :=
  (PureDifferenceStage.expansion hℳ).function .omega .nil
noncomputable abbrev zero (hℳ : Theory.Models ℳ theory) : Carrier ℳ :=
  (PureDifferenceStage.expansion hℳ).function .emptySet .nil
noncomputable abbrev succ (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) : Carrier ℳ :=
  (PureDifferenceStage.expansion hℳ).function .successor (.cons input .nil)
noncomputable abbrev value (hℳ : Theory.Models ℳ theory) (function input : Carrier ℳ) : Carrier ℳ :=
  (PureDifferenceStage.expansion hℳ).function .application (.cons function (.cons input .nil))

theorem omega_project (hℳ : Theory.Models ℳ theory) :
    (Project.FirstOrderSemantics.reduct ℳ).IsOmega (omega hℳ) :=
  (PureOmegaAndReverse.omega_correct hℳ _).mp
    (((PureDifferenceStage.realizes hℳ).function .omega .nil _).mpr rfl)

theorem zero_spec (hℳ : Theory.Models ℳ theory) : ∀ element, ¬ membership ℳ element (zero hℳ) :=
  (PureFunctionDefinitions.empty_correct _).mp
    (((PureDifferenceStage.realizes hℳ).function .emptySet .nil _).mpr rfl)

theorem succ_spec (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    ∀ element, membership ℳ element (succ hℳ input) ↔ membership ℳ element input ∨ element = input :=
  (PureFunctionDefinitions.successor_correct _ input).mp
    (((PureDifferenceStage.realizes hℳ).function .successor (.cons input .nil) _).mpr rfl)

theorem succ_project (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    (Project.FirstOrderSemantics.reduct ℳ).SuccessorOf (succ hℳ input) input :=
  fun element => (succ_spec hℳ input element).trans
    (or_congr Iff.rfl (PureStageSemantics.same_members_iff hℳ element input).symm)

/-- 当前核的任意纯公式都可用于模型内部的自然数归纳。 -/
theorem pure_induction (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: parameters))
    (args : Values ℳ.Carrier parameters)
    (hZero : body.satisfies (templateEnv (.cons (zero hℳ) args)))
    (hStep : ∀ input, membership ℳ input (omega hℳ) →
      body.satisfies (templateEnv (.cons input args)) →
        body.satisfies (templateEnv (.cons (succ hℳ input) args))) :
    ∀ input, membership ℳ input (omega hℳ) → body.satisfies (templateEnv (.cons input args)) := by
  apply (omega_project hℳ).induction (fun input => body.satisfies (templateEnv (.cons input args)))
  · exact PureSeparation.exists_subset hℳ body args (omega hℳ)
  · intro empty hEmpty
    have hEqual : empty = zero hℳ := extensionality hℳ empty (zero hℳ)
      (fun element => ⟨fun h => False.elim (hEmpty element h), fun h => False.elim (zero_spec hℳ element h)⟩)
    exact hEqual.symm ▸ hZero
  · intro input hInput hProperty successor hSuccessor
    have hEqual := _root_.YesMetaZFC.SetTheory.Structure.SuccessorOf.eq
      (project_models hℳ).1 hSuccessor (succ_project hℳ input)
    exact hEqual.symm ▸ hStep input hInput hProperty

/-- 源公式经当前纯翻译后也获得同一内部归纳接口。 -/
theorem source_induction (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext S} (body : Formula S [] (s :: parameters))
    (args : Values (PureDifferenceStage.expansion hℳ).model.Carrier parameters)
    (hZero : body.satisfies (templateEnv (.cons (zero hℳ) args) : Env (PureDifferenceStage.expansion hℳ).model [] (s :: parameters)))
    (hStep : ∀ input, membership ℳ input (omega hℳ) →
      body.satisfies (templateEnv (.cons input args) : Env (PureDifferenceStage.expansion hℳ).model [] (s :: parameters)) →
        body.satisfies (templateEnv (.cons (succ hℳ input) args) : Env (PureDifferenceStage.expansion hℳ).model [] (s :: parameters))) :
    ∀ input, membership ℳ input (omega hℳ) → body.satisfies (templateEnv (.cons input args) : Env (PureDifferenceStage.expansion hℳ).model [] (s :: parameters)) := by
  have hCorrect (input : Carrier ℳ) := openFormula_correct
    (PureDifferenceStage.expansion hℳ) (PureDifferenceStage.realizes hℳ) body (.cons input args)
  have hInduction := pure_induction hℳ (openFormula PureDifferenceStage.interpretation body)
    (mapValues PureDifferenceStage.interpretation args) ((hCorrect _).mpr hZero)
    (fun input hInput hProperty => (hCorrect _).mpr (hStep input hInput ((hCorrect _).mp hProperty)))
  exact fun input hInput => (hCorrect input).mp (hInduction input hInput)

theorem application_member (hℳ : Theory.Models ℳ theory)
    {function source target input : Carrier ℳ}
    (hMapping : PureMappingDefinitions.IsMapping ℳ function source target)
    (hInput : membership ℳ input source) :
    PureKuratowski.PairMember ℳ input (value hℳ function input) function :=
  (PureRelationFunctions.application_spec hMapping.1 ((hMapping.2.1 input).mp hInput) _).mp
    (((PureDifferenceStage.realizes hℳ).function .application (.cons function (.cons input .nil)) _).mpr rfl)

def equalValues : Formula S [] [s,s,s] :=
  .equal (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there .here)) (.fvar .here))
    (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there (.there .here))) (.fvar .here))

/-- ω 上两个递推函数具有相同初值且保持相等时，整个函数图相等。 -/
theorem omega_recurrence_ext (hℳ : Theory.Models ℳ theory)
    {first second target : Carrier ℳ}
    (hFirst : PureMappingDefinitions.IsMapping ℳ first (omega hℳ) target)
    (hSecond : PureMappingDefinitions.IsMapping ℳ second (omega hℳ) target)
    (hZero : value hℳ first (zero hℳ) = value hℳ second (zero hℳ))
    (hStep : ∀ input, membership ℳ input (omega hℳ) →
      value hℳ first input = value hℳ second input →
        value hℳ first (succ hℳ input) = value hℳ second (succ hℳ input)) : first = second := by
  have hValues : ∀ input, membership ℳ input (omega hℳ) → value hℳ first input = value hℳ second input :=
    source_induction hℳ equalValues (.cons first (.cons second .nil)) hZero hStep
  exact PureMappingSpecifications.mapping_ext hℳ hFirst hSecond (fun input hInput =>
    ⟨_, application_member hℳ hFirst hInput, (hValues input hInput).symm ▸ application_member hℳ hSecond hInput⟩)

def equalValuesWithin : Formula S [] [s,s,s,s] :=
  .imp (Nonlogical.BasicSetTheory.membership_formula (.fvar .here) (.fvar (.there (.there (.there .here)))))
    (.equal (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there .here)) (.fvar .here))
      (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there (.there .here))) (.fvar .here)))

/-- 后继落在自然数的后继内，则其前驱已落在该自然数内。 -/
theorem predecessor_mem (hℳ : Theory.Models ℳ theory)
    {length input : Carrier ℳ} (hLength : membership ℳ length (omega hℳ))
    (hInput : membership ℳ (succ hℳ input) (succ hℳ length)) : membership ℳ input length := by
  have hSelf := (succ_spec hℳ input input).mpr (Or.inr rfl)
  rcases (succ_spec hℳ length (succ hℳ input)).mp hInput with hLess | hEqual
  · exact ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) length hLength).transitive
      (succ hℳ input) hLess input hSelf
  · exact hEqual ▸ hSelf

/-- 内部有限长度上的递推唯一性；长度可以是模型的非标准自然数。 -/
theorem finite_recurrence_ext (hℳ : Theory.Models ℳ theory)
    {length first second target : Carrier ℳ} (hLength : membership ℳ length (omega hℳ))
    (hFirst : PureMappingDefinitions.IsMapping ℳ first (succ hℳ length) target)
    (hSecond : PureMappingDefinitions.IsMapping ℳ second (succ hℳ length) target)
    (hZero : value hℳ first (zero hℳ) = value hℳ second (zero hℳ))
    (hStep : ∀ input, membership ℳ input length →
      value hℳ first input = value hℳ second input →
        value hℳ first (succ hℳ input) = value hℳ second (succ hℳ input)) : first = second := by
  have hValues : ∀ input, membership ℳ input (omega hℳ) → membership ℳ input (succ hℳ length) →
      value hℳ first input = value hℳ second input := by
    apply source_induction hℳ equalValuesWithin (.cons first (.cons second (.cons (succ hℳ length) .nil)))
    · exact fun _ => hZero
    · intro input _ hEqual hSuccessor
      have hInput := predecessor_mem hℳ hLength hSuccessor
      exact hStep input hInput (hEqual ((succ_spec hℳ length input).mpr (Or.inl hInput)))
  apply PureMappingSpecifications.mapping_ext hℳ hFirst hSecond
  intro input hInput
  have hInputOmega : membership ℳ input (omega hℳ) := by
    rcases (succ_spec hℳ length input).mp hInput with hLess | rfl
    · exact (omega_project hℳ).transitive (project_modelsZF hℳ) length hLength input hLess
    · exact hLength
  exact ⟨_, application_member hℳ hFirst hInput,
    (hValues input hInputOmega hInput).symm ▸ application_member hℳ hSecond hInput⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalInduction
