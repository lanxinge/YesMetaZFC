import YesMetaZFC.Model.ZFC.Pure.PureNaturalInduction

/-! # 加、乘、幂原递推规格的唯一性

三种原规格都由内部有限序列迭代给出。先统一其序列语义，再用内部归纳证明
输出唯一；存在性仍须独立构造，不能把本模块的唯一性计作函数消去完成。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticRecurrence
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

inductive Operation where
  | addition | multiplication | exponentiation

def specification (operation : Operation) : Formula S [] [s,s,s] :=
  match operation with
  | .addition => Nonlogical.BasicSetTheory.natural_addition_spec (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  | .multiplication => Nonlogical.BasicSetTheory.natural_multiplication_spec (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  | .exponentiation => Nonlogical.BasicSetTheory.natural_exponentiation_spec (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

def length (operation : Operation) (left right : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition | .multiplication => left
  | .exponentiation => right

noncomputable def seed (hℳ : Theory.Models ℳ theory) (operation : Operation) (right : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition => right
  | .multiplication => zero hℳ
  | .exponentiation => succ hℳ (zero hℳ)

noncomputable def step (hℳ : Theory.Models ℳ theory) (operation : Operation) (left right current : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition => succ hℳ current
  | .multiplication => (PureDifferenceStage.expansion hℳ).function .naturalAddition (.cons current (.cons right .nil))
  | .exponentiation => (PureDifferenceStage.expansion hℳ).function .naturalMultiplication (.cons current (.cons left .nil))

/-- 固定初值和后继步的有限迭代序列，域包含最后一个输出位置。 -/
def Iteration (hℳ : Theory.Models ℳ theory) (length seed : Carrier ℳ)
    (step : Carrier ℳ → Carrier ℳ) (sequence output : Carrier ℳ) : Prop :=
  PureMappingDefinitions.IsMapping ℳ sequence (succ hℳ length) (omega hℳ) ∧
    value hℳ sequence (zero hℳ) = seed ∧
      (∀ input, membership ℳ input length → value hℳ sequence (succ hℳ input) = step (value hℳ sequence input)) ∧
        value hℳ sequence length = output

theorem mapping_correct (hℳ : Theory.Models ℳ theory) (function source target : Carrier ℳ) :
    (PureDifferenceStage.expansion hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil))) ↔
      PureMappingDefinitions.IsMapping ℳ function source target :=
  ((PureDifferenceStage.realizes hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil)))).symm.trans
    (PureMappingDefinitions.isMapping_correct function source target)

/-- 原加、乘、幂正文与迭代序列的实际语义逐参数一致。 -/
theorem specification_correct (hℳ : Theory.Models ℳ theory) (operation : Operation)
    (left right output : Carrier ℳ) :
    (specification operation).satisfies
        (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (PureDifferenceStage.expansion hℳ).model [] [s,s,s]) ↔
      membership ℳ output (omega hℳ) ∧
        ∃ sequence, Iteration hℳ (length operation left right) (seed hℳ operation right)
          (step hℳ operation left right) sequence output := by
  cases operation <;>
    simp only [specification, Nonlogical.BasicSetTheory.natural_addition_spec,
      Nonlogical.BasicSetTheory.natural_multiplication_spec, Nonlogical.BasicSetTheory.natural_exponentiation_spec,
      Nonlogical.BasicSetTheory.natural_addition_bound_graph_condition,
      Nonlogical.BasicSetTheory.natural_multiplication_bound_graph_condition,
      Nonlogical.BasicSetTheory.natural_exponentiation_bound_graph_condition,
      Nonlogical.BasicSetTheory.natural_addition_graph_condition,
      Nonlogical.BasicSetTheory.natural_multiplication_graph_condition,
      Nonlogical.BasicSetTheory.natural_exponentiation_graph_condition,
      Formula.satisfies_existsFreeTop, Formula.satisfies_forallFreeTop, Formula.satisfies]
  all_goals
    apply and_congr Iff.rfl
    apply exists_congr
    intro sequence
    exact and_congr (mapping_correct hℳ _ _ _) Iff.rfl

/-- 相同有限迭代的两个见证图及其最后输出都相等。 -/
theorem iteration_unique (hℳ : Theory.Models ℳ theory)
    {length seed first second left right : Carrier ℳ} {step : Carrier ℳ → Carrier ℳ}
    (hLength : membership ℳ length (omega hℳ))
    (hFirst : Iteration hℳ length seed step first left)
    (hSecond : Iteration hℳ length seed step second right) : first = second ∧ left = right := by
  have hEqual : first = second := finite_recurrence_ext hℳ hLength hFirst.1 hSecond.1
    (hFirst.2.1.trans hSecond.2.1.symm) (fun input hInput hSame =>
      (hFirst.2.2.1 input hInput).trans ((congrArg step hSame).trans (hSecond.2.2.1 input hInput).symm))
  refine ⟨hEqual, hFirst.2.2.2.symm.trans ?_⟩
  exact (congrArg (fun sequence => value hℳ sequence length) hEqual).trans hSecond.2.2.2

/-- 原自然数 guard 下，三种原算术规格的输出唯一。 -/
theorem specification_unique (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right first second : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hFirst : (specification operation).satisfies
      (templateEnv (.cons first (.cons left (.cons right .nil))) : Env (PureDifferenceStage.expansion hℳ).model [] [s,s,s]))
    (hSecond : (specification operation).satisfies
      (templateEnv (.cons second (.cons left (.cons right .nil))) : Env (PureDifferenceStage.expansion hℳ).model [] [s,s,s])) : first = second := by
  obtain ⟨_, firstSequence, hFirstSequence⟩ := (specification_correct hℳ operation left right first).mp hFirst
  obtain ⟨_, secondSequence, hSecondSequence⟩ := (specification_correct hℳ operation left right second).mp hSecond
  have hLength : membership ℳ (length operation left right) (omega hℳ) := by
    cases operation
    · exact hLeft
    · exact hLeft
    · exact hRight
  exact (iteration_unique hℳ hLength hFirstSequence hSecondSequence).2

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticRecurrence
