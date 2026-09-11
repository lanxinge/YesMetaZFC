import YesMetaZFC.Model.ZFC.Pure.PureOmegaIteration

/-! # 并集与幂集的内部迭代 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSetIterations
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

def Union (input output : Carrier ℳ) : Prop := ∀ element, membership ℳ element output ↔
  ∃ member, membership ℳ member input ∧ membership ℳ element member

def Power (input output : Carrier ℳ) : Prop := ∀ subset, membership ℳ subset output ↔
  ∀ member, membership ℳ member subset → membership ℳ member input

def unionStep : Project.BinarySchema 0 where
  body := Project.Formula.isUnion (.bound 0) (.bound 1)
def powerStep : Project.BinarySchema 0 where
  body := Project.Formula.isPowerSet (.bound 0) (.bound 1)
theorem union_rep : PureOmegaIteration.Represents (ℳ := ℳ) unionStep Union := by
  intro env input output
  exact Project.Formula.satisfies_isUnion_iff ((env.push input).push output) (.bound 0) (.bound 1)

theorem power_rep : PureOmegaIteration.Represents (ℳ := ℳ) powerStep Power := by
  intro env input output
  exact Project.Formula.satisfies_isPowerSet_iff ((env.push input).push output) (.bound 0) (.bound 1)

theorem union_total (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    ∃ output, Union input output ∧ ∀ other, Union input other → other = output := by
  obtain ⟨output,hOutput⟩ := PureModel.union hℳ input
  exact ⟨output,hOutput,fun other hOther => extensionality hℳ other output
    (fun element => (hOther element).trans (hOutput element).symm)⟩

theorem power_total (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    ∃ output, Power input output ∧ ∀ other, Power input other → other = output := by
  obtain ⟨output,hOutput⟩ := PureModel.power hℳ input
  exact ⟨output,hOutput,fun other hOther => extensionality hℳ other output
    (fun element => (hOther element).trans (hOutput element).symm)⟩

/-- 有限层级是从空集开始的幂集迭代；其图不使用待解释的层级符号。 -/
def hierarchyGraph : Formula ℒ [] [setSort] :=
  .existsE setSort <| .conj (applyTemplate (PureFunctionDefinitions.graph .emptySet) (.cons (.bvar .here) .nil))
    (applyTemplate (PureOmegaIteration.graph powerStep) (.cons (.fvar .here) (.cons (.bvar .here) .nil)))

theorem hierarchy_correct (hℳ : Theory.Models ℳ theory) (sequence : Carrier ℳ) :
    hierarchyGraph.satisfies (templateEnv (.cons sequence .nil)) ↔
      (PureOmegaIteration.graph powerStep).satisfies (templateEnv (.cons sequence (.cons (zero hℳ) .nil))) := by
  simp only [hierarchyGraph,Formula.satisfies,applyTemplate_satisfies]
  change (∃ empty, (PureFunctionDefinitions.graph .emptySet).satisfies (templateEnv (.cons empty .nil)) ∧
    (PureOmegaIteration.graph powerStep).satisfies (templateEnv (.cons sequence (.cons empty .nil)))) ↔ _
  constructor
  · rintro ⟨empty,hEmpty,hSequence⟩
    have hEqual : empty = zero hℳ := ((PureDifferenceStage.realizes hℳ).function .emptySet .nil empty).mp hEmpty
    exact hEqual ▸ hSequence
  · intro hSequence
    exact ⟨zero hℳ,((PureDifferenceStage.realizes hℳ).function .emptySet .nil _).mpr rfl,hSequence⟩

theorem hierarchy_functional (hℳ : Theory.Models ℳ theory) :
    ∃ sequence : Carrier ℳ, hierarchyGraph.satisfies (templateEnv (.cons sequence .nil)) ∧
      ∀ other, hierarchyGraph.satisfies (templateEnv (.cons other .nil)) → other = sequence := by
  obtain ⟨sequence,hSequence,hUnique⟩ := PureOmegaIteration.functional hℳ power_rep (power_total hℳ) (zero hℳ)
  exact ⟨sequence,(hierarchy_correct hℳ sequence).mpr hSequence,
    fun other hOther => hUnique other ((hierarchy_correct hℳ other).mp hOther)⟩

theorem hierarchy_iterates (hℳ : Theory.Models ℳ theory) {sequence : Carrier ℳ}
    (hSequence : hierarchyGraph.satisfies (templateEnv (.cons sequence .nil))) :
    PureOmegaIteration.Iterates hℳ Power sequence (zero hℳ) :=
  PureOmegaIteration.iterates_of_graph hℳ power_rep (power_total hℳ) ((hierarchy_correct hℳ sequence).mp hSequence)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSetIterations
