import YesMetaZFC.Model.ZFC.Pure.PureBoundedDefinitions

/-! # 有限序列空间的纯图

任意有限序列的图均包含于 ω 与值域的笛卡尔积，所以整个有限序列空间可以从
该积的幂集中分离。ω 是模型内部的最小归纳集，不要求所有序列外部有限。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteSequenceSpace
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def condition : Nonlogical.BasicSetTheory.SetFormula [] [s,s] :=
  Nonlogical.BasicSetTheory.finite_sequence_member_condition (.fvar (.there .here)) (.fvar .here)

def body : Formula ℒ [] [setSort,setSort] := openFormula PureNaturalRelations.interpretation condition
def graph : Formula ℒ [] [setSort,setSort] := PureFunctionDefinitions.comprehension body

theorem dependencies_covered :
    formulaCovered PureStageTwoBase.functionCovered PureNaturalRelations.relationCovered condition = true := rfl

theorem condition_correct (hℳ : Theory.Models ℳ theory) (sequence source : Carrier ℳ) :
    condition.satisfies
        (templateEnv (.cons sequence (.cons source .nil)) : Env (PureStageTwoSemantics.expansion hℳ).model [] [s,s]) ↔
      ∃ length, membership ℳ length ((PureStageTwoSemantics.expansion hℳ).function .omega .nil) ∧
        PureMappingDefinitions.IsMapping ℳ sequence length source := by
  simp only [condition, Nonlogical.BasicSetTheory.finite_sequence_member_condition,
    Formula.satisfies_existsFreeTop, Formula.satisfies]
  apply exists_congr
  intro length
  exact and_congr Iff.rfl (PureMappingDefinitions.isMapping_correct sequence length source)

theorem omega_project (hℳ : Theory.Models ℳ theory) :
    (Project.FirstOrderSemantics.reduct ℳ).IsOmega ((PureStageTwoSemantics.expansion hℳ).function .omega .nil) :=
  (PureOmegaAndReverse.omega_correct hℳ _).mp
    (((PureStageTwoSemantics.realizes hℳ).function .omega .nil _).mpr rfl)

/-- 域属于 ω 的映射，其每个序对都落在 ω 与目标集的积内。 -/
theorem mapping_bounded (hℳ : Theory.Models ℳ theory) (sequence length source product : Carrier ℳ)
    (hLength : membership ℳ length ((PureStageTwoSemantics.expansion hℳ).function .omega .nil))
    (hMapping : PureMappingDefinitions.IsMapping ℳ sequence length source)
    (hProduct : (PureMappingDefinitions.graph .cartesianProduct).satisfies
      (templateEnv (.cons product (.cons ((PureStageTwoSemantics.expansion hℳ).function .omega .nil) (.cons source .nil))))) :
    ∀ pair, membership ℳ pair sequence → membership ℳ pair product := by
  intro pair hPair
  obtain ⟨input, output, hCode⟩ := hMapping.1.1 pair hPair
  have hMember : PureKuratowski.PairMember ℳ input output sequence := ⟨pair, hCode, hPair⟩
  have hInput := (hMapping.2.1 input).mpr ⟨output, hMember⟩
  obtain ⟨value, hValue, hGraph⟩ := hMapping.2.2 input hInput
  have hOutput : membership ℳ output source := (hMapping.1.2 input value output hGraph hMember) ▸ hValue
  have hOmegaInput : membership ℳ input ((PureStageTwoSemantics.expansion hℳ).function .omega .nil) :=
    (omega_project hℳ).transitive (project_modelsZF hℳ) length hLength input hInput
  exact ((PureMappingDefinitions.cartesian_correct _ _ _).mp hProduct pair).mpr
    ⟨input, hOmegaInput, output, hOutput, hCode⟩

theorem graph_correct (hℳ : Theory.Models ℳ theory) (output source : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons source .nil))) ↔
      (Nonlogical.BasicSetTheory.finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here)).satisfies
        (templateEnv (.cons output (.cons source .nil)) : Env (PureStageTwoSemantics.expansion hℳ).model [] [s,s]) := by
  rw [graph, PureFunctionDefinitions.comprehension_correct]
  simp only [Nonlogical.BasicSetTheory.finite_sequence_space_spec, Formula.satisfies_forallFreeTop, Formula.satisfies]
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (openFormula_correct (PureStageTwoSemantics.expansion hℳ)
    (PureStageTwoSemantics.realizes hℳ) condition (.cons element (.cons source .nil)))

theorem functional (hℳ : Theory.Models ℳ theory) (source : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons source .nil))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons source .nil))) → other = output := by
  let omega := (PureStageTwoSemantics.expansion hℳ).function .omega .nil
  obtain ⟨product, hProduct, _⟩ := PureMappingDefinitions.functional hℳ .cartesianProduct (.cons omega (.cons source .nil))
  obtain ⟨power, hPower⟩ := PureModel.power hℳ product
  apply PureSeparation.bounded_functional hℳ body (.cons source .nil) power
  intro sequence hSequence
  have hCondition := (openFormula_correct (PureStageTwoSemantics.expansion hℳ)
    (PureStageTwoSemantics.realizes hℳ) condition (.cons sequence (.cons source .nil))).mp hSequence
  obtain ⟨length, hLength, hMapping⟩ := (condition_correct hℳ sequence source).mp hCondition
  exact (hPower sequence).mpr (mapping_bounded hℳ sequence length source product hLength hMapping hProduct)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteSequenceSpace
