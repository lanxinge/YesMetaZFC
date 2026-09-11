import YesMetaZFC.Model.ZFC.Pure.PureBoundedNaturalOrder

/-! # 自然数子集序型的纯消去

有界分支使用有限坍缩；无界分支严格保留原定义的 ω 值。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalSubsetType
open PureModel PureNaturalInduction PureOrderSemantics PureFiniteOrderTypes
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def Bounded (hℳ : Theory.Models ℳ theory) (subset : Carrier ℳ) : Prop :=
  ∃ bound, membership ℳ bound (omega hℳ) ∧ ∀ input, membership ℳ input subset → membership ℳ input bound

theorem bounded_correct (hℳ : Theory.Models ℳ theory) {subset : Carrier ℳ}
    (hSubset : ∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) :
    (E hℳ).relation .isBoundedSubset (.cons subset (.cons (epsilon hℳ (omega hℳ)) (.cons (omega hℳ) .nil))) ↔ Bounded hℳ subset := by
  rw [PureNaturalDifferenceStage.round_one_definition_correct hℳ .isBoundedSubset]
  simp only [PureRoundOneRelations.condition,Nonlogical.BasicSetTheory.bounded_subset_condition,
    Formula.satisfies_existsFreeTop,Formula.satisfies_forallFreeTop,Formula.satisfies]
  change ((∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) ∧
    ∃ bound, membership ℳ bound (omega hℳ) ∧ ∀ input, membership ℳ input subset →
      membership ℳ ((E hℳ).function .orderedPair (.cons input (.cons bound .nil))) (epsilon hℳ (omega hℳ))) ↔ _
  simp only [edge_correct hℳ,epsilon_correct hℳ]
  constructor
  · rintro ⟨_,bound,hBound,hUpper⟩
    exact ⟨bound,hBound,fun input hInput => (hUpper input hInput).2.2⟩
  · rintro ⟨bound,hBound,hUpper⟩
    exact ⟨hSubset,bound,hBound,fun input hInput => ⟨hSubset input hInput,hBound,hUpper input hInput⟩⟩

def guard : Formula S [] [s,s] := Nonlogical.BasicSetTheory.subset_formula (.fvar (.there .here)) Nonlogical.BasicSetTheory.omega_term

def specification : Formula S [] [s,s] := Nonlogical.BasicSetTheory.natural_subset_type_condition (.fvar (.there .here)) (.fvar .here)

def Spec (hℳ : Theory.Models ℳ theory) (subset output : Carrier ℳ) : Prop :=
  membership ℳ output (succ hℳ (omega hℳ)) ∧
    (Bounded hℳ subset → membership ℳ output (omega hℳ) ∧ ∃ function, Iso hℳ (epsilon hℳ subset) subset output function) ∧
      (¬ Bounded hℳ subset → output = omega hℳ)

theorem specification_correct (hℳ : Theory.Models ℳ theory) {subset : Carrier ℳ}
    (hSubset : ∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) (output : Carrier ℳ) :
    specification.satisfies (templateEnv (.cons output (.cons subset .nil)) : Env (E hℳ).model [] [s,s]) ↔ Spec hℳ subset output := by
  change (membership ℳ output ((E hℳ).function .successor (.cons ((E hℳ).function .omega .nil) .nil)) ∧
    (((E hℳ).relation .isBoundedSubset (.cons subset (.cons (epsilon hℳ ((E hℳ).function .omega .nil)) (.cons ((E hℳ).function .omega .nil) .nil))) →
      membership ℳ output ((E hℳ).function .omega .nil) ∧
      (E hℳ).relation .isOrderIsomorphic (.cons (epsilon hℳ subset) (.cons subset (.cons (epsilon hℳ output) (.cons output .nil))))) ∧
    (¬ (E hℳ).relation .isBoundedSubset (.cons subset (.cons (epsilon hℳ ((E hℳ).function .omega .nil)) (.cons ((E hℳ).function .omega .nil) .nil))) → output = (E hℳ).function .omega .nil))) ↔ _
  rw [omega_eq hℳ,PureNaturalDifferenceStage.function_from_difference hℳ .successor rfl,bounded_correct hℳ hSubset]
  have hLinear := epsilon_linear hℳ ((omega_project hℳ).isOrdinal (project_modelsZF hℳ)) hSubset
  constructor
  · rintro ⟨hOutput,hBounded,hUnbounded⟩
    refine ⟨hOutput,?_,hUnbounded⟩
    intro hB
    have hData := hBounded hB
    exact ⟨hData.1,(isomorphic_correct hℳ hLinear ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) output hData.1)).mp hData.2⟩
  · rintro ⟨hOutput,hBounded,hUnbounded⟩
    refine ⟨hOutput,?_,hUnbounded⟩
    intro hB
    have hData := hBounded hB
    exact ⟨hData.1,(isomorphic_correct hℳ hLinear ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) output hData.1)).mpr hData.2⟩

def body : Formula ℒ [] [setSort,setSort] := openFormula PureNaturalDifferenceStage.interpretation (.conj guard specification)
def graph : Formula ℒ [] [setSort,setSort] := _root_.YesMetaZFC.Automation.TotalizedGraph.formula body PureRelationFunctions.emptyFallback

theorem body_correct (hℳ : Theory.Models ℳ theory) (subset output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons subset .nil))) ↔
      (∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) ∧ Spec hℳ subset output := by
  apply (openFormula_correct (E hℳ) (PureNaturalDifferenceStage.realizes hℳ) (.conj guard specification) (.cons output (.cons subset .nil))).trans
  have hGuard : guard.satisfies (templateEnv (.cons output (.cons subset .nil)) : Env (E hℳ).model [] [s,s]) ↔
      ∀ input, membership ℳ input subset → membership ℳ input (omega hℳ) := by
    change (∀ input, membership ℳ input subset → membership ℳ input ((E hℳ).function .omega .nil)) ↔ _
    rw [omega_eq hℳ]
  constructor
  · rintro ⟨hSubset,hSpec⟩
    have hSubset := hGuard.mp hSubset
    exact ⟨hSubset,(specification_correct hℳ hSubset output).mp hSpec⟩
  · rintro ⟨hSubset,hSpec⟩
    exact ⟨hGuard.mpr hSubset,(specification_correct hℳ hSubset output).mpr hSpec⟩

theorem exists_body (hℳ : Theory.Models ℳ theory) {subset : Carrier ℳ}
    (hSubset : ∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) :
    ∃ output, body.satisfies (templateEnv (.cons output (.cons subset .nil))) := by
  classical
  by_cases hBounded : Bounded hℳ subset
  · obtain ⟨bound,hBound,hUpper⟩ := hBounded
    have hOrder := PureBoundedNaturalOrder.natural_order hℳ hBound hUpper
    obtain ⟨output,hOutput,hIso⟩ := natural_type_exists hℳ hOrder.1 hOrder.2.2 hOrder.2.1
    exact ⟨output,(body_correct hℳ subset output).mpr ⟨hSubset,(succ_spec hℳ (omega hℳ) output).mpr (Or.inl hOutput),
      fun _ => ⟨hOutput,hIso⟩,fun hNo => False.elim (hNo ⟨bound,hBound,hUpper⟩)⟩⟩
  · exact ⟨omega hℳ,(body_correct hℳ subset (omega hℳ)).mpr ⟨hSubset,(succ_spec hℳ (omega hℳ) _).mpr (Or.inr rfl),
      fun hB => False.elim (hBounded hB),fun _ => rfl⟩⟩

theorem functional (hℳ : Theory.Models ℳ theory) (subset : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons subset .nil))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons subset .nil))) → other = output := by
  classical
  apply PureRelationFunctions.totalized_functional hℳ body (.cons subset .nil)
  intro first second hFirst hSecond
  have hF := (body_correct hℳ subset first).mp hFirst
  have hS := (body_correct hℳ subset second).mp hSecond
  by_cases hBounded : Bounded hℳ subset
  · obtain ⟨hFirst,f,hFIso⟩ := hF.2.2.1 hBounded
    obtain ⟨hSecond,g,hGIso⟩ := hS.2.2.1 hBounded
    exact natural_type_unique hℳ (epsilon_linear hℳ ((omega_project hℳ).isOrdinal (project_modelsZF hℳ)) hF.1)
      (PureBoundedNaturalOrder.least_on_subset hℳ hF.1) hFirst hSecond hFIso hGIso
  · exact (hF.2.2.2 hBounded).trans (hS.2.2.2 hBounded).symm

theorem agrees (hℳ : Theory.Models ℳ theory) {subset : Carrier ℳ}
    (hSubset : ∀ input, membership ℳ input subset → membership ℳ input (omega hℳ)) (output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons subset .nil))) ↔
      specification.satisfies (templateEnv (.cons output (.cons subset .nil)) : Env (E hℳ).model [] [s,s]) :=
  (PureRelationFunctions.totalized_agrees body (.cons subset .nil) (exists_body hℳ hSubset) output).trans
    ((body_correct hℳ subset output).trans (Iff.trans ⟨And.right,fun h => ⟨hSubset,h⟩⟩ (specification_correct hℳ hSubset output).symm))

theorem dependencies_covered : formulaCovered PureNaturalDifferenceStage.functionCovered PureNaturalDifferenceStage.relationCovered (.conj guard specification) = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalSubsetType
