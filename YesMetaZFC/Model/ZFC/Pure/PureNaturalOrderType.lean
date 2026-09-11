import YesMetaZFC.Model.ZFC.Pure.PureFiniteOrderTypes

/-! # 自然离散序型函数的纯消去 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalOrderType
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

def guard : Formula S [] [s,s,s] := Nonlogical.BasicSetTheory.is_natural_discrete_linear_order_formula
  (.fvar (.there .here)) (.fvar (.there (.there .here)))
def specification : Formula S [] [s,s,s] := Nonlogical.BasicSetTheory.natural_order_type_condition
  (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
def body : Formula ℒ [] [setSort,setSort,setSort] := openFormula PureNaturalDifferenceStage.interpretation (.conj guard specification)
def graph : Formula ℒ [] [setSort,setSort,setSort] := _root_.YesMetaZFC.Automation.TotalizedGraph.formula body PureRelationFunctions.emptyFallback

theorem specification_correct (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ}
    (hLinear : Linear relation carrier) (output : Carrier ℳ) :
    specification.satisfies (templateEnv (.cons output (.cons relation (.cons carrier .nil))) : Env (E hℳ).model [] [s,s,s]) ↔
      membership ℳ output (omega hℳ) ∧ ∃ function, Iso hℳ relation carrier output function := by
  change (membership ℳ output ((E hℳ).function .omega .nil) ∧
    (E hℳ).relation .isOrderIsomorphic (.cons relation (.cons carrier (.cons (epsilon hℳ output) (.cons output .nil))))) ↔ _
  rw [omega_eq hℳ]
  constructor
  · rintro ⟨hOutput,hIso⟩
    exact ⟨hOutput,(isomorphic_correct hℳ hLinear ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) output hOutput)).mp hIso⟩
  · rintro ⟨hOutput,hIso⟩
    exact ⟨hOutput,(isomorphic_correct hℳ hLinear ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) output hOutput)).mpr hIso⟩

theorem body_correct (hℳ : Theory.Models ℳ theory) (relation carrier output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons relation (.cons carrier .nil)))) ↔
      (E hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil)) ∧
        specification.satisfies (templateEnv (.cons output (.cons relation (.cons carrier .nil))) : Env (E hℳ).model [] [s,s,s]) :=
  openFormula_correct (E hℳ) (PureNaturalDifferenceStage.realizes hℳ) (.conj guard specification) (.cons output (.cons relation (.cons carrier .nil)))

theorem exists_body (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ}
    (hNatural : (E hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil))) :
    ∃ output, body.satisfies (templateEnv (.cons output (.cons relation (.cons carrier .nil)))) := by
  have hOrder := (natural_order_correct hℳ relation carrier).mp hNatural
  obtain ⟨output,hOutput,hIso⟩ := natural_type_exists hℳ hOrder.1 hOrder.2.2 hOrder.2.1
  exact ⟨output,(body_correct hℳ relation carrier output).mpr ⟨hNatural,(specification_correct hℳ hOrder.1 output).mpr ⟨hOutput,hIso⟩⟩⟩

theorem functional (hℳ : Theory.Models ℳ theory) (relation carrier : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons relation (.cons carrier .nil)))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons relation (.cons carrier .nil)))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ body (.cons relation (.cons carrier .nil))
  intro first second hFirst hSecond
  have hF := (body_correct hℳ relation carrier first).mp hFirst
  have hS := (body_correct hℳ relation carrier second).mp hSecond
  have hOrder := (natural_order_correct hℳ relation carrier).mp hF.1
  obtain ⟨hFirst,f,hFIso⟩ := (specification_correct hℳ hOrder.1 first).mp hF.2
  obtain ⟨hSecond,g,hGIso⟩ := (specification_correct hℳ hOrder.1 second).mp hS.2
  exact natural_type_unique hℳ hOrder.1 hOrder.2.2 hFirst hSecond hFIso hGIso

theorem agrees (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ}
    (hNatural : (E hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil))) (output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons relation (.cons carrier .nil)))) ↔
      specification.satisfies (templateEnv (.cons output (.cons relation (.cons carrier .nil))) : Env (E hℳ).model [] [s,s,s]) :=
  (PureRelationFunctions.totalized_agrees body (.cons relation (.cons carrier .nil)) (exists_body hℳ hNatural) output).trans
    ((body_correct hℳ relation carrier output).trans ⟨And.right,fun h => ⟨hNatural,h⟩⟩)

theorem dependencies_covered : formulaCovered PureNaturalDifferenceStage.functionCovered PureNaturalDifferenceStage.relationCovered (.conj guard specification) = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalOrderType
