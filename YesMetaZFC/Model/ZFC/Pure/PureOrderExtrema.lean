import YesMetaZFC.Model.ZFC.Pure.PureStageSemantics

/-! # 最小元和最大元的实际纯图

图先要求关系在所选子集上非对称，再使用原极值规格；其余输入规范取空集。
原良序／自然离散序 guard 保证非对称性与极值存在，所以合法输入保留原规格。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOrderExtrema
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev Obj (ℳ : Structure.{0, 0, 0, x} S) := ℳ.Carrier s

def Mem (ℳ : Structure.{0, 0, 0, x} S) (left right : Obj ℳ) : Prop :=
  ℳ.relInterp .membership (.cons left (.cons right .nil))
def Edge (ℳ : Structure.{0, 0, 0, x} S) (relation left right : Obj ℳ) : Prop :=
  Mem ℳ (ℳ.funcInterp .orderedPair (.cons left (.cons right .nil))) relation

def Asymmetric (ℳ : Structure.{0, 0, 0, x} S) (relation subset : Obj ℳ) : Prop :=
  ∀ left right, Mem ℳ left subset → Mem ℳ right subset → Edge ℳ relation left right → ¬ Edge ℳ relation right left

inductive Direction where
  | minimum | maximum

def Extreme (ℳ : Structure.{0, 0, 0, x} S) (direction : Direction) (relation subset output : Obj ℳ) : Prop :=
  Mem ℳ output subset ∧ ∀ element, Mem ℳ element subset → output ≠ element →
    match direction with
    | .minimum => Edge ℳ relation output element
    | .maximum => Edge ℳ relation element output

def specification (direction : Direction) : Formula S [] [s, s, s] :=
  match direction with
  | .minimum => Nonlogical.BasicSetTheory.minimum_spec (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  | .maximum => Nonlogical.BasicSetTheory.maximum_spec (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

def asymmetricCondition : Formula S [] [s, s, s] :=
  .forallE s <| .forallE s <|
    .imp (Nonlogical.BasicSetTheory.membership_formula (.bvar (.there .here)) (.fvar (.there (.there .here)))) <|
    .imp (Nonlogical.BasicSetTheory.membership_formula (.bvar .here) (.fvar (.there (.there .here)))) <|
    .imp (Nonlogical.BasicSetTheory.membership_formula
      (Nonlogical.BasicSetTheory.ordered_pair_term (.bvar (.there .here)) (.bvar .here)) (.fvar (.there .here))) <|
      .neg (Nonlogical.BasicSetTheory.membership_formula
        (Nonlogical.BasicSetTheory.ordered_pair_term (.bvar .here) (.bvar (.there .here))) (.fvar (.there .here)))

theorem asymmetric_correct (ℳ : Structure.{0, 0, 0, x} S) (output relation subset : Obj ℳ) :
    asymmetricCondition.satisfies (templateEnv (.cons output (.cons relation (.cons subset .nil)))) ↔
      Asymmetric ℳ relation subset := Iff.rfl

theorem specification_correct (ℳ : Structure.{0, 0, 0, x} S) (direction : Direction) (output relation subset : Obj ℳ) :
    (specification direction).satisfies (templateEnv (.cons output (.cons relation (.cons subset .nil)))) ↔
      Extreme ℳ direction relation subset output := by
  cases direction <;>
    simp only [specification, Nonlogical.BasicSetTheory.minimum_spec, Nonlogical.BasicSetTheory.maximum_spec,
      Formula.satisfies_forallFreeTop, Formula.satisfies]
  all_goals
    constructor
    · intro h
      exact ⟨(h output).1, fun element => (h element).2⟩
    · intro h element
      exact ⟨h.1, h.2 element⟩

def body (direction : Direction) : Formula ℒ [] [setSort, setSort, setSort] :=
  openFormula PureRoundOneRelations.interpretation (.conj asymmetricCondition (specification direction))

theorem body_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    (direction : Direction) (output relation subset : Carrier ℳ) :
    (body direction).satisfies (templateEnv (.cons output (.cons relation (.cons subset .nil)))) ↔
      Asymmetric (PureStageSemantics.expansion hℳ).model relation subset ∧
        Extreme (PureStageSemantics.expansion hℳ).model direction relation subset output := by
  apply (openFormula_correct (PureStageSemantics.expansion hℳ) (PureStageSemantics.realizes hℳ)
    (.conj asymmetricCondition (specification direction)) (.cons output (.cons relation (.cons subset .nil)))).trans
  exact and_congr (asymmetric_correct (PureStageSemantics.expansion hℳ).model output relation subset)
    (specification_correct (PureStageSemantics.expansion hℳ).model direction output relation subset)

theorem extreme_unique (ℳ : Structure.{0, 0, 0, x} S) (direction : Direction) (relation subset : Obj ℳ)
    (hAsymmetric : Asymmetric ℳ relation subset) {left right : Obj ℳ}
    (hLeft : Extreme ℳ direction relation subset left) (hRight : Extreme ℳ direction relation subset right) : left = right := by
  classical
  by_cases hEq : left = right
  · exact hEq
  · apply False.elim
    cases direction with
    | minimum => exact hAsymmetric left right hLeft.1 hRight.1 (hLeft.2 right hRight.1 hEq) (hRight.2 left hLeft.1 (Ne.symm hEq))
    | maximum => exact hAsymmetric right left hRight.1 hLeft.1 (hLeft.2 right hRight.1 hEq) (hRight.2 left hLeft.1 (Ne.symm hEq))

def extremeGraph (direction : Direction) : Formula ℒ [] [setSort, setSort, setSort] :=
  _root_.YesMetaZFC.Automation.TotalizedGraph.formula (body direction) PureRelationFunctions.emptyFallback

inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | minimum : Primitive .minimum
  | maximum : Primitive .maximum

def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match primitive with
  | .minimum => extremeGraph .minimum
  | .maximum => extremeGraph .maximum

theorem extreme_functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    (direction : Direction) (relation subset : Carrier ℳ) :
    ∃ output, (extremeGraph direction).satisfies (templateEnv (.cons output (.cons relation (.cons subset .nil)))) ∧
      ∀ other, (extremeGraph direction).satisfies (templateEnv (.cons other (.cons relation (.cons subset .nil)))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ (body direction) (.cons relation (.cons subset .nil))
  intro left right hLeft hRight
  have hL := (body_correct hℳ direction left relation subset).mp hLeft
  have hR := (body_correct hℳ direction right relation subset).mp hRight
  exact extreme_unique (PureStageSemantics.expansion hℳ).model direction relation subset hL.1 hL.2 hR.2

theorem functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  cases primitive <;> cases args with | cons relation tail =>
    cases tail with | cons subset tail =>
    cases tail
    exact extreme_functional hℳ _ relation subset

/-- 有合法极值的非对称输入上，总化图与原极值条件逐输出等价。 -/
theorem agrees {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    (direction : Direction) (relation subset : Carrier ℳ)
    (hAsymmetric : Asymmetric (PureStageSemantics.expansion hℳ).model relation subset)
    (hExists : ∃ output, Extreme (PureStageSemantics.expansion hℳ).model direction relation subset output)
    (output : Carrier ℳ) :
    (extremeGraph direction).satisfies (templateEnv (.cons output (.cons relation (.cons subset .nil)))) ↔
      Extreme (PureStageSemantics.expansion hℳ).model direction relation subset output := by
  obtain ⟨witness, hWitness⟩ := hExists
  apply (PureRelationFunctions.totalized_agrees (body direction) (.cons relation (.cons subset .nil))
    ⟨witness, (body_correct hℳ direction witness relation subset).mpr ⟨hAsymmetric, hWitness⟩⟩ output).trans
  exact (body_correct hℳ direction output relation subset).trans ⟨And.right, fun h => ⟨hAsymmetric, h⟩⟩

/-- 第一轮的原线序定义直接给出任意子集上的非对称性。 -/
theorem linear_asymmetric {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    (relation carrier subset : Carrier ℳ)
    (hLinear : (PureStageSemantics.expansion hℳ).relation .isLinearOrder (.cons relation (.cons carrier .nil)))
    (hSubset : ∀ element, Mem (PureStageSemantics.expansion hℳ).model element subset →
      Mem (PureStageSemantics.expansion hℳ).model element carrier) :
    Asymmetric (PureStageSemantics.expansion hℳ).model relation subset := by
  have hDef := (PureRoundOneRelations.definition_correct hℳ .isLinearOrder (.cons relation (.cons carrier .nil))).mp hLinear
  have hIrrefl := hDef.2.2.1.1
  have hTrans := hDef.2.2.1.2
  simp only [Nonlogical.BasicSetTheory.linear_order_irreflexive_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies] at hIrrefl
  simp only [Nonlogical.BasicSetTheory.linear_order_transitive_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies] at hTrans
  change ∀ element, Mem (PureStageSemantics.expansion hℳ).model element carrier →
    ¬ Edge (PureStageSemantics.expansion hℳ).model relation element element at hIrrefl
  change ∀ first second third,
    (Mem (PureStageSemantics.expansion hℳ).model first carrier ∧
      Mem (PureStageSemantics.expansion hℳ).model second carrier ∧
      Mem (PureStageSemantics.expansion hℳ).model third carrier) →
    (Edge (PureStageSemantics.expansion hℳ).model relation first second ∧
      Edge (PureStageSemantics.expansion hℳ).model relation second third) →
    Edge (PureStageSemantics.expansion hℳ).model relation first third at hTrans
  intro left right hLeft hRight hForward hBackward
  exact hIrrefl left (hSubset left hLeft)
    (hTrans left right left ⟨hSubset left hLeft, hSubset right hRight, hSubset left hLeft⟩ ⟨hForward, hBackward⟩)

private theorem power_contains {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    (subset carrier : Carrier ℳ)
    (hSubset : ∀ element, Mem (PureStageSemantics.expansion hℳ).model element subset →
      Mem (PureStageSemantics.expansion hℳ).model element carrier) :
    Mem (PureStageSemantics.expansion hℳ).model subset
      ((PureStageSemantics.expansion hℳ).function .powerSet (.cons carrier .nil)) := by
  have hGraph := ((PureStageSemantics.realizes hℳ).function .powerSet (.cons carrier .nil) _).mpr rfl
  have hPower := (PureFunctionDefinitions.comprehension_correct _ _ _).mp hGraph
  change ∀ element, membership ℳ element ((PureStageSemantics.expansion hℳ).function .powerSet (.cons carrier .nil)) ↔
    ∀ value, membership ℳ value element → membership ℳ value carrier at hPower
  exact (hPower subset).mpr hSubset

/-- 良序 guard 给出原最小元规格，无需额外假定极值存在。 -/
theorem minimum_spec_of_wellOrder {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    (relation carrier subset output : Carrier ℳ)
    (hOrder : (PureStageSemantics.expansion hℳ).relation .isWellOrder (.cons relation (.cons carrier .nil)))
    (hSubset : ∀ element, Mem (PureStageSemantics.expansion hℳ).model element subset →
      Mem (PureStageSemantics.expansion hℳ).model element carrier)
    (hNonempty : subset ≠ (PureStageSemantics.expansion hℳ).function .emptySet .nil) :
    (graph .minimum).satisfies (templateEnv (.cons output (.cons relation (.cons subset .nil)))) ↔
      (specification .minimum).satisfies
        (templateEnv (.cons output (.cons relation (.cons subset .nil))) : Env (PureStageSemantics.expansion hℳ).model [] [s, s, s]) := by
  have hDef := (PureRoundOneRelations.definition_correct hℳ .isWellOrder (.cons relation (.cons carrier .nil))).mp hOrder
  have hLeast := hDef.2
  simp only [Nonlogical.BasicSetTheory.natural_order_least_element_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies] at hLeast
  have hExists : ∃ candidate, Extreme (PureStageSemantics.expansion hℳ).model .minimum relation subset candidate :=
    hLeast subset ⟨power_contains hℳ subset carrier hSubset, hNonempty⟩
  exact (agrees hℳ .minimum relation subset (linear_asymmetric hℳ relation carrier subset hDef.1 hSubset)
    hExists output).trans (specification_correct (PureStageSemantics.expansion hℳ).model .minimum output relation subset).symm

/-- 自然离散线序同时提供原最小元与最大元规格。 -/
theorem spec_of_naturalOrder {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    (direction : Direction) (relation carrier subset output : Carrier ℳ)
    (hOrder : (PureStageSemantics.expansion hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil)))
    (hSubset : ∀ element, Mem (PureStageSemantics.expansion hℳ).model element subset →
      Mem (PureStageSemantics.expansion hℳ).model element carrier)
    (hNonempty : subset ≠ (PureStageSemantics.expansion hℳ).function .emptySet .nil) :
    (extremeGraph direction).satisfies (templateEnv (.cons output (.cons relation (.cons subset .nil)))) ↔
      (specification direction).satisfies
        (templateEnv (.cons output (.cons relation (.cons subset .nil))) : Env (PureStageSemantics.expansion hℳ).model [] [s, s, s]) := by
  have hDef := (PureRoundOneRelations.definition_correct hℳ .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil))).mp hOrder
  have hExists : ∃ candidate, Extreme (PureStageSemantics.expansion hℳ).model direction relation subset candidate := by
    cases direction with
    | minimum =>
      have hLeast := hDef.2.2
      simp only [Nonlogical.BasicSetTheory.natural_order_least_element_condition,
        Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies] at hLeast
      exact hLeast subset ⟨power_contains hℳ subset carrier hSubset, hNonempty⟩
    | maximum =>
      have hGreatest := hDef.2.1
      simp only [Nonlogical.BasicSetTheory.natural_order_greatest_element_condition,
        Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies] at hGreatest
      exact hGreatest subset ⟨power_contains hℳ subset carrier hSubset, hNonempty⟩
  exact (agrees hℳ direction relation subset (linear_asymmetric hℳ relation carrier subset hDef.1 hSubset)
    hExists output).trans (specification_correct (PureStageSemantics.expansion hℳ).model direction output relation subset).symm

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOrderExtrema
