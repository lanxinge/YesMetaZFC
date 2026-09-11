import YesMetaZFC.Model.ZFC.Pure.PureSequenceStage
import YesMetaZFC.Model.ZFC.Pure.PureMappingSpecifications

/-! # 良序上的最小差异点

同域而不同的映射具有非空差异点集。纯公式分离构造此集，原良序定义提供最小元；
线序保证其唯一性。非法输入沿用空集缺省，不给原支撑公理添加前提。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMinimumDifference
open PureModel PureOrderExtrema
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature

abbrev value (ℳ : Structure.{0,0,0,x} S) (function input : Obj ℳ) : Obj ℳ :=
  ℳ.funcInterp .application (.cons function (.cons input .nil))

def MinimumDifference (ℳ : Structure.{0,0,0,x} S)
    (relation carrier first second output : Obj ℳ) : Prop :=
  Mem ℳ output carrier ∧ value ℳ first output ≠ value ℳ second output ∧
    ∀ earlier, Mem ℳ earlier carrier ∧ Edge ℳ relation earlier output →
      value ℳ first earlier = value ℳ second earlier

def specification : Formula S [] [s,s,s,s,s] :=
  Nonlogical.BasicSetTheory.minimum_difference_spec
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar .here)

theorem specification_correct (ℳ : Structure.{0,0,0,x} S)
    (relation carrier first second output : Obj ℳ) :
    specification.satisfies (templateEnv (.cons output (.cons relation (.cons carrier (.cons first (.cons second .nil)))))) ↔
      MinimumDifference ℳ relation carrier first second output := Iff.rfl

theorem specification_eval {ℳ : Structure.{0,0,0,x} S} {bound free : SortContext S}
    (env : Env ℳ bound free) (relation carrier first second output : Term S bound free s) :
    (Nonlogical.BasicSetTheory.minimum_difference_spec relation carrier first second output).satisfies env ↔
      MinimumDifference ℳ (relation.eval env) (carrier.eval env) (first.eval env) (second.eval env) (output.eval env) := by
  simp only [Nonlogical.BasicSetTheory.minimum_difference_spec, Formula.satisfies,
    Nonlogical.BasicSetTheory.membership_formula, Nonlogical.BasicSetTheory.function_application_term,
    Nonlogical.BasicSetTheory.ordered_pair_term, Term.eval, Arguments.eval, Term.eval_weakenBound]
  rfl

def linearCondition : Formula S [] [s,s,s,s,s] :=
  Nonlogical.BasicSetTheory.is_linear_order_formula (.fvar (.there .here)) (.fvar (.there (.there .here)))

def body : Formula ℒ [] [setSort,setSort,setSort,setSort,setSort] :=
  openFormula PureSequenceStage.interpretation (.conj linearCondition specification)

def graph : Formula ℒ [] [setSort,setSort,setSort,setSort,setSort] :=
  _root_.YesMetaZFC.Automation.TotalizedGraph.formula body PureRelationFunctions.emptyFallback

theorem dependencies_covered : formulaCovered PureSequenceStage.functionCovered
    PureNaturalRelations.relationCovered (.conj linearCondition specification) = true := rfl

theorem body_correct {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (relation carrier first second output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons relation (.cons carrier (.cons first (.cons second .nil)))))) ↔
      (PureSequenceStage.expansion hℳ).relation .isLinearOrder (.cons relation (.cons carrier .nil)) ∧
        MinimumDifference (PureSequenceStage.expansion hℳ).model relation carrier first second output := by
  exact (openFormula_correct (PureSequenceStage.expansion hℳ) (PureSequenceStage.realizes hℳ)
    (.conj linearCondition specification)
    (.cons output (.cons relation (.cons carrier (.cons first (.cons second .nil)))))).trans
      (and_congr Iff.rfl (specification_correct (PureSequenceStage.expansion hℳ).model relation carrier first second output))

theorem linear_connex {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {relation carrier : Carrier ℳ}
    (hLinear : (PureSequenceStage.expansion hℳ).relation .isLinearOrder (.cons relation (.cons carrier .nil)))
    {left right : Carrier ℳ} (hLeft : Mem (PureSequenceStage.expansion hℳ).model left carrier)
    (hRight : Mem (PureSequenceStage.expansion hℳ).model right carrier) (hNe : left ≠ right) :
    Edge (PureSequenceStage.expansion hℳ).model relation left right ∨
      Edge (PureSequenceStage.expansion hℳ).model relation right left := by
  classical
  have hConnex := ((PureSequenceStage.round_one_definition_correct hℳ .isLinearOrder
    (.cons relation (.cons carrier .nil))).mp hLinear).2.2.2
  simp only [Nonlogical.BasicSetTheory.linear_order_connex_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies] at hConnex
  by_cases hEdge : Edge (PureSequenceStage.expansion hℳ).model relation left right
  · exact Or.inl hEdge
  · exact Or.inr (hConnex left right ⟨hLeft, hRight⟩ hEdge hNe)

theorem linear_asymmetric {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {relation carrier : Carrier ℳ}
    (hLinear : (PureSequenceStage.expansion hℳ).relation .isLinearOrder (.cons relation (.cons carrier .nil))) :
    Asymmetric (PureSequenceStage.expansion hℳ).model relation carrier := by
  have hDef := (PureSequenceStage.round_one_definition_correct hℳ .isLinearOrder
    (.cons relation (.cons carrier .nil))).mp hLinear
  have hIrrefl := hDef.2.2.1.1
  have hTrans := hDef.2.2.1.2
  simp only [Nonlogical.BasicSetTheory.linear_order_irreflexive_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies] at hIrrefl
  simp only [Nonlogical.BasicSetTheory.linear_order_transitive_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies] at hTrans
  intro left right hLeft hRight hForward hBackward
  exact hIrrefl left hLeft (hTrans left right left ⟨hLeft, hRight, hLeft⟩ ⟨hForward, hBackward⟩)

/-- 最小差异点的唯一性只使用线序，不要求映射或良序。 -/
theorem unique {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {relation carrier first second left right : Carrier ℳ}
    (hLinear : (PureSequenceStage.expansion hℳ).relation .isLinearOrder (.cons relation (.cons carrier .nil)))
    (hLeft : MinimumDifference (PureSequenceStage.expansion hℳ).model relation carrier first second left)
    (hRight : MinimumDifference (PureSequenceStage.expansion hℳ).model relation carrier first second right) : left = right := by
  classical
  by_cases hEqual : left = right
  · exact hEqual
  · rcases linear_connex hℳ hLinear hLeft.1 hRight.1 hEqual with hForward | hBackward
    · exact False.elim (hLeft.2.1 (hRight.2.2 left ⟨hLeft.1, hForward⟩))
    · exact False.elim (hRight.2.1 (hLeft.2.2 right ⟨hRight.1, hBackward⟩))

theorem functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (relation carrier first second : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons relation (.cons carrier (.cons first (.cons second .nil)))))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons relation (.cons carrier (.cons first (.cons second .nil)))))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ body (.cons relation (.cons carrier (.cons first (.cons second .nil))))
  intro left right hLeft hRight
  have hL := (body_correct hℳ relation carrier first second left).mp hLeft
  have hR := (body_correct hℳ relation carrier first second right).mp hRight
  exact unique hℳ hL.1 hL.2 hR.2

theorem mapping_correct {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (function source target : Carrier ℳ) :
    (PureSequenceStage.expansion hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil))) ↔
      PureMappingDefinitions.IsMapping ℳ function source target := by
  exact ((PureSequenceStage.realizes hℳ).relation .isMapping
    (.cons function (.cons source (.cons target .nil)))).symm.trans
      (PureMappingDefinitions.isMapping_correct function source target)

/-- 所选扩张的求值在映射的定义域内等于实际函数图取值。 -/
theorem application_member {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {function source target input : Carrier ℳ}
    (hMapping : PureMappingDefinitions.IsMapping ℳ function source target)
    (hInput : membership ℳ input source) :
    PureKuratowski.PairMember ℳ input (value (PureSequenceStage.expansion hℳ).model function input) function := by
  exact (PureRelationFunctions.application_spec hMapping.1 ((hMapping.2.1 input).mp hInput) _).mp
    (((PureSequenceStage.realizes hℳ).function .application (.cons function (.cons input .nil)) _).mpr rfl)

/-- 不同的同域映射不能在定义域内处处相等。 -/
theorem difference_exists {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {first second source target : Carrier ℳ}
    (hFirst : PureMappingDefinitions.IsMapping ℳ first source target)
    (hSecond : PureMappingDefinitions.IsMapping ℳ second source target) (hNe : first ≠ second) :
    ∃ input, membership ℳ input source ∧
      value (PureSequenceStage.expansion hℳ).model first input ≠ value (PureSequenceStage.expansion hℳ).model second input := by
  classical
  by_cases hExists : ∃ input, membership ℳ input source ∧
      value (PureSequenceStage.expansion hℳ).model first input ≠ value (PureSequenceStage.expansion hℳ).model second input
  · exact hExists
  · apply False.elim
    apply hNe (PureMappingSpecifications.mapping_ext hℳ hFirst hSecond ?_)
    intro input hInput
    have hEqual : value (PureSequenceStage.expansion hℳ).model first input =
        value (PureSequenceStage.expansion hℳ).model second input := by
      by_cases hEqual : value (PureSequenceStage.expansion hℳ).model first input =
          value (PureSequenceStage.expansion hℳ).model second input
      · exact hEqual
      · exact False.elim (hExists ⟨input, hInput, hEqual⟩)
    exact ⟨_, application_member hℳ hFirst hInput, hEqual.symm ▸ application_member hℳ hSecond hInput⟩

def differenceCondition : Formula S [] [s,s,s] :=
  .neg (.equal
    (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there .here)) (.fvar .here))
    (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there (.there .here))) (.fvar .here)))

/-- 差异点集由裸 ZFC 的分离公理产生。 -/
theorem difference_set_exists {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (carrier first second : Carrier ℳ) :
    ∃ subset, ∀ input, membership ℳ input subset ↔ membership ℳ input carrier ∧
      value (PureSequenceStage.expansion hℳ).model first input ≠ value (PureSequenceStage.expansion hℳ).model second input := by
  obtain ⟨subset, hSubset⟩ := PureSeparation.exists_subset hℳ
    (openFormula PureSequenceStage.interpretation differenceCondition) (.cons first (.cons second .nil)) carrier
  refine ⟨subset, fun input => (hSubset input).trans (and_congr Iff.rfl ?_)⟩
  exact openFormula_correct (PureSequenceStage.expansion hℳ) (PureSequenceStage.realizes hℳ)
    differenceCondition (.cons input (.cons first (.cons second .nil)))

/-- 原良序与不同映射 guard 足以推出最小差异点存在。 -/
theorem exists_of_guard {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {relation carrier target first second : Carrier ℳ}
    (hOrder : (PureSequenceStage.expansion hℳ).relation .isWellOrder (.cons relation (.cons carrier .nil)))
    (hFirst : (PureSequenceStage.expansion hℳ).relation .isMapping (.cons first (.cons carrier (.cons target .nil))))
    (hSecond : (PureSequenceStage.expansion hℳ).relation .isMapping (.cons second (.cons carrier (.cons target .nil))))
    (hNe : first ≠ second) :
    ∃ output, MinimumDifference (PureSequenceStage.expansion hℳ).model relation carrier first second output := by
  classical
  obtain ⟨input, hInput, hDifferent⟩ := difference_exists hℳ
    ((mapping_correct hℳ first carrier target).mp hFirst) ((mapping_correct hℳ second carrier target).mp hSecond) hNe
  obtain ⟨subset, hSubset⟩ := difference_set_exists hℳ carrier first second
  have hNonempty : subset ≠ (PureSequenceStage.expansion hℳ).function .emptySet .nil := by
    intro hEmpty
    have hGraph := ((PureSequenceStage.realizes hℳ).function .emptySet .nil _).mpr rfl
    exact ((PureFunctionDefinitions.empty_correct _).mp hGraph input)
      (hEmpty ▸ (hSubset input).mpr ⟨hInput, hDifferent⟩)
  have hPower : Mem (PureSequenceStage.expansion hℳ).model subset
      ((PureSequenceStage.expansion hℳ).function .powerSet (.cons carrier .nil)) := by
    have hGraph := ((PureSequenceStage.realizes hℳ).function .powerSet (.cons carrier .nil) _).mpr rfl
    have hContains := (PureFunctionDefinitions.comprehension_correct _ _ _).mp hGraph
    change ∀ element, membership ℳ element ((PureSequenceStage.expansion hℳ).function .powerSet (.cons carrier .nil)) ↔
      ∀ member, membership ℳ member element → membership ℳ member carrier at hContains
    exact (hContains subset).mpr (fun member hMember => ((hSubset member).mp hMember).1)
  have hDef := (PureSequenceStage.round_one_definition_correct hℳ .isWellOrder
    (.cons relation (.cons carrier .nil))).mp hOrder
  have hLeast := hDef.2
  simp only [Nonlogical.BasicSetTheory.natural_order_least_element_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies_existsFreeTop, Formula.satisfies] at hLeast
  obtain ⟨output, hOutput⟩ : ∃ output, Extreme (PureSequenceStage.expansion hℳ).model .minimum relation subset output :=
    hLeast subset ⟨hPower, hNonempty⟩
  have hOutputCondition := (hSubset output).mp hOutput.1
  refine ⟨output, hOutputCondition.1, hOutputCondition.2, ?_⟩
  intro earlier hEarlier
  by_cases hEqual : value (PureSequenceStage.expansion hℳ).model first earlier =
      value (PureSequenceStage.expansion hℳ).model second earlier
  · exact hEqual
  · have hEarlierSubset := (hSubset earlier).mpr ⟨hEarlier.1, hEqual⟩
    by_cases hSame : output = earlier
    · subst earlier
      exact False.elim (linear_asymmetric hℳ hDef.1 output output hOutputCondition.1 hOutputCondition.1 hEarlier.2 hEarlier.2)
    · exact False.elim (linear_asymmetric hℳ hDef.1 earlier output hEarlier.1 hOutputCondition.1
        hEarlier.2 (hOutput.2 earlier hEarlierSubset hSame))

/-- 合法输入上，总化图逐输出等价于原最小差异点规格。 -/
theorem agrees {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {relation carrier target first second : Carrier ℳ}
    (hOrder : (PureSequenceStage.expansion hℳ).relation .isWellOrder (.cons relation (.cons carrier .nil)))
    (hFirst : (PureSequenceStage.expansion hℳ).relation .isMapping (.cons first (.cons carrier (.cons target .nil))))
    (hSecond : (PureSequenceStage.expansion hℳ).relation .isMapping (.cons second (.cons carrier (.cons target .nil))))
    (hNe : first ≠ second) (output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons relation (.cons carrier (.cons first (.cons second .nil)))))) ↔
      specification.satisfies (templateEnv (.cons output (.cons relation (.cons carrier (.cons first (.cons second .nil))))) :
        Env (PureSequenceStage.expansion hℳ).model [] [s,s,s,s,s]) := by
  obtain ⟨witness, hWitness⟩ := exists_of_guard hℳ hOrder hFirst hSecond hNe
  have hLinear := ((PureSequenceStage.round_one_definition_correct hℳ .isWellOrder
    (.cons relation (.cons carrier .nil))).mp hOrder).1
  exact (PureRelationFunctions.totalized_agrees body (.cons relation (.cons carrier (.cons first (.cons second .nil))))
    ⟨witness, (body_correct hℳ relation carrier first second witness).mpr ⟨hLinear, hWitness⟩⟩ output).trans
      ((body_correct hℳ relation carrier first second output).trans
        (Iff.trans ⟨And.right, fun h => ⟨hLinear, h⟩⟩ (specification_correct (PureSequenceStage.expansion hℳ).model relation carrier first second output).symm))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMinimumDifference
