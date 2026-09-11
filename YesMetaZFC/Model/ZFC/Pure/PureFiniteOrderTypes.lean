import YesMetaZFC.Model.ZFC.Pure.PureOrderSemantics

/-! # 自然离散线序的有限坍缩

序同构到序数的任意双射都是规范坍缩函数；所有非空子集有最大元时，
坍缩值域不能包含 ω，因而是模型内部自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteOrderTypes
open PureModel PureNaturalInduction PureOrderSemantics PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

def Iso (hℳ : Theory.Models ℳ theory) (relation carrier ordinal function : Carrier ℳ) : Prop :=
  (Project.FirstOrderSemantics.reduct ℳ).IsSetBijectionFromTo (PureKuratowskiProject.interpretation hℳ) function carrier ordinal ∧
    ∀ left right, membership ℳ left carrier → membership ℳ right carrier →
      (PureKuratowski.PairMember ℳ left right relation ↔ membership ℳ (value hℳ function left) (value hℳ function right))

theorem iso_function_correct (hℳ : Theory.Models ℳ theory) {relation carrier ordinal : Carrier ℳ}
    (hLinear : Linear relation carrier) (hOrdinal : (Project.FirstOrderSemantics.reduct ℳ).IsOrdinal ordinal) (function : Carrier ℳ) :
    (E hℳ).relation .isOrderIsomorphism (.cons function (.cons relation (.cons carrier (.cons (epsilon hℳ ordinal) (.cons ordinal .nil))))) ↔
      Iso hℳ relation carrier ordinal function := by
  rw [PureNaturalDifferenceStage.round_one_definition_correct hℳ .isOrderIsomorphism]
  simp only [PureRoundOneRelations.condition,Nonlogical.BasicSetTheory.is_order_isomorphism_condition,
    Nonlogical.BasicSetTheory.order_preservation_condition,Formula.satisfies_forallFreeTop,Formula.satisfies]
  change ((E hℳ).relation .isLinearOrder (.cons relation (.cons carrier .nil)) ∧
    ((E hℳ).relation .isLinearOrder (.cons (epsilon hℳ ordinal) (.cons ordinal .nil)) ∧
      (E hℳ).relation .isBijection (.cons function (.cons carrier (.cons ordinal .nil)))) ∧
    ∀ left right, membership ℳ left carrier ∧ membership ℳ right carrier →
      (membership ℳ ((E hℳ).function .orderedPair (.cons left (.cons right .nil))) relation ↔
        membership ℳ ((E hℳ).function .orderedPair
          (.cons ((E hℳ).function .application (.cons function (.cons left .nil)))
            (.cons ((E hℳ).function .application (.cons function (.cons right .nil))) .nil))) (epsilon hℳ ordinal))) ↔ _
  simp only [linear_correct hℳ,bijection_correct hℳ,edge_correct hℳ,value_eq hℳ,epsilon_correct hℳ]
  have hTarget := epsilon_linear hℳ hOrdinal (fun input hInput => hInput)
  constructor
  · rintro ⟨_,⟨_,hBij⟩,hPreserve⟩
    exact ⟨hBij,fun left right hLeft hRight => (hPreserve left right ⟨hLeft,hRight⟩).trans
      ⟨fun h => h.2.2,fun h => ⟨value_mem hℳ hBij.1.1 hLeft,value_mem hℳ hBij.1.1 hRight,h⟩⟩⟩
  · rintro ⟨hBij,hPreserve⟩
    exact ⟨hLinear,⟨hTarget,hBij⟩,fun left right hMem => (hPreserve left right hMem.1 hMem.2).trans
      ⟨fun h => ⟨value_mem hℳ hBij.1.1 hMem.1,value_mem hℳ hBij.1.1 hMem.2,h⟩,fun h => h.2.2⟩⟩

theorem isomorphic_correct (hℳ : Theory.Models ℳ theory) {relation carrier ordinal : Carrier ℳ}
    (hLinear : Linear relation carrier) (hOrdinal : (Project.FirstOrderSemantics.reduct ℳ).IsOrdinal ordinal) :
    (E hℳ).relation .isOrderIsomorphic (.cons relation (.cons carrier (.cons (epsilon hℳ ordinal) (.cons ordinal .nil)))) ↔
      ∃ function, Iso hℳ relation carrier ordinal function := by
  rw [PureNaturalDifferenceStage.round_one_definition_correct hℳ .isOrderIsomorphic]
  simp only [PureRoundOneRelations.condition,Nonlogical.BasicSetTheory.is_order_isomorphic_condition,Formula.satisfies_existsFreeTop,Formula.satisfies]
  exact exists_congr (fun function => iso_function_correct hℳ hLinear hOrdinal function)

theorem pair_preserves (hℳ : Theory.Models ℳ theory) {relation carrier ordinal function left right leftValue rightValue : Carrier ℳ}
    (hIso : Iso hℳ relation carrier ordinal function)
    (hLeft : PureKuratowski.PairMember ℳ left leftValue function) (hRight : PureKuratowski.PairMember ℳ right rightValue function) :
    PureKuratowski.PairMember ℳ left right relation ↔ membership ℳ leftValue rightValue := by
  have hLeftIn := (hIso.1.1.1.2.1 left).mpr ⟨leftValue,hLeft⟩
  have hRightIn := (hIso.1.1.1.2.1 right).mpr ⟨rightValue,hRight⟩
  have hLV := hIso.1.1.1.1.2 left leftValue _ hLeft (application_member hℳ hIso.1.1.1 hLeftIn)
  have hRV := hIso.1.1.1.1.2 right rightValue _ hRight (application_member hℳ hIso.1.1.1 hRightIn)
  exact (hIso.2 left right hLeftIn hRightIn).trans (by rw [hLV,hRV])

/-- 任意到序数的原序同构都给出同一个规范坍缩值域。 -/
theorem iso_type (hℳ : Theory.Models ℳ theory) {relation carrier ordinal function : Carrier ℳ}
    (hOrdinal : (Project.FirstOrderSemantics.reduct ℳ).IsOrdinal ordinal) (hIso : Iso hℳ relation carrier ordinal function) :
    (Project.FirstOrderSemantics.reduct ℳ).IsWellOrderType (PureKuratowskiProject.interpretation hℳ) relation carrier ordinal := by
  refine ⟨function,⟨hIso.1.1.1.1,hIso.1.1.1.2.1,
    _root_.YesMetaZFC.SetTheory.Structure.IsRelationInitialSegment.refl (PureKuratowskiProject.interpretation hℳ) relation carrier,?_⟩,?_⟩
  · intro current hCurrent output hOutput member
    constructor
    · intro hMember
      have hOutputIn := hIso.1.1.1.output_mem_of_pairMember hOutput
      obtain ⟨previous,hPrevious,hPair⟩ := hIso.1.2 member (hOrdinal.transitive output hOutputIn member hMember)
      exact ⟨previous,hPrevious,(pair_preserves hℳ hIso hPair hOutput).mpr hMember,hPair⟩
    · rintro ⟨previous,_,hEdge,hPair⟩
      exact (pair_preserves hℳ hIso hPair hOutput).mp hEdge
  · intro output
    constructor
    · intro hOutput
      obtain ⟨input,_,hPair⟩ := hIso.1.2 output hOutput
      exact ⟨input,hPair⟩
    · rintro ⟨input,hPair⟩
      exact hIso.1.1.1.output_mem_of_pairMember hPair

theorem collapse_iso (hℳ : Theory.Models ℳ theory) {relation carrier ordinal function : Carrier ℳ}
    (hOrder : (Project.FirstOrderSemantics.reduct ℳ).IsSetCodedWellOrder (PureKuratowskiProject.interpretation hℳ) relation carrier)
    (hFunction : (Project.FirstOrderSemantics.reduct ℳ).IsWellOrderCollapseFunction (PureKuratowskiProject.interpretation hℳ) function relation carrier carrier)
    (hRange : (Project.FirstOrderSemantics.reduct ℳ).IsRangeOf (PureKuratowskiProject.interpretation hℳ) ordinal function) :
    Iso hℳ relation carrier ordinal function := by
  have hMap : PureMappingDefinitions.IsMapping ℳ function carrier ordinal := by
    refine ⟨hFunction.1,hFunction.2.1,?_⟩
    intro input hInput
    obtain ⟨output,hPair⟩ := (hFunction.2.1 input).mp hInput
    exact ⟨output,(hRange output).mpr ⟨input,hPair⟩,hPair⟩
  refine ⟨⟨⟨hMap,hFunction.isSetInjective (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hOrder⟩,?_⟩,?_⟩
  · intro output hOutput
    obtain ⟨input,hPair⟩ := (hRange output).mp hOutput
    exact ⟨input,(hFunction.2.1 input).mpr ⟨output,hPair⟩,hPair⟩
  · intro left right hLeft hRight
    exact hFunction.relation_iff_mem (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hOrder
      (application_member hℳ hMap hLeft) (application_member hℳ hMap hRight)

def preimageCondition : Formula S [] [s,s,s] := Nonlogical.BasicSetTheory.membership_formula
  (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there .here)) (.fvar .here)) (.fvar (.there (.there .here)))

/-- 每个非空子集有最大元，故坍缩序型不能包含内部 ω。 -/
theorem type_natural (hℳ : Theory.Models ℳ theory) {relation carrier ordinal function : Carrier ℳ}
    (hOrdinal : (Project.FirstOrderSemantics.reduct ℳ).IsOrdinal ordinal)
    (hIso : Iso hℳ relation carrier ordinal function) (hGreatest : Extremes relation carrier true) : membership ℳ ordinal (omega hℳ) := by
  classical
  by_cases hNatural : membership ℳ ordinal (omega hℳ)
  · exact hNatural
  · have hOmegaSubset : ∀ input, membership ℳ input (omega hℳ) → membership ℳ input ordinal := by
      rcases _root_.YesMetaZFC.SetTheory.Structure.IsOrdinal.trichotomy (project_models hℳ).1 hOrdinal
        ((omega_project hℳ).isOrdinal (project_modelsZF hℳ))
        (_root_.YesMetaZFC.SetTheory.KP.difference_exists_d (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ)))
        (_root_.YesMetaZFC.SetTheory.KP.intersection_exists_d (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ)) ordinal (omega hℳ)) with hSame | hLess | hGreater
      · exact fun input hInput => (hSame input).mpr hInput
      · exact False.elim (hNatural hLess)
      · exact fun input hInput => hOrdinal.transitive (omega hℳ) hGreater input hInput
    obtain ⟨preimage,hPreimage⟩ := PureSeparation.exists_subset hℳ
      (openFormula PureNaturalDifferenceStage.interpretation preimageCondition)
      (.cons function (.cons (omega hℳ) .nil)) carrier
    have hP (input : Carrier ℳ) : membership ℳ input preimage ↔ membership ℳ input carrier ∧ membership ℳ (value hℳ function input) (omega hℳ) := by
      apply (hPreimage input).trans
      apply and_congr Iff.rfl
      exact (openFormula_correct (E hℳ) (PureNaturalDifferenceStage.realizes hℳ) preimageCondition
        (.cons input (.cons function (.cons (omega hℳ) .nil)))).trans (by change membership ℳ ((E hℳ).function .application (.cons function (.cons input .nil))) (omega hℳ) ↔ _; rw [value_eq hℳ])
    obtain ⟨zeroInput,hZeroInput,hZeroPair⟩ := hIso.1.2 (zero hℳ) (hOmegaSubset _ (zero_mem hℳ))
    have hZeroValue := hIso.1.1.1.1.2 zeroInput (zero hℳ) _ hZeroPair (application_member hℳ hIso.1.1.1 hZeroInput)
    obtain ⟨maximum,hMaximum,hMaximal⟩ := hGreatest preimage (fun input h => ((hP input).mp h).1)
      ⟨zeroInput,(hP zeroInput).mpr ⟨hZeroInput,hZeroValue ▸ zero_mem hℳ⟩⟩
    have hMaxIn := (hP maximum).mp hMaximum
    have hNext := succ_mem hℳ hMaxIn.2
    obtain ⟨nextInput,hNextInput,hNextPair⟩ := hIso.1.2 (succ hℳ (value hℳ function maximum)) (hOmegaSubset _ hNext)
    have hNextValue := hIso.1.1.1.1.2 nextInput _ _ hNextPair (application_member hℳ hIso.1.1.1 hNextInput)
    have hNextP := (hP nextInput).mpr ⟨hNextInput,hNextValue ▸ hNext⟩
    have hSelfMember := (succ_spec hℳ (value hℳ function maximum) _).mpr (Or.inr rfl)
    have hMaxOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) _ hMaxIn.2
    by_cases hEqual : maximum = nextInput
    · have hEqualValue : succ hℳ (value hℳ function maximum) = value hℳ function maximum := hNextValue.trans (congrArg (value hℳ function) hEqual.symm)
      have hSelf : membership ℳ (value hℳ function maximum) (value hℳ function maximum) :=
        (congrArg (membership ℳ (value hℳ function maximum)) hEqualValue).mp hSelfMember
      exact False.elim (hMaxOrdinal.wellOrder.linear.irrefl _ hSelf hSelf)
    · have hEdge := hMaximal nextInput hNextP hEqual
      have hMember := (pair_preserves hℳ hIso hNextPair (application_member hℳ hIso.1.1.1 hMaxIn.1)).mp hEdge
      have hSelf := hMaxOrdinal.transitive _ hMember _ hSelfMember
      exact False.elim (hMaxOrdinal.wellOrder.linear.irrefl _ hSelf hSelf)

theorem natural_type_exists (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ}
    (hLinear : Linear relation carrier) (hLeast : Extremes relation carrier false) (hGreatest : Extremes relation carrier true) :
    ∃ ordinal, membership ℳ ordinal (omega hℳ) ∧ ∃ function, Iso hℳ relation carrier ordinal function := by
  have hOrder := well_order hℳ hLinear hLeast
  obtain ⟨ordinal,hType,_⟩ := _root_.YesMetaZFC.SetTheory.ZF.wellOrderType_existsUnique (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hOrder
  have hOrdinal := hType.isOrdinal (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hOrder
  obtain ⟨function,hFunction,hRange⟩ := hType
  have hIso := collapse_iso hℳ hOrder hFunction hRange
  exact ⟨ordinal,type_natural hℳ hOrdinal hIso hGreatest,function,hIso⟩

theorem natural_type_unique (hℳ : Theory.Models ℳ theory) {relation carrier first second f g : Carrier ℳ}
    (hLinear : Linear relation carrier) (hLeast : Extremes relation carrier false)
    (hFirst : membership ℳ first (omega hℳ)) (hSecond : membership ℳ second (omega hℳ))
    (hF : Iso hℳ relation carrier first f) (hG : Iso hℳ relation carrier second g) : first = second := by
  obtain ⟨_,_,hUnique⟩ := _root_.YesMetaZFC.SetTheory.ZF.wellOrderType_existsUnique (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (well_order hℳ hLinear hLeast)
  exact (hUnique first (iso_type hℳ ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) first hFirst) hF)).trans
    (hUnique second (iso_type hℳ ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) second hSecond) hG)).symm

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFiniteOrderTypes
