import YesMetaZFC.Model.ZFC.Pure.PureNaturalDifferenceStage
import YesMetaZFC.SetTheory.Ord.OrderType

/-! # 原序关系与集合编码序的语义桥

固定当前纯扩张及 Kuratowski 解释，将原线序、双射、序同构逐项接入 Project 集合模型。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOrderSemantics
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureNaturalDifferenceStage.expansion hℳ
noncomputable abbrev epsilon (hℳ : Theory.Models ℳ theory) (carrier : Carrier ℳ) := (E hℳ).function .membershipRelation (.cons carrier .nil)
noncomputable abbrev domain (hℳ : Theory.Models ℳ theory) (function : Carrier ℳ) := (E hℳ).function .domain (.cons function .nil)
noncomputable abbrev range (hℳ : Theory.Models ℳ theory) (function : Carrier ℳ) := (E hℳ).function .range (.cons function .nil)

theorem value_eq (hℳ : Theory.Models ℳ theory) (function input : Carrier ℳ) :
    (E hℳ).function .application (.cons function (.cons input .nil)) = value hℳ function input :=
  PureNaturalDifferenceStage.function_from_difference hℳ .application rfl _
theorem zero_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .emptySet .nil = zero hℳ :=
  PureNaturalDifferenceStage.function_from_difference hℳ .emptySet rfl _
theorem omega_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .omega .nil = omega hℳ :=
  PureNaturalDifferenceStage.function_from_difference hℳ .omega rfl _

theorem edge_correct (hℳ : Theory.Models ℳ theory) (relation left right : Carrier ℳ) :
    membership ℳ ((E hℳ).function .orderedPair (.cons left (.cons right .nil))) relation ↔
      PureKuratowski.PairMember ℳ left right relation := by
  have hCode := (PureRelationDefinitions.orderedPair_correct _ left right).mp
    (((PureNaturalDifferenceStage.realizes hℳ).function .orderedPair (.cons left (.cons right .nil)) _).mpr rfl)
  exact ⟨fun h => ⟨_,hCode,h⟩,fun ⟨pair,hPair,hMem⟩ => (PureKuratowski.code_unique hℳ hPair hCode) ▸ hMem⟩

theorem function_correct (hℳ : Theory.Models ℳ theory) (function : Carrier ℳ) :
    (E hℳ).relation .isFunction (.cons function .nil) ↔ PureKuratowski.IsFunction ℳ function :=
  ((PureNaturalDifferenceStage.realizes hℳ).relation .isFunction _).symm.trans
    (PureRelationDefinitions.isFunction_satisfies (templateEnv (.cons function .nil)) (.fvar .here))
theorem relation_correct (hℳ : Theory.Models ℳ theory) (relation : Carrier ℳ) :
    (E hℳ).relation .isRelation (.cons relation .nil) ↔ PureKuratowski.IsRelation ℳ relation :=
  ((PureNaturalDifferenceStage.realizes hℳ).relation .isRelation _).symm.trans
    (PureRelationDefinitions.isRelation_satisfies (templateEnv (.cons relation .nil)) (.fvar .here))
theorem mapping_correct (hℳ : Theory.Models ℳ theory) (function source target : Carrier ℳ) :
    (E hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil))) ↔ PureMappingDefinitions.IsMapping ℳ function source target :=
  ((PureNaturalDifferenceStage.realizes hℳ).relation .isMapping _).symm.trans (PureMappingDefinitions.isMapping_correct function source target)
theorem domain_correct (hℳ : Theory.Models ℳ theory) (function input : Carrier ℳ) :
    membership ℳ input (domain hℳ function) ↔ ∃ output, PureKuratowski.PairMember ℳ input output function :=
  (PureRelationCoordinates.domain_correct _ function).mp (((PureNaturalDifferenceStage.realizes hℳ).function .domain (.cons function .nil) _).mpr rfl) input
theorem range_correct (hℳ : Theory.Models ℳ theory) (function output : Carrier ℳ) :
    membership ℳ output (range hℳ function) ↔ ∃ input, PureKuratowski.PairMember ℳ input output function :=
  (PureRelationCoordinates.range_correct _ function).mp (((PureNaturalDifferenceStage.realizes hℳ).function .range (.cons function .nil) _).mpr rfl) output

theorem value_mem (hℳ : Theory.Models ℳ theory) {function source target input : Carrier ℳ}
    (hMap : PureMappingDefinitions.IsMapping ℳ function source target) (hInput : membership ℳ input source) :
    membership ℳ (value hℳ function input) target := by
  obtain ⟨output,hOutput,hPair⟩ := hMap.2.2 input hInput
  exact (hMap.1.2 input output _ hPair (application_member hℳ hMap hInput)) ▸ hOutput

theorem bijection_correct (hℳ : Theory.Models ℳ theory) (function source target : Carrier ℳ) :
    (E hℳ).relation .isBijection (.cons function (.cons source (.cons target .nil))) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsSetBijectionFromTo (PureKuratowskiProject.interpretation hℳ) function source target := by
  rw [PureNaturalDifferenceStage.round_one_definition_correct hℳ .isBijection]
  change ((E hℳ).relation .isInjective (.cons function (.cons source (.cons target .nil))) ∧
    (E hℳ).relation .isSurjective (.cons function (.cons source (.cons target .nil)))) ↔ _
  rw [PureNaturalDifferenceStage.round_one_definition_correct hℳ .isInjective,
    PureNaturalDifferenceStage.round_one_definition_correct hℳ .isSurjective]
  simp only [PureRoundOneRelations.condition,Nonlogical.BasicSetTheory.is_injective_condition,
    Nonlogical.BasicSetTheory.injectivity_condition,Nonlogical.BasicSetTheory.is_surjective_condition,
    Formula.satisfies_forallFreeTop,Formula.satisfies]
  change (((E hℳ).relation .isMapping (.cons function (.cons source (.cons target .nil))) ∧
      (∀ first second output, membership ℳ ((E hℳ).function .orderedPair (.cons first (.cons output .nil))) function ∧
        membership ℳ ((E hℳ).function .orderedPair (.cons second (.cons output .nil))) function → first = second)) ∧
    (E hℳ).relation .isFunction (.cons function .nil) ∧ source = domain hℳ function ∧ target = range hℳ function) ↔ _
  simp only [mapping_correct hℳ,edge_correct hℳ,function_correct hℳ]
  constructor
  · rintro ⟨⟨hMap,hInject⟩,_,_,hRange⟩
    refine ⟨⟨hMap,fun first second output hFirst hSecond => hInject first second output ⟨hFirst,hSecond⟩⟩,?_⟩
    intro output hOutput
    obtain ⟨input,hPair⟩ := (range_correct hℳ function output).mp (hRange ▸ hOutput)
    exact ⟨input,(hMap.2.1 input).mpr ⟨output,hPair⟩,hPair⟩
  · rintro ⟨⟨hMap,hInject⟩,hSurject⟩
    refine ⟨⟨hMap,fun first second output h => hInject first second output h.1 h.2⟩,hMap.1,?_,?_⟩
    · exact extensionality hℳ source _ (fun input => (hMap.2.1 input).trans (domain_correct hℳ function input).symm)
    · apply extensionality hℳ target _
      intro output
      rw [range_correct]
      constructor
      · intro hOutput
        obtain ⟨input,_,hPair⟩ := hSurject output hOutput
        exact ⟨input,hPair⟩
      · rintro ⟨input,hPair⟩
        obtain ⟨other,hOther,hOtherPair⟩ := hMap.2.2 input ((hMap.2.1 input).mpr ⟨output,hPair⟩)
        exact (hMap.1.2 input other output hOtherPair hPair) ▸ hOther

/-- 原线序的逐点条件；保留其额外的载体限制。 -/
def Linear (relation carrier : Carrier ℳ) : Prop :=
  PureKuratowski.IsRelation ℳ relation ∧
    (∀ left right, PureKuratowski.PairMember ℳ left right relation → membership ℳ left carrier ∧ membership ℳ right carrier) ∧
      (∀ input, membership ℳ input carrier → ¬ PureKuratowski.PairMember ℳ input input relation) ∧
        (∀ left middle right, membership ℳ left carrier → membership ℳ middle carrier → membership ℳ right carrier →
          PureKuratowski.PairMember ℳ left middle relation → PureKuratowski.PairMember ℳ middle right relation → PureKuratowski.PairMember ℳ left right relation) ∧
          ∀ left right, membership ℳ left carrier → membership ℳ right carrier → left = right ∨
            PureKuratowski.PairMember ℳ left right relation ∨ PureKuratowski.PairMember ℳ right left relation

theorem linear_correct (hℳ : Theory.Models ℳ theory) (relation carrier : Carrier ℳ) :
    (E hℳ).relation .isLinearOrder (.cons relation (.cons carrier .nil)) ↔ Linear relation carrier := by
  classical
  rw [PureNaturalDifferenceStage.round_one_definition_correct hℳ .isLinearOrder]
  simp only [PureRoundOneRelations.condition,Nonlogical.BasicSetTheory.is_linear_order_condition,
    Nonlogical.BasicSetTheory.linear_order_irreflexive_condition,Nonlogical.BasicSetTheory.linear_order_transitive_condition,
    Nonlogical.BasicSetTheory.linear_order_connex_condition,Formula.satisfies_forallFreeTop,Formula.satisfies]
  change ((E hℳ).relation .isRelation (.cons relation .nil) ∧
    (∀ pair, membership ℳ pair relation → membership ℳ pair ((E hℳ).function .cartesianProduct (.cons carrier (.cons carrier .nil)))) ∧
    ((∀ input, membership ℳ input carrier → ¬ membership ℳ ((E hℳ).function .orderedPair (.cons input (.cons input .nil))) relation) ∧
    (∀ left middle right, membership ℳ left carrier ∧ membership ℳ middle carrier ∧ membership ℳ right carrier →
      membership ℳ ((E hℳ).function .orderedPair (.cons left (.cons middle .nil))) relation ∧
      membership ℳ ((E hℳ).function .orderedPair (.cons middle (.cons right .nil))) relation →
      membership ℳ ((E hℳ).function .orderedPair (.cons left (.cons right .nil))) relation)) ∧
    ∀ left right, membership ℳ left carrier ∧ membership ℳ right carrier →
      ¬ membership ℳ ((E hℳ).function .orderedPair (.cons left (.cons right .nil))) relation → left ≠ right →
        membership ℳ ((E hℳ).function .orderedPair (.cons right (.cons left .nil))) relation) ↔ _
  simp only [relation_correct hℳ,edge_correct hℳ]
  have hProduct := (PureMappingDefinitions.cartesian_correct _ carrier carrier).mp
    (((PureNaturalDifferenceStage.realizes hℳ).function .cartesianProduct (.cons carrier (.cons carrier .nil)) _).mpr rfl)
  constructor
  · rintro ⟨hRelation,hBound,⟨hIrrefl,hTrans⟩,hCompare⟩
    refine ⟨hRelation,?_,hIrrefl,fun a b c ha hb hc hab hbc => hTrans a b c ⟨ha,hb,hc⟩ ⟨hab,hbc⟩,?_⟩
    · rintro left right ⟨pair,hCode,hPair⟩
      obtain ⟨a,ha,b,hb,hAB⟩ := (hProduct pair).mp (hBound pair hPair)
      have hEqual := PureKuratowski.code_injective hCode hAB
      exact ⟨hEqual.1.symm ▸ ha,hEqual.2.symm ▸ hb⟩
    · intro left right hLeft hRight
      by_cases hEqual : left = right
      · exact Or.inl hEqual
      · by_cases hEdge : PureKuratowski.PairMember ℳ left right relation
        · exact Or.inr (Or.inl hEdge)
        · exact Or.inr (Or.inr (hCompare left right ⟨hLeft,hRight⟩ hEdge hEqual))
  · rintro ⟨hRelation,hBound,hIrrefl,hTrans,hCompare⟩
    refine ⟨hRelation,?_,⟨hIrrefl,fun a b c h hEdge => hTrans a b c h.1 h.2.1 h.2.2 hEdge.1 hEdge.2⟩,?_⟩
    · intro pair hPair
      obtain ⟨left,right,hCode⟩ := hRelation pair hPair
      have hB := hBound left right ⟨pair,hCode,hPair⟩
      exact (hProduct pair).mpr ⟨left,hB.1,right,hB.2,hCode⟩
    · intro left right hMem hNo hNe
      rcases hCompare left right hMem.1 hMem.2 with hEqual | hEdge | hEdge
      · exact False.elim (hNe hEqual)
      · exact False.elim (hNo hEdge)
      · exact hEdge

theorem linear_project (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ} (hLinear : Linear relation carrier) :
    (Project.FirstOrderSemantics.reduct ℳ).IsSetCodedLinearOrder (PureKuratowskiProject.interpretation hℳ) relation carrier := by
  refine ⟨hLinear.1,⟨hLinear.2.2.1,fun a ha b hb c hc => hLinear.2.2.2.1 a b c ha hb hc⟩,?_⟩
  intro left hLeft right hRight
  rcases hLinear.2.2.2.2 left right hLeft hRight with hEqual | hLess | hGreater
  · exact Or.inl (hEqual ▸ (fun _ => Iff.rfl))
  · exact Or.inr (Or.inl hLess)
  · exact Or.inr (Or.inr hGreater)


/-- 所选成员关系的全部成员都使用给定载体。 -/
theorem epsilon_members (hℳ : Theory.Models ℳ theory) (carrier pair : Carrier ℳ) :
    membership ℳ pair (epsilon hℳ carrier) ↔ PureRelationSetOperations.membershipRelationMember ℳ carrier pair :=
  (PureRelationSetOperations.membershipRelation_correct hℳ _ carrier).mp
    (((PureNaturalDifferenceStage.realizes hℳ).function .membershipRelation (.cons carrier .nil) _).mpr rfl) pair

theorem epsilon_correct (hℳ : Theory.Models ℳ theory) (carrier left right : Carrier ℳ) :
    PureKuratowski.PairMember ℳ left right (epsilon hℳ carrier) ↔
      membership ℳ left carrier ∧ membership ℳ right carrier ∧ membership ℳ left right := by
  constructor
  · rintro ⟨pair,hCode,hPair⟩
    obtain ⟨a,b,ha,hb,hAB,hab⟩ := (epsilon_members hℳ carrier pair).mp hPair
    have hEq := PureKuratowski.code_injective hCode hAB
    exact ⟨hEq.1.symm ▸ ha,hEq.2.symm ▸ hb,hEq.1.symm ▸ hEq.2.symm ▸ hab⟩
  · rintro ⟨hLeft,hRight,hEdge⟩
    obtain ⟨pair,hCode⟩ := PureKuratowski.exists_code hℳ left right
    exact ⟨pair,hCode,(epsilon_members hℳ carrier pair).mpr ⟨left,right,hLeft,hRight,hCode,hEdge⟩⟩

theorem epsilon_linear (hℳ : Theory.Models ℳ theory) {carrier ordinal : Carrier ℳ}
    (hOrdinal : (Project.FirstOrderSemantics.reduct ℳ).IsOrdinal ordinal)
    (hSubset : ∀ input, membership ℳ input carrier → membership ℳ input ordinal) : Linear (epsilon hℳ carrier) carrier := by
  refine ⟨?_,fun left right h => ⟨((epsilon_correct hℳ carrier left right).mp h).1,((epsilon_correct hℳ carrier left right).mp h).2.1⟩,?_,?_,?_⟩
  · intro pair hPair
    obtain ⟨left,right,_,_,hCode,_⟩ := (epsilon_members hℳ carrier pair).mp hPair
    exact ⟨left,right,hCode⟩
  · intro input hInput hEdge
    exact hOrdinal.wellOrder.linear.irrefl input (hSubset input hInput) ((epsilon_correct hℳ carrier input input).mp hEdge).2.2
  · intro left middle right hLeft hMiddle hRight hLM hMR
    exact (epsilon_correct hℳ carrier left right).mpr ⟨hLeft,hRight,
      hOrdinal.wellOrder.linear.trans left (hSubset left hLeft) middle (hSubset middle hMiddle) right (hSubset right hRight)
        ((epsilon_correct hℳ carrier left middle).mp hLM).2.2 ((epsilon_correct hℳ carrier middle right).mp hMR).2.2⟩
  · intro left right hLeft hRight
    rcases hOrdinal.wellOrder.linear.compare left (hSubset left hLeft) right (hSubset right hRight) with hSame | hLess | hGreater
    · exact Or.inl ((project_models hℳ).1.eq_of_same_members left right hSame)
    · exact Or.inr (Or.inl ((epsilon_correct hℳ carrier left right).mpr ⟨hLeft,hRight,hLess⟩))
    · exact Or.inr (Or.inr ((epsilon_correct hℳ carrier right left).mpr ⟨hRight,hLeft,hGreater⟩))

/-- 任意非空子集均有给定方向的极值。 -/
def Extremes (relation carrier : Carrier ℳ) (greatest : Bool) : Prop :=
  ∀ subset, (∀ input, membership ℳ input subset → membership ℳ input carrier) → (∃ input, membership ℳ input subset) →
    ∃ candidate, membership ℳ candidate subset ∧ ∀ input, membership ℳ input subset → candidate ≠ input →
      if greatest then PureKuratowski.PairMember ℳ input candidate relation else PureKuratowski.PairMember ℳ candidate input relation

theorem extremes_correct (hℳ : Theory.Models ℳ theory) (relation carrier : Carrier ℳ) (greatest : Bool) :
    ((if greatest then Nonlogical.BasicSetTheory.natural_order_greatest_element_condition else
      Nonlogical.BasicSetTheory.natural_order_least_element_condition) (.fvar .here) (.fvar (.there .here))).satisfies
      (templateEnv (.cons relation (.cons carrier .nil)) : Env (E hℳ).model [] [s,s]) ↔ Extremes relation carrier greatest := by
  have hPower := (PureFunctionDefinitions.comprehension_correct _ _ _).mp
    (((PureNaturalDifferenceStage.realizes hℳ).function .powerSet (.cons carrier .nil) _).mpr rfl)
  have hNonempty (subset : Carrier ℳ) : subset ≠ (E hℳ).function .emptySet .nil ↔ ∃ input, membership ℳ input subset := by
    classical
    rw [zero_eq hℳ]
    constructor
    · intro hNe
      by_cases h : ∃ input, membership ℳ input subset
      · exact h
      · exact False.elim (hNe (extensionality hℳ subset (zero hℳ) (fun input => iff_of_false (fun hi => h ⟨input,hi⟩) (zero_spec hℳ input))))
    · rintro ⟨input,hInput⟩ hEq
      exact zero_spec hℳ input (hEq ▸ hInput)
  cases greatest <;>
    simp only [Bool.false_eq_true,↓reduceIte,Nonlogical.BasicSetTheory.natural_order_greatest_element_condition,
      Nonlogical.BasicSetTheory.natural_order_least_element_condition,Formula.satisfies_forallFreeTop,
      Formula.satisfies_existsFreeTop,Formula.satisfies]
  all_goals
    change (∀ subset, (membership ℳ subset ((E hℳ).function .powerSet (.cons carrier .nil)) ∧ subset ≠ (E hℳ).function .emptySet .nil) → _) ↔ _
    simp only [hPower,hNonempty]
    constructor
    · intro h subset hSubset hInhabited
      obtain ⟨candidate,hCandidate,hExtreme⟩ := h subset ⟨hSubset,hInhabited⟩
      exact ⟨candidate,hCandidate,fun input hInput hNe => (edge_correct hℳ _ _ _).mp (hExtreme input hInput hNe)⟩
    · intro h subset hData
      obtain ⟨candidate,hCandidate,hExtreme⟩ := h subset hData.1 hData.2
      exact ⟨candidate,hCandidate,fun input hInput hNe => (edge_correct hℳ _ _ _).mpr (hExtreme input hInput hNe)⟩

theorem natural_order_correct (hℳ : Theory.Models ℳ theory) (relation carrier : Carrier ℳ) :
    (E hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil)) ↔
      Linear relation carrier ∧ Extremes relation carrier true ∧ Extremes relation carrier false := by
  rw [PureNaturalDifferenceStage.round_one_definition_correct hℳ .isNaturalDiscreteLinearOrder]
  exact and_congr (linear_correct hℳ relation carrier) (and_congr (extremes_correct hℳ relation carrier true) (extremes_correct hℳ relation carrier false))

theorem well_order (hℳ : Theory.Models ℳ theory) {relation carrier : Carrier ℳ}
    (hLinear : Linear relation carrier) (hLeast : Extremes relation carrier false) :
    (Project.FirstOrderSemantics.reduct ℳ).IsSetCodedWellOrder (PureKuratowskiProject.interpretation hℳ) relation carrier := by
  classical
  refine ⟨linear_project hℳ hLinear,?_⟩
  intro subset hSubset hNonempty
  obtain ⟨candidate,hCandidate,hExtreme⟩ := hLeast subset hSubset hNonempty
  refine ⟨candidate,hCandidate,fun input hInput => ?_⟩
  by_cases hEqual : candidate = input
  · exact Or.inl (hEqual ▸ (fun _ => Iff.rfl))
  · exact Or.inr (hExtreme input hInput hEqual)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOrderSemantics
