import YesMetaZFC.Model.ZFC.Pure.PureStageSemantics

/-! # 第一轮函数图与原规格的母集、投影和归纳核条件

分离构造中的简洁成员条件在此还原原公理的母集限制。ω 保留原规格中的
“归纳且归纳核等于自身”；关系逆还原有序对反转，复合还原左右投影。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundOneSpecifications
open PureModel PureRelationSetOperations
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureFunctionDefinitions.parameterSorts Expansion.model
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

/-- 原关系逆规格中的母集与逐对反转。 -/
theorem converse_spec (hℳ : Theory.Models ℳ theory) (output relation domain range product : Carrier ℳ)
    (hRelation : PureKuratowski.IsRelation ℳ relation)
    (hDomain : ∀ input, membership ℳ input domain ↔ ∃ value, PureKuratowski.PairMember ℳ input value relation)
    (hRange : ∀ value, membership ℳ value range ↔ ∃ input, PureKuratowski.PairMember ℳ input value relation)
    (hProduct : ∀ pair, membership ℳ pair product ↔
      ∃ left, membership ℳ left range ∧ ∃ right, membership ℳ right domain ∧ PureKuratowski.Code ℳ pair left right) :
    relationConverseGraph.satisfies (templateEnv (.cons output (.cons relation .nil))) ↔
      ∀ element, membership ℳ element output ↔ membership ℳ element product ∧
        ∃ original, membership ℳ original relation ∧
          PureOmegaAndReverse.reverseGraph.satisfies (templateEnv (.cons element (.cons original .nil))) := by
  rw [relationConverse_correct hℳ]
  apply forall_congr'
  intro element
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨left, right, hCode, original, hOriginalCode, hOriginal⟩
    refine ⟨(hProduct element).mpr ⟨left, (hRange left).mpr ⟨right, original, hOriginalCode, hOriginal⟩,
      right, (hDomain right).mpr ⟨left, original, hOriginalCode, hOriginal⟩, hCode⟩,
      original, hOriginal, ?_⟩
    exact (PureOmegaAndReverse.reverse_correct hℳ hOriginalCode element).mpr hCode
  · rintro ⟨_, original, hOriginal, hReverse⟩
    obtain ⟨left, right, hCode⟩ := hRelation original hOriginal
    exact ⟨right, left, (PureOmegaAndReverse.reverse_correct hℳ hCode element).mp hReverse,
      original, hCode, hOriginal⟩

/-- 原复合规格中的母集与两投影；函数槽遵循 `second ∘ first`。 -/
theorem composition_spec (hℳ : Theory.Models ℳ theory) (output first second domain range product : Carrier ℳ)
    (hDomain : ∀ input, membership ℳ input domain ↔ ∃ value, PureKuratowski.PairMember ℳ input value first)
    (hRange : ∀ value, membership ℳ value range ↔ ∃ input, PureKuratowski.PairMember ℳ input value second)
    (hProduct : ∀ pair, membership ℳ pair product ↔
      ∃ left, membership ℳ left domain ∧ ∃ right, membership ℳ right range ∧ PureKuratowski.Code ℳ pair left right) :
    relationCompositionGraph.satisfies (templateEnv (.cons output (.cons second (.cons first .nil)))) ↔
      ∀ element, membership ℳ element output ↔ membership ℳ element product ∧
        ∃ left right,
          (PureRelationFunctions.graph .leftProjection).satisfies (templateEnv (.cons left (.cons element .nil))) ∧
          (PureRelationFunctions.graph .rightProjection).satisfies (templateEnv (.cons right (.cons element .nil))) ∧
          ∃ middle, PureKuratowski.PairMember ℳ left middle first ∧ PureKuratowski.PairMember ℳ middle right second := by
  rw [relationComposition_correct hℳ]
  apply forall_congr'
  intro element
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨left, right, middle, hCode, hFirst, hSecond⟩
    exact ⟨(hProduct element).mpr ⟨left, (hDomain left).mpr ⟨middle, hFirst⟩,
      right, (hRange right).mpr ⟨middle, hSecond⟩, hCode⟩,
      left, right, (PureRelationFunctions.left_value hCode left).mpr rfl,
      (PureRelationFunctions.right_value hCode right).mpr rfl, middle, hFirst, hSecond⟩
  · rintro ⟨hElement, left, right, hLeft, hRight, middle, hFirst, hSecond⟩
    obtain ⟨actualLeft, _, actualRight, _, hCode⟩ := (hProduct element).mp hElement
    obtain rfl := (PureRelationFunctions.left_value hCode left).mp hLeft
    obtain rfl := (PureRelationFunctions.right_value hCode right).mp hRight
    exact ⟨left, right, middle, hCode, hFirst, hSecond⟩

/-- 隶属关系保留原规格的源集平方母集。 -/
theorem membership_spec (hℳ : Theory.Models ℳ theory) (output source product : Carrier ℳ)
    (hProduct : ∀ pair, membership ℳ pair product ↔
      ∃ left, membership ℳ left source ∧ ∃ right, membership ℳ right source ∧ PureKuratowski.Code ℳ pair left right) :
    membershipRelationGraph.satisfies (templateEnv (.cons output (.cons source .nil))) ↔
      ∀ element, membership ℳ element output ↔ membership ℳ element product ∧
        ∃ left right, PureKuratowski.Code ℳ element left right ∧ membership ℳ left right := by
  rw [membershipRelation_correct hℳ]
  apply forall_congr'
  intro element
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨left, right, hLeft, hRight, hCode, hMember⟩
    exact ⟨(hProduct element).mpr ⟨left, hLeft, right, hRight, hCode⟩, left, right, hCode, hMember⟩
  · rintro ⟨hElement, left, right, hCode, hMember⟩
    obtain ⟨actualLeft, hLeft, actualRight, hRight, hActual⟩ := (hProduct element).mp hElement
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hCode hActual
    exact ⟨left, right, hLeft, hRight, hActual, hMember⟩

/-- 原像集公理中任意目标集的母集限制由映射与子集条件推出。 -/
theorem image_spec (hℳ : Theory.Models ℳ theory) (output function source target subset : Carrier ℳ)
    (hMapping : PureMappingDefinitions.IsMapping ℳ function source target)
    (hSubset : ∀ input, membership ℳ input subset → membership ℳ input source) :
    imageGraph.satisfies (templateEnv (.cons output (.cons function (.cons subset .nil)))) ↔
      ∀ element, membership ℳ element output ↔ membership ℳ element target ∧
        ∃ input, membership ℳ input subset ∧ PureKuratowski.PairMember ℳ input element function := by
  rw [image_correct hℳ]
  have hBound (element : Carrier ℳ) (h : imageMember ℳ function subset element) : membership ℳ element target := by
    obtain ⟨input, hInput, hPair⟩ := h
    obtain ⟨value, hValue, hValuePair⟩ := hMapping.2.2 input (hSubset input hInput)
    exact (hMapping.1.2 input value element hValuePair hPair) ▸ hValue
  exact ⟨fun h element => (h element).trans ⟨fun h => ⟨hBound element h, h⟩, And.right⟩,
    fun h element => (h element).trans ⟨And.right, fun h => ⟨hBound element h, h⟩⟩⟩

/-- 原 ω 规格正是“归纳且归纳核不变”。 -/
theorem omega_core_spec (hℳ : Theory.Models ℳ theory) (candidate core : Carrier ℳ)
    (hCore : inductiveCoreGraph.satisfies (templateEnv (.cons core (.cons candidate .nil)))) :
    PureOmegaAndReverse.omegaGraph.satisfies (templateEnv (.cons candidate .nil)) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsInductive candidate ∧ core = candidate := by
  rw [PureOmegaAndReverse.omega_correct hℳ]
  have hCoreSpec := (inductiveCore_correct hℳ core candidate).mp hCore
  constructor
  · intro hOmega
    refine ⟨hOmega.1, extensionality hℳ core candidate (fun element => ?_)⟩
    exact (hCoreSpec element).trans ⟨And.left,
      fun h => ⟨h, fun inductiveSet hInductive => hOmega.2 inductiveSet hInductive element h⟩⟩
  · rintro ⟨hInductive, rfl⟩
    exact ⟨hInductive, fun inductiveSet hSet element hElement => ((hCoreSpec element).mp hElement).2 inductiveSet hSet⟩

/-- 对称差原规格中的二元并母集由成员条件推出。 -/
theorem symmetric_difference_spec (hℳ : Theory.Models ℳ theory) (output left right union : Carrier ℳ)
    (hUnion : ∀ element, membership ℳ element union ↔ membership ℳ element left ∨ membership ℳ element right) :
    symmetricDifferenceGraph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      ∀ element, membership ℳ element output ↔ membership ℳ element union ∧
        symmetricDifferenceMember ℳ left right element := by
  rw [symmetricDifference_correct hℳ]
  have hBound (element : Carrier ℳ) (h : symmetricDifferenceMember ℳ left right element) :
      membership ℳ element union :=
    (hUnion element).mpr (h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  exact ⟨fun h element => (h element).trans ⟨fun h => ⟨hBound element h, h⟩, And.right⟩,
    fun h element => (h element).trans ⟨And.right, fun h => ⟨hBound element h, h⟩⟩⟩

/-- 具体扩张对任意候选对象满足原语言的 ω 定义实例。 -/
theorem omega_definition_correct (hℳ : Theory.Models ℳ theory) (candidate : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.omega_definition_instance (.fvar .here)).satisfies
      (templateEnv (.cons candidate .nil) : Env (PureStageSemantics.expansion hℳ).model []
        [Nonlogical.BasicSetTheory.SetSort.set]) := by
  let E := PureStageSemantics.expansion hℳ
  have hCore : inductiveCoreGraph.satisfies
      (templateEnv (.cons (E.function .inductiveCore (.cons candidate .nil)) (.cons candidate .nil))) :=
    ((PureStageSemantics.realizes hℳ).function .inductiveCore (.cons candidate .nil) _).mpr rfl
  have hOmega : PureOmegaAndReverse.omegaGraph.satisfies (templateEnv (.cons candidate .nil)) ↔
      candidate = E.function .omega .nil :=
    (PureStageSemantics.realizes hℳ).function .omega .nil candidate
  have hInductive : E.relation .isInductiveSet (.cons candidate .nil) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsInductive candidate :=
    PureStageSemantics.inductive_correct hℳ candidate
  change candidate = E.function .omega .nil ↔
    E.relation .isInductiveSet (.cons candidate .nil) ∧ E.function .inductiveCore (.cons candidate .nil) = candidate
  exact hOmega.symm.trans ((omega_core_spec hℳ candidate _ hCore).trans (and_congr hInductive.symm Iff.rfl))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRoundOneSpecifications
