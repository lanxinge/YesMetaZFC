import YesMetaZFC.Model.ZFC.Pure.PureMappingDefinitions

/-! # 纯笛卡尔积和映射收集保留原支撑规格

原公理的成员条件还含有幂集母集限制。Kuratowski 编码自动落在二重幂集内，
函数图自动是源集与目标集的笛卡尔积的子集，因此两处限制均由实际定义推出。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMappingSpecifications
open PureModel PureMappingDefinitions
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

/-- 同域映射若逐点有共同取值，则两个函数图相等。 -/
theorem mapping_ext (hℳ : Theory.Models ℳ theory)
    {first second source target : Carrier ℳ}
    (hFirst : IsMapping ℳ first source target)
    (hSecond : IsMapping ℳ second source target)
    (hValues : ∀ input, membership ℳ input source → ∃ value,
      PureKuratowski.PairMember ℳ input value first ∧
        PureKuratowski.PairMember ℳ input value second) : first = second := by
  have hSubset {left right : Carrier ℳ}
      (hLeft : IsMapping ℳ left source target)
      (hCommon : ∀ input, membership ℳ input source → ∃ value,
        PureKuratowski.PairMember ℳ input value left ∧
          PureKuratowski.PairMember ℳ input value right) :
      ∀ pair, membership ℳ pair left → membership ℳ pair right := by
    intro pair hPair
    obtain ⟨input, output, hCode⟩ := hLeft.1.1 pair hPair
    have hMember : PureKuratowski.PairMember ℳ input output left := ⟨pair, hCode, hPair⟩
    obtain ⟨value, hValueLeft, other, hOtherCode, hOther⟩ :=
      hCommon input ((hLeft.2.1 input).mpr ⟨output, hMember⟩)
    have hEqual := hLeft.1.2 input output value hMember hValueLeft
    subst value
    exact (PureKuratowski.code_unique hℳ hOtherCode hCode) ▸ hOther
  exact extensionality hℳ first second (fun pair =>
    ⟨hSubset hFirst hValues pair,
      hSubset hSecond (fun input hInput => by
        obtain ⟨value, hFirstValue, hSecondValue⟩ := hValues input hInput
        exact ⟨value, hSecondValue, hFirstValue⟩) pair⟩)

/-- 坐标落在同一母集内时，其 Kuratowski 编码属于母集的二重幂集。 -/
theorem code_mem_double_power (ambient power doublePower pair left right : Carrier ℳ)
    (hPower : ∀ subset, membership ℳ subset power ↔
      ∀ element, membership ℳ element subset → membership ℳ element ambient)
    (hDoublePower : ∀ subset, membership ℳ subset doublePower ↔
      ∀ element, membership ℳ element subset → membership ℳ element power)
    (hLeft : membership ℳ left ambient) (hRight : membership ℳ right ambient)
    (hCode : PureKuratowski.Code ℳ pair left right) : membership ℳ pair doublePower := by
  obtain ⟨single, unordered, hSingle, hUnordered, hPair⟩ := hCode
  apply (hDoublePower pair).mpr
  intro member hMember
  rcases (hPair member).mp hMember with rfl | rfl
  · apply (hPower member).mpr
    intro element hElement
    exact (hSingle element).mp hElement ▸ hLeft
  · apply (hPower member).mpr
    intro element hElement
    rcases (hUnordered element).mp hElement with rfl | rfl
    · exact hLeft
    · exact hRight

/-- 纯笛卡尔积图与原公理的二重幂集受限成员规格一致。 -/
theorem cartesian_spec (output left right union power doublePower : Carrier ℳ)
    (hUnion : ∀ element, membership ℳ element union ↔
      membership ℳ element left ∨ membership ℳ element right)
    (hPower : ∀ subset, membership ℳ subset power ↔
      ∀ element, membership ℳ element subset → membership ℳ element union)
    (hDoublePower : ∀ subset, membership ℳ subset doublePower ↔
      ∀ element, membership ℳ element subset → membership ℳ element power) :
    (graph .cartesianProduct).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      ∀ pair, membership ℳ pair output ↔ membership ℳ pair doublePower ∧
        ∃ leftValue, membership ℳ leftValue left ∧
          ∃ rightValue, membership ℳ rightValue right ∧ PureKuratowski.Code ℳ pair leftValue rightValue := by
  rw [cartesian_correct]
  have hBound : ∀ pair, (∃ leftValue, membership ℳ leftValue left ∧
      ∃ rightValue, membership ℳ rightValue right ∧ PureKuratowski.Code ℳ pair leftValue rightValue) →
      membership ℳ pair doublePower := by
    rintro pair ⟨leftValue, hLeft, rightValue, hRight, hCode⟩
    exact code_mem_double_power union power doublePower pair leftValue rightValue hPower hDoublePower
      ((hUnion leftValue).mpr (Or.inl hLeft)) ((hUnion rightValue).mpr (Or.inr hRight)) hCode
  constructor
  · intro hOutput pair
    exact (hOutput pair).trans ⟨fun h => ⟨hBound pair h, h⟩, And.right⟩
  · intro hOutput pair
    exact (hOutput pair).trans ⟨And.right, fun h => ⟨hBound pair h, h⟩⟩

/-- 从源集到目标集的整个函数图包含于相应笛卡尔积。 -/
theorem mapping_subset_product (function source target product : Carrier ℳ)
    (hProduct : (graph .cartesianProduct).satisfies
      (templateEnv (.cons product (.cons source (.cons target .nil)))))
    (hMapping : IsMapping ℳ function source target) :
    ∀ pair, membership ℳ pair function → membership ℳ pair product := by
  intro pair hPair
  obtain ⟨input, output, hCode⟩ := hMapping.1.1 pair hPair
  have hMember : PureKuratowski.PairMember ℳ input output function := ⟨pair, hCode, hPair⟩
  have hInput := (hMapping.2.1 input).mpr ⟨output, hMember⟩
  obtain ⟨value, hValue, hGraph⟩ := hMapping.2.2 input hInput
  have hOutput : membership ℳ output target := (hMapping.1.2 input value output hGraph hMember) ▸ hValue
  exact ((cartesian_correct product source target).mp hProduct pair).mpr
    ⟨input, hInput, output, hOutput, hCode⟩

/-- 纯映射收集图与原公理的笛卡尔积幂集受限成员规格一致。 -/
theorem mappingCollection_spec (output source target product power : Carrier ℳ)
    (hProduct : (graph .cartesianProduct).satisfies
      (templateEnv (.cons product (.cons source (.cons target .nil)))))
    (hPower : ∀ subset, membership ℳ subset power ↔
      ∀ element, membership ℳ element subset → membership ℳ element product) :
    (graph .mappingCollection).satisfies (templateEnv (.cons output (.cons source (.cons target .nil)))) ↔
      ∀ function, membership ℳ function output ↔
        membership ℳ function power ∧ IsMapping ℳ function source target := by
  rw [mappingCollection_correct]
  have hBound : ∀ function, IsMapping ℳ function source target → membership ℳ function power :=
    fun function hMapping => (hPower function).mpr
      (mapping_subset_product function source target product hProduct hMapping)
  constructor
  · intro hOutput function
    exact (hOutput function).trans ⟨fun h => ⟨hBound function h, h⟩, And.right⟩
  · intro hOutput function
    exact (hOutput function).trans ⟨And.right, fun h => ⟨hBound function h, h⟩⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMappingSpecifications
