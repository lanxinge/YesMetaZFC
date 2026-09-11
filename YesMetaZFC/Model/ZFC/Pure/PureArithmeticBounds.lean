import YesMetaZFC.Model.ZFC.Pure.PureGodelPairing
import YesMetaZFC.SetTheory.Ord.NaturalPrime

/-! # 内部自然数的六类编码上界

复用所选算术图与 Project 序数算术。有限交换律来自模型内部归纳，
这里不把非标准自然数当作外部有限数，也不假设待验证的增长公理。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticBounds
open PureModel PureNaturalInduction PureArithmeticStage PureArithmeticSpecifications
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable abbrev add (hℳ : Theory.Models ℳ theory) := arithmetic hℳ .addition
noncomputable abbrev mul (hℳ : Theory.Models ℳ theory) := arithmetic hℳ .multiplication
noncomputable abbrev power (hℳ : Theory.Models ℳ theory) := arithmetic hℳ .exponentiation

def Le (left right : Carrier ℳ) : Prop := left = right ∨ membership ℳ left right

theorem ordinal (hℳ : Theory.Models ℳ theory) {value : Carrier ℳ}
    (hValue : membership ℳ value (omega hℳ)) :
    (Project.FirstOrderSemantics.reduct ℳ).IsOrdinal value :=
  (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) value hValue

theorem lt_le (hℳ : Theory.Models ℳ theory) {point middle upper : Carrier ℳ}
    (hUpper : membership ℳ upper (omega hℳ))
    (hPoint : membership ℳ point middle) (hOrder : Le middle upper) :
    membership ℳ point upper := by
  rcases hOrder with rfl | hLess
  · exact hPoint
  · exact (ordinal hℳ hUpper).transitive middle hLess point hPoint

theorem le_lt (hℳ : Theory.Models ℳ theory) {point middle upper : Carrier ℳ}
    (hUpper : membership ℳ upper (omega hℳ))
    (hOrder : Le point middle) (hMiddle : membership ℳ middle upper) :
    membership ℳ point upper := by
  rcases hOrder with rfl | hLess
  · exact hMiddle
  · exact (ordinal hℳ hUpper).transitive middle hMiddle point hLess

theorem le_trans (hℳ : Theory.Models ℳ theory) {point middle upper : Carrier ℳ}
    (hUpper : membership ℳ upper (omega hℳ))
    (hFirst : Le point middle) (hSecond : Le middle upper) : Le point upper := by
  rcases hFirst with rfl | hLess
  · exact hSecond
  · exact Or.inr (lt_le hℳ hUpper hLess hSecond)

theorem le_iff_succ (hℳ : Theory.Models ℳ theory) (point upper : Carrier ℳ) :
    Le point upper ↔ membership ℳ point (succ hℳ upper) := by
  rw [succ_spec]
  exact or_comm

theorem add_left (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    Le left (add hℳ left right) :=
  _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_left_eq_or_mem (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ hRight)
    (arithmetic_correct hℳ .addition hLeft hRight)

theorem add_right (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    Le right (add hℳ left right) :=
  _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_right_eq_or_mem (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ hLeft) (ordinal hℳ hRight)
    (arithmetic_correct hℳ .addition hLeft hRight)

theorem addition_upper_bound (hℳ : Theory.Models ℳ theory) {point left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hPoint : membership ℳ point (succ hℳ left) ∨ membership ℳ point (succ hℳ right)) :
    membership ℳ point (succ hℳ (add hℳ left right)) := by
  apply (le_iff_succ hℳ _ _).mp
  rcases hPoint with h | h
  · exact le_trans hℳ (arithmetic_closed hℳ .addition hLeft hRight)
      ((le_iff_succ hℳ _ _).mpr h) (add_left hℳ hLeft hRight)
  · exact le_trans hℳ (arithmetic_closed hℳ .addition hLeft hRight)
      ((le_iff_succ hℳ _ _).mpr h) (add_right hℳ hLeft hRight)

theorem positive_left_addition (hℳ : Theory.Models ℳ theory) {point left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hPositive : membership ℳ (zero hℳ) left) (hPoint : membership ℳ point (succ hℳ right)) :
    membership ℳ point (add hℳ left right) := by
  have hComm := _root_.YesMetaZFC.SetTheory.Structure.natural_add_comm (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight
    (arithmetic_correct hℳ .addition hLeft hRight) (arithmetic_correct hℳ .addition hRight hLeft)
  have hRightLess : membership ℳ right (add hℳ right left) :=
    (_root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_mem_iff (project_modelsZF hℳ)
      (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ hLeft)
      (arithmetic_correct hℳ .addition hRight hLeft)).mpr
        (Or.inr ⟨zero hℳ, hPositive,
          (_root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_zero_iff (project_modelsZF hℳ)
            (PureKuratowskiProject.interpretation hℳ) (zero_spec hℳ)).mpr rfl⟩)
  change add hℳ left right = add hℳ right left at hComm
  rw [hComm]
  exact le_lt hℳ (arithmetic_closed hℳ .addition hRight hLeft)
    ((le_iff_succ hℳ _ _).mpr hPoint) hRightLess

theorem le_lt_transitivity (hℳ : Theory.Models ℳ theory) {point middle upper : Carrier ℳ}
    (hUpper : membership ℳ upper (omega hℳ))
    (hPoint : membership ℳ point (succ hℳ middle)) (hMiddle : membership ℳ middle upper) :
    membership ℳ point upper :=
  le_lt hℳ hUpper ((le_iff_succ hℳ _ _).mpr hPoint) hMiddle

theorem exponent_index (hℳ : Theory.Models ℳ theory) {base index : Carrier ℳ}
    (hBase : membership ℳ base (omega hℳ)) (hIndex : membership ℳ index (omega hℳ))
    (hBaseLarge : membership ℳ (succ hℳ (zero hℳ)) base) :
    membership ℳ index (power hℳ base (succ hℳ index)) := by
  have hBound : Le (succ hℳ index) (power hℳ base (succ hℳ index)) :=
    _root_.YesMetaZFC.SetTheory.ZF.ordinalExponentiation_exponent_eq_or_mem (project_modelsZF hℳ)
      (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ hBase)
      ⟨zero hℳ, zero_spec hℳ, succ_project hℳ _⟩ hBaseLarge (ordinal hℳ (succ_mem hℳ hIndex))
      (arithmetic_correct hℳ .exponentiation hBase (succ_mem hℳ hIndex))
  exact lt_le hℳ (arithmetic_closed hℳ .exponentiation hBase (succ_mem hℳ hIndex))
    ((succ_spec hℳ index index).mpr (Or.inr rfl)) hBound

theorem mul_right (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hPositive : ∃ element, membership ℳ element left) : Le right (mul hℳ left right) :=
  _root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_right_eq_or_mem (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ hLeft) hPositive (ordinal hℳ hRight)
    (arithmetic_correct hℳ .multiplication hLeft hRight)

theorem mul_left (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hPositive : ∃ element, membership ℳ element right) : Le left (mul hℳ left right) := by
  have hComm := _root_.YesMetaZFC.SetTheory.Structure.natural_mul_comm (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight
    (arithmetic_correct hℳ .multiplication hLeft hRight) (arithmetic_correct hℳ .multiplication hRight hLeft)
  change mul hℳ left right = mul hℳ right left at hComm
  rw [hComm]
  exact mul_right hℳ hRight hLeft hPositive

theorem exponent_product_indices (hℳ : Theory.Models ℳ theory)
    {leftBase leftIndex rightBase rightIndex : Carrier ℳ}
    (hLeftBase : membership ℳ leftBase (omega hℳ)) (hLeftIndex : membership ℳ leftIndex (omega hℳ))
    (hLeftLarge : membership ℳ (succ hℳ (zero hℳ)) leftBase)
    (hRightBase : membership ℳ rightBase (omega hℳ)) (hRightIndex : membership ℳ rightIndex (omega hℳ))
    (hRightLarge : membership ℳ (succ hℳ (zero hℳ)) rightBase) :
    membership ℳ leftIndex (mul hℳ (power hℳ leftBase (succ hℳ leftIndex)) (power hℳ rightBase (succ hℳ rightIndex))) ∧
    membership ℳ rightIndex (mul hℳ (power hℳ leftBase (succ hℳ leftIndex)) (power hℳ rightBase (succ hℳ rightIndex))) := by
  have hLeft := exponent_index hℳ hLeftBase hLeftIndex hLeftLarge
  have hRight := exponent_index hℳ hRightBase hRightIndex hRightLarge
  have hLeftPower := arithmetic_closed hℳ .exponentiation hLeftBase (succ_mem hℳ hLeftIndex)
  have hRightPower := arithmetic_closed hℳ .exponentiation hRightBase (succ_mem hℳ hRightIndex)
  have hProduct := arithmetic_closed hℳ .multiplication hLeftPower hRightPower
  exact ⟨lt_le hℳ hProduct hLeft (mul_left hℳ hLeftPower hRightPower ⟨rightIndex, hRight⟩),
    lt_le hℳ hProduct hRight (mul_right hℳ hLeftPower hRightPower ⟨leftIndex, hLeft⟩)⟩

theorem positive_square_bound (hℳ : Theory.Models ℳ theory) {base : Carrier ℳ}
    (hBase : membership ℳ base (omega hℳ)) (hPositive : ∃ element, membership ℳ element base) :
    Le base (power hℳ base (PureGodelPairing.two hℳ)) := by
  have hOne := succ_mem hℳ (zero_mem hℳ)
  have hPrevious := arithmetic_correct hℳ .exponentiation hBase hOne
  have hNonempty := _root_.YesMetaZFC.SetTheory.ZF.ordinalExponentiation_isNonemptyOnOrdinals
    (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ hBase)
    hPositive (succ hℳ (zero hℳ)) (ordinal hℳ hOne) _ hPrevious
  obtain ⟨previous, hValue, hProduct⟩ :=
    (_root_.YesMetaZFC.SetTheory.ZF.ordinalExponentiation_successor_iff (project_modelsZF hℳ)
      (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ hBase) (ordinal hℳ hOne)
      (succ_project hℳ _)).mp (arithmetic_correct hℳ .exponentiation hBase (succ_mem hℳ hOne))
  have hEqual := PureOrdinalArithmetic.ordinal_unique hℳ .exponentiation hBase hOne hValue hPrevious
  subst previous
  exact _root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_right_eq_or_mem (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ)
    (ordinal hℳ (arithmetic_closed hℳ .exponentiation hBase hOne)) hNonempty (ordinal hℳ hBase) hProduct

theorem pairing_coordinates (hℳ : Theory.Models ℳ theory) {left right output : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hGraph : PureGodelPairing.graph.satisfies
      (_root_.YesMetaZFC.Automation.RelationalTranslation.templateEnv (.cons output (.cons left (.cons right .nil))))) :
    membership ℳ left (succ hℳ output) ∧ membership ℳ right (succ hℳ output) := by
  have hSpec := (PureGodelPairing.specification_correct hℳ left right output).mp
    ((PureGodelPairing.agrees hℳ hLeft hRight output).mp hGraph)
  have hTwo := succ_mem hℳ (succ_mem hℳ (zero_mem hℳ))
  rcases PureGodelPairing.compare hℳ hLeft hRight with hLess | hOther
  · rw [hSpec.2.1 hLess]
    have hSquare := arithmetic_closed hℳ .exponentiation hRight hTwo
    exact ⟨(le_iff_succ hℳ _ _).mp (add_right hℳ hSquare hLeft),
      (le_iff_succ hℳ _ _).mp (le_trans hℳ
        (arithmetic_closed hℳ .addition hSquare hLeft)
        (positive_square_bound hℳ hRight ⟨left,hLess⟩) (add_left hℳ hSquare hLeft))⟩
  · rw [hSpec.2.2 hOther]
    have hSquare := arithmetic_closed hℳ .exponentiation hLeft hTwo
    have hFirst := arithmetic_closed hℳ .addition hSquare hLeft
    exact ⟨(le_iff_succ hℳ _ _).mp (le_trans hℳ
        (arithmetic_closed hℳ .addition hFirst hRight)
        (add_right hℳ hSquare hLeft) (add_left hℳ hFirst hRight)),
      (le_iff_succ hℳ _ _).mp (add_right hℳ hFirst hRight)⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticBounds
