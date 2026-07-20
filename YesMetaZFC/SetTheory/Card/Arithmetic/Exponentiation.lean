import YesMetaZFC.SetTheory.Card.Arithmetic.Equinumerosity
import YesMetaZFC.SetTheory.FunctionSpaceAlgebra

/-!
# 基数指数

本层证明函数集定义的基数指数与代表元选择无关，并导出指数律、单调性与零一律。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure.IsCardinalExponentiation

/-- 固定底数和指数基数时，基数指数的结果唯一。 -/
theorem eq {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second base exponent : ℳ.Domain}
    (hFirst :
      ℳ.IsCardinalExponentiation 𝕀 first base exponent)
    (hSecond :
      ℳ.IsCardinalExponentiation 𝕀 second base exponent) :
    first = second := by
  rcases hFirst with
    ⟨firstBase, firstExponent, firstSpace,
      hFirstBase, hFirstExponent, hFirstSpace, hFirstCardinal⟩
  rcases hSecond with
    ⟨secondBase, secondExponent, secondSpace,
      hSecondBase, hSecondExponent, hSecondSpace, hSecondCardinal⟩
  have hBaseEquinumerous :
      ℳ.Equinumerous 𝕀 firstBase secondBase :=
    hFirstBase.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondBase.2
  have hExponentEquinumerous :
      ℳ.Equinumerous 𝕀 firstExponent secondExponent :=
    hFirstExponent.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondExponent.2
  have hSpaceEquinumerous :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hFirstSpace hSecondSpace
      hExponentEquinumerous hBaseEquinumerous
  apply hFirstCardinal.1.eq_of_equinumerous
      hZF 𝕀 hSecondCardinal.1
  exact hFirstCardinal.2.trans hZF 𝕀 <|
    hSpaceEquinumerous.trans hZF 𝕀 <|
      hSecondCardinal.2.symm hZF 𝕀

/-- `(3.5)`：乘积底数的幂等于两个幂的乘积。 -/
theorem multiplicative_base {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {firstBase secondBase baseProduct exponent
      leftPower firstPower secondPower rightPower : ℳ.Domain}
    (hBaseProduct :
      ℳ.IsCardinalMultiplication 𝕀
        baseProduct firstBase secondBase)
    (hLeftPower :
      ℳ.IsCardinalExponentiation 𝕀
        leftPower baseProduct exponent)
    (hFirstPower :
      ℳ.IsCardinalExponentiation 𝕀
        firstPower firstBase exponent)
    (hSecondPower :
      ℳ.IsCardinalExponentiation 𝕀
        secondPower secondBase exponent)
    (hRightPower :
      ℳ.IsCardinalMultiplication 𝕀
        rightPower firstPower secondPower) :
    leftPower = rightPower := by
  rcases hBaseProduct with
    ⟨firstBaseSet, secondBaseSet, baseProductSet,
      hFirstBaseSet, hSecondBaseSet,
      hBaseProductSet, hBaseProductCardinal⟩
  rcases hLeftPower with
    ⟨leftPowerBaseSet, exponentSet, leftSpace,
      hLeftPowerBaseSet, hExponentSet,
      hLeftSpace, hLeftCardinal⟩
  rcases hFirstPower with
    ⟨firstBaseSet', firstExponentSet, firstSpace,
      hFirstBaseSet', hFirstExponentSet,
      hFirstSpace, hFirstPowerCardinal⟩
  rcases hSecondPower with
    ⟨secondBaseSet', secondExponentSet, secondSpace,
      hSecondBaseSet', hSecondExponentSet,
      hSecondSpace, hSecondPowerCardinal⟩
  rcases hRightPower with
    ⟨firstPowerSet, secondPowerSet, rightProduct,
      hFirstPowerSet, hSecondPowerSet,
      hRightProduct, hRightCardinal⟩

  rcases ZF.exists_functionSpace hZF 𝕀 exponentSet baseProductSet with
    ⟨normalizedLeft, hNormalizedLeft⟩
  rcases ZF.exists_functionSpace hZF 𝕀 exponentSet firstBaseSet with
    ⟨normalizedFirst, hNormalizedFirst⟩
  rcases ZF.exists_functionSpace hZF 𝕀 exponentSet secondBaseSet with
    ⟨normalizedSecond, hNormalizedSecond⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀
      normalizedFirst normalizedSecond with
    ⟨normalizedRight, hNormalizedRight⟩

  have hBaseToProduct :
      ℳ.Equinumerous 𝕀 leftPowerBaseSet baseProductSet :=
    hLeftPowerBaseSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hBaseProductCardinal.2
  have hLeftNormalized :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hLeftSpace hNormalizedLeft
      (Structure.Equinumerous.refl hZF 𝕀 exponentSet)
      hBaseToProduct

  have hSplit :=
    ZF.equinumerous_functionSpaceIntoProduct hZF 𝕀
      hNormalizedLeft hNormalizedFirst hNormalizedSecond
      hNormalizedRight hBaseProductSet

  have hFirstExponentEquinumerous :
      ℳ.Equinumerous 𝕀 exponentSet firstExponentSet :=
    hExponentSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hFirstExponentSet.2
  have hFirstBaseEquinumerous :
      ℳ.Equinumerous 𝕀 firstBaseSet firstBaseSet' :=
    hFirstBaseSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hFirstBaseSet'.2
  have hNormalizedFirstToSpace :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hNormalizedFirst hFirstSpace
      hFirstExponentEquinumerous hFirstBaseEquinumerous
  have hNormalizedFirstToPower :
      ℳ.Equinumerous 𝕀 normalizedFirst firstPowerSet :=
    hNormalizedFirstToSpace.trans hZF 𝕀 <|
      (hFirstPowerCardinal.2.symm hZF 𝕀).trans hZF 𝕀
        hFirstPowerSet.2

  have hSecondExponentEquinumerous :
      ℳ.Equinumerous 𝕀 exponentSet secondExponentSet :=
    hExponentSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hSecondExponentSet.2
  have hSecondBaseEquinumerous :
      ℳ.Equinumerous 𝕀 secondBaseSet secondBaseSet' :=
    hSecondBaseSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hSecondBaseSet'.2
  have hNormalizedSecondToSpace :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hNormalizedSecond hSecondSpace
      hSecondExponentEquinumerous hSecondBaseEquinumerous
  have hNormalizedSecondToPower :
      ℳ.Equinumerous 𝕀 normalizedSecond secondPowerSet :=
    hNormalizedSecondToSpace.trans hZF 𝕀 <|
      (hSecondPowerCardinal.2.symm hZF 𝕀).trans hZF 𝕀
        hSecondPowerSet.2

  rcases hNormalizedFirstToPower with
    ⟨firstMap, hFirstMap⟩
  rcases hNormalizedSecondToPower with
    ⟨secondMap, hSecondMap⟩
  have hRightNormalized :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hNormalizedRight hRightProduct hFirstMap hSecondMap

  apply hLeftCardinal.1.eq_of_equinumerous
      hZF 𝕀 hRightCardinal.1
  exact hLeftCardinal.2.trans hZF 𝕀 <|
    hLeftNormalized.trans hZF 𝕀 <|
      hSplit.trans hZF 𝕀 <|
        hRightNormalized.trans hZF 𝕀 <|
          hRightCardinal.2.symm hZF 𝕀

/-- `(3.6)`：指数上的基数加法转化为两个幂的乘法。 -/
theorem additive_exponent {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base firstExponent secondExponent exponentSum
      leftPower firstPower secondPower rightPower : ℳ.Domain}
    (hExponentSum :
      ℳ.IsCardinalAddition 𝕀
        exponentSum firstExponent secondExponent)
    (hLeftPower :
      ℳ.IsCardinalExponentiation 𝕀
        leftPower base exponentSum)
    (hFirstPower :
      ℳ.IsCardinalExponentiation 𝕀
        firstPower base firstExponent)
    (hSecondPower :
      ℳ.IsCardinalExponentiation 𝕀
        secondPower base secondExponent)
    (hRightPower :
      ℳ.IsCardinalMultiplication 𝕀
        rightPower firstPower secondPower) :
    leftPower = rightPower := by
  rcases hExponentSum with
    ⟨firstExponentSet, secondExponentSet, exponentUnion,
      hFirstExponentSet, hSecondExponentSet, hExponentDisjoint,
      hExponentUnion, hExponentSumCardinal⟩
  rcases hLeftPower with
    ⟨baseSet, exponentSumSet, leftSpace,
      hBaseSet, hExponentSumSet, hLeftSpace, hLeftCardinal⟩
  rcases hFirstPower with
    ⟨firstBaseSet, firstExponentSet', firstSpace,
      hFirstBaseSet, hFirstExponentSet',
      hFirstSpace, hFirstPowerCardinal⟩
  rcases hSecondPower with
    ⟨secondBaseSet, secondExponentSet', secondSpace,
      hSecondBaseSet, hSecondExponentSet',
      hSecondSpace, hSecondPowerCardinal⟩
  rcases hRightPower with
    ⟨firstPowerSet, secondPowerSet, rightProduct,
      hFirstPowerSet, hSecondPowerSet,
      hRightProduct, hRightCardinal⟩

  rcases ZF.exists_functionSpace hZF 𝕀 exponentUnion baseSet with
    ⟨normalizedLeft, hNormalizedLeft⟩
  rcases ZF.exists_functionSpace hZF 𝕀 firstExponentSet baseSet with
    ⟨normalizedFirst, hNormalizedFirst⟩
  rcases ZF.exists_functionSpace hZF 𝕀 secondExponentSet baseSet with
    ⟨normalizedSecond, hNormalizedSecond⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀
      normalizedFirst normalizedSecond with
    ⟨normalizedRight, hNormalizedRight⟩

  have hExponentSumToUnion :
      ℳ.Equinumerous 𝕀 exponentSumSet exponentUnion :=
    hExponentSumSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hExponentSumCardinal.2
  have hLeftNormalized :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hLeftSpace hNormalizedLeft
      hExponentSumToUnion
      (Structure.Equinumerous.refl hZF 𝕀 baseSet)

  have hSplit :=
    ZF.equinumerous_functionSpaceOverUnion hZF 𝕀
      hNormalizedLeft hNormalizedFirst hNormalizedSecond
      hNormalizedRight hExponentUnion hExponentDisjoint

  have hFirstExponentEquinumerous :
      ℳ.Equinumerous 𝕀 firstExponentSet firstExponentSet' :=
    hFirstExponentSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hFirstExponentSet'.2
  have hFirstBaseEquinumerous :
      ℳ.Equinumerous 𝕀 baseSet firstBaseSet :=
    hBaseSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hFirstBaseSet.2
  have hNormalizedFirstToSpace :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hNormalizedFirst hFirstSpace
      hFirstExponentEquinumerous hFirstBaseEquinumerous
  have hNormalizedFirstToPower :
      ℳ.Equinumerous 𝕀 normalizedFirst firstPowerSet :=
    hNormalizedFirstToSpace.trans hZF 𝕀 <|
      (hFirstPowerCardinal.2.symm hZF 𝕀).trans hZF 𝕀
        hFirstPowerSet.2

  have hSecondExponentEquinumerous :
      ℳ.Equinumerous 𝕀 secondExponentSet secondExponentSet' :=
    hSecondExponentSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hSecondExponentSet'.2
  have hSecondBaseEquinumerous :
      ℳ.Equinumerous 𝕀 baseSet secondBaseSet :=
    hBaseSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondBaseSet.2
  have hNormalizedSecondToSpace :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hNormalizedSecond hSecondSpace
      hSecondExponentEquinumerous hSecondBaseEquinumerous
  have hNormalizedSecondToPower :
      ℳ.Equinumerous 𝕀 normalizedSecond secondPowerSet :=
    hNormalizedSecondToSpace.trans hZF 𝕀 <|
      (hSecondPowerCardinal.2.symm hZF 𝕀).trans hZF 𝕀
        hSecondPowerSet.2

  rcases hNormalizedFirstToPower with
    ⟨firstMap, hFirstMap⟩
  rcases hNormalizedSecondToPower with
    ⟨secondMap, hSecondMap⟩
  have hRightNormalized :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hNormalizedRight hRightProduct hFirstMap hSecondMap

  apply hLeftCardinal.1.eq_of_equinumerous
      hZF 𝕀 hRightCardinal.1
  exact hLeftCardinal.2.trans hZF 𝕀 <|
    hLeftNormalized.trans hZF 𝕀 <|
      hSplit.trans hZF 𝕀 <|
        hRightNormalized.trans hZF 𝕀 <|
          hRightCardinal.2.symm hZF 𝕀

/-- `(3.7)`：幂的幂等于以指数乘积为指数的幂。 -/
theorem iterated_exponent {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base firstExponent secondExponent innerPower
      leftPower exponentProduct rightPower : ℳ.Domain}
    (hInnerPower :
      ℳ.IsCardinalExponentiation 𝕀
        innerPower base firstExponent)
    (hLeftPower :
      ℳ.IsCardinalExponentiation 𝕀
        leftPower innerPower secondExponent)
    (hExponentProduct :
      ℳ.IsCardinalMultiplication 𝕀
        exponentProduct firstExponent secondExponent)
    (hRightPower :
      ℳ.IsCardinalExponentiation 𝕀
        rightPower base exponentProduct) :
    leftPower = rightPower := by
  rcases hInnerPower with
    ⟨baseSet, firstExponentSet, innerSpace,
      hBaseSet, hFirstExponentSet,
      hInnerSpace, hInnerPowerCardinal⟩
  rcases hLeftPower with
    ⟨leftBaseSet, secondExponentSet, leftSpace,
      hLeftBaseSet, hSecondExponentSet,
      hLeftSpace, hLeftCardinal⟩
  rcases hExponentProduct with
    ⟨firstExponentSet', secondExponentSet', exponentProductSet,
      hFirstExponentSet', hSecondExponentSet',
      hExponentProductSet, hExponentProductCardinal⟩
  rcases hRightPower with
    ⟨rightBaseSet, rightExponentSet, rightSpace,
      hRightBaseSet, hRightExponentSet,
      hRightSpace, hRightCardinal⟩

  rcases ZF.exists_functionSpace hZF 𝕀
      secondExponentSet innerSpace with
    ⟨normalizedLeft, hNormalizedLeft⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀
      firstExponentSet secondExponentSet with
    ⟨normalizedProduct, hNormalizedProduct⟩
  rcases ZF.exists_functionSpace hZF 𝕀
      normalizedProduct baseSet with
    ⟨normalizedRight, hNormalizedRight⟩

  have hLeftBaseToInner :
      ℳ.Equinumerous 𝕀 leftBaseSet innerSpace :=
    hLeftBaseSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hInnerPowerCardinal.2
  have hLeftNormalized :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hLeftSpace hNormalizedLeft
      (Structure.Equinumerous.refl hZF 𝕀 secondExponentSet)
      hLeftBaseToInner

  have hCurry :=
    ZF.equinumerous_nestedFunctionSpace hZF 𝕀
      hInnerSpace hNormalizedLeft hNormalizedProduct hNormalizedRight

  have hFirstExponentEquinumerous :
      ℳ.Equinumerous 𝕀 firstExponentSet firstExponentSet' :=
    hFirstExponentSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hFirstExponentSet'.2
  have hSecondExponentEquinumerous :
      ℳ.Equinumerous 𝕀 secondExponentSet secondExponentSet' :=
    hSecondExponentSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hSecondExponentSet'.2
  rcases hFirstExponentEquinumerous with
    ⟨firstExponentMap, hFirstExponentMap⟩
  rcases hSecondExponentEquinumerous with
    ⟨secondExponentMap, hSecondExponentMap⟩
  have hProductEquinumerous :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hNormalizedProduct hExponentProductSet
      hFirstExponentMap hSecondExponentMap
  have hProductToRightExponent :
      ℳ.Equinumerous 𝕀 normalizedProduct rightExponentSet :=
    hProductEquinumerous.trans hZF 𝕀 <|
      (hExponentProductCardinal.2.symm hZF 𝕀).trans hZF 𝕀
        hRightExponentSet.2
  have hBaseEquinumerous :
      ℳ.Equinumerous 𝕀 baseSet rightBaseSet :=
    hBaseSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hRightBaseSet.2
  have hRightNormalized :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hNormalizedRight hRightSpace
      hProductToRightExponent hBaseEquinumerous

  apply hLeftCardinal.1.eq_of_equinumerous
      hZF 𝕀 hRightCardinal.1
  exact hLeftCardinal.2.trans hZF 𝕀 <|
    hLeftNormalized.trans hZF 𝕀 <|
      hCurry.trans hZF 𝕀 <|
        hRightNormalized.trans hZF 𝕀 <|
          hRightCardinal.2.symm hZF 𝕀

/-- `(3.8)`：固定指数时，基数指数关于底数单调。 -/
theorem monotone_base {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {firstPower secondPower firstBase secondBase exponent : ℳ.Domain}
    (hBase :
      ℳ.CardinalLessOrEqual 𝕀 firstBase secondBase)
    (hFirst :
      ℳ.IsCardinalExponentiation 𝕀
        firstPower firstBase exponent)
    (hSecond :
      ℳ.IsCardinalExponentiation 𝕀
        secondPower secondBase exponent) :
    ℳ.CardinalLessOrEqual 𝕀 firstPower secondPower := by
  rcases hFirst with
    ⟨firstBaseSet, firstExponentSet, firstSpace,
      hFirstBase, hFirstExponent, hFirstSpace, hFirstPower⟩
  rcases hSecond with
    ⟨secondBaseSet, secondExponentSet, secondSpace,
      hSecondBase, hSecondExponent, hSecondSpace, hSecondPower⟩
  have hExponentEquinumerous :
      ℳ.Equinumerous 𝕀 firstExponentSet secondExponentSet :=
    hFirstExponent.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondExponent.2
  rcases hExponentEquinumerous with
    ⟨domainMap, hDomainMap⟩
  rcases hFirstBase.2.symm hZF 𝕀 with
    ⟨firstBaseMap, hFirstBaseMap⟩
  rcases hBase with ⟨baseInjection, hBaseInjection⟩
  rcases hSecondBase.2 with
    ⟨secondBaseMap, hSecondBaseMap⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hFirstBaseMap.1 hBaseInjection with
    ⟨firstComposite, hFirstComposite⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hFirstComposite hSecondBaseMap.1 with
    ⟨baseMap, hBaseMap⟩
  rcases ZF.exists_functionSpaceTransportInjection hZF 𝕀
      hFirstSpace hSecondSpace hDomainMap hBaseMap with
    ⟨spaceInjection, hSpaceInjection⟩
  rcases hFirstPower.2 with
    ⟨firstPowerMap, hFirstPowerMap⟩
  rcases hSecondPower.2.symm hZF 𝕀 with
    ⟨secondPowerMap, hSecondPowerMap⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hFirstPowerMap.1 hSpaceInjection with
    ⟨toSecondSpace, hToSecondSpace⟩
  exact ZF.exists_compositionInjection hZF 𝕀
    hToSecondSpace hSecondPowerMap.1

/-- `(3.9)`：非空的较小指数不大于较大指数时，基数指数保持单调。 -/
theorem monotone_exponent_of_nonempty {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {firstPower secondPower base firstExponent secondExponent : ℳ.Domain}
    (hFirstExponentNonempty :
      ∃ value, ℳ.mem value firstExponent)
    (hExponent :
      ℳ.CardinalLessOrEqual 𝕀 firstExponent secondExponent)
    (hFirst :
      ℳ.IsCardinalExponentiation 𝕀
        firstPower base firstExponent)
    (hSecond :
      ℳ.IsCardinalExponentiation 𝕀
        secondPower base secondExponent) :
    ℳ.CardinalLessOrEqual 𝕀 firstPower secondPower := by
  rcases hFirst with
    ⟨firstBaseSet, firstExponentSet, firstSpace,
      hFirstBase, hFirstExponent, hFirstSpace, hFirstPower⟩
  rcases hSecond with
    ⟨secondBaseSet, secondExponentSet, secondSpace,
      hSecondBase, hSecondExponent, hSecondSpace, hSecondPower⟩

  have hFirstExponentSetNonempty :
      ∃ value, ℳ.mem value firstExponentSet := by
    rcases hFirstExponent.2 with
      ⟨firstExponentMap, hFirstExponentMap⟩
    rcases hFirstExponentNonempty with
      ⟨value, hValue⟩
    rcases hFirstExponentMap.1.1.2.2 value hValue with
      ⟨image, hImage, _⟩
    exact ⟨image, hImage⟩

  rcases hFirstExponent.2.symm hZF 𝕀 with
    ⟨toFirstExponent, hToFirstExponent⟩
  rcases hExponent with
    ⟨exponentInjection, hExponentInjection⟩
  rcases hSecondExponent.2 with
    ⟨toSecondExponentSet, hToSecondExponentSet⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hToFirstExponent.1 hExponentInjection with
    ⟨toSecondExponent, hToSecondExponent⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hToSecondExponent hToSecondExponentSet.1 with
    ⟨domainMap, hDomainMap⟩

  have hBaseEquinumerous :
      ℳ.Equinumerous 𝕀 firstBaseSet secondBaseSet :=
    hFirstBase.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondBase.2
  rcases hBaseEquinumerous with
    ⟨baseMap, hBaseMap⟩

  have hSpaceInjection :
      ∃ map,
        ℳ.IsSetInjectionFromTo 𝕀 map firstSpace secondSpace := by
    classical
    by_cases hSecondBaseNonempty :
        ∃ value, ℳ.mem value secondBaseSet
    · rcases hSecondBaseNonempty with
        ⟨defaultValue, hDefaultValue⟩
      exact ZF.exists_functionSpaceExtensionInjection
        hZF 𝕀 hFirstSpace hSecondSpace
        hDomainMap hBaseMap.1 hDefaultValue
    · have hFirstBaseEmpty :
          ∀ value, ¬ ℳ.mem value firstBaseSet := by
        intro value hValue
        rcases hBaseMap.1.1.2.2 value hValue with
          ⟨image, hImage, _⟩
        exact hSecondBaseNonempty ⟨image, hImage⟩
      have hFirstSpaceEmpty :
          ∀ function, ¬ ℳ.mem function firstSpace := by
        intro function hFunction
        have hSetFunction := (hFirstSpace function).mp hFunction
        rcases hFirstExponentSetNonempty with
          ⟨input, hInput⟩
        rcases hSetFunction.2.2 input hInput with
          ⟨output, hOutput, _⟩
        exact hFirstBaseEmpty output hOutput
      let emptyEnv : Env ℳ 0 := {
        bound := Fin.elim0
        free := fun _ => Classical.choice ℳ.nonempty
      }
      apply ZF.exists_setInjectionFromTo_of_denote
          hZF 𝕀 Definitional.Project.BinarySchema.identityValue emptyEnv
      · intro input hInput
        exact False.elim <| hFirstSpaceEmpty input hInput
      · intro input hInput
        exact False.elim <| hFirstSpaceEmpty input hInput
      · intro input _ hInput
        exact False.elim <| hFirstSpaceEmpty input hInput
      · intro first _ _ hFirstMem
        exact False.elim <| hFirstSpaceEmpty first hFirstMem

  rcases hSpaceInjection with
    ⟨spaceInjection, hSpaceInjection⟩
  rcases hFirstPower.2 with
    ⟨firstPowerMap, hFirstPowerMap⟩
  rcases hSecondPower.2.symm hZF 𝕀 with
    ⟨secondPowerMap, hSecondPowerMap⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hFirstPowerMap.1 hSpaceInjection with
    ⟨toSecondSpace, hToSecondSpace⟩
  exact ZF.exists_compositionInjection hZF 𝕀
    hToSecondSpace hSecondPowerMap.1

/-- `(3.10)`：任意基数的零次幂等于一。 -/
theorem zero_exponent {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power base zero one zeroSet oneSet oneValue : ℳ.Domain}
    (hZero : ℳ.IsCardinalOf 𝕀 zero zeroSet)
    (hZeroSet : ∀ value, ¬ ℳ.mem value zeroSet)
    (hOne : ℳ.IsCardinalOf 𝕀 one oneSet)
    (hOneSet : ℳ.IsSingletonOf oneSet oneValue)
    (hPower :
      ℳ.IsCardinalExponentiation 𝕀 power base zero) :
    power = one := by
  rcases hPower with
    ⟨baseSet, exponentSet, space,
      _, hExponent, hSpace, hResult⟩
  have hExponentSetEquinumerous :
      ℳ.Equinumerous 𝕀 exponentSet zeroSet :=
    hExponent.2.symm hZF 𝕀 |>.trans hZF 𝕀 hZero.2
  have hExponentSetEmpty :
      ∀ value, ¬ ℳ.mem value exponentSet := by
    rcases hExponentSetEquinumerous with
      ⟨exponentMap, hExponentMap⟩
    intro value hValue
    rcases hExponentMap.1.1.2.2 value hValue with
      ⟨image, hImage, _⟩
    exact hZeroSet image hImage
  have hSpaceToOneSet :=
    ZF.equinumerous_functionSpaceFromEmpty
      hZF 𝕀 hSpace hExponentSetEmpty hOneSet
  apply hResult.1.eq_of_equinumerous hZF 𝕀 hOne.1
  exact hResult.2.trans hZF 𝕀 <|
    hSpaceToOneSet.trans hZF 𝕀 <|
      hOne.2.symm hZF 𝕀

/-- `(3.10)`：一的任意基数次幂仍等于一。 -/
theorem one_base {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power exponent one oneSet oneValue : ℳ.Domain}
    (hOne : ℳ.IsCardinalOf 𝕀 one oneSet)
    (hOneSet : ℳ.IsSingletonOf oneSet oneValue)
    (hPower :
      ℳ.IsCardinalExponentiation 𝕀 power one exponent) :
    power = one := by
  rcases hPower with
    ⟨baseSet, exponentSet, space,
      hBase, _, hSpace, hResult⟩
  rcases ZF.exists_functionSpace hZF 𝕀 exponentSet oneSet with
    ⟨normalizedSpace, hNormalizedSpace⟩
  have hBaseToOneSet :
      ℳ.Equinumerous 𝕀 baseSet oneSet :=
    hBase.2.symm hZF 𝕀 |>.trans hZF 𝕀 hOne.2
  have hSpaceToNormalized :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hSpace hNormalizedSpace
      (Structure.Equinumerous.refl hZF 𝕀 exponentSet)
      hBaseToOneSet
  have hNormalizedToOneSet :=
    ZF.equinumerous_functionSpaceIntoSingleton
      hZF 𝕀 hNormalizedSpace hOneSet
  apply hResult.1.eq_of_equinumerous hZF 𝕀 hOne.1
  exact hResult.2.trans hZF 𝕀 <|
    hSpaceToNormalized.trans hZF 𝕀 <|
      hNormalizedToOneSet.trans hZF 𝕀 <|
        hOne.2.symm hZF 𝕀

/-- `(3.10)`：非空指数下，零的基数次幂等于零。 -/
theorem zero_base_of_nonempty_exponent {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power exponent zero zeroSet : ℳ.Domain}
    (hExponentNonempty : ∃ value, ℳ.mem value exponent)
    (hZero : ℳ.IsCardinalOf 𝕀 zero zeroSet)
    (hZeroSet : ∀ value, ¬ ℳ.mem value zeroSet)
    (hPower :
      ℳ.IsCardinalExponentiation 𝕀 power zero exponent) :
    power = zero := by
  rcases hPower with
    ⟨baseSet, exponentSet, space,
      hBase, hExponent, hSpace, hResult⟩
  have hExponentSetNonempty :
      ∃ value, ℳ.mem value exponentSet := by
    rcases hExponent.2 with
      ⟨exponentMap, hExponentMap⟩
    rcases hExponentNonempty with
      ⟨value, hValue⟩
    rcases hExponentMap.1.1.2.2 value hValue with
      ⟨image, hImage, _⟩
    exact ⟨image, hImage⟩
  rcases ZF.exists_functionSpace hZF 𝕀 exponentSet zeroSet with
    ⟨normalizedSpace, hNormalizedSpace⟩
  have hBaseToZeroSet :
      ℳ.Equinumerous 𝕀 baseSet zeroSet :=
    hBase.2.symm hZF 𝕀 |>.trans hZF 𝕀 hZero.2
  have hSpaceToNormalized :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hSpace hNormalizedSpace
      (Structure.Equinumerous.refl hZF 𝕀 exponentSet)
      hBaseToZeroSet
  have hNormalizedToZeroSet :=
    ZF.equinumerous_functionSpaceIntoEmpty_of_nonempty
      hZF 𝕀 hNormalizedSpace hExponentSetNonempty hZeroSet
  apply hResult.1.eq_of_equinumerous hZF 𝕀 hZero.1
  exact hResult.2.trans hZF 𝕀 <|
    hSpaceToNormalized.trans hZF 𝕀 <|
      hNormalizedToZeroSet.trans hZF 𝕀 <|
        hZero.2.symm hZF 𝕀

end Structure.IsCardinalExponentiation

end SetTheory
end YesMetaZFC
