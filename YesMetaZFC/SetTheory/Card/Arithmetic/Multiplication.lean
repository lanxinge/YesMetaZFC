import YesMetaZFC.SetTheory.Card.Arithmetic.Equinumerosity

/-!
# 基数乘法

本层证明笛卡尔积定义的基数乘法与代表元选择无关，并导出结合律与对加法的分配律。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure.IsCardinalMultiplication

/-- 固定两个输入基数时，基数乘法的结果唯一。 -/
theorem eq {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second left right : ℳ.Domain}
    (hFirst :
      ℳ.IsCardinalMultiplication 𝕀 first left right)
    (hSecond :
      ℳ.IsCardinalMultiplication 𝕀 second left right) :
    first = second := by
  rcases hFirst with
    ⟨firstLeft, firstRight, firstProduct,
      hFirstLeft, hFirstRight, hFirstProduct, hFirstCardinal⟩
  rcases hSecond with
    ⟨secondLeft, secondRight, secondProduct,
      hSecondLeft, hSecondRight, hSecondProduct, hSecondCardinal⟩
  have hLeftEquinumerous :
      ℳ.Equinumerous 𝕀 firstLeft secondLeft :=
    hFirstLeft.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondLeft.2
  have hRightEquinumerous :
      ℳ.Equinumerous 𝕀 firstRight secondRight :=
    hFirstRight.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondRight.2
  rcases hLeftEquinumerous with ⟨leftFunction, hLeftFunction⟩
  rcases hRightEquinumerous with ⟨rightFunction, hRightFunction⟩
  have hProductEquinumerous :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hFirstProduct hSecondProduct hLeftFunction hRightFunction
  apply hFirstCardinal.1.eq_of_equinumerous
      hZF 𝕀 hSecondCardinal.1
  exact hFirstCardinal.2.trans hZF 𝕀 <|
    hProductEquinumerous.trans hZF 𝕀 <|
      hSecondCardinal.2.symm hZF 𝕀

/-- 基数乘法满足交换律。 -/
theorem commutative {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second left right : ℳ.Domain}
    (hFirst :
      ℳ.IsCardinalMultiplication 𝕀 first left right)
    (hSecond :
      ℳ.IsCardinalMultiplication 𝕀 second right left) :
    first = second := by
  rcases hFirst with
    ⟨firstLeft, firstRight, firstProduct,
      hFirstLeft, hFirstRight, hFirstProduct, hFirstCardinal⟩
  rcases hSecond with
    ⟨secondLeft, secondRight, secondProduct,
      hSecondLeft, hSecondRight, hSecondProduct, hSecondCardinal⟩
  have hLeftEquinumerous :
      ℳ.Equinumerous 𝕀 firstLeft secondRight :=
    hFirstLeft.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondRight.2
  have hRightEquinumerous :
      ℳ.Equinumerous 𝕀 firstRight secondLeft :=
    hFirstRight.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondLeft.2
  rcases hLeftEquinumerous with ⟨leftFunction, hLeftFunction⟩
  rcases hRightEquinumerous with ⟨rightFunction, hRightFunction⟩
  have hProductEquinumerous :=
    ZF.equinumerous_swappedCartesianProduct hZF 𝕀
      hFirstProduct hSecondProduct hLeftFunction hRightFunction
  apply hFirstCardinal.1.eq_of_equinumerous
      hZF 𝕀 hSecondCardinal.1
  exact hFirstCardinal.2.trans hZF 𝕀 <|
    hProductEquinumerous.trans hZF 𝕀 <|
      hSecondCardinal.2.symm hZF 𝕀

/-- `(3.4)`：基数乘法满足结合律。 -/
theorem associative {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second third firstSecond secondThird
      leftAssociated rightAssociated : ℳ.Domain}
    (hFirstSecond :
      ℳ.IsCardinalMultiplication 𝕀 firstSecond first second)
    (hLeftAssociated :
      ℳ.IsCardinalMultiplication 𝕀
        leftAssociated firstSecond third)
    (hSecondThird :
      ℳ.IsCardinalMultiplication 𝕀 secondThird second third)
    (hRightAssociated :
      ℳ.IsCardinalMultiplication 𝕀
        rightAssociated first secondThird) :
    leftAssociated = rightAssociated := by
  rcases hFirstSecond with
    ⟨firstSet, secondSet, firstProduct,
      hFirstSet, hSecondSet, hFirstProduct, hFirstSecondCardinal⟩
  rcases hLeftAssociated with
    ⟨firstSecondSet, thirdSet, leftProduct,
      hFirstSecondSet, hThirdSet, hLeftProduct, hLeftCardinal⟩
  rcases hSecondThird with
    ⟨secondSet', thirdSet', secondProduct,
      hSecondSet', hThirdSet', hSecondProduct, hSecondThirdCardinal⟩
  rcases hRightAssociated with
    ⟨firstSet', secondThirdSet, rightProduct,
      hFirstSet', hSecondThirdSet, hRightProduct, hRightCardinal⟩

  rcases ZF.exists_cartesianProduct hZF 𝕀
      firstProduct thirdSet with
    ⟨normalizedLeft, hNormalizedLeft⟩
  have hFirstSecondEquinumerous :
      ℳ.Equinumerous 𝕀 firstSecondSet firstProduct :=
    hFirstSecondSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hFirstSecondCardinal.2
  rcases hFirstSecondEquinumerous with
    ⟨firstSecondMap, hFirstSecondMap⟩
  rcases Structure.Equinumerous.refl hZF 𝕀 thirdSet with
    ⟨thirdIdentity, hThirdIdentity⟩
  have hLeftNormalized :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hLeftProduct hNormalizedLeft
      hFirstSecondMap hThirdIdentity

  rcases ZF.exists_cartesianProduct hZF 𝕀
      secondSet thirdSet with
    ⟨normalizedSecondThird, hNormalizedSecondThird⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀
      firstSet normalizedSecondThird with
    ⟨normalizedRight, hNormalizedRight⟩
  have hAssociate :=
    ZF.equinumerous_associatedCartesianProduct hZF 𝕀
      hFirstProduct hNormalizedLeft
      hNormalizedSecondThird hNormalizedRight

  have hFirstEquinumerous :
      ℳ.Equinumerous 𝕀 firstSet firstSet' :=
    hFirstSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hFirstSet'.2
  have hSecondEquinumerous :
      ℳ.Equinumerous 𝕀 secondSet secondSet' :=
    hSecondSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondSet'.2
  have hThirdEquinumerous :
      ℳ.Equinumerous 𝕀 thirdSet thirdSet' :=
    hThirdSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hThirdSet'.2
  rcases hSecondEquinumerous with
    ⟨secondMap, hSecondMap⟩
  rcases hThirdEquinumerous with
    ⟨thirdMap, hThirdMap⟩
  have hSecondThirdProducts :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hNormalizedSecondThird hSecondProduct
      hSecondMap hThirdMap
  have hSecondThirdToOuter :
      ℳ.Equinumerous 𝕀 normalizedSecondThird secondThirdSet :=
    hSecondThirdProducts.trans hZF 𝕀 <|
      hSecondThirdCardinal.2.symm hZF 𝕀 |>.trans hZF 𝕀
        hSecondThirdSet.2
  rcases hFirstEquinumerous with
    ⟨firstMap, hFirstMap⟩
  rcases hSecondThirdToOuter with
    ⟨secondThirdMap, hSecondThirdMap⟩
  have hRightNormalized :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hNormalizedRight hRightProduct
      hFirstMap hSecondThirdMap

  apply hLeftCardinal.1.eq_of_equinumerous
      hZF 𝕀 hRightCardinal.1
  exact hLeftCardinal.2.trans hZF 𝕀 <|
    hLeftNormalized.trans hZF 𝕀 <|
      hAssociate.trans hZF 𝕀 <|
        hRightNormalized.trans hZF 𝕀 <|
          hRightCardinal.2.symm hZF 𝕀

/-- 基数乘法对基数加法满足左分配律。 -/
theorem leftDistributive {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second third secondThird firstSecond firstThird
      leftDistributed rightDistributed : ℳ.Domain}
    (hSecondThird :
      ℳ.IsCardinalAddition 𝕀 secondThird second third)
    (hLeftDistributed :
      ℳ.IsCardinalMultiplication 𝕀
        leftDistributed first secondThird)
    (hFirstSecond :
      ℳ.IsCardinalMultiplication 𝕀 firstSecond first second)
    (hFirstThird :
      ℳ.IsCardinalMultiplication 𝕀 firstThird first third)
    (hRightDistributed :
      ℳ.IsCardinalAddition 𝕀
        rightDistributed firstSecond firstThird) :
    leftDistributed = rightDistributed := by
  rcases hSecondThird with
    ⟨secondSet, thirdSet, secondUnion,
      hSecondSet, hThirdSet, hSecondDisjoint,
      hSecondUnion, hSecondThirdCardinal⟩
  rcases hLeftDistributed with
    ⟨leftSet, secondThirdSet, leftProduct,
      hLeftSet, hSecondThirdSet,
      hLeftProduct, hLeftCardinal⟩
  rcases hFirstSecond with
    ⟨firstSet, secondSet', firstProduct,
      hFirstSet, hSecondSet',
      hFirstProduct, hFirstSecondCardinal⟩
  rcases hFirstThird with
    ⟨firstSet', thirdSet', thirdProduct,
      hFirstSet', hThirdSet',
      hThirdProduct, hFirstThirdCardinal⟩
  rcases hRightDistributed with
    ⟨firstSecondSet, firstThirdSet, rightUnion,
      hFirstSecondSet, hFirstThirdSet, hRightDisjoint,
      hRightUnion, hRightCardinal⟩

  rcases KP.exists_empty (ZF.modelsKP hZF) with
    ⟨leftTag, hLeftTag⟩
  rcases KP.exists_singleton (ZF.modelsKP hZF) leftTag with
    ⟨rightTag, hRightTag⟩
  have hTags : leftTag ≠ rightTag := by
    intro hEq
    have hMember : ℳ.mem leftTag rightTag :=
      (hRightTag leftTag).mpr rfl
    rw [← hEq] at hMember
    exact hLeftTag leftTag hMember

  rcases ZF.exists_taggedUnion hZF 𝕀 hTags secondSet thirdSet with
    ⟨normalizedSum, hNormalizedSum⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀 leftSet normalizedSum with
    ⟨normalizedLeft, hNormalizedLeft⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀 leftSet secondSet with
    ⟨normalizedFirstProduct, hNormalizedFirstProduct⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀 leftSet thirdSet with
    ⟨normalizedThirdProduct, hNormalizedThirdProduct⟩
  rcases ZF.exists_taggedUnion hZF 𝕀 hTags
      normalizedFirstProduct normalizedThirdProduct with
    ⟨normalizedRight, hNormalizedRight⟩

  have hSecondUnionToNormalized :=
    ZF.equinumerous_unionToTaggedUnion hZF 𝕀
      hSecondUnion hSecondDisjoint hNormalizedSum
      (Structure.Equinumerous.refl hZF 𝕀 secondSet)
      (Structure.Equinumerous.refl hZF 𝕀 thirdSet)
  have hSecondThirdToNormalized :
      ℳ.Equinumerous 𝕀 secondThirdSet normalizedSum :=
    hSecondThirdSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hSecondThirdCardinal.2 |>.trans hZF 𝕀
        hSecondUnionToNormalized
  rcases Structure.Equinumerous.refl hZF 𝕀 leftSet with
    ⟨leftIdentity, hLeftIdentity⟩
  rcases hSecondThirdToNormalized with
    ⟨secondThirdMap, hSecondThirdMap⟩
  have hLeftNormalized :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hLeftProduct hNormalizedLeft
      hLeftIdentity hSecondThirdMap

  have hDistribute :=
    ZF.equinumerous_productOverTaggedUnion hZF 𝕀
      hNormalizedSum hNormalizedLeft
      hNormalizedFirstProduct hNormalizedThirdProduct
      hNormalizedRight

  have hLeftToFirst :
      ℳ.Equinumerous 𝕀 leftSet firstSet :=
    hLeftSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hFirstSet.2
  have hSecondToSecond :
      ℳ.Equinumerous 𝕀 secondSet secondSet' :=
    hSecondSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondSet'.2
  rcases hLeftToFirst with ⟨firstMap, hFirstMap⟩
  rcases hSecondToSecond with ⟨secondMap, hSecondMap⟩
  have hNormalizedFirstToProduct :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hNormalizedFirstProduct hFirstProduct
      hFirstMap hSecondMap
  have hNormalizedFirstToRight :
      ℳ.Equinumerous 𝕀 normalizedFirstProduct firstSecondSet :=
    hNormalizedFirstToProduct.trans hZF 𝕀 <|
      (hFirstSecondCardinal.2.symm hZF 𝕀).trans hZF 𝕀
        hFirstSecondSet.2

  have hLeftToThird :
      ℳ.Equinumerous 𝕀 leftSet firstSet' :=
    hLeftSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hFirstSet'.2
  have hThirdToThird :
      ℳ.Equinumerous 𝕀 thirdSet thirdSet' :=
    hThirdSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hThirdSet'.2
  rcases hLeftToThird with ⟨thirdFirstMap, hThirdFirstMap⟩
  rcases hThirdToThird with ⟨thirdMap, hThirdMap⟩
  have hNormalizedThirdToProduct :=
    ZF.equinumerous_cartesianProduct hZF 𝕀
      hNormalizedThirdProduct hThirdProduct
      hThirdFirstMap hThirdMap
  have hNormalizedThirdToRight :
      ℳ.Equinumerous 𝕀 normalizedThirdProduct firstThirdSet :=
    hNormalizedThirdToProduct.trans hZF 𝕀 <|
      (hFirstThirdCardinal.2.symm hZF 𝕀).trans hZF 𝕀
        hFirstThirdSet.2

  have hRightToNormalized :=
    ZF.equinumerous_unionToTaggedUnion hZF 𝕀
      hRightUnion hRightDisjoint hNormalizedRight
      (hNormalizedFirstToRight.symm hZF 𝕀)
      (hNormalizedThirdToRight.symm hZF 𝕀)

  apply hLeftCardinal.1.eq_of_equinumerous
      hZF 𝕀 hRightCardinal.1
  exact hLeftCardinal.2.trans hZF 𝕀 <|
    hLeftNormalized.trans hZF 𝕀 <|
      hDistribute.trans hZF 𝕀 <|
        (hRightToNormalized.symm hZF 𝕀).trans hZF 𝕀 <|
          hRightCardinal.2.symm hZF 𝕀

end Structure.IsCardinalMultiplication

end SetTheory
end YesMetaZFC
