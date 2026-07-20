import YesMetaZFC.SetTheory.Card.Arithmetic.Equinumerosity

/-!
# 基数加法

本层证明基数加法与不交代表元的选择无关，并导出交换律与结合律。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure.IsCardinalAddition

/-- 固定两个输入基数时，基数加法的结果唯一。 -/
theorem eq {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second left right : ℳ.Domain}
    (hFirst : ℳ.IsCardinalAddition 𝕀 first left right)
    (hSecond : ℳ.IsCardinalAddition 𝕀 second left right) :
    first = second := by
  rcases hFirst with
    ⟨firstLeft, firstRight, firstUnion,
      hFirstLeft, hFirstRight, hFirstDisjoint,
      hFirstUnion, hFirstCardinal⟩
  rcases hSecond with
    ⟨secondLeft, secondRight, secondUnion,
      hSecondLeft, hSecondRight, hSecondDisjoint,
      hSecondUnion, hSecondCardinal⟩
  have hLeftEquinumerous :
      ℳ.Equinumerous 𝕀 firstLeft secondLeft :=
    hFirstLeft.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondLeft.2
  have hRightEquinumerous :
      ℳ.Equinumerous 𝕀 firstRight secondRight :=
    hFirstRight.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondRight.2
  rcases hLeftEquinumerous with ⟨leftFunction, hLeftFunction⟩
  rcases hRightEquinumerous with ⟨rightFunction, hRightFunction⟩
  have hUnionEquinumerous :=
    ZF.equinumerous_unionOfTwo hZF 𝕀
      hFirstUnion hSecondUnion hFirstDisjoint hSecondDisjoint
      hLeftFunction hRightFunction
  apply hFirstCardinal.1.eq_of_equinumerous
      hZF 𝕀 hSecondCardinal.1
  exact hFirstCardinal.2.trans hZF 𝕀 <|
    hUnionEquinumerous.trans hZF 𝕀 <|
      hSecondCardinal.2.symm hZF 𝕀

/-- 基数加法满足交换律。 -/
theorem commutative {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second left right : ℳ.Domain}
    (hFirst : ℳ.IsCardinalAddition 𝕀 first left right)
    (hSecond : ℳ.IsCardinalAddition 𝕀 second right left) :
    first = second := by
  rcases hFirst with
    ⟨leftSet, rightSet, union,
      hLeft, hRight, hDisjoint, hUnion, hCardinal⟩
  apply IsCardinalAddition.eq hZF 𝕀
      (first := first) (second := second)
  · exact ⟨rightSet, leftSet, union,
      hRight, hLeft, hDisjoint.symm, hUnion.swap, hCardinal⟩
  · exact hSecond

/-- `(3.3)`：基数加法满足结合律。 -/
theorem associative {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second third firstSecond secondThird
      leftAssociated rightAssociated : ℳ.Domain}
    (hFirstSecond :
      ℳ.IsCardinalAddition 𝕀 firstSecond first second)
    (hLeftAssociated :
      ℳ.IsCardinalAddition 𝕀
        leftAssociated firstSecond third)
    (hSecondThird :
      ℳ.IsCardinalAddition 𝕀 secondThird second third)
    (hRightAssociated :
      ℳ.IsCardinalAddition 𝕀
        rightAssociated first secondThird) :
    leftAssociated = rightAssociated := by
  rcases hFirstSecond with
    ⟨firstSet, secondSet, firstUnion,
      hFirstSet, hSecondSet, hFirstDisjoint,
      hFirstUnion, hFirstSecondCardinal⟩
  rcases hLeftAssociated with
    ⟨firstSecondSet, thirdSet, leftUnion,
      hFirstSecondSet, hThirdSet, hLeftDisjoint,
      hLeftUnion, hLeftCardinal⟩
  rcases hSecondThird with
    ⟨secondSet', thirdSet', secondUnion,
      hSecondSet', hThirdSet', hSecondDisjoint,
      hSecondUnion, hSecondThirdCardinal⟩
  rcases hRightAssociated with
    ⟨firstSet', secondThirdSet, rightUnion,
      hFirstSet', hSecondThirdSet, hRightDisjoint,
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

  rcases ZF.exists_taggedUnion hZF 𝕀 hTags firstSet secondSet with
    ⟨leftMiddle, hLeftMiddle⟩
  rcases ZF.exists_taggedUnion hZF 𝕀 hTags leftMiddle thirdSet with
    ⟨normalizedLeft, hNormalizedLeft⟩
  rcases ZF.exists_taggedUnion hZF 𝕀 hTags secondSet thirdSet with
    ⟨middleRight, hMiddleRight⟩
  rcases ZF.exists_taggedUnion hZF 𝕀 hTags firstSet middleRight with
    ⟨normalizedRight, hNormalizedRight⟩

  have hFirstUnionToLeftMiddle :=
    ZF.equinumerous_unionToTaggedUnion hZF 𝕀
      hFirstUnion hFirstDisjoint hLeftMiddle
      (Structure.Equinumerous.refl hZF 𝕀 firstSet)
      (Structure.Equinumerous.refl hZF 𝕀 secondSet)
  have hFirstSecondToLeftMiddle :
      ℳ.Equinumerous 𝕀 firstSecondSet leftMiddle :=
    hFirstSecondSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hFirstSecondCardinal.2 |>.trans hZF 𝕀
        hFirstUnionToLeftMiddle
  have hLeftNormalized :=
    ZF.equinumerous_unionToTaggedUnion hZF 𝕀
      hLeftUnion hLeftDisjoint hNormalizedLeft
      hFirstSecondToLeftMiddle
      (Structure.Equinumerous.refl hZF 𝕀 thirdSet)

  have hAssociate :=
    ZF.equinumerous_associatedTaggedUnion hZF 𝕀
      hTags hLeftMiddle hNormalizedLeft
      hMiddleRight hNormalizedRight

  have hSecondEquinumerous :
      ℳ.Equinumerous 𝕀 secondSet' secondSet :=
    hSecondSet'.2.symm hZF 𝕀 |>.trans hZF 𝕀 hSecondSet.2
  have hThirdEquinumerous :
      ℳ.Equinumerous 𝕀 thirdSet' thirdSet :=
    hThirdSet'.2.symm hZF 𝕀 |>.trans hZF 𝕀 hThirdSet.2
  have hSecondUnionToMiddleRight :=
    ZF.equinumerous_unionToTaggedUnion hZF 𝕀
      hSecondUnion hSecondDisjoint hMiddleRight
      hSecondEquinumerous hThirdEquinumerous
  have hSecondThirdToMiddleRight :
      ℳ.Equinumerous 𝕀 secondThirdSet middleRight :=
    hSecondThirdSet.2.symm hZF 𝕀 |>.trans hZF 𝕀
      hSecondThirdCardinal.2 |>.trans hZF 𝕀
        hSecondUnionToMiddleRight
  have hFirstEquinumerous :
      ℳ.Equinumerous 𝕀 firstSet' firstSet :=
    hFirstSet'.2.symm hZF 𝕀 |>.trans hZF 𝕀 hFirstSet.2
  have hRightToNormalized :=
    ZF.equinumerous_unionToTaggedUnion hZF 𝕀
      hRightUnion hRightDisjoint hNormalizedRight
      hFirstEquinumerous hSecondThirdToMiddleRight

  apply hLeftCardinal.1.eq_of_equinumerous
      hZF 𝕀 hRightCardinal.1
  exact hLeftCardinal.2.trans hZF 𝕀 <|
    hLeftNormalized.trans hZF 𝕀 <|
      hAssociate.trans hZF 𝕀 <|
        (hRightToNormalized.symm hZF 𝕀).trans hZF 𝕀 <|
          hRightCardinal.2.symm hZF 𝕀

end Structure.IsCardinalAddition

end SetTheory
end YesMetaZFC
