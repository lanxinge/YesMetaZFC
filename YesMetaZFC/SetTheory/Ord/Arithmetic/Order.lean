import YesMetaZFC.SetTheory.Ord.Arithmetic.Semantics

/-!
# 线性序的序和与右字典序积

本文件证明定义 2.22、2.23 的结构性内容：不相交线性序的序和仍是线性序，
两个线性序的右字典序积仍是线性序。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure.IsLinearOrderSum

/-- 不相交线性序的序和关系在并载体上仍是严格线序。 -/
theorem isSetCodedLinearOrder
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sumCarrier sumRelation leftCarrier leftRelation
      rightCarrier rightRelation : ℳ.Domain}
    (hSum : ℳ.IsLinearOrderSum 𝕀
      sumCarrier sumRelation leftCarrier leftRelation
      rightCarrier rightRelation) :
    ℳ.IsSetCodedLinearOrder 𝕀 sumRelation sumCarrier := by
  rcases hSum with
    ⟨hLeft, hRight, hDisjoint, hCarrier,
      hSetRelation, hRelation⟩
  refine ⟨hSetRelation, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro value hValue hSelf
    rcases (hCarrier value).mp hValue with
      hValueLeft | hValueRight
    · rcases (hRelation value value).mp hSelf with
        hInsideLeft | hInsideRight | hAcross
      · exact hLeft.2.1.1 value hValueLeft hInsideLeft.2.2
      · exact hDisjoint value
          ⟨hValueLeft, hInsideRight.1⟩
      · exact hDisjoint value
          ⟨hAcross.1, hAcross.2⟩
    · rcases (hRelation value value).mp hSelf with
        hInsideLeft | hInsideRight | hAcross
      · exact hDisjoint value
          ⟨hInsideLeft.1, hValueRight⟩
      · exact hRight.2.1.1 value hValueRight hInsideRight.2.2
      · exact hDisjoint value
          ⟨hAcross.1, hAcross.2⟩
  · intro left hLeftCarrier middle hMiddleCarrier
      right hRightCarrier hLeftMiddle hMiddleRight
    rcases (hRelation left middle).mp hLeftMiddle with
      hLeftLeft | hLeftRight | hLeftAcross
    · rcases (hRelation middle right).mp hMiddleRight with
        hRightLeft | hRightRight | hRightAcross
      · exact (hRelation left right).mpr <| Or.inl
          ⟨hLeftLeft.1, hRightLeft.2.1,
            hLeft.2.1.2 left hLeftLeft.1
              middle hLeftLeft.2.1
              right hRightLeft.2.1
              hLeftLeft.2.2 hRightLeft.2.2⟩
      · exact False.elim <| hDisjoint middle
          ⟨hLeftLeft.2.1, hRightRight.1⟩
      · exact (hRelation left right).mpr <| Or.inr <| Or.inr
          ⟨hLeftLeft.1, hRightAcross.2⟩
    · rcases (hRelation middle right).mp hMiddleRight with
        hRightLeft | hRightRight | hRightAcross
      · exact False.elim <| hDisjoint middle
          ⟨hRightLeft.1, hLeftRight.2.1⟩
      · exact (hRelation left right).mpr <| Or.inr <| Or.inl
          ⟨hLeftRight.1, hRightRight.2.1,
            hRight.2.1.2 left hLeftRight.1
              middle hLeftRight.2.1
              right hRightRight.2.1
              hLeftRight.2.2 hRightRight.2.2⟩
      · exact False.elim <| hDisjoint middle
          ⟨hRightAcross.1, hLeftRight.2.1⟩
    · rcases (hRelation middle right).mp hMiddleRight with
        hRightLeft | hRightRight | hRightAcross
      · exact False.elim <| hDisjoint middle
          ⟨hRightLeft.1, hLeftAcross.2⟩
      · exact (hRelation left right).mpr <| Or.inr <| Or.inr
          ⟨hLeftAcross.1, hRightRight.2.1⟩
      · exact False.elim <| hDisjoint middle
          ⟨hRightAcross.1, hLeftAcross.2⟩
  · intro left hLeftCarrier right hRightCarrier
    rcases (hCarrier left).mp hLeftCarrier with
      hLeftInLeft | hLeftInRight
    · rcases (hCarrier right).mp hRightCarrier with
        hRightInLeft | hRightInRight
      · rcases hLeft.2.2 left hLeftInLeft
            right hRightInLeft with
          hSame | hLess | hGreater
        · exact Or.inl hSame
        · exact Or.inr <| Or.inl <|
            (hRelation left right).mpr <| Or.inl
              ⟨hLeftInLeft, hRightInLeft, hLess⟩
        · exact Or.inr <| Or.inr <|
            (hRelation right left).mpr <| Or.inl
              ⟨hRightInLeft, hLeftInLeft, hGreater⟩
      · exact Or.inr <| Or.inl <|
          (hRelation left right).mpr <| Or.inr <| Or.inr
            ⟨hLeftInLeft, hRightInRight⟩
    · rcases (hCarrier right).mp hRightCarrier with
        hRightInLeft | hRightInRight
      · exact Or.inr <| Or.inr <|
          (hRelation right left).mpr <| Or.inr <| Or.inr
            ⟨hRightInLeft, hLeftInRight⟩
      · rcases hRight.2.2 left hLeftInRight
            right hRightInRight with
          hSame | hLess | hGreater
        · exact Or.inl hSame
        · exact Or.inr <| Or.inl <|
            (hRelation left right).mpr <| Or.inr <| Or.inl
              ⟨hLeftInRight, hRightInRight, hLess⟩
        · exact Or.inr <| Or.inr <|
            (hRelation right left).mpr <| Or.inr <| Or.inl
              ⟨hRightInRight, hLeftInRight, hGreater⟩

end Structure.IsLinearOrderSum

namespace Structure.IsLinearOrderProduct

/-- 右字典序积关系在笛卡尔积载体上仍是严格线序。 -/
theorem isSetCodedLinearOrder
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {productCarrier productRelation leftCarrier leftRelation
      rightCarrier rightRelation : ℳ.Domain}
    (hProduct : ℳ.IsLinearOrderProduct 𝕀
      productCarrier productRelation leftCarrier leftRelation
      rightCarrier rightRelation) :
    ℳ.IsSetCodedLinearOrder 𝕀
      productRelation productCarrier := by
  rcases hProduct with
    ⟨hLeft, hRight, hCarrier, hSetRelation, hRelation⟩
  have lex_iff
      {firstPair secondPair firstLeft firstRight
        secondLeft secondRight : ℳ.Domain}
      (hFirstCode :
        𝕀.Codes firstPair firstLeft firstRight)
      (hSecondCode :
        𝕀.Codes secondPair secondLeft secondRight)
      (hFirstLeft : ℳ.mem firstLeft leftCarrier)
      (hFirstRight : ℳ.mem firstRight rightCarrier)
      (hSecondLeft : ℳ.mem secondLeft leftCarrier)
      (hSecondRight : ℳ.mem secondRight rightCarrier) :
      ℳ.PairMember 𝕀 firstPair secondPair productRelation ↔
        ℳ.PairMember 𝕀 firstRight secondRight
            rightRelation ∨
          (ℳ.SameMembers firstRight secondRight ∧
            ℳ.PairMember 𝕀 firstLeft secondLeft
              leftRelation) := by
    constructor
    · intro hPair
      rcases (hRelation firstPair secondPair).mp hPair with
        ⟨encodedFirstLeft, hEncodedFirstLeft,
          encodedFirstRight, hEncodedFirstRight,
          encodedSecondLeft, hEncodedSecondLeft,
          encodedSecondRight, hEncodedSecondRight,
          hEncodedFirst, hEncodedSecond, hOrder⟩
      have hFirstCoordinates :=
        𝕀.injective hFirstCode hEncodedFirst
      have hSecondCoordinates :=
        𝕀.injective hSecondCode hEncodedSecond
      simpa [hFirstCoordinates.1, hFirstCoordinates.2,
        hSecondCoordinates.1, hSecondCoordinates.2] using hOrder
    · intro hOrder
      exact (hRelation firstPair secondPair).mpr
        ⟨firstLeft, hFirstLeft,
          firstRight, hFirstRight,
          secondLeft, hSecondLeft,
          secondRight, hSecondRight,
          hFirstCode, hSecondCode, hOrder⟩
  refine ⟨hSetRelation, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro pair hPair hSelf
    rcases (hCarrier pair).mp hPair with
      ⟨left, hLeftCarrier, right, hRightCarrier, hCode⟩
    rcases (lex_iff hCode hCode
      hLeftCarrier hRightCarrier hLeftCarrier hRightCarrier).mp
      hSelf with
      hRightSelf | ⟨_, hLeftSelf⟩
    · exact hRight.2.1.1 right hRightCarrier hRightSelf
    · exact hLeft.2.1.1 left hLeftCarrier hLeftSelf
  · intro firstPair hFirstPair secondPair hSecondPair
      thirdPair hThirdPair hFirstSecond hSecondThird
    rcases (hCarrier firstPair).mp hFirstPair with
      ⟨firstLeft, hFirstLeft, firstRight, hFirstRight, hFirstCode⟩
    rcases (hCarrier secondPair).mp hSecondPair with
      ⟨secondLeft, hSecondLeft, secondRight, hSecondRight,
        hSecondCode⟩
    rcases (hCarrier thirdPair).mp hThirdPair with
      ⟨thirdLeft, hThirdLeft, thirdRight, hThirdRight, hThirdCode⟩
    rcases (lex_iff hFirstCode hSecondCode
        hFirstLeft hFirstRight hSecondLeft hSecondRight).mp
        hFirstSecond with
      hFirstRightSecond | hFirstEqual
    · rcases (lex_iff hSecondCode hThirdCode
        hSecondLeft hSecondRight hThirdLeft hThirdRight).mp
        hSecondThird with
        hSecondRightThird | hSecondEqual
      · exact (lex_iff hFirstCode hThirdCode
          hFirstLeft hFirstRight hThirdLeft hThirdRight).mpr <| Or.inl <|
          hRight.2.1.2 firstRight hFirstRight
            secondRight hSecondRight thirdRight hThirdRight
            hFirstRightSecond hSecondRightThird
      · have hSecondThirdEq :=
          hExt.eq_of_same_members secondRight thirdRight
            hSecondEqual.1
        subst thirdRight
        exact (lex_iff hFirstCode hThirdCode
          hFirstLeft hFirstRight hThirdLeft hThirdRight).mpr <|
          Or.inl hFirstRightSecond
    · rcases (lex_iff hSecondCode hThirdCode
        hSecondLeft hSecondRight hThirdLeft hThirdRight).mp
        hSecondThird with
        hSecondRightThird | hSecondEqual
      · have hFirstSecondEq :=
          hExt.eq_of_same_members firstRight secondRight
            hFirstEqual.1
        subst secondRight
        exact (lex_iff hFirstCode hThirdCode
          hFirstLeft hFirstRight hThirdLeft hThirdRight).mpr <|
          Or.inl hSecondRightThird
      · have hFirstSecondEq :=
          hExt.eq_of_same_members firstRight secondRight
            hFirstEqual.1
        have hSecondThirdEq :=
          hExt.eq_of_same_members secondRight thirdRight
            hSecondEqual.1
        subst secondRight
        subst thirdRight
        exact (lex_iff hFirstCode hThirdCode
          hFirstLeft hFirstRight hThirdLeft hThirdRight).mpr <| Or.inr
          ⟨fun _ => Iff.rfl,
            hLeft.2.1.2 firstLeft hFirstLeft
              secondLeft hSecondLeft thirdLeft hThirdLeft
              hFirstEqual.2 hSecondEqual.2⟩
  · intro firstPair hFirstPair secondPair hSecondPair
    rcases (hCarrier firstPair).mp hFirstPair with
      ⟨firstLeft, hFirstLeft, firstRight, hFirstRight, hFirstCode⟩
    rcases (hCarrier secondPair).mp hSecondPair with
      ⟨secondLeft, hSecondLeft, secondRight, hSecondRight,
        hSecondCode⟩
    rcases hRight.2.2 firstRight hFirstRight
        secondRight hSecondRight with
      hSameRight | hRightLess | hRightGreater
    · have hRightEq :=
        hExt.eq_of_same_members firstRight secondRight hSameRight
      subst secondRight
      rcases hLeft.2.2 firstLeft hFirstLeft
          secondLeft hSecondLeft with
        hSameLeft | hLeftLess | hLeftGreater
      · have hLeftEq :=
          hExt.eq_of_same_members firstLeft secondLeft hSameLeft
        subst secondLeft
        have hPairEq :=
          𝕀.unique hFirstCode hSecondCode
        subst secondPair
        exact Or.inl fun _ => Iff.rfl
      · exact Or.inr <| Or.inl <|
          (lex_iff hFirstCode hSecondCode
            hFirstLeft hFirstRight hSecondLeft hSecondRight).mpr <| Or.inr
            ⟨fun _ => Iff.rfl, hLeftLess⟩
      · exact Or.inr <| Or.inr <|
          (lex_iff hSecondCode hFirstCode
            hSecondLeft hSecondRight hFirstLeft hFirstRight).mpr <| Or.inr
            ⟨fun _ => Iff.rfl, hLeftGreater⟩
    · exact Or.inr <| Or.inl <|
        (lex_iff hFirstCode hSecondCode
          hFirstLeft hFirstRight hSecondLeft hSecondRight).mpr <|
          Or.inl hRightLess
    · exact Or.inr <| Or.inr <|
        (lex_iff hSecondCode hFirstCode
          hSecondLeft hSecondRight hFirstLeft hFirstRight).mpr <|
          Or.inl hRightGreater

end Structure.IsLinearOrderProduct

end SetTheory
end YesMetaZFC
