import YesMetaZFC.SetTheory.Ord.OrderType

/-!
# 序数对的典范次序

本层形式化基数论中使用的典范序数对次序：先比较两个坐标的最大值，最大值相同时
依次比较第一、第二坐标。关系本身由对象语言 schema 定义，并可在任意序数方块的
模型内部笛卡尔积上集合化。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `maximum` 是两个可比较对象按隶属次序取得的最大者；相等时固定选择左侧。 -/
def IsOrdinalMaximum {ℳ : Structure.{u}}
    (left right maximum : ℳ.Domain) : Prop :=
  (maximum = left ∧ (right = left ∨ ℳ.mem right left)) ∨
    (maximum = right ∧ ℳ.mem left right)

/-- 两个有序数坐标编码之间的典范次序。 -/
def CanonicalOrdinalPairLess {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (first second : ℳ.Domain) : Prop :=
  ∃ firstLeft firstRight secondLeft secondRight firstMaximum secondMaximum,
    𝕀.Codes first firstLeft firstRight ∧
      𝕀.Codes second secondLeft secondRight ∧
        ℳ.IsOrdinalMaximum firstLeft firstRight firstMaximum ∧
          ℳ.IsOrdinalMaximum secondLeft secondRight secondMaximum ∧
            (ℳ.mem firstMaximum secondMaximum ∨
              (firstMaximum = secondMaximum ∧
                (ℳ.mem firstLeft secondLeft ∨
                  (firstLeft = secondLeft ∧
                    ℳ.mem firstRight secondRight))))

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- 两个序数中的较大者，相等时固定选择左侧。 -/
def isOrdinalMaximum {depth : Nat}
    (left right maximum : Term depth) : Formula 1 depth :=
  .disj
    (.conj (extensionalEq maximum left)
      (.disj (extensionalEq right left) (.mem right left)))
    (.conj (extensionalEq maximum right) (.mem left right))

/-- 文献中的序数对典范次序。 -/
def canonicalOrdinalPairLess
    (𝒞 : OrderedPairConvention) {depth : Nat}
    (first second : Term depth) : Formula 1 depth :=
  .existsE <| .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
    .conj
      (𝒞.code first.weaken.weaken.weaken.weaken.weaken.weaken
        (.bound 5) (.bound 4)) <|
    .conj
      (𝒞.code second.weaken.weaken.weaken.weaken.weaken.weaken
        (.bound 3) (.bound 2)) <|
    .conj
      (isOrdinalMaximum (.bound 5) (.bound 4) (.bound 1)) <|
    .conj
      (isOrdinalMaximum (.bound 3) (.bound 2) (.bound 0)) <|
      .disj
        (.mem (.bound 1) (.bound 0))
        (.conj (extensionalEq (.bound 1) (.bound 0)) <|
          .disj
            (.mem (.bound 5) (.bound 3))
            (.conj (extensionalEq (.bound 5) (.bound 3))
              (.mem (.bound 4) (.bound 2))))

end Formula

namespace BinarySchema

/-- 无参数的序数对典范次序 schema。 -/
def canonicalOrdinalPairLess
    (𝒞 : OrderedPairConvention) : BinarySchema 0 where
  body := Formula.canonicalOrdinalPairLess 𝒞 (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.canonicalOrdinalPairLess, Formula.isOrdinalMaximum,
      Formula.extensionalEq, Formula.FreeClosed]

/-- 从有序对编码取第一坐标。 -/
def orderedPairFirst
    (𝒞 : OrderedPairConvention) : BinarySchema 0 where
  body := .existsE <| 𝒞.code (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.FreeClosed]

/-- 从有序对编码取第二坐标。 -/
def orderedPairSecond
    (𝒞 : OrderedPairConvention) : BinarySchema 0 where
  body := .existsE <| 𝒞.code (.bound 2) (.bound 0) (.bound 1)
  freeClosed := by
    simp [Formula.FreeClosed]

/-- 从有序数坐标编码取规范最大坐标。 -/
def ordinalPairMaximum
    (𝒞 : OrderedPairConvention) : BinarySchema 0 where
  body := .existsE <| .existsE <| .conj
    (𝒞.code (.bound 3) (.bound 1) (.bound 0))
    (Formula.isOrdinalMaximum (.bound 1) (.bound 0) (.bound 2))
  freeClosed := by
    simp [Formula.isOrdinalMaximum, Formula.extensionalEq,
      Formula.FreeClosed]

end BinarySchema

namespace UnarySchema

/-- 候选有序对的规范最大坐标等于给定参数。 -/
def hasOrdinalPairMaximum
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .existsE <| .existsE <| .conj
    (𝒞.code (.bound 2) (.bound 1) (.bound 0))
    (Formula.isOrdinalMaximum (.bound 1) (.bound 0) (.bound 3))
  freeClosed := by
    simp [Formula.isOrdinalMaximum, Formula.extensionalEq,
      Formula.FreeClosed]

/-- 候选有序对的第一坐标等于给定参数。 -/
def hasOrderedPairFirst
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .existsE <| 𝒞.code (.bound 1) (.bound 2) (.bound 0)
  freeClosed := by
    simp [Formula.FreeClosed]

end UnarySchema

namespace Formula

/-- 序数最大值公式的模型语义。 -/
theorem satisfies_isOrdinalMaximum_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (left right maximum : Term depth) :
    satisfies env (isOrdinalMaximum left right maximum) ↔
      ℳ.IsOrdinalMaximum
        (left.eval env) (right.eval env) (maximum.eval env) := by
  simp only [isOrdinalMaximum, Structure.IsOrdinalMaximum,
    satisfies_disj_iff, satisfies_conj_iff,
    satisfies_extensionalEq_iff_eq hExt, satisfies_mem_iff]

/-- 典范序数对 schema 精确解释为纸面关系。 -/
theorem denote_canonicalOrdinalPairLess_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 0) (first second : ℳ.Domain) :
    (BinarySchema.canonicalOrdinalPairLess 𝒞).denote env first second ↔
      ℳ.CanonicalOrdinalPairLess 𝕀 first second := by
  simp only [BinarySchema.canonicalOrdinalPairLess,
    BinarySchema.denote, canonicalOrdinalPairLess,
    Structure.CanonicalOrdinalPairLess,
    satisfies_exists_iff, satisfies_conj_iff, satisfies_disj_iff,
    𝕀.satisfies_code_iff,
    satisfies_isOrdinalMaximum_iff hExt,
    satisfies_extensionalEq_iff_eq hExt, satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Definitional.Term.eval_weaken]

/-- 第一坐标投影 schema 的模型语义。 -/
theorem denote_orderedPairFirst_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 0) (pair first : ℳ.Domain) :
    (BinarySchema.orderedPairFirst 𝒞).denote env pair first ↔
      ∃ second, 𝕀.Codes pair first second := by
  simp only [BinarySchema.orderedPairFirst, BinarySchema.denote,
    satisfies_exists_iff, 𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]

/-- 第二坐标投影 schema 的模型语义。 -/
theorem denote_orderedPairSecond_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 0) (pair second : ℳ.Domain) :
    (BinarySchema.orderedPairSecond 𝒞).denote env pair second ↔
      ∃ first, 𝕀.Codes pair first second := by
  simp only [BinarySchema.orderedPairSecond, BinarySchema.denote,
    satisfies_exists_iff, 𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]

/-- 最大坐标投影 schema 的模型语义。 -/
theorem denote_ordinalPairMaximum_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    (env : Env ℳ 0) (pair maximum : ℳ.Domain) :
    (BinarySchema.ordinalPairMaximum 𝒞).denote env pair maximum ↔
      ∃ left right,
        𝕀.Codes pair left right ∧
          ℳ.IsOrdinalMaximum left right maximum := by
  simp only [BinarySchema.ordinalPairMaximum, BinarySchema.denote,
    satisfies_exists_iff, satisfies_conj_iff,
    𝕀.satisfies_code_iff, satisfies_isOrdinalMaximum_iff hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push]

/-- 最大坐标筛选 schema 的模型语义。 -/
theorem satisfies_hasOrdinalPairMaximum_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    (env : Env ℳ 1) (pair : ℳ.Domain) :
    satisfies (env.push pair)
        (UnarySchema.hasOrdinalPairMaximum 𝒞).body ↔
      ∃ left right,
        𝕀.Codes pair left right ∧
          ℳ.IsOrdinalMaximum left right (env.bound 0) := by
  simp only [UnarySchema.hasOrdinalPairMaximum,
    satisfies_exists_iff, satisfies_conj_iff,
    𝕀.satisfies_code_iff, satisfies_isOrdinalMaximum_iff hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push]
  rfl

/-- 第一坐标筛选 schema 的模型语义。 -/
theorem satisfies_hasOrderedPairFirst_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (pair : ℳ.Domain) :
    satisfies (env.push pair)
        (UnarySchema.hasOrderedPairFirst 𝒞).body ↔
      ∃ second, 𝕀.Codes pair (env.bound 0) second := by
  simp only [UnarySchema.hasOrderedPairFirst,
    satisfies_exists_iff, 𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]
  rfl

end Formula
end Project
end Definitional

namespace Structure.IsOrdinalMaximum

/-- 两个序数成员总有规范最大值。 -/
theorem exists_of_mem
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {α left right : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hLeft : ℳ.mem left α) (hRight : ℳ.mem right α) :
    ∃ maximum, ℳ.IsOrdinalMaximum left right maximum := by
  rcases hα.wellOrder.linear.compare left hLeft right hRight with
    hSame | hLeftRight | hRightLeft
  · have hEq := hExt.eq_of_same_members left right hSame
    exact ⟨left, Or.inl ⟨rfl, Or.inl hEq.symm⟩⟩
  · exact ⟨right, Or.inr ⟨rfl, hLeftRight⟩⟩
  · exact ⟨left, Or.inl ⟨rfl, Or.inr hRightLeft⟩⟩

/-- 最大值仍是同一序数载体的成员。 -/
theorem mem
    {ℳ : Structure.{u}} {α left right maximum : ℳ.Domain}
    (hMaximum : ℳ.IsOrdinalMaximum left right maximum)
    (hLeft : ℳ.mem left α) (hRight : ℳ.mem right α) :
    ℳ.mem maximum α := by
  rcases hMaximum with
    ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact hLeft
  · exact hRight

/-- 第一坐标严格小于最大值，或就是最大值。 -/
theorem left_mem_or_eq
    {ℳ : Structure.{u}} {left right maximum : ℳ.Domain}
    (hMaximum : ℳ.IsOrdinalMaximum left right maximum) :
    ℳ.mem left maximum ∨ left = maximum := by
  rcases hMaximum with
    ⟨hMaximumEq, _⟩ | ⟨hMaximumEq, hLeftRight⟩
  · exact Or.inr hMaximumEq.symm
  · exact Or.inl <| by simpa [hMaximumEq] using hLeftRight

/-- 第二坐标严格小于最大值，或就是最大值。 -/
theorem right_mem_or_eq
    {ℳ : Structure.{u}} {left right maximum : ℳ.Domain}
    (hMaximum : ℳ.IsOrdinalMaximum left right maximum) :
    ℳ.mem right maximum ∨ right = maximum := by
  rcases hMaximum with
    ⟨hMaximumEq, hRightLeft⟩ | ⟨hMaximumEq, _⟩
  · rcases hRightLeft with hRightEq | hRightLeft
    · exact Or.inr <| hRightEq.trans hMaximumEq.symm
    · exact Or.inl <| by simpa [hMaximumEq] using hRightLeft
  · exact Or.inr hMaximumEq.symm

/-- 两个序数坐标的规范最大值唯一。 -/
theorem eq
    {ℳ : Structure.{u}}
    {α left right first second : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hLeft : ℳ.mem left α) (hRight : ℳ.mem right α)
    (hFirst : ℳ.IsOrdinalMaximum left right first)
    (hSecond : ℳ.IsOrdinalMaximum left right second) :
    first = second := by
  rcases hFirst with hFirst | hFirst
  · rcases hFirst with ⟨hFirstEq, hRightLeft⟩
    rcases hSecond with hSecond | hSecond
    · exact hFirstEq.trans hSecond.1.symm
    · rcases hSecond with ⟨hSecondEq, hLeftRight⟩
      rcases hRightLeft with hEq | hRightLeft
      · exact hFirstEq.trans <| hEq.symm.trans hSecondEq.symm
      · have hSelf : ℳ.mem left left :=
          hα.wellOrder.linear.trans left hLeft right hRight left hLeft
            hLeftRight hRightLeft
        exact False.elim <|
          hα.wellOrder.linear.irrefl left hLeft hSelf
  · rcases hFirst with ⟨hFirstEq, hLeftRight⟩
    rcases hSecond with hSecond | hSecond
    · rcases hSecond with ⟨hSecondEq, hRightLeft⟩
      rcases hRightLeft with hEq | hRightLeft
      · exact hFirstEq.trans <| hEq.trans hSecondEq.symm
      · have hSelf : ℳ.mem right right :=
          hα.wellOrder.linear.trans right hRight left hLeft right hRight
            hRightLeft hLeftRight
        exact False.elim <|
          hα.wellOrder.linear.irrefl right hRight hSelf
    · exact hFirstEq.trans hSecond.1.symm

end Structure.IsOrdinalMaximum

namespace ZF

/-- 典范序数对关系可在任意集合载体上集合化。 -/
theorem exists_canonicalOrdinalPairRelation
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (carrier : ℳ.Domain) :
    ∃ relation,
      ℳ.IsSetRelationOn 𝕀 relation carrier ∧
        ∀ first second,
          ℳ.PairMember 𝕀 first second relation ↔
            ℳ.mem first carrier ∧
              ℳ.mem second carrier ∧
                ℳ.CanonicalOrdinalPairLess 𝕀 first second := by
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_setRelationOn_of_denote hZF 𝕀
      (Definitional.Project.BinarySchema.canonicalOrdinalPairLess 𝒞)
      env carrier with
    ⟨relation, hRelationOn, hRelation⟩
  refine ⟨relation, hRelationOn, fun first second => ?_⟩
  rw [hRelation first second,
    Definitional.Project.Formula.denote_canonicalOrdinalPairLess_iff
      𝕀 hZF.1 env first second]

end ZF

namespace Structure

/-- 一个关系集合在给定序数方块上精确实现典范序数对次序。 -/
def IsCanonicalOrdinalPairOrder {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier α : ℳ.Domain) : Prop :=
  ℳ.IsCartesianProduct 𝕀 carrier α α ∧
    ℳ.IsSetRelationOn 𝕀 relation carrier ∧
      ∀ first second,
        ℳ.PairMember 𝕀 first second relation ↔
          ℳ.mem first carrier ∧
            ℳ.mem second carrier ∧
              ℳ.CanonicalOrdinalPairLess 𝕀 first second

end Structure

namespace Structure.IsCanonicalOrdinalPairOrder

/-- 固定两端编码后，典范关系只剩坐标最大值上的三重字典序比较。 -/
private theorem pairMember_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation carrier α first second
      firstLeft firstRight secondLeft secondRight : ℳ.Domain}
    (hOrder : ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α)
    (hFirstCode : 𝕀.Codes first firstLeft firstRight)
    (hSecondCode : 𝕀.Codes second secondLeft secondRight)
    (hFirst : ℳ.mem first carrier)
    (hSecond : ℳ.mem second carrier) :
    ℳ.PairMember 𝕀 first second relation ↔
      ∃ firstMaximum secondMaximum,
        ℳ.IsOrdinalMaximum firstLeft firstRight firstMaximum ∧
          ℳ.IsOrdinalMaximum secondLeft secondRight secondMaximum ∧
            (ℳ.mem firstMaximum secondMaximum ∨
              (firstMaximum = secondMaximum ∧
                (ℳ.mem firstLeft secondLeft ∨
                  (firstLeft = secondLeft ∧
                    ℳ.mem firstRight secondRight)))) := by
  rw [hOrder.2.2 first second]
  constructor
  · rintro ⟨_, _, firstLeft', firstRight',
      secondLeft', secondRight', firstMaximum, secondMaximum,
      hFirstCode', hSecondCode', hFirstMaximum, hSecondMaximum, hLess⟩
    rcases 𝕀.injective hFirstCode hFirstCode' with
      ⟨rfl, rfl⟩
    rcases 𝕀.injective hSecondCode hSecondCode' with
      ⟨rfl, rfl⟩
    exact ⟨firstMaximum, secondMaximum,
      hFirstMaximum, hSecondMaximum, hLess⟩
  · rintro ⟨firstMaximum, secondMaximum,
      hFirstMaximum, hSecondMaximum, hLess⟩
    exact ⟨hFirst, hSecond,
      firstLeft, firstRight, secondLeft, secondRight,
      firstMaximum, secondMaximum,
      hFirstCode, hSecondCode,
      hFirstMaximum, hSecondMaximum, hLess⟩

/-- 典范序数对关系在序数方块上是严格线序。 -/
theorem isSetCodedLinearOrder
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation carrier α : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hOrder : ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α) :
    ℳ.IsSetCodedLinearOrder 𝕀 relation carrier := by
  have coordinate_data
      {pair : ℳ.Domain} (hPair : ℳ.mem pair carrier) :
      ∃ left, ℳ.mem left α ∧
        ∃ right, ℳ.mem right α ∧ 𝕀.Codes pair left right :=
    (hOrder.1 pair).mp hPair
  refine ⟨hOrder.2.1.1, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro pair hPair hSelf
    rcases coordinate_data hPair with
      ⟨left, hLeft, right, hRight, hCode⟩
    rcases (pairMember_iff hOrder hCode hCode hPair hPair).mp hSelf with
      ⟨firstMaximum, secondMaximum,
        hFirstMaximum, hSecondMaximum, hLess⟩
    have hMaximumEq :=
      hFirstMaximum.eq hα hLeft hRight hSecondMaximum
    subst secondMaximum
    rcases hLess with hMaximumSelf | ⟨_, hCoordinates⟩
    · exact hα.wellOrder.linear.irrefl firstMaximum
        (hFirstMaximum.mem hLeft hRight) hMaximumSelf
    · rcases hCoordinates with hLeftSelf | ⟨_, hRightSelf⟩
      · exact hα.wellOrder.linear.irrefl left hLeft hLeftSelf
      · exact hα.wellOrder.linear.irrefl right hRight hRightSelf
  · intro first hFirst second hSecond third hThird hFirstSecond hSecondThird
    rcases coordinate_data hFirst with
      ⟨firstLeft, hFirstLeft, firstRight, hFirstRight, hFirstCode⟩
    rcases coordinate_data hSecond with
      ⟨secondLeft, hSecondLeft, secondRight, hSecondRight, hSecondCode⟩
    rcases coordinate_data hThird with
      ⟨thirdLeft, hThirdLeft, thirdRight, hThirdRight, hThirdCode⟩
    rcases (pairMember_iff hOrder hFirstCode hSecondCode
        hFirst hSecond).mp hFirstSecond with
      ⟨firstMaximum, firstSecondMaximum,
        hFirstMaximum, hFirstSecondMaximum, hFirstLess⟩
    rcases (pairMember_iff hOrder hSecondCode hThirdCode
        hSecond hThird).mp hSecondThird with
      ⟨secondThirdMaximum, thirdMaximum,
        hSecondThirdMaximum, hThirdMaximum, hSecondLess⟩
    have hMiddleMaximumEq :=
      hFirstSecondMaximum.eq hα hSecondLeft hSecondRight
        hSecondThirdMaximum
    subst secondThirdMaximum
    apply (pairMember_iff hOrder hFirstCode hThirdCode hFirst hThird).mpr
    refine ⟨firstMaximum, thirdMaximum,
      hFirstMaximum, hThirdMaximum, ?_⟩
    rcases hFirstLess with hFirstMaximumLess | ⟨hFirstMaximumEq, hFirstLex⟩
    · rcases hSecondLess with hSecondMaximumLess | ⟨hSecondMaximumEq, _⟩
      · exact Or.inl <| hα.wellOrder.linear.trans
          firstMaximum (hFirstMaximum.mem hFirstLeft hFirstRight)
          firstSecondMaximum
            (hFirstSecondMaximum.mem hSecondLeft hSecondRight)
          thirdMaximum (hThirdMaximum.mem hThirdLeft hThirdRight)
          hFirstMaximumLess hSecondMaximumLess
      · subst thirdMaximum
        exact Or.inl hFirstMaximumLess
    · subst firstSecondMaximum
      rcases hSecondLess with hSecondMaximumLess | ⟨hSecondMaximumEq, hSecondLex⟩
      · exact Or.inl hSecondMaximumLess
      · subst thirdMaximum
        refine Or.inr ⟨rfl, ?_⟩
        rcases hFirstLex with hFirstLeftLess | ⟨hFirstLeftEq, hFirstRightLess⟩
        · rcases hSecondLex with hSecondLeftLess | ⟨hSecondLeftEq, _⟩
          · exact Or.inl <| hα.wellOrder.linear.trans
              firstLeft hFirstLeft secondLeft hSecondLeft
              thirdLeft hThirdLeft hFirstLeftLess hSecondLeftLess
          · subst thirdLeft
            exact Or.inl hFirstLeftLess
        · subst secondLeft
          rcases hSecondLex with hSecondLeftLess | ⟨hSecondLeftEq, hSecondRightLess⟩
          · exact Or.inl hSecondLeftLess
          · subst thirdLeft
            exact Or.inr ⟨rfl,
              hα.wellOrder.linear.trans
                firstRight hFirstRight secondRight hSecondRight
                thirdRight hThirdRight
                hFirstRightLess hSecondRightLess⟩
  · intro first hFirst second hSecond
    rcases coordinate_data hFirst with
      ⟨firstLeft, hFirstLeft, firstRight, hFirstRight, hFirstCode⟩
    rcases coordinate_data hSecond with
      ⟨secondLeft, hSecondLeft, secondRight, hSecondRight, hSecondCode⟩
    rcases Structure.IsOrdinalMaximum.exists_of_mem hExt hα
        hFirstLeft hFirstRight with
      ⟨firstMaximum, hFirstMaximum⟩
    rcases Structure.IsOrdinalMaximum.exists_of_mem hExt hα
        hSecondLeft hSecondRight with
      ⟨secondMaximum, hSecondMaximum⟩
    rcases hα.wellOrder.linear.compare
        firstMaximum (hFirstMaximum.mem hFirstLeft hFirstRight)
        secondMaximum (hSecondMaximum.mem hSecondLeft hSecondRight) with
      hSameMaximum | hFirstMaximumLess | hSecondMaximumLess
    · have hMaximumEq :=
        hExt.eq_of_same_members firstMaximum secondMaximum hSameMaximum
      subst secondMaximum
      rcases hα.wellOrder.linear.compare
          firstLeft hFirstLeft secondLeft hSecondLeft with
        hSameLeft | hFirstLeftLess | hSecondLeftLess
      · have hLeftEq := hExt.eq_of_same_members firstLeft secondLeft hSameLeft
        subst secondLeft
        rcases hα.wellOrder.linear.compare
            firstRight hFirstRight secondRight hSecondRight with
          hSameRight | hFirstRightLess | hSecondRightLess
        · have hRightEq :=
            hExt.eq_of_same_members firstRight secondRight hSameRight
          subst secondRight
          have hPairEq := 𝕀.unique hFirstCode hSecondCode
          subst second
          exact Or.inl fun _ => Iff.rfl
        · exact Or.inr <| Or.inl <|
            (pairMember_iff hOrder hFirstCode hSecondCode hFirst hSecond).mpr
              ⟨firstMaximum, firstMaximum,
                hFirstMaximum, hSecondMaximum, Or.inr
                  ⟨rfl, Or.inr ⟨rfl, hFirstRightLess⟩⟩⟩
        · exact Or.inr <| Or.inr <|
            (pairMember_iff hOrder hSecondCode hFirstCode hSecond hFirst).mpr
              ⟨firstMaximum, firstMaximum,
                hSecondMaximum, hFirstMaximum, Or.inr
                  ⟨rfl, Or.inr ⟨rfl, hSecondRightLess⟩⟩⟩
      · exact Or.inr <| Or.inl <|
          (pairMember_iff hOrder hFirstCode hSecondCode hFirst hSecond).mpr
            ⟨firstMaximum, firstMaximum,
              hFirstMaximum, hSecondMaximum,
              Or.inr ⟨rfl, Or.inl hFirstLeftLess⟩⟩
      · exact Or.inr <| Or.inr <|
          (pairMember_iff hOrder hSecondCode hFirstCode hSecond hFirst).mpr
            ⟨firstMaximum, firstMaximum,
              hSecondMaximum, hFirstMaximum,
              Or.inr ⟨rfl, Or.inl hSecondLeftLess⟩⟩
    · exact Or.inr <| Or.inl <|
        (pairMember_iff hOrder hFirstCode hSecondCode hFirst hSecond).mpr
          ⟨firstMaximum, secondMaximum,
            hFirstMaximum, hSecondMaximum, Or.inl hFirstMaximumLess⟩
    · exact Or.inr <| Or.inr <|
        (pairMember_iff hOrder hSecondCode hFirstCode hSecond hFirst).mpr
          ⟨secondMaximum, firstMaximum,
            hSecondMaximum, hFirstMaximum, Or.inl hSecondMaximumLess⟩

/--
典范序数对关系在序数方块上是良序。

最小元按“最小最大坐标、最小第一坐标、最小第二坐标”三层模型内部选择得到。
-/
theorem isSetCodedWellOrder
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation carrier α : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hOrder : ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α) :
    ℳ.IsSetCodedWellOrder 𝕀 relation carrier := by
  let emptyEnv : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have coordinate_data
      {pair : ℳ.Domain} (hPair : ℳ.mem pair carrier) :
      ∃ left, ℳ.mem left α ∧
        ∃ right, ℳ.mem right α ∧ 𝕀.Codes pair left right :=
    (hOrder.1 pair).mp hPair
  refine ⟨hOrder.isSetCodedLinearOrder hZF.1 hα, ?_⟩
  intro subset hSubset ⟨selected, hSelected⟩

  have hMaximumTotal :
      ∀ pair, ℳ.mem pair subset →
        ∃ maximum,
          (Definitional.Project.BinarySchema.ordinalPairMaximum 𝒞).denote
            emptyEnv pair maximum := by
    intro pair hPair
    rcases coordinate_data (hSubset pair hPair) with
      ⟨left, hLeft, right, hRight, hCode⟩
    rcases Structure.IsOrdinalMaximum.exists_of_mem hZF.1 hα
        hLeft hRight with
      ⟨maximum, hMaximum⟩
    exact ⟨maximum,
      (Definitional.Project.Formula.denote_ordinalPairMaximum_iff
        𝕀 hZF.1 emptyEnv pair maximum).mpr
        ⟨left, right, hCode, hMaximum⟩⟩
  have hMaximumUnique :
      ∀ pair, ℳ.mem pair subset → ∀ first second,
        (Definitional.Project.BinarySchema.ordinalPairMaximum 𝒞).denote
            emptyEnv pair first →
          (Definitional.Project.BinarySchema.ordinalPairMaximum 𝒞).denote
            emptyEnv pair second →
          first = second := by
    intro pair hPair first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_ordinalPairMaximum_iff
      𝕀 hZF.1] at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstRight, hFirstCode, hFirstMaximum⟩
    rcases hSecond with
      ⟨secondLeft, secondRight, hSecondCode, hSecondMaximum⟩
    rcases 𝕀.injective hFirstCode hSecondCode with
      ⟨hLeftEq, hRightEq⟩
    subst secondLeft
    subst secondRight
    rcases coordinate_data (hSubset pair hPair) with
      ⟨left, hLeft, right, hRight, hCode⟩
    rcases 𝕀.injective hCode hFirstCode with
      ⟨hSelectedLeft, hSelectedRight⟩
    subst firstLeft
    subst firstRight
    exact hFirstMaximum.eq hα hLeft hRight hSecondMaximum
  rcases ZF.exists_functionalImageOn hZF
      (Definitional.Project.BinarySchema.ordinalPairMaximum 𝒞)
      emptyEnv subset hMaximumTotal hMaximumUnique with
    ⟨maximums, hMaximums⟩
  have hMaximumsSubset : ℳ.MemberSubset maximums α := by
    intro maximum hMaximum
    rcases (hMaximums maximum).mp hMaximum with
      ⟨pair, hPair, hPairMaximum⟩
    rw [Definitional.Project.Formula.denote_ordinalPairMaximum_iff
      𝕀 hZF.1] at hPairMaximum
    rcases hPairMaximum with
      ⟨left, right, hCode, hMaximumData⟩
    rcases coordinate_data (hSubset pair hPair) with
      ⟨selectedLeft, hLeft, selectedRight, hRight, hSelectedCode⟩
    rcases 𝕀.injective hCode hSelectedCode with
      ⟨hLeftEq, hRightEq⟩
    subst selectedLeft
    subst selectedRight
    exact hMaximumData.mem hLeft hRight
  have hMaximumsNonempty : ∃ maximum, ℳ.mem maximum maximums := by
    rcases hMaximumTotal selected hSelected with
      ⟨maximum, hMaximum⟩
    exact ⟨maximum, (hMaximums maximum).mpr
      ⟨selected, hSelected, hMaximum⟩⟩
  rcases hα.wellOrder.least maximums
      hMaximumsSubset hMaximumsNonempty with
    ⟨leastMaximum, hLeastMaximumMember, hLeastMaximum⟩

  let maximumEnv : Env ℳ 1 := {
    bound := fun _ => leastMaximum
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases ZF.exists_separation hZF
      (Definitional.Project.UnarySchema.hasOrdinalPairMaximum 𝒞)
      maximumEnv subset with
    ⟨maximumPairs, hMaximumPairsRaw⟩
  have hMaximumPairs (pair : ℳ.Domain) :
      ℳ.mem pair maximumPairs ↔
        ℳ.mem pair subset ∧
          ∃ left right,
            𝕀.Codes pair left right ∧
              ℳ.IsOrdinalMaximum left right leastMaximum := by
    rw [hMaximumPairsRaw pair,
      Definitional.Project.Formula.satisfies_hasOrdinalPairMaximum_iff
        𝕀 hZF.1 maximumEnv pair]
  have hMaximumPairsNonempty :
      ∃ pair, ℳ.mem pair maximumPairs := by
    rcases (hMaximums leastMaximum).mp hLeastMaximumMember with
      ⟨pair, hPair, hPairMaximum⟩
    rw [Definitional.Project.Formula.denote_ordinalPairMaximum_iff
      𝕀 hZF.1] at hPairMaximum
    exact ⟨pair, (hMaximumPairs pair).mpr
      ⟨hPair, hPairMaximum⟩⟩

  have hFirstTotal :
      ∀ pair, ℳ.mem pair maximumPairs →
        ∃ first,
          (Definitional.Project.BinarySchema.orderedPairFirst 𝒞).denote
            emptyEnv pair first := by
    intro pair hPair
    rcases (hMaximumPairs pair).mp hPair with
      ⟨_, left, right, hCode, _⟩
    exact ⟨left,
      (Definitional.Project.Formula.denote_orderedPairFirst_iff
        𝕀 emptyEnv pair left).mpr ⟨right, hCode⟩⟩
  have hFirstUnique :
      ∀ pair, ℳ.mem pair maximumPairs → ∀ first second,
        (Definitional.Project.BinarySchema.orderedPairFirst 𝒞).denote
            emptyEnv pair first →
          (Definitional.Project.BinarySchema.orderedPairFirst 𝒞).denote
            emptyEnv pair second →
          first = second := by
    intro pair _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_orderedPairFirst_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with ⟨firstRight, hFirstCode⟩
    rcases hSecond with ⟨secondRight, hSecondCode⟩
    exact (𝕀.injective hFirstCode hSecondCode).1
  rcases ZF.exists_functionalImageOn hZF
      (Definitional.Project.BinarySchema.orderedPairFirst 𝒞)
      emptyEnv maximumPairs hFirstTotal hFirstUnique with
    ⟨firsts, hFirsts⟩
  have hFirstsSubset : ℳ.MemberSubset firsts α := by
    intro first hFirst
    rcases (hFirsts first).mp hFirst with
      ⟨pair, hPair, hPairFirst⟩
    rw [Definitional.Project.Formula.denote_orderedPairFirst_iff 𝕀]
      at hPairFirst
    rcases hPairFirst with ⟨right, hCode⟩
    rcases coordinate_data
        (hSubset pair ((hMaximumPairs pair).mp hPair).1) with
      ⟨selectedFirst, hSelectedFirst, selectedRight, _,
        hSelectedCode⟩
    exact (by
      have hEq := (𝕀.injective hCode hSelectedCode).1
      simpa [hEq] using hSelectedFirst)
  have hFirstsNonempty : ∃ first, ℳ.mem first firsts := by
    rcases hMaximumPairsNonempty with ⟨pair, hPair⟩
    rcases hFirstTotal pair hPair with ⟨first, hFirst⟩
    exact ⟨first, (hFirsts first).mpr ⟨pair, hPair, hFirst⟩⟩
  rcases hα.wellOrder.least firsts hFirstsSubset hFirstsNonempty with
    ⟨leastFirst, hLeastFirstMember, hLeastFirst⟩

  let firstEnv : Env ℳ 1 := {
    bound := fun _ => leastFirst
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases ZF.exists_separation hZF
      (Definitional.Project.UnarySchema.hasOrderedPairFirst 𝒞)
      firstEnv maximumPairs with
    ⟨firstPairs, hFirstPairsRaw⟩
  have hFirstPairs (pair : ℳ.Domain) :
      ℳ.mem pair firstPairs ↔
        ℳ.mem pair maximumPairs ∧
          ∃ second, 𝕀.Codes pair leastFirst second := by
    rw [hFirstPairsRaw pair,
      Definitional.Project.Formula.satisfies_hasOrderedPairFirst_iff
        𝕀 firstEnv pair]
  have hFirstPairsNonempty : ∃ pair, ℳ.mem pair firstPairs := by
    rcases (hFirsts leastFirst).mp hLeastFirstMember with
      ⟨pair, hPair, hPairFirst⟩
    rw [Definitional.Project.Formula.denote_orderedPairFirst_iff 𝕀]
      at hPairFirst
    exact ⟨pair, (hFirstPairs pair).mpr ⟨hPair, hPairFirst⟩⟩

  have hSecondTotal :
      ∀ pair, ℳ.mem pair firstPairs →
        ∃ second,
          (Definitional.Project.BinarySchema.orderedPairSecond 𝒞).denote
            emptyEnv pair second := by
    intro pair hPair
    rcases (hFirstPairs pair).mp hPair with
      ⟨_, second, hCode⟩
    exact ⟨second,
      (Definitional.Project.Formula.denote_orderedPairSecond_iff
        𝕀 emptyEnv pair second).mpr ⟨leastFirst, hCode⟩⟩
  have hSecondUnique :
      ∀ pair, ℳ.mem pair firstPairs → ∀ first second,
        (Definitional.Project.BinarySchema.orderedPairSecond 𝒞).denote
            emptyEnv pair first →
          (Definitional.Project.BinarySchema.orderedPairSecond 𝒞).denote
            emptyEnv pair second →
          first = second := by
    intro pair _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_orderedPairSecond_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with ⟨firstLeft, hFirstCode⟩
    rcases hSecond with ⟨secondLeft, hSecondCode⟩
    exact (𝕀.injective hFirstCode hSecondCode).2
  rcases ZF.exists_functionalImageOn hZF
      (Definitional.Project.BinarySchema.orderedPairSecond 𝒞)
      emptyEnv firstPairs hSecondTotal hSecondUnique with
    ⟨seconds, hSeconds⟩
  have hSecondsSubset : ℳ.MemberSubset seconds α := by
    intro second hSecond
    rcases (hSeconds second).mp hSecond with
      ⟨pair, hPair, hPairSecond⟩
    rw [Definitional.Project.Formula.denote_orderedPairSecond_iff 𝕀]
      at hPairSecond
    rcases hPairSecond with ⟨left, hCode⟩
    have hPairSubset :=
      (hMaximumPairs pair).mp ((hFirstPairs pair).mp hPair).1 |>.1
    rcases coordinate_data (hSubset pair hPairSubset) with
      ⟨selectedLeft, _, selectedRight, hSelectedRight, hSelectedCode⟩
    exact (by
      have hEq := (𝕀.injective hCode hSelectedCode).2
      simpa [hEq] using hSelectedRight)
  have hSecondsNonempty : ∃ second, ℳ.mem second seconds := by
    rcases hFirstPairsNonempty with ⟨pair, hPair⟩
    rcases hSecondTotal pair hPair with ⟨second, hSecond⟩
    exact ⟨second, (hSeconds second).mpr ⟨pair, hPair, hSecond⟩⟩
  rcases hα.wellOrder.least seconds hSecondsSubset hSecondsNonempty with
    ⟨leastSecond, hLeastSecondMember, hLeastSecond⟩

  rcases (hSeconds leastSecond).mp hLeastSecondMember with
    ⟨candidate, hCandidateFirstPairs, hCandidateSecondProjection⟩
  rcases (hFirstPairs candidate).mp hCandidateFirstPairs with
    ⟨hCandidateMaximumPairs, candidateRight, hCandidateFirstCode⟩
  rcases (hMaximumPairs candidate).mp hCandidateMaximumPairs with
    ⟨hCandidateSubset, candidateLeft, candidateRight',
      hCandidateMaximumCode, hCandidateMaximum⟩
  rw [Definitional.Project.Formula.denote_orderedPairSecond_iff 𝕀]
    at hCandidateSecondProjection
  rcases hCandidateSecondProjection with
    ⟨candidateLeft', hCandidateSecondCode⟩
  have hCandidateFirstCoordinates :=
    𝕀.injective hCandidateFirstCode hCandidateSecondCode
  have hCandidateMaximumCoordinates :=
    𝕀.injective hCandidateMaximumCode hCandidateSecondCode
  have hCandidateCode :
      𝕀.Codes candidate leastFirst leastSecond := by
    simpa [hCandidateFirstCoordinates.2] using hCandidateFirstCode
  have hCandidateMaximum' :
      ℳ.IsOrdinalMaximum leastFirst leastSecond leastMaximum := by
    have hCandidateLeftEq : candidateLeft = leastFirst :=
      hCandidateMaximumCoordinates.1.trans
        hCandidateFirstCoordinates.1.symm
    simpa [hCandidateLeftEq, hCandidateMaximumCoordinates.2] using
      hCandidateMaximum
  have hCandidateCarrier : ℳ.mem candidate carrier :=
    hSubset candidate hCandidateSubset
  refine ⟨candidate, hCandidateSubset, ?_⟩
  intro value hValueSubset
  have hValueCarrier := hSubset value hValueSubset
  rcases coordinate_data hValueCarrier with
    ⟨valueLeft, hValueLeft, valueRight, hValueRight, hValueCode⟩
  rcases Structure.IsOrdinalMaximum.exists_of_mem hZF.1 hα
      hValueLeft hValueRight with
    ⟨valueMaximum, hValueMaximum⟩
  have hValueMaximumMember : ℳ.mem valueMaximum maximums :=
    (hMaximums valueMaximum).mpr
      ⟨value, hValueSubset,
        (Definitional.Project.Formula.denote_ordinalPairMaximum_iff
          𝕀 hZF.1 emptyEnv value valueMaximum).mpr
          ⟨valueLeft, valueRight, hValueCode, hValueMaximum⟩⟩
  rcases hLeastMaximum valueMaximum hValueMaximumMember with
    hSameMaximum | hMaximumLess
  · have hMaximumEq :=
      hZF.1.eq_of_same_members leastMaximum valueMaximum hSameMaximum
    subst valueMaximum
    have hValueMaximumPairs : ℳ.mem value maximumPairs :=
      (hMaximumPairs value).mpr
        ⟨hValueSubset, valueLeft, valueRight,
          hValueCode, hValueMaximum⟩
    have hValueLeftMember : ℳ.mem valueLeft firsts :=
      (hFirsts valueLeft).mpr
        ⟨value, hValueMaximumPairs,
          (Definitional.Project.Formula.denote_orderedPairFirst_iff
            𝕀 emptyEnv value valueLeft).mpr
            ⟨valueRight, hValueCode⟩⟩
    rcases hLeastFirst valueLeft hValueLeftMember with
      hSameFirst | hFirstLess
    · have hFirstEq :=
        hZF.1.eq_of_same_members leastFirst valueLeft hSameFirst
      subst valueLeft
      have hValueFirstPairs : ℳ.mem value firstPairs :=
        (hFirstPairs value).mpr
          ⟨hValueMaximumPairs, valueRight, hValueCode⟩
      have hValueRightMember : ℳ.mem valueRight seconds :=
        (hSeconds valueRight).mpr
          ⟨value, hValueFirstPairs,
            (Definitional.Project.Formula.denote_orderedPairSecond_iff
              𝕀 emptyEnv value valueRight).mpr
              ⟨leastFirst, hValueCode⟩⟩
      rcases hLeastSecond valueRight hValueRightMember with
        hSameSecond | hSecondLess
      · have hSecondEq :=
          hZF.1.eq_of_same_members leastSecond valueRight hSameSecond
        subst valueRight
        have hPairEq := 𝕀.unique hCandidateCode hValueCode
        exact Or.inl <| by
          intro member
          simp [hPairEq]
      · exact Or.inr <|
          (pairMember_iff hOrder hCandidateCode hValueCode
            hCandidateCarrier hValueCarrier).mpr
            ⟨leastMaximum, leastMaximum,
              hCandidateMaximum', hValueMaximum,
              Or.inr ⟨rfl, Or.inr ⟨rfl, hSecondLess⟩⟩⟩
    · exact Or.inr <|
        (pairMember_iff hOrder hCandidateCode hValueCode
          hCandidateCarrier hValueCarrier).mpr
          ⟨leastMaximum, leastMaximum,
            hCandidateMaximum', hValueMaximum,
            Or.inr ⟨rfl, Or.inl hFirstLess⟩⟩
  · exact Or.inr <|
      (pairMember_iff hOrder hCandidateCode hValueCode
        hCandidateCarrier hValueCarrier).mpr
        ⟨leastMaximum, valueMaximum,
          hCandidateMaximum', hValueMaximum, Or.inl hMaximumLess⟩

/--
典范次序中一点的整个前段都落在其最大坐标后继的方块中。
-/
theorem predecessorSet_boundedByMaximumSquare
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation carrier α current predecessors : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hOrder : ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α)
    (hCurrent : ℳ.mem current carrier)
    (hPredecessors :
      ℳ.IsPredecessorSet 𝕀 predecessors relation carrier current) :
    ∃ left right maximum successor square,
      𝕀.Codes current left right ∧
        ℳ.mem left α ∧ ℳ.mem right α ∧
        ℳ.IsOrdinalMaximum left right maximum ∧
        ℳ.SuccessorOf successor maximum ∧
        ℳ.IsCartesianProduct 𝕀 square successor successor ∧
        ℳ.MemberSubset predecessors square := by
  rcases (hOrder.1 current).mp hCurrent with
    ⟨left, hLeft, right, hRight, hCurrentCode⟩
  rcases Structure.IsOrdinalMaximum.exists_of_mem hZF.1 hα
      hLeft hRight with
    ⟨maximum, hMaximum⟩
  have hMaximumMem : ℳ.mem maximum α :=
    hMaximum.mem hLeft hRight
  have hMaximumOrdinal : ℳ.IsOrdinal maximum :=
    hα.mem hMaximumMem
  rcases KP.exists_successor (ZF.modelsKP hZF) maximum with
    ⟨successor, hSuccessor⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀 successor successor with
    ⟨square, hSquare⟩
  refine ⟨left, right, maximum, successor, square,
    hCurrentCode, hLeft, hRight, hMaximum, hSuccessor, hSquare, ?_⟩
  intro predecessor hPredecessor
  have hPredecessorData := (hPredecessors predecessor).mp hPredecessor
  rcases (hOrder.1 predecessor).mp hPredecessorData.1 with
    ⟨predecessorLeft, hPredecessorLeft,
      predecessorRight, hPredecessorRight, hPredecessorCode⟩
  rcases (pairMember_iff hOrder hPredecessorCode hCurrentCode
      hPredecessorData.1 hCurrent).mp hPredecessorData.2 with
    ⟨predecessorMaximum, currentMaximum,
      hPredecessorMaximum, hCurrentMaximum, hLess⟩
  have hCurrentMaximumEq :=
    hCurrentMaximum.eq hα hLeft hRight hMaximum
  subst currentMaximum
  have hPredecessorMaximumBelow :
      ℳ.mem predecessorMaximum maximum ∨
        predecessorMaximum = maximum := by
    rcases hLess with hMaximumLess | ⟨hMaximumEq, _⟩
    · exact Or.inl hMaximumLess
    · exact Or.inr hMaximumEq
  have coordinate_mem_successor
      {coordinate : ℳ.Domain}
      (hCoordinate :
        ℳ.mem coordinate predecessorMaximum ∨
          coordinate = predecessorMaximum) :
      ℳ.mem coordinate successor := by
    apply (hSuccessor coordinate).mpr
    rcases hPredecessorMaximumBelow with
      hPredecessorMaximumBelow | hPredecessorMaximumEq
    · rcases hCoordinate with hCoordinate | hCoordinateEq
      · exact Or.inl <|
          hMaximumOrdinal.transitive predecessorMaximum
            hPredecessorMaximumBelow coordinate hCoordinate
      · exact Or.inl <| by
          simpa [hCoordinateEq] using hPredecessorMaximumBelow
    · subst predecessorMaximum
      rcases hCoordinate with hCoordinate | hCoordinateEq
      · exact Or.inl hCoordinate
      · exact Or.inr <| by
          intro member
          simp [hCoordinateEq]
  exact (hSquare predecessor).mpr
    ⟨predecessorLeft,
      coordinate_mem_successor hPredecessorMaximum.left_mem_or_eq,
      predecessorRight,
      coordinate_mem_successor hPredecessorMaximum.right_mem_or_eq,
      hPredecessorCode⟩

end Structure.IsCanonicalOrdinalPairOrder

namespace ZF

/-- 任意序数方块都具有模型内部集合编码的典范严格线序。 -/
theorem exists_canonicalOrdinalPairLinearOrder
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {α carrier : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hCarrier : ℳ.IsCartesianProduct 𝕀 carrier α α) :
    ∃ relation,
      ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α ∧
        ℳ.IsSetCodedLinearOrder 𝕀 relation carrier := by
  rcases exists_canonicalOrdinalPairRelation hZF 𝕀 carrier with
    ⟨relation, hRelationOn, hRelation⟩
  have hOrder :
      ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α :=
    ⟨hCarrier, hRelationOn, hRelation⟩
  exact ⟨relation, hOrder,
    hOrder.isSetCodedLinearOrder hZF.1 hα⟩

/-- 任意序数方块都具有模型内部集合编码的典范良序。 -/
theorem exists_canonicalOrdinalPairWellOrder
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {α carrier : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hCarrier : ℳ.IsCartesianProduct 𝕀 carrier α α) :
    ∃ relation,
      ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α ∧
        ℳ.IsSetCodedWellOrder 𝕀 relation carrier := by
  rcases exists_canonicalOrdinalPairRelation hZF 𝕀 carrier with
    ⟨relation, hRelationOn, hRelation⟩
  have hOrder :
      ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α :=
    ⟨hCarrier, hRelationOn, hRelation⟩
  exact ⟨relation, hOrder,
    hOrder.isSetCodedWellOrder hZF hα⟩

end ZF

namespace Structure

/-- `ordinal` 是序数方块典范良序的规范序型。 -/
def IsCanonicalOrdinalPairOrderType {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ordinal α : ℳ.Domain) : Prop :=
  ∃ carrier relation,
    ℳ.IsCanonicalOrdinalPairOrder 𝕀 relation carrier α ∧
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier ∧
        ℳ.IsWellOrderType 𝕀 relation carrier ordinal

end Structure

namespace Structure.IsWellOrderCollapseValue

/-- 某点的坍缩值与该点在原良序中的前驱集等势。 -/
theorem predecessorSet_equinumerous
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {relation carrier current value : ℳ.Domain}
    (hOrder : ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hValue :
      ℳ.IsWellOrderCollapseValue 𝕀 relation carrier current value) :
    ∃ predecessors,
      ℳ.IsPredecessorSet 𝕀 predecessors relation carrier current ∧
        ℳ.Equinumerous 𝕀 predecessors value := by
  rcases hValue with
    ⟨predecessors, function, hPredecessors, hFunction, hRange⟩
  have hFunctionFromTo :
      ℳ.IsSetFunctionFromTo 𝕀 function predecessors value := by
    refine ⟨hFunction.1, hFunction.2.1, ?_⟩
    intro input hInput
    rcases (hFunction.2.1 input).mp hInput with
      ⟨output, hPair⟩
    exact ⟨output, (hRange output).mpr ⟨input, hPair⟩, hPair⟩
  have hInjective : ℳ.IsSetInjective 𝕀 function := by
    intro first second output hFirst hSecond
    have hFirstDomain :
        ℳ.mem first predecessors :=
      (hFunction.2.1 first).mpr ⟨output, hFirst⟩
    have hSecondDomain :
        ℳ.mem second predecessors :=
      (hFunction.2.1 second).mpr ⟨output, hSecond⟩
    have hFirstCarrier :=
      hFunction.2.2.1.1 first hFirstDomain
    have hSecondCarrier :=
      hFunction.2.2.1.1 second hSecondDomain
    rcases hOrder.compare hFirstCarrier hSecondCarrier with
      hSame | hFirstSecond | hSecondFirst
    · exact hZF.1.eq_of_same_members first second hSame
    · have hSelf : ℳ.mem output output :=
        (hFunction.2.2.2 second hSecondDomain
          output hSecond output).mpr
          ⟨first, hFirstDomain, hFirstSecond, hFirst⟩
      exact False.elim <|
        KP.mem_irrefl (ZF.modelsKP hZF) output hSelf
    · have hSelf : ℳ.mem output output :=
        (hFunction.2.2.2 first hFirstDomain
          output hFirst output).mpr
          ⟨second, hSecondDomain, hSecondFirst, hSecond⟩
      exact False.elim <|
        KP.mem_irrefl (ZF.modelsKP hZF) output hSelf
  have hSurjective :
      ℳ.IsSetSurjectiveOnto 𝕀 function predecessors value := by
    intro output hOutput
    rcases (hRange output).mp hOutput with
      ⟨input, hPair⟩
    exact ⟨input,
      (hFunction.2.1 input).mpr ⟨output, hPair⟩, hPair⟩
  exact ⟨predecessors, hPredecessors,
    ⟨function, ⟨⟨hFunctionFromTo, hInjective⟩, hSurjective⟩⟩⟩

end Structure.IsWellOrderCollapseValue

namespace ZF

/-- 每个序数方块的典范良序都有唯一规范序型。 -/
theorem canonicalOrdinalPairOrderType_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {α : ℳ.Domain} (hα : ℳ.IsOrdinal α) :
    ∃ ordinal,
      ℳ.IsCanonicalOrdinalPairOrderType 𝕀 ordinal α ∧
        ∀ other,
          ℳ.IsCanonicalOrdinalPairOrderType 𝕀 other α →
            other = ordinal := by
  rcases exists_cartesianProduct hZF 𝕀 α α with
    ⟨carrier, hCarrier⟩
  rcases exists_canonicalOrdinalPairWellOrder hZF 𝕀 hα hCarrier with
    ⟨relation, hOrder, hWellOrder⟩
  rcases wellOrderType_existsUnique hZF 𝕀 hWellOrder with
    ⟨ordinal, hType, _⟩
  refine ⟨ordinal, ⟨carrier, relation, hOrder, hWellOrder, hType⟩, ?_⟩
  intro other hOther
  rcases hOther with
    ⟨otherCarrier, otherRelation,
      hOtherOrder, hOtherWellOrder, hOtherType⟩
  have hCarrierEq : otherCarrier = carrier := by
    apply hZF.1.eq_of_same_members
    intro pair
    rw [hOtherOrder.1 pair, hCarrier pair]
  subst otherCarrier
  have hRelationEq : otherRelation = relation := by
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hOtherOrder.2.1.1 hOrder.2.1.1
    intro first second
    rw [hOtherOrder.2.2 first second, hOrder.2.2 first second]
  subst otherRelation
  rcases wellOrderType_existsUnique hZF 𝕀 hWellOrder with
    ⟨selected, _, hUnique⟩
  exact (hUnique other hOtherType).trans
    (hUnique ordinal hType).symm

end ZF

namespace Structure.IsCanonicalOrdinalPairOrderType

/-- 典范方块序型是序数。 -/
theorem isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ordinal α : ℳ.Domain}
    (hType : ℳ.IsCanonicalOrdinalPairOrderType 𝕀 ordinal α) :
    ℳ.IsOrdinal ordinal := by
  rcases hType with
    ⟨carrier, relation, _, hOrder, hWellOrderType⟩
  exact hWellOrderType.isOrdinal hZF 𝕀 hOrder

/-- 序数方块与其典范规范序型等势。 -/
theorem equinumerous
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ordinal α : ℳ.Domain}
    (hType : ℳ.IsCanonicalOrdinalPairOrderType 𝕀 ordinal α) :
    ∃ carrier,
      ℳ.IsCartesianProduct 𝕀 carrier α α ∧
        ℳ.Equinumerous 𝕀 carrier ordinal := by
  rcases hType with
    ⟨carrier, relation, hCanonical, hOrder, hWellOrderType⟩
  exact ⟨carrier, hCanonical.1,
    hWellOrderType.equinumerous hZF 𝕀 hOrder⟩

/--
典范方块序型的每个成员都与某个前驱集等势，而此前驱集受当前点最大坐标的后继方块
控制。
-/
theorem member_equinumerous_predecessorSet_boundedByMaximumSquare
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ordinal α member : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hType : ℳ.IsCanonicalOrdinalPairOrderType 𝕀 ordinal α)
    (hMember : ℳ.mem member ordinal) :
    ∃ maximum successor square predecessors,
      ℳ.mem maximum α ∧
        ℳ.SuccessorOf successor maximum ∧
        ℳ.IsCartesianProduct 𝕀 square successor successor ∧
        ℳ.MemberSubset predecessors square ∧
        ℳ.Equinumerous 𝕀 predecessors member := by
  rcases hType with
    ⟨carrier, relation, hCanonical, hOrder,
      function, hFunction, hRange⟩
  rcases (hRange member).mp hMember with
    ⟨current, hCurrentValue⟩
  have hCurrent :
      ℳ.mem current carrier :=
    (hFunction.2.1 current).mpr ⟨member, hCurrentValue⟩
  have hCollapseValue :=
    hFunction.collapseValue_of_pairMember
      hZF 𝕀 hOrder hCurrent hCurrentValue
  rcases hCollapseValue.predecessorSet_equinumerous
      hZF 𝕀 hOrder with
    ⟨predecessors, hPredecessors, hEquinumerous⟩
  rcases hCanonical.predecessorSet_boundedByMaximumSquare
      hZF hα hCurrent hPredecessors with
    ⟨left, right, maximum, successor, square,
      _, hLeft, hRight, hMaximum, hSuccessor,
      hSquare, hSubset⟩
  exact ⟨maximum, successor, square, predecessors,
    hMaximum.mem hLeft hRight, hSuccessor,
    hSquare, hSubset, hEquinumerous⟩

end Structure.IsCanonicalOrdinalPairOrderType

end SetTheory
end YesMetaZFC
