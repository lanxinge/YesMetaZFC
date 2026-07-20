import YesMetaZFC.SetTheory.Ord.Arithmetic.Normal

/-!
# 序数算术的代数律

本文件证明序数加法结合律、乘法对右侧加法的左分配律，以及序数乘法结合律。
证明统一使用可定义类关系上的序数归纳；极限步通过正规函数的共尾性处理。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Definitional
namespace Project
namespace BinarySchema

/-- `right ↦ left + (middle + right)` 的类关系。 -/
private def ordinalAdditionLeftAssociated
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalAddition 𝒞
      Term.newest (.bound 4) (.bound 2))
    (Formula.isOrdinalAddition 𝒞
      (.bound 1) (.bound 3) Term.newest)
  freeClosed := by
    simp [Formula.isOrdinalAddition, Formula.related,
      Formula.FreeClosed, Term.newest]
    constructor <;>
      apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

/-- `right ↦ (left + middle) + right` 的类关系。 -/
private def ordinalAdditionRightAssociated
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalAddition 𝒞
      Term.newest (.bound 3) (.bound 4))
    (Formula.isOrdinalAddition 𝒞
      (.bound 1) Term.newest (.bound 2))
  freeClosed := by
    simp [Formula.isOrdinalAddition, Formula.related,
      Formula.FreeClosed, Term.newest]
    constructor <;>
      apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

private theorem denote_ordinalAdditionLeftAssociated_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right result : ℳ.Domain) :
    (ordinalAdditionLeftAssociated 𝒞).denote env right result ↔
      ∃ middleRight,
        ℳ.IsOrdinalAddition 𝕀
          middleRight (env.bound 1) right ∧
        ℳ.IsOrdinalAddition 𝕀
          result (env.bound 0) middleRight := by
  simp only [ordinalAdditionLeftAssociated, denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

private theorem denote_ordinalAdditionRightAssociated_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right result : ℳ.Domain) :
    (ordinalAdditionRightAssociated 𝒞).denote env right result ↔
      ∃ leftMiddle,
        ℳ.IsOrdinalAddition 𝕀
          leftMiddle (env.bound 0) (env.bound 1) ∧
        ℳ.IsOrdinalAddition 𝕀
          result leftMiddle right := by
  simp only [ordinalAdditionRightAssociated, denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

/-- `right ↦ left * (middle + right)` 的类关系。 -/
private def ordinalMultiplicationAdditionLeft
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalAddition 𝒞
      Term.newest (.bound 4) (.bound 2))
    (Formula.isOrdinalMultiplication 𝒞
      (.bound 1) (.bound 3) Term.newest)
  freeClosed := by
    simp [Formula.isOrdinalAddition,
      Formula.isOrdinalMultiplication, Formula.related,
      Formula.FreeClosed, Term.newest]
    constructor <;>
      apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

/-- `right ↦ left * middle + left * right` 的类关系。 -/
private def ordinalMultiplicationAdditionRight
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalMultiplication 𝒞
      Term.newest (.bound 3) (.bound 4)) <|
    .existsE <| .conj
      (Formula.isOrdinalMultiplication 𝒞
        Term.newest (.bound 4) (.bound 3))
      (Formula.isOrdinalAddition 𝒞
        (.bound 2) (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.isOrdinalAddition,
      Formula.isOrdinalMultiplication, Formula.related,
      Formula.FreeClosed, Term.newest]
    constructor
    · apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]
    · constructor <;>
        apply Formula.related_freeClosed_of_closed <;>
          simp [TermVector.FreeClosed, TermVector.singleton]

private theorem denote_ordinalMultiplicationAdditionLeft_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right result : ℳ.Domain) :
    (ordinalMultiplicationAdditionLeft 𝒞).denote
        env right result ↔
      ∃ middleRight,
        ℳ.IsOrdinalAddition 𝕀
          middleRight (env.bound 1) right ∧
        ℳ.IsOrdinalMultiplication 𝕀
          result (env.bound 0) middleRight := by
  simp only [ordinalMultiplicationAdditionLeft, denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

private theorem denote_ordinalMultiplicationAdditionRight_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right result : ℳ.Domain) :
    (ordinalMultiplicationAdditionRight 𝒞).denote
        env right result ↔
      ∃ leftMiddle,
        ℳ.IsOrdinalMultiplication 𝕀
          leftMiddle (env.bound 0) (env.bound 1) ∧
        ∃ leftRight,
          ℳ.IsOrdinalMultiplication 𝕀
            leftRight (env.bound 0) right ∧
          ℳ.IsOrdinalAddition 𝕀
            result leftMiddle leftRight := by
  simp only [ordinalMultiplicationAdditionRight, denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

/-- `right ↦ left * (middle * right)` 的类关系。 -/
private def ordinalMultiplicationLeftAssociated
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalMultiplication 𝒞
      Term.newest (.bound 4) (.bound 2))
    (Formula.isOrdinalMultiplication 𝒞
      (.bound 1) (.bound 3) Term.newest)
  freeClosed := by
    simp [Formula.isOrdinalMultiplication, Formula.related,
      Formula.FreeClosed, Term.newest]
    constructor <;>
      apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

/-- `right ↦ (left * middle) * right` 的类关系。 -/
private def ordinalMultiplicationRightAssociated
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalMultiplication 𝒞
      Term.newest (.bound 3) (.bound 4))
    (Formula.isOrdinalMultiplication 𝒞
      (.bound 1) Term.newest (.bound 2))
  freeClosed := by
    simp [Formula.isOrdinalMultiplication, Formula.related,
      Formula.FreeClosed, Term.newest]
    constructor <;>
      apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

private theorem denote_ordinalMultiplicationLeftAssociated_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right result : ℳ.Domain) :
    (ordinalMultiplicationLeftAssociated 𝒞).denote
        env right result ↔
      ∃ middleRight,
        ℳ.IsOrdinalMultiplication 𝕀
          middleRight (env.bound 1) right ∧
        ℳ.IsOrdinalMultiplication 𝕀
          result (env.bound 0) middleRight := by
  simp only [ordinalMultiplicationLeftAssociated, denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

private theorem denote_ordinalMultiplicationRightAssociated_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right result : ℳ.Domain) :
    (ordinalMultiplicationRightAssociated 𝒞).denote
        env right result ↔
      ∃ leftMiddle,
        ℳ.IsOrdinalMultiplication 𝕀
          leftMiddle (env.bound 0) (env.bound 1) ∧
        ℳ.IsOrdinalMultiplication 𝕀
          result leftMiddle right := by
  simp only [ordinalMultiplicationRightAssociated, denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

end BinarySchema
end Project
end Definitional

namespace ZF

/-- 空序数作为左因子时，任意序数乘法值仍为空。 -/
theorem ordinalMultiplication_empty_left
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeftEmpty : ∀ value, ¬ ℳ.mem value left) :
    ∀ right, ℳ.IsOrdinal right →
      ∀ product,
        ℳ.IsOrdinalMultiplication 𝕀 product left right →
          ∀ value, ¬ ℳ.mem value product := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env =
        fun right product =>
          ℳ.IsOrdinalMultiplication 𝕀 product left right := by
    funext right product
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalMultiplication_iff
        𝕀 hZF.1 env right product
  have hLeftOrdinal : ℳ.IsOrdinal left :=
    Structure.IsOrdinal.of_no_members hLeftEmpty
  have hEmptyValues :=
    emptyValuesOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞)
      (fun α hα hPrevious product hProduct => by
        rw [hRelation] at hPrevious hProduct
        rcases hα.classify hZF.1 with
          hEmpty | hSuccessor | hLimit
        · exact
            (ordinalMultiplication_zero_iff
              hZF 𝕀
              hLeftOrdinal
              hEmpty).mp hProduct
        · rcases hSuccessor with
            ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
          rcases (ordinalMultiplication_successor_iff
              hZF 𝕀
              hLeftOrdinal
              hPredecessorOrdinal hSuccessor).mp hProduct with
            ⟨previous, hPreviousValue, hProductAddition⟩
          have hPredecessorMem : ℳ.mem predecessor α :=
            (hSuccessor predecessor).mpr
              (Or.inr fun _ => Iff.rfl)
          have hProductEq : product = previous :=
            (ordinalAddition_zero_iff
              hZF 𝕀 hLeftEmpty).mp
              hProductAddition
          simpa [hProductEq] using
            hPrevious predecessor hPredecessorMem
              previous hPreviousValue
        · rcases (ordinalMultiplication_limit_iff
              hZF 𝕀
              hLeftOrdinal
              hLimit).mp hProduct with
            ⟨range, hRange, hUnion⟩
          intro value hValue
          rcases (hUnion value).mp hValue with
            ⟨member, hMemberRange, hValueMember⟩
          rcases (hRange member).mp hMemberRange with
            ⟨index, hIndex, hMemberValue⟩
          exact hPrevious index hIndex
            member hMemberValue value hValueMember)
  intro right hRight product hProduct
  rw [hRelation] at hEmptyValues
  exact hEmptyValues right hRight product hProduct

/-- 序数加法满足结合律。 -/
theorem ordinalAddition_assoc
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left middle right leftMiddle middleRight
      leftAssociated rightAssociated : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hMiddle : ℳ.IsOrdinal middle)
    (hRight : ℳ.IsOrdinal right)
    (hLeftMiddle :
      ℳ.IsOrdinalAddition 𝕀 leftMiddle left middle)
    (hMiddleRight :
      ℳ.IsOrdinalAddition 𝕀 middleRight middle right)
    (hLeftAssociated :
      ℳ.IsOrdinalAddition 𝕀
        leftAssociated left middleRight)
    (hRightAssociated :
      ℳ.IsOrdinalAddition 𝕀
        rightAssociated leftMiddle right) :
    leftAssociated = rightAssociated := by
  let env : Env ℳ 2 := {
    bound := fun
      | 0 => left
      | 1 => middle
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hAgreement :=
    agreeOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalAdditionLeftAssociated 𝒞)
      (Definitional.Project.BinarySchema.ordinalAdditionRightAssociated 𝒞)
      (fun α hα hPrevious firstValue secondValue
          hFirstValue hSecondValue => by
        rw [Definitional.Project.BinarySchema.denote_ordinalAdditionLeftAssociated_iff
          𝕀 hZF.1] at hFirstValue
        rw [Definitional.Project.BinarySchema.denote_ordinalAdditionRightAssociated_iff
          𝕀 hZF.1] at hSecondValue
        rcases hFirstValue with
          ⟨middleValue, hMiddleValue, hFirstValue⟩
        rcases hSecondValue with
          ⟨leftMiddleValue, hLeftMiddleValue, hSecondValue⟩
        rcases hα.classify hZF.1 with
          hEmpty | hSuccessor | hLimit
        · have hMiddleValueEq :=
            (ordinalAddition_zero_iff
              hZF 𝕀 hEmpty).mp hMiddleValue
          have hSecondValueEq :=
            (ordinalAddition_zero_iff
              hZF 𝕀 hEmpty).mp hSecondValue
          subst middleValue
          subst secondValue
          rcases ordinalAddition_existsUnique hZF 𝕀
              (env.bound 0) hMiddle with
            ⟨_, _, hUnique⟩
          exact
            (hUnique firstValue hFirstValue).trans
              (hUnique leftMiddleValue hLeftMiddleValue).symm
        · rcases hSuccessor with
            ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
          rcases (ordinalAddition_successor_iff
              hZF 𝕀
              hPredecessorOrdinal hSuccessor).mp hMiddleValue with
            ⟨middlePredecessor, hMiddlePredecessor,
              hMiddleValueSuccessor⟩
          have hMiddlePredecessorOrdinal :=
            ordinalAddition_isOrdinal hZF 𝕀
              hMiddle hPredecessorOrdinal hMiddlePredecessor
          rcases (ordinalAddition_successor_iff
              hZF 𝕀 hMiddlePredecessorOrdinal
              hMiddleValueSuccessor).mp hFirstValue with
            ⟨firstPredecessor, hFirstPredecessor,
              hFirstSuccessor⟩
          rcases (ordinalAddition_successor_iff
              hZF 𝕀 hPredecessorOrdinal
              hSuccessor).mp hSecondValue with
            ⟨secondPredecessor, hSecondPredecessor,
              hSecondSuccessor⟩
          have hPredecessorMem : ℳ.mem predecessor α :=
            (hSuccessor predecessor).mpr
              (Or.inr fun _ => Iff.rfl)
          have hPredecessorEq :=
            hPrevious predecessor hPredecessorMem
              firstPredecessor secondPredecessor
              ((Definitional.Project.BinarySchema.denote_ordinalAdditionLeftAssociated_iff
                𝕀 hZF.1 env predecessor
                firstPredecessor).mpr
                ⟨middlePredecessor, hMiddlePredecessor,
                  hFirstPredecessor⟩)
              ((Definitional.Project.BinarySchema.denote_ordinalAdditionRightAssociated_iff
                𝕀 hZF.1 env predecessor
                secondPredecessor).mpr
                ⟨leftMiddleValue, hLeftMiddleValue,
                  hSecondPredecessor⟩)
          subst secondPredecessor
          exact Structure.SuccessorOf.eq
            hZF.1 hFirstSuccessor hSecondSuccessor
        · rcases (ordinalAddition_limit_iff
              hZF 𝕀 hLimit).mp hSecondValue with
            ⟨range, hRange, hUnion⟩
          have hOuterNormal :=
            ordinalAddition_isNormalOrdinalFunction
              hZF 𝕀 hLeft
          have hInnerNormal :=
            ordinalAddition_isNormalOrdinalFunction
              hZF 𝕀 hMiddle
          apply Eq.symm
          apply hOuterNormal.compose_limit_union_eq
            hZF.1 hInnerNormal hLimit
            hMiddleValue hFirstValue
          · intro member
            constructor
            · intro hMember
              rcases (hRange member).mp hMember with
                ⟨index, hIndex, hRightValue⟩
              rcases ordinalAddition_existsUnique hZF
                  𝕀 middle (hLimit.1.mem hIndex) with
                ⟨innerValue, hInnerValue, _⟩
              rcases ordinalAddition_existsUnique hZF
                  𝕀 left
                  (ordinalAddition_isOrdinal hZF 𝕀
                    hMiddle (hLimit.1.mem hIndex) hInnerValue) with
                ⟨outerValue, hOuterValue, _⟩
              have hValueEq :=
                hPrevious index hIndex outerValue member
                  ((Definitional.Project.BinarySchema.denote_ordinalAdditionLeftAssociated_iff
                    𝕀 hZF.1 env index outerValue).mpr
                    ⟨innerValue, hInnerValue, hOuterValue⟩)
                  ((Definitional.Project.BinarySchema.denote_ordinalAdditionRightAssociated_iff
                    𝕀 hZF.1 env index member).mpr
                    ⟨leftMiddleValue, hLeftMiddleValue,
                      hRightValue⟩)
              subst outerValue
              exact ⟨index, hIndex, innerValue,
                hInnerValue, hOuterValue⟩
            · rintro ⟨index, hIndex, innerValue,
                hInnerValue, hOuterValue⟩
              rcases ordinalAddition_existsUnique hZF
                  𝕀 leftMiddleValue
                  (hLimit.1.mem hIndex) with
                ⟨rightValue, hRightValue, _⟩
              have hValueEq :=
                hPrevious index hIndex member rightValue
                  ((Definitional.Project.BinarySchema.denote_ordinalAdditionLeftAssociated_iff
                    𝕀 hZF.1 env index member).mpr
                    ⟨innerValue, hInnerValue, hOuterValue⟩)
                  ((Definitional.Project.BinarySchema.denote_ordinalAdditionRightAssociated_iff
                    𝕀 hZF.1 env index rightValue).mpr
                    ⟨leftMiddleValue, hLeftMiddleValue,
                      hRightValue⟩)
              subst rightValue
              exact (hRange member).mpr
                ⟨index, hIndex, hRightValue⟩
          · exact hUnion)
  exact hAgreement right hRight leftAssociated rightAssociated
    ((Definitional.Project.BinarySchema.denote_ordinalAdditionLeftAssociated_iff
      𝕀 hZF.1 env right leftAssociated).mpr
      ⟨middleRight, hMiddleRight, hLeftAssociated⟩)
    ((Definitional.Project.BinarySchema.denote_ordinalAdditionRightAssociated_iff
      𝕀 hZF.1 env right rightAssociated).mpr
      ⟨leftMiddle, hLeftMiddle, hRightAssociated⟩)

/-- 序数乘法对右侧序数加法满足左分配律。 -/
theorem ordinalMultiplication_add
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left middle right middleRight
      leftMiddle leftRight leftResult rightResult : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hMiddle : ℳ.IsOrdinal middle)
    (hRight : ℳ.IsOrdinal right)
    (hMiddleRight :
      ℳ.IsOrdinalAddition 𝕀 middleRight middle right)
    (hLeftResult :
      ℳ.IsOrdinalMultiplication 𝕀
        leftResult left middleRight)
    (hLeftMiddle :
      ℳ.IsOrdinalMultiplication 𝕀
        leftMiddle left middle)
    (hLeftRight :
      ℳ.IsOrdinalMultiplication 𝕀
        leftRight left right)
    (hRightResult :
      ℳ.IsOrdinalAddition 𝕀
        rightResult leftMiddle leftRight) :
    leftResult = rightResult := by
  classical
  by_cases hLeftNonempty : ∃ value, ℳ.mem value left
  · let env : Env ℳ 2 := {
      bound := fun
        | 0 => left
        | 1 => middle
      free := fun _ => Classical.choice ℳ.nonempty
    }
    have hAgreement :=
      agreeOnOrdinals_of_progressive hZF env
        (Definitional.Project.BinarySchema.ordinalMultiplicationAdditionLeft 𝒞)
        (Definitional.Project.BinarySchema.ordinalMultiplicationAdditionRight 𝒞)
        (fun α hα hPrevious firstValue secondValue
            hFirstValue hSecondValue => by
          rw [Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionLeft_iff
            𝕀 hZF.1] at hFirstValue
          rw [Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionRight_iff
            𝕀 hZF.1] at hSecondValue
          rcases hFirstValue with
            ⟨middleValue, hMiddleValue, hFirstValue⟩
          rcases hSecondValue with
            ⟨leftMiddleValue, hLeftMiddleValue,
              leftRightValue, hLeftRightValue, hSecondValue⟩
          rcases hα.classify hZF.1 with
            hEmpty | hSuccessor | hLimit
          · have hMiddleValueEq :=
              (ordinalAddition_zero_iff
                hZF 𝕀 hEmpty).mp hMiddleValue
            have hLeftRightEmpty :=
              (ordinalMultiplication_zero_iff
                hZF 𝕀 hLeft hEmpty).mp
                hLeftRightValue
            have hSecondValueEq :=
              (ordinalAddition_zero_iff
                hZF 𝕀 hLeftRightEmpty).mp
                hSecondValue
            subst middleValue
            subst secondValue
            rcases ordinalMultiplication_existsUnique hZF
                𝕀 (env.bound 0) hMiddle with
              ⟨_, _, hUnique⟩
            exact
              (hUnique firstValue hFirstValue).trans
                (hUnique leftMiddleValue hLeftMiddleValue).symm
          · rcases hSuccessor with
              ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
            rcases (ordinalAddition_successor_iff
                hZF 𝕀
                hPredecessorOrdinal hSuccessor).mp hMiddleValue with
              ⟨middlePredecessor, hMiddlePredecessor,
                hMiddleValueSuccessor⟩
            have hMiddlePredecessorOrdinal :=
              ordinalAddition_isOrdinal hZF 𝕀
                hMiddle hPredecessorOrdinal hMiddlePredecessor
            rcases (ordinalMultiplication_successor_iff
                hZF 𝕀 hLeft
                hMiddlePredecessorOrdinal hMiddleValueSuccessor).mp
                hFirstValue with
              ⟨firstPredecessor, hFirstPredecessor,
                hFirstAddition⟩
            rcases (ordinalMultiplication_successor_iff
                hZF 𝕀 hLeft
                hPredecessorOrdinal hSuccessor).mp
                hLeftRightValue with
              ⟨rightPredecessor, hRightPredecessor,
                hRightAddition⟩
            have hLeftMiddleValueOrdinal :=
              ordinalMultiplication_isOrdinal hZF 𝕀
                hLeft hMiddle hLeftMiddleValue
            have hRightPredecessorOrdinal :=
              ordinalMultiplication_isOrdinal hZF 𝕀
                hLeft hPredecessorOrdinal hRightPredecessor
            rcases ordinalAddition_existsUnique hZF 𝕀
                leftMiddleValue hRightPredecessorOrdinal with
              ⟨secondPredecessor, hSecondPredecessor, _⟩
            have hPredecessorMem : ℳ.mem predecessor α :=
              (hSuccessor predecessor).mpr
                (Or.inr fun _ => Iff.rfl)
            have hPredecessorEq :=
              hPrevious predecessor hPredecessorMem
                firstPredecessor secondPredecessor
                ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionLeft_iff
                  𝕀 hZF.1 env predecessor
                  firstPredecessor).mpr
                  ⟨middlePredecessor, hMiddlePredecessor,
                    hFirstPredecessor⟩)
                ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionRight_iff
                  𝕀 hZF.1 env predecessor
                  secondPredecessor).mpr
                  ⟨leftMiddleValue, hLeftMiddleValue,
                    rightPredecessor, hRightPredecessor,
                    hSecondPredecessor⟩)
            subst secondPredecessor
            exact (ordinalAddition_assoc hZF 𝕀
              hLeftMiddleValueOrdinal hRightPredecessorOrdinal hLeft
              hSecondPredecessor hRightAddition
              hSecondValue hFirstAddition).symm
          · have hFirstOuter :=
              ordinalMultiplication_isNormalOrdinalFunction
                hZF 𝕀 hLeft hLeftNonempty
            have hFirstInner :=
              ordinalAddition_isNormalOrdinalFunction
                hZF 𝕀 hMiddle
            have hSecondOuter :=
              ordinalAddition_isNormalOrdinalFunction
                hZF 𝕀
                (ordinalMultiplication_isOrdinal hZF 𝕀
                  hLeft hMiddle hLeftMiddleValue)
            have hSecondInner :=
              ordinalMultiplication_isNormalOrdinalFunction
                hZF 𝕀 hLeft hLeftNonempty
            apply hFirstOuter.compose_limit_eq_of_pointwise_eq
              hZF.1 hFirstInner hSecondOuter hSecondInner
              hLimit hMiddleValue hFirstValue
              hLeftRightValue hSecondValue
            intro index hIndex firstInnerValue
              firstComposedValue secondInnerValue
              secondComposedValue hFirstInnerValue
              hFirstComposedValue hSecondInnerValue
              hSecondComposedValue
            exact hPrevious index hIndex
              firstComposedValue secondComposedValue
              ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionLeft_iff
                𝕀 hZF.1 env index
                firstComposedValue).mpr
                ⟨firstInnerValue, hFirstInnerValue,
                  hFirstComposedValue⟩)
              ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionRight_iff
                𝕀 hZF.1 env index
                secondComposedValue).mpr
                ⟨leftMiddleValue, hLeftMiddleValue,
                  secondInnerValue, hSecondInnerValue,
                  hSecondComposedValue⟩))
    exact hAgreement right hRight leftResult rightResult
      ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionLeft_iff
        𝕀 hZF.1 env right leftResult).mpr
        ⟨middleRight, hMiddleRight, hLeftResult⟩)
      ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationAdditionRight_iff
        𝕀 hZF.1 env right rightResult).mpr
        ⟨leftMiddle, hLeftMiddle, leftRight,
          hLeftRight, hRightResult⟩)
  · have hLeftEmpty : ∀ value, ¬ ℳ.mem value left := by
      simpa only [not_exists] using hLeftNonempty
    have hLeftResultEmpty :=
      ordinalMultiplication_empty_left hZF 𝕀
        hLeftEmpty middleRight
        (ordinalAddition_isOrdinal hZF 𝕀
          hMiddle hRight hMiddleRight)
        leftResult hLeftResult
    have hLeftMiddleEmpty :=
      ordinalMultiplication_empty_left hZF 𝕀
        hLeftEmpty middle hMiddle leftMiddle hLeftMiddle
    have hLeftRightEmpty :=
      ordinalMultiplication_empty_left hZF 𝕀
        hLeftEmpty right hRight leftRight hLeftRight
    have hRightResultEq :=
      (ordinalAddition_zero_iff
        hZF 𝕀 hLeftRightEmpty).mp hRightResult
    subst rightResult
    apply hZF.1.eq_of_same_members
    intro value
    exact iff_of_false
      (hLeftResultEmpty value) (hLeftMiddleEmpty value)

/-- 序数乘法满足结合律。 -/
theorem ordinalMultiplication_assoc
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left middle right leftMiddle middleRight
      leftAssociated rightAssociated : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hMiddle : ℳ.IsOrdinal middle)
    (hRight : ℳ.IsOrdinal right)
    (hLeftMiddle :
      ℳ.IsOrdinalMultiplication 𝕀
        leftMiddle left middle)
    (hMiddleRight :
      ℳ.IsOrdinalMultiplication 𝕀
        middleRight middle right)
    (hLeftAssociated :
      ℳ.IsOrdinalMultiplication 𝕀
        leftAssociated left middleRight)
    (hRightAssociated :
      ℳ.IsOrdinalMultiplication 𝕀
        rightAssociated leftMiddle right) :
    leftAssociated = rightAssociated := by
  classical
  by_cases hLeftNonempty : ∃ value, ℳ.mem value left
  · by_cases hMiddleNonempty : ∃ value, ℳ.mem value middle
    · let env : Env ℳ 2 := {
        bound := fun
          | 0 => left
          | 1 => middle
        free := fun _ => Classical.choice ℳ.nonempty
      }
      have hAgreement :=
        agreeOnOrdinals_of_progressive hZF env
          (Definitional.Project.BinarySchema.ordinalMultiplicationLeftAssociated 𝒞)
          (Definitional.Project.BinarySchema.ordinalMultiplicationRightAssociated 𝒞)
          (fun α hα hPrevious firstValue secondValue
              hFirstValue hSecondValue => by
            rw [Definitional.Project.BinarySchema.denote_ordinalMultiplicationLeftAssociated_iff
              𝕀 hZF.1] at hFirstValue
            rw [Definitional.Project.BinarySchema.denote_ordinalMultiplicationRightAssociated_iff
              𝕀 hZF.1] at hSecondValue
            rcases hFirstValue with
              ⟨middleValue, hMiddleValue, hFirstValue⟩
            rcases hSecondValue with
              ⟨leftMiddleValue, hLeftMiddleValue, hSecondValue⟩
            rcases hα.classify hZF.1 with
              hEmpty | hSuccessor | hLimit
            · have hMiddleValueEmpty :=
                (ordinalMultiplication_zero_iff
                  hZF 𝕀 hMiddle hEmpty).mp
                  hMiddleValue
              have hFirstValueEmpty :=
                (ordinalMultiplication_zero_iff
                  hZF 𝕀 hLeft hMiddleValueEmpty).mp
                  hFirstValue
              have hSecondValueEmpty :=
                (ordinalMultiplication_zero_iff
                  hZF 𝕀
                  (ordinalMultiplication_isOrdinal hZF
                    𝕀 hLeft hMiddle hLeftMiddleValue)
                  hEmpty).mp hSecondValue
              apply hZF.1.eq_of_same_members
              intro value
              exact iff_of_false
                (hFirstValueEmpty value) (hSecondValueEmpty value)
            · rcases hSuccessor with
                ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
              rcases (ordinalMultiplication_successor_iff
                  hZF 𝕀 hMiddle
                  hPredecessorOrdinal hSuccessor).mp hMiddleValue with
                ⟨middlePredecessor, hMiddlePredecessor,
                  hMiddleAddition⟩
              have hMiddlePredecessorOrdinal :=
                ordinalMultiplication_isOrdinal hZF 𝕀
                  hMiddle hPredecessorOrdinal hMiddlePredecessor
              rcases ordinalMultiplication_existsUnique hZF
                  𝕀 left hMiddlePredecessorOrdinal with
                ⟨firstPredecessor, hFirstPredecessor, _⟩
              have hLeftMiddleValueOrdinal :=
                ordinalMultiplication_isOrdinal hZF 𝕀
                  hLeft hMiddle hLeftMiddleValue
              rcases ordinalAddition_existsUnique hZF 𝕀
                  firstPredecessor hLeftMiddleValueOrdinal with
                ⟨firstAddition, hFirstAddition, _⟩
              have hFirstValueEq :=
                ordinalMultiplication_add hZF 𝕀
                  hLeft hMiddlePredecessorOrdinal hMiddle
                  hMiddleAddition hFirstValue
                  hFirstPredecessor hLeftMiddleValue hFirstAddition
              rcases (ordinalMultiplication_successor_iff
                  hZF 𝕀 hLeftMiddleValueOrdinal
                  hPredecessorOrdinal hSuccessor).mp hSecondValue with
                ⟨secondPredecessor, hSecondPredecessor,
                  hSecondAddition⟩
              have hPredecessorMem : ℳ.mem predecessor α :=
                (hSuccessor predecessor).mpr
                  (Or.inr fun _ => Iff.rfl)
              have hPredecessorEq :=
                hPrevious predecessor hPredecessorMem
                  firstPredecessor secondPredecessor
                  ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationLeftAssociated_iff
                    𝕀 hZF.1 env predecessor
                    firstPredecessor).mpr
                    ⟨middlePredecessor, hMiddlePredecessor,
                      hFirstPredecessor⟩)
                  ((
                    Definitional.Project.BinarySchema.denote_ordinalMultiplicationRightAssociated_iff
                    𝕀 hZF.1 env predecessor
                    secondPredecessor).mpr
                    ⟨leftMiddleValue, hLeftMiddleValue,
                      hSecondPredecessor⟩)
              subst secondPredecessor
              rcases ordinalAddition_existsUnique hZF 𝕀
                  firstPredecessor hLeftMiddleValueOrdinal with
                ⟨_, _, hUnique⟩
              have hAdditionEq : firstAddition = secondValue :=
                (hUnique firstAddition hFirstAddition).trans
                  (hUnique secondValue hSecondAddition).symm
              exact hFirstValueEq.trans hAdditionEq
            · rcases (ordinalMultiplication_limit_iff
                  hZF 𝕀
                  (ordinalMultiplication_isOrdinal hZF
                    𝕀 hLeft hMiddle hLeftMiddleValue)
                  hLimit).mp hSecondValue with
                ⟨range, hRange, hUnion⟩
              have hOuterNormal :=
                ordinalMultiplication_isNormalOrdinalFunction
                  hZF 𝕀 hLeft hLeftNonempty
              have hInnerNormal :=
                ordinalMultiplication_isNormalOrdinalFunction
                  hZF 𝕀 hMiddle hMiddleNonempty
              apply Eq.symm
              apply hOuterNormal.compose_limit_union_eq
                hZF.1 hInnerNormal hLimit
                hMiddleValue hFirstValue
              · intro member
                constructor
                · intro hMember
                  rcases (hRange member).mp hMember with
                    ⟨index, hIndex, hRightValue⟩
                  rcases ordinalMultiplication_existsUnique hZF
                      𝕀 middle (hLimit.1.mem hIndex) with
                    ⟨innerValue, hInnerValue, _⟩
                  rcases ordinalMultiplication_existsUnique hZF
                      𝕀 left
                      (ordinalMultiplication_isOrdinal hZF
                        𝕀 hMiddle
                        (hLimit.1.mem hIndex) hInnerValue) with
                    ⟨outerValue, hOuterValue, _⟩
                  have hValueEq :=
                    hPrevious index hIndex outerValue member
                      ((
                        Definitional.Project.BinarySchema.denote_ordinalMultiplicationLeftAssociated_iff
                        𝕀 hZF.1 env index
                        outerValue).mpr
                        ⟨innerValue, hInnerValue, hOuterValue⟩)
                      ((
                        Definitional.Project.BinarySchema.denote_ordinalMultiplicationRightAssociated_iff
                        𝕀 hZF.1 env index member).mpr
                        ⟨leftMiddleValue, hLeftMiddleValue,
                          hRightValue⟩)
                  subst outerValue
                  exact ⟨index, hIndex, innerValue,
                    hInnerValue, hOuterValue⟩
                · rintro ⟨index, hIndex, innerValue,
                    hInnerValue, hOuterValue⟩
                  rcases ordinalMultiplication_existsUnique hZF
                      𝕀 leftMiddleValue
                      (hLimit.1.mem hIndex) with
                    ⟨rightValue, hRightValue, _⟩
                  have hValueEq :=
                    hPrevious index hIndex member rightValue
                      ((
                        Definitional.Project.BinarySchema.denote_ordinalMultiplicationLeftAssociated_iff
                        𝕀 hZF.1 env index member).mpr
                        ⟨innerValue, hInnerValue, hOuterValue⟩)
                      ((
                        Definitional.Project.BinarySchema.denote_ordinalMultiplicationRightAssociated_iff
                        𝕀 hZF.1 env index rightValue).mpr
                        ⟨leftMiddleValue, hLeftMiddleValue,
                          hRightValue⟩)
                  subst rightValue
                  exact (hRange member).mpr
                    ⟨index, hIndex, hRightValue⟩
              · exact hUnion)
      exact hAgreement right hRight leftAssociated rightAssociated
        ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationLeftAssociated_iff
          𝕀 hZF.1 env right leftAssociated).mpr
          ⟨middleRight, hMiddleRight, hLeftAssociated⟩)
        ((Definitional.Project.BinarySchema.denote_ordinalMultiplicationRightAssociated_iff
          𝕀 hZF.1 env right rightAssociated).mpr
          ⟨leftMiddle, hLeftMiddle, hRightAssociated⟩)
    · have hMiddleEmpty : ∀ value, ¬ ℳ.mem value middle := by
        simpa only [not_exists] using hMiddleNonempty
      have hMiddleRightEmpty :=
        ordinalMultiplication_empty_left hZF 𝕀
          hMiddleEmpty right hRight middleRight hMiddleRight
      have hLeftAssociatedEmpty :=
        (ordinalMultiplication_zero_iff
          hZF 𝕀 hLeft hMiddleRightEmpty).mp
          hLeftAssociated
      have hLeftMiddleEmpty :=
        (ordinalMultiplication_zero_iff
          hZF 𝕀 hLeft hMiddleEmpty).mp hLeftMiddle
      have hRightAssociatedEmpty :=
        ordinalMultiplication_empty_left hZF 𝕀
          hLeftMiddleEmpty right hRight
          rightAssociated hRightAssociated
      apply hZF.1.eq_of_same_members
      intro value
      exact iff_of_false
        (hLeftAssociatedEmpty value)
        (hRightAssociatedEmpty value)
  · have hLeftEmpty : ∀ value, ¬ ℳ.mem value left := by
      simpa only [not_exists] using hLeftNonempty
    have hLeftAssociatedEmpty :=
      ordinalMultiplication_empty_left hZF 𝕀
        hLeftEmpty middleRight
        (ordinalMultiplication_isOrdinal hZF 𝕀
          hMiddle hRight hMiddleRight)
        leftAssociated hLeftAssociated
    have hLeftMiddleEmpty :=
      ordinalMultiplication_empty_left hZF 𝕀
        hLeftEmpty middle hMiddle leftMiddle hLeftMiddle
    have hRightAssociatedEmpty :=
      ordinalMultiplication_empty_left hZF 𝕀
        hLeftMiddleEmpty right hRight
        rightAssociated hRightAssociated
    apply hZF.1.eq_of_same_members
    intro value
    exact iff_of_false
      (hLeftAssociatedEmpty value)
      (hRightAssociatedEmpty value)

end ZF

end SetTheory
end YesMetaZFC
