import YesMetaZFC.SetTheory.Ord.Arithmetic.Closure

/-!
# 序数算术的单位律

本文件证明序数加法的左单位律与序数乘法的右单位律。两者同时服务于正规性和后续
代数律，因此位于 `Normal` 与 `Algebra` 之前的公共层。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Definitional
namespace Project
namespace BinarySchema

/-- 忽略固定参数、把每个输入映到自身的恒等类关系。 -/
private def ordinalIdentity : BinarySchema 1 where
  body := Formula.extensionalEq (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.extensionalEq, Formula.FreeClosed]

private theorem denote_ordinalIdentity_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    (env : Env ℳ 1) (input output : ℳ.Domain) :
    ordinalIdentity.denote env input output ↔ input = output := by
  simp only [ordinalIdentity, denote,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

end BinarySchema

end Project
end Definitional

namespace ZF

/-- 空序数作为左加数时，任意序数加法值等于右加数。 -/
theorem ordinalAddition_empty_left
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeftEmpty : ∀ value, ¬ ℳ.mem value left) :
    ∀ right, ℳ.IsOrdinal right →
      ∀ sum,
        ℳ.IsOrdinalAddition 𝕀 sum left right →
          sum = right := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env =
        fun right sum =>
          ℳ.IsOrdinalAddition 𝕀 sum left right := by
    funext right sum
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalAddition_iff
        𝕀 hZF.1 env right sum
  have hAgreement :=
    agreeOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞)
      Definitional.Project.BinarySchema.ordinalIdentity
      (fun α hα hPrevious
          sum identityValue hSum hIdentity => by
        rw [hRelation] at hPrevious hSum
        have hIdentityEq : α = identityValue :=
          (Definitional.Project.BinarySchema.denote_ordinalIdentity_iff
            hZF.1 env α identityValue).mp hIdentity
        rcases hα.classify hZF.1 with
          hEmpty | hSuccessor | hLimit
        · have hSumEq :=
            (ordinalAddition_zero_iff
              hZF 𝕀 hEmpty).mp hSum
          have hLeftEq : left = α := by
            apply hZF.1.eq_of_same_members
            intro value
            exact iff_of_false
              (hLeftEmpty value) (hEmpty value)
          exact hSumEq.trans (hLeftEq.trans hIdentityEq)
        · rcases hSuccessor with
            ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
          rcases (ordinalAddition_successor_iff
              hZF 𝕀
              hPredecessorOrdinal hSuccessor).mp hSum with
            ⟨previous, hPreviousValue, hSumSuccessor⟩
          have hPredecessorMem : ℳ.mem predecessor α :=
            (hSuccessor predecessor).mpr
              (Or.inr fun _ => Iff.rfl)
          have hPreviousEq : previous = predecessor :=
            hPrevious predecessor hPredecessorMem
              previous predecessor hPreviousValue
              ((Definitional.Project.BinarySchema.denote_ordinalIdentity_iff
                hZF.1 env predecessor predecessor).mpr rfl)
          subst previous
          exact
            (Structure.SuccessorOf.eq hZF.1
              hSumSuccessor hSuccessor).trans hIdentityEq
        · rcases (ordinalAddition_limit_iff
              hZF 𝕀 hLimit).mp hSum with
            ⟨range, hRange, hUnion⟩
          have hSumEq : sum = α := by
            apply hZF.1.eq_of_same_members
            intro value
            constructor
            · intro hValue
              rcases (hUnion value).mp hValue with
                ⟨rangeValue, hRangeValue, hValueRange⟩
              rcases (hRange rangeValue).mp hRangeValue with
                ⟨index, hIndex, hIndexValue⟩
              have hRangeValueEq : rangeValue = index :=
                hPrevious index hIndex
                  rangeValue index hIndexValue
                  ((Definitional.Project.BinarySchema.denote_ordinalIdentity_iff
                    hZF.1 env index index).mpr rfl)
              subst rangeValue
              exact hLimit.1.transitive index hIndex
                value hValueRange
            · intro hValue
              rcases hLimit.2.2 value hValue with
                ⟨larger, hLarger, hValueLarger⟩
              rcases ordinalAddition_existsUnique
                  hZF 𝕀 left
                  (hLimit.1.mem hLarger) with
                ⟨largerValue, hLargerValue, _⟩
              have hLargerValueEq : largerValue = larger :=
                hPrevious larger hLarger
                  largerValue larger hLargerValue
                  ((Definitional.Project.BinarySchema.denote_ordinalIdentity_iff
                    hZF.1 env larger larger).mpr rfl)
              subst largerValue
              exact (hUnion value).mpr
                ⟨larger, (hRange larger).mpr
                  ⟨larger, hLarger, hLargerValue⟩,
                  hValueLarger⟩
          exact hSumEq.trans hIdentityEq)
  intro right hRight sum hSum
  rw [hRelation] at hAgreement
  exact hAgreement right hRight sum right hSum
    ((Definitional.Project.BinarySchema.denote_ordinalIdentity_iff
      hZF.1 env right right).mpr rfl)

/-- 乘以序数一保持原序数。 -/
theorem ordinalMultiplication_one_right
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left one : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hOne : ℳ.IsOrdinalOne one)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left one) :
    product = left := by
  rcases hOne with ⟨zero, hZero, hSuccessor⟩
  rcases (ordinalMultiplication_successor_iff
      hZF 𝕀 hLeft
      (Structure.IsOrdinal.of_no_members hZero)
      hSuccessor).mp hProduct with
    ⟨previous, hPrevious, hProductAddition⟩
  have hPreviousEmpty :=
    (ordinalMultiplication_zero_iff
      hZF 𝕀 hLeft hZero).mp hPrevious
  exact ordinalAddition_empty_left hZF 𝕀
    hPreviousEmpty left hLeft product hProductAddition

end ZF

end SetTheory
end YesMetaZFC
