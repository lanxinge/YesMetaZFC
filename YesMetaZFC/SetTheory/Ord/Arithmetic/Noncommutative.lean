import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Ord.Arithmetic.Algebra

/-!
# 序数加法与乘法的非交换性实例

本文件形式化文献中的两个标准实例：

* `1 + ω = ω`，而 `ω + 1` 是 `ω` 的后继；
* `2 * ω = ω`，而 `ω * 2 = ω + ω` 且严格大于 `ω`。

有限阶段的计算通过最小归纳集上的可分离性质完成，极限阶段统一消费序数算术的递归
方程。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `two` 是某个序数一的后继。 -/
def IsOrdinalTwo (ℳ : Structure.{u}) (two : ℳ.Domain) : Prop :=
  ∃ one, ℳ.IsOrdinalOne one ∧ ℳ.SuccessorOf two one

namespace IsOrdinalTwo

/-- 序数二确实是序数。 -/
theorem isOrdinal {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    {two : ℳ.Domain} (hTwo : ℳ.IsOrdinalTwo two) :
    ℳ.IsOrdinal two := by
  rcases hTwo with ⟨one, hOne, hSuccessor⟩
  exact KP.successor_isOrdinal hKP
    (KP.ordinalOne_isOrdinal hKP hOne) hSuccessor

/-- 序数二非空。 -/
theorem nonempty {ℳ : Structure.{u}}
    {two : ℳ.Domain} (hTwo : ℳ.IsOrdinalTwo two) :
    ∃ value, ℳ.mem value two := by
  prove_auto

end IsOrdinalTwo

end Structure

namespace KP

/-- KP 中存在序数二。 -/
theorem exists_ordinalTwo {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) :
    ∃ two, ℳ.IsOrdinalTwo two := by
  rcases exists_ordinalOne hKP with ⟨one, hOne⟩
  rcases exists_successor hKP one with
    ⟨two, hSuccessor⟩
  exact ⟨two, one, hOne, hSuccessor⟩

end KP

namespace Definitional
namespace Project
namespace UnarySchema

/-- 在当前自然数处，`one + n` 的每个值都是 `n` 的后继。 -/
private def ordinalAdditionOneSuccessor
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .forallE <| .imp
    (Formula.isOrdinalAddition 𝒞
      Term.newest (.bound 2) (.bound 1))
    (Formula.isSuccessor Term.newest (.bound 1))
  freeClosed := by
    simp [Formula.isOrdinalAddition, Formula.isSuccessor,
      Formula.related, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]
    apply Formula.related_freeClosed_of_closed <;>
      simp [TermVector.FreeClosed, TermVector.singleton]

/--
在当前自然数处，`two * n` 的值仍属于 `ω`，并且不小于 `n`。
-/
private def ordinalMultiplicationTwoBounded
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := .forallE <| .imp
    (Formula.isOrdinalMultiplication 𝒞
      Term.newest (.bound 2) (.bound 1)) <|
    .conj (.mem Term.newest (.bound 3)) <|
      .disj (Formula.extensionalEq (.bound 1) Term.newest)
        (.mem (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.isOrdinalMultiplication,
      Formula.related, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]
    apply Formula.related_freeClosed_of_closed <;>
      simp [TermVector.FreeClosed, TermVector.singleton]

end UnarySchema

namespace Formula

private theorem satisfies_ordinalAdditionOneSuccessor_iff
    {ℳ : Structure.{u}}
    {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 1)
    (α : ℳ.Domain) :
    satisfies (env.push α)
        (UnarySchema.ordinalAdditionOneSuccessor 𝒞).body ↔
      ∀ sum,
        ℳ.IsOrdinalAddition 𝕀
            sum (env.bound 0) α →
          ℳ.SuccessorOf sum α := by
  simp only [UnarySchema.ordinalAdditionOneSuccessor,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Formula.satisfies_isSuccessor_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_newest]
  rfl

private theorem satisfies_ordinalMultiplicationTwoBounded_iff
    {ℳ : Structure.{u}}
    {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (α : ℳ.Domain) :
    satisfies (env.push α)
        (UnarySchema.ordinalMultiplicationTwoBounded 𝒞).body ↔
      ∀ product,
        ℳ.IsOrdinalMultiplication 𝕀
            product (env.bound 0) α →
          ℳ.mem product (env.bound 1) ∧
            (ℳ.SameMembers α product ∨
              ℳ.mem α product) := by
  simp only [UnarySchema.ordinalMultiplicationTwoBounded,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff,
    Formula.satisfies_isOrdinalMultiplication_iff 𝕀 hExt,
    Formula.satisfies_extensionalEq_iff,
    Structure.SameMembers,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest]
  rfl

end Formula

end Project
end Definitional

namespace ZF

/-- 加一等价于取集合后继。 -/
theorem ordinalAddition_one_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left one : ℳ.Domain}
    (hOne : ℳ.IsOrdinalOne one) :
    ℳ.IsOrdinalAddition 𝕀 sum left one ↔
      ℳ.SuccessorOf sum left := by
  rcases hOne with ⟨zero, hZero, hSuccessor⟩
  rw [ordinalAddition_successor_iff
    hZF 𝕀
    (Structure.IsOrdinal.of_no_members hZero) hSuccessor]
  constructor
  · rintro ⟨previous, hPrevious, hSum⟩
    have hPreviousEq :=
      (ordinalAddition_zero_iff
        hZF 𝕀 hZero).mp hPrevious
    simpa [hPreviousEq] using hSum
  · intro hSum
    exact ⟨left,
      (ordinalAddition_zero_iff
        hZF 𝕀 hZero).mpr rfl,
      hSum⟩

/-- 加二等价于连续取两次集合后继。 -/
theorem ordinalAddition_two_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left two : ℳ.Domain}
    (hTwo : ℳ.IsOrdinalTwo two) :
    ℳ.IsOrdinalAddition 𝕀 sum left two ↔
      ∃ middle,
        ℳ.SuccessorOf middle left ∧
          ℳ.SuccessorOf sum middle := by
  rcases hTwo with ⟨one, hOne, hTwoSuccessor⟩
  rw [ordinalAddition_successor_iff
    hZF 𝕀
    (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hOne)
    hTwoSuccessor]
  constructor
  · rintro ⟨middle, hMiddle, hSum⟩
    exact ⟨middle,
      (ordinalAddition_one_iff
        hZF 𝕀 hOne).mp hMiddle,
      hSum⟩
  · rintro ⟨middle, hMiddle, hSum⟩
    exact ⟨middle,
      (ordinalAddition_one_iff
        hZF 𝕀 hOne).mpr hMiddle,
      hSum⟩

/-- 对每个 `n ∈ ω`，`one + n` 都是 `n` 的后继。 -/
theorem ordinalAddition_one_isSuccessor_on_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω one : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hOne : ℳ.IsOrdinalOne one) :
    ∀ α, ℳ.mem α ω →
      ∀ sum,
        ℳ.IsOrdinalAddition 𝕀 sum one α →
          ℳ.SuccessorOf sum α := by
  let env : Env ℳ 1 := {
    bound := fun _ => one
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply hω.induction
      (fun α => ∀ sum,
        ℳ.IsOrdinalAddition 𝕀 sum one α →
          ℳ.SuccessorOf sum α)
  · rcases exists_separation hZF
        (Definitional.Project.UnarySchema.ordinalAdditionOneSuccessor 𝒞)
        env ω with ⟨closed, hClosed⟩
    refine ⟨closed, fun α => ?_⟩
    rw [hClosed α]
    exact and_congr_right fun _ =>
      Definitional.Project.Formula.satisfies_ordinalAdditionOneSuccessor_iff
        𝕀 hZF.1 env α
  · intro empty hEmpty sum hSum
    have hSumEq :=
      (ordinalAddition_zero_iff
        hZF 𝕀 hEmpty).mp hSum
    rcases hOne with ⟨oneZero, hOneZero, hOneSuccessor⟩
    have hZeroEq : oneZero = empty := by
      apply hZF.1.eq_of_same_members
      intro value
      exact iff_of_false (hOneZero value) (hEmpty value)
    simpa [hSumEq, hZeroEq] using hOneSuccessor
  · intro predecessor hPredecessorOmega hPredecessorProperty
      successor hSuccessor sum hSum
    have hPredecessorOrdinal :=
      hω.members_areOrdinals hZF
        predecessor hPredecessorOmega
    rcases (ordinalAddition_successor_iff
        hZF 𝕀
        hPredecessorOrdinal hSuccessor).mp hSum with
      ⟨previous, hPrevious, hSumSuccessor⟩
    have hPreviousSuccessor :=
      hPredecessorProperty previous hPrevious
    have hPreviousEq :=
      Structure.SuccessorOf.eq hZF.1
        hPreviousSuccessor hSuccessor
    simpa [hPreviousEq] using hSumSuccessor

/-- `one + ω = ω`。 -/
theorem ordinalAddition_one_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω one sum : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hOne : ℳ.IsOrdinalOne one)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum one ω) :
    sum = ω := by
  have hFinite :=
    ordinalAddition_one_isSuccessor_on_omega
      hZF 𝕀 hω hOne
  rcases (ordinalAddition_limit_iff
      hZF 𝕀 (hω.isLimitOrdinal hZF)).mp
      hSum with
    ⟨range, hRange, hUnion⟩
  apply hZF.1.eq_of_same_members
  intro value
  constructor
  · intro hValue
    rcases (hUnion value).mp hValue with
      ⟨rangeValue, hRangeValue, hValueRange⟩
    rcases (hRange rangeValue).mp hRangeValue with
      ⟨index, hIndex, hIndexValue⟩
    have hRangeSuccessor :=
      hFinite index hIndex rangeValue hIndexValue
    rcases hω.1.2 index hIndex with
      ⟨successor, hSuccessor, hSuccessorOmega⟩
    have hRangeEq :=
      Structure.SuccessorOf.eq hZF.1
        hRangeSuccessor hSuccessor
    subst rangeValue
    exact (hω.transitive hZF)
      successor hSuccessorOmega value hValueRange
  · intro hValue
    rcases ordinalAddition_existsUnique hZF 𝕀
        one (hω.members_areOrdinals hZF value hValue) with
      ⟨successor, hSuccessorValue, _⟩
    have hSuccessor :=
      hFinite value hValue successor hSuccessorValue
    exact (hUnion value).mpr
      ⟨successor,
        (hRange successor).mpr
          ⟨value, hValue, hSuccessorValue⟩,
        (hSuccessor value).mpr
          (Or.inr fun _ => Iff.rfl)⟩

/-- `ω + one` 是 `ω` 的后继，因此不等于 `ω`。 -/
theorem ordinalAddition_omega_one_ne_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω one sum : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hOne : ℳ.IsOrdinalOne one)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum ω one) :
    sum ≠ ω := by
  have hSuccessor :=
    (ordinalAddition_one_iff
      hZF 𝕀 hOne).mp hSum
  intro hEq
  subst sum
  have hSelf : ℳ.mem ω ω :=
    (hSuccessor ω).mpr
      (Or.inr fun _ => Iff.rfl)
  exact (hω.isOrdinal hZF).wellOrder.linear.irrefl
    ω hSelf hSelf

/-- 加法在 `one` 与 `ω` 上不交换。 -/
theorem ordinalAddition_not_commutative_at_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω one onePlusOmega omegaPlusOne : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hOne : ℳ.IsOrdinalOne one)
    (hOnePlusOmega :
      ℳ.IsOrdinalAddition 𝕀 onePlusOmega one ω)
    (hωPlusOne :
      ℳ.IsOrdinalAddition 𝕀 omegaPlusOne ω one) :
    onePlusOmega = ω ∧ omegaPlusOne ≠ ω :=
  ⟨ordinalAddition_one_omega
      hZF 𝕀 hω hOne hOnePlusOmega,
    ordinalAddition_omega_one_ne_omega
      hZF 𝕀 hω hOne hωPlusOne⟩

/--
`two * n` 的有限阶段值仍在 `ω` 中，并且不小于输入 `n`。
-/
theorem ordinalMultiplication_two_bounded_on_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω two : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hTwo : ℳ.IsOrdinalTwo two) :
    ∀ α, ℳ.mem α ω →
      ∀ product,
        ℳ.IsOrdinalMultiplication 𝕀
            product two α →
          ℳ.mem product ω ∧
            (ℳ.SameMembers α product ∨
              ℳ.mem α product) := by
  let env : Env ℳ 2 := {
    bound := fun index =>
      Fin.cases two (fun _ => ω) index
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hTwoOrdinal :=
    hTwo.isOrdinal (ZF.modelsKP hZF)
  apply hω.induction
      (fun α => ∀ product,
        ℳ.IsOrdinalMultiplication 𝕀
            product two α →
          ℳ.mem product ω ∧
            (ℳ.SameMembers α product ∨
              ℳ.mem α product))
  · rcases exists_separation hZF
        (Definitional.Project.UnarySchema.ordinalMultiplicationTwoBounded 𝒞)
        env ω with ⟨closed, hClosed⟩
    refine ⟨closed, fun α => ?_⟩
    rw [hClosed α]
    exact and_congr_right fun _ =>
      Definitional.Project.Formula.satisfies_ordinalMultiplicationTwoBounded_iff
        𝕀 hZF.1 env α
  · intro empty hEmpty product hProduct
    have hProductEmpty :=
      (ordinalMultiplication_zero_iff
        hZF 𝕀 hTwoOrdinal hEmpty).mp hProduct
    rcases hω.1.1 with
      ⟨omegaEmpty, hωEmpty, hωEmptyMem⟩
    have hProductEq : product = omegaEmpty := by
      apply hZF.1.eq_of_same_members
      intro value
      exact iff_of_false
        (hProductEmpty value) (hωEmpty value)
    refine ⟨hProductEq ▸ hωEmptyMem, Or.inl ?_⟩
    intro value
    exact iff_of_false (hEmpty value) (hProductEmpty value)
  · intro predecessor hPredecessor hPrevious
      successor hSuccessor product hProduct
    have hPredecessorOrdinal :=
      hω.members_areOrdinals hZF
        predecessor hPredecessor
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        hPredecessorOrdinal hSuccessor
    rcases (ordinalMultiplication_successor_iff
        hZF 𝕀 hTwoOrdinal
        hPredecessorOrdinal hSuccessor).mp hProduct with
      ⟨previous, hPreviousValue, hProductAddition⟩
    have hPreviousData :=
      hPrevious previous hPreviousValue
    rcases (ordinalAddition_two_iff
        hZF 𝕀 hTwo).mp hProductAddition with
      ⟨middle, hMiddleSuccessor, hProductSuccessor⟩
    have hMiddleOmega : ℳ.mem middle ω := by
      rcases hω.1.2 previous hPreviousData.1 with
        ⟨selected, hSelectedSuccessor, hSelectedOmega⟩
      have hSelectedEq :=
        Structure.SuccessorOf.eq hZF.1
          hSelectedSuccessor hMiddleSuccessor
      simpa [hSelectedEq] using hSelectedOmega
    have hProductOmega : ℳ.mem product ω := by
      rcases hω.1.2 middle hMiddleOmega with
        ⟨selected, hSelectedSuccessor, hSelectedOmega⟩
      have hSelectedEq :=
        Structure.SuccessorOf.eq hZF.1
          hSelectedSuccessor hProductSuccessor
      simpa [hSelectedEq] using hSelectedOmega
    refine ⟨hProductOmega, Or.inr ?_⟩
    have hProductOrdinal :=
      ordinalMultiplication_isOrdinal hZF 𝕀
        hTwoOrdinal hSuccessorOrdinal hProduct
    have hMiddleMemProduct : ℳ.mem middle product :=
      (hProductSuccessor middle).mpr
        (Or.inr fun _ => Iff.rfl)
    have hPreviousMemMiddle : ℳ.mem previous middle :=
      (hMiddleSuccessor previous).mpr
        (Or.inr fun _ => Iff.rfl)
    have hPreviousMemProduct : ℳ.mem previous product :=
      hProductOrdinal.transitive middle hMiddleMemProduct
        previous hPreviousMemMiddle
    rcases hPreviousData.2 with
      hSame | hPredecessorPrevious
    · have hPredecessorEq :=
        hZF.1.eq_of_same_members predecessor previous hSame
      subst previous
      have hSuccessorEq :=
        Structure.SuccessorOf.eq hZF.1
          hSuccessor hMiddleSuccessor
      simpa [hSuccessorEq] using hMiddleMemProduct
    · have hPreviousOrdinal :=
        hω.members_areOrdinals hZF
          previous hPreviousData.1
      rcases Structure.IsOrdinal.trichotomy hZF.1
          hSuccessorOrdinal hPreviousOrdinal
          (KP.exists_difference (ZF.modelsKP hZF))
          (KP.exists_intersection (ZF.modelsKP hZF)
            successor previous) with
        hSame | hSuccessorPrevious | hPreviousSuccessor
      · have hEq :=
          hZF.1.eq_of_same_members successor previous hSame
        simpa [hEq] using hPreviousMemProduct
      · exact hProductOrdinal.transitive previous
          hPreviousMemProduct successor hSuccessorPrevious
      · rcases (hSuccessor previous).mp hPreviousSuccessor with
          hPreviousPredecessor | hSame
        · have hSelf : ℳ.mem previous previous :=
            hPreviousOrdinal.transitive predecessor
              hPredecessorPrevious previous hPreviousPredecessor
          exact False.elim <|
            hPreviousOrdinal.wellOrder.linear.irrefl
              previous hSelf hSelf
        · have hEq :=
            hZF.1.eq_of_same_members previous predecessor hSame
          subst previous
          exact False.elim <|
            hPredecessorOrdinal.wellOrder.linear.irrefl
              predecessor hPredecessorPrevious
              hPredecessorPrevious

/-- `two * ω = ω`。 -/
theorem ordinalMultiplication_two_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω two product : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hTwo : ℳ.IsOrdinalTwo two)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product two ω) :
    product = ω := by
  have hTwoOrdinal :=
    hTwo.isOrdinal (ZF.modelsKP hZF)
  have hFinite :=
    ordinalMultiplication_two_bounded_on_omega
      hZF 𝕀 hω hTwo
  rcases (ordinalMultiplication_limit_iff
      hZF 𝕀 hTwoOrdinal
      (hω.isLimitOrdinal hZF)).mp hProduct with
    ⟨range, hRange, hUnion⟩
  apply hZF.1.eq_of_same_members
  intro value
  constructor
  · intro hValue
    rcases (hUnion value).mp hValue with
      ⟨rangeValue, hRangeValue, hValueRange⟩
    rcases (hRange rangeValue).mp hRangeValue with
      ⟨index, hIndex, hIndexValue⟩
    have hRangeOmega :=
      (hFinite index hIndex rangeValue hIndexValue).1
    exact (hω.transitive hZF)
      rangeValue hRangeOmega value hValueRange
  · intro hValue
    rcases hω.1.2 value hValue with
      ⟨successor, hSuccessor, hSuccessorOmega⟩
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        (hω.members_areOrdinals hZF value hValue)
        hSuccessor
    rcases ordinalMultiplication_existsUnique hZF
        𝕀 two hSuccessorOrdinal with
      ⟨successorValue, hSuccessorValue, _⟩
    have hSuccessorData :=
      hFinite successor hSuccessorOmega
        successorValue hSuccessorValue
    have hValueSuccessor : ℳ.mem value successor :=
      (hSuccessor value).mpr
        (Or.inr fun _ => Iff.rfl)
    have hValueSuccessorValue : ℳ.mem value successorValue := by
      rcases hSuccessorData.2 with hSame | hMember
      · exact (hSame value).mp hValueSuccessor
      · exact
          (ordinalMultiplication_isOrdinal
            hZF 𝕀 hTwoOrdinal
            hSuccessorOrdinal hSuccessorValue).transitive
            successor hMember value hValueSuccessor
    exact (hUnion value).mpr
      ⟨successorValue,
        (hRange successorValue).mpr
          ⟨successor, hSuccessorOmega, hSuccessorValue⟩,
        hValueSuccessorValue⟩

/-- `ω + ω` 严格大于 `ω`。 -/
theorem ordinalAddition_omega_self_ne_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω sum : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hSum :
      ℳ.IsOrdinalAddition 𝕀 sum ω ω) :
    sum ≠ ω := by
  rcases hω.1.1 with
    ⟨zero, hZero, hZeroOmega⟩
  have hωOrdinal := hω.isOrdinal hZF
  have hωPlusZero :
      ℳ.IsOrdinalAddition 𝕀 ω ω zero :=
    (ordinalAddition_zero_iff
      hZF 𝕀 hZero).mpr rfl
  have hωMemSum :=
    ordinalAddition_isIncreasingOnOrdinals
      hZF 𝕀 hωOrdinal
      zero ω
      (Structure.IsOrdinal.of_no_members hZero)
      hωOrdinal hZeroOmega
      ω sum hωPlusZero hSum
  intro hEq
  subst sum
  exact hωOrdinal.wellOrder.linear.irrefl
    ω hωMemSum hωMemSum

/-- `ω * two = ω + ω`。 -/
theorem ordinalMultiplication_omega_two_eq_addition
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω two product sum : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hTwo : ℳ.IsOrdinalTwo two)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product ω two)
    (hSum :
      ℳ.IsOrdinalAddition 𝕀 sum ω ω) :
    product = sum := by
  rcases hTwo with ⟨one, hOne, hTwoSuccessor⟩
  have hωOrdinal := hω.isOrdinal hZF
  rcases (ordinalMultiplication_successor_iff
      hZF 𝕀 hωOrdinal
      (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hOne)
      hTwoSuccessor).mp hProduct with
    ⟨omegaTimesOne, hωTimesOne, hProductAddition⟩
  rcases hOne with ⟨zero, hZero, hOneSuccessor⟩
  rcases (ordinalMultiplication_successor_iff
      hZF 𝕀 hωOrdinal
      (Structure.IsOrdinal.of_no_members hZero)
      hOneSuccessor).mp hωTimesOne with
    ⟨omegaTimesZero, hωTimesZero, hωTimesOneAddition⟩
  have hωTimesZeroEmpty :=
    (ordinalMultiplication_zero_iff
      hZF 𝕀 hωOrdinal hZero).mp
      hωTimesZero
  have hωTimesOneEq :
      omegaTimesOne = ω :=
    ordinalAddition_empty_left hZF 𝕀
      hωTimesZeroEmpty ω hωOrdinal
      omegaTimesOne hωTimesOneAddition
  subst omegaTimesOne
  rcases ordinalAddition_existsUnique hZF 𝕀
      ω hωOrdinal with ⟨_, _, hUnique⟩
  exact
    (hUnique product hProductAddition).trans
      (hUnique sum hSum).symm

/-- 乘法在 `two` 与 `ω` 上不交换。 -/
theorem ordinalMultiplication_not_commutative_at_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω two twoTimesOmega omegaTimesTwo
      omegaPlusOmega : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (hTwo : ℳ.IsOrdinalTwo two)
    (hTwoTimesOmega :
      ℳ.IsOrdinalMultiplication 𝕀
        twoTimesOmega two ω)
    (hωTimesTwo :
      ℳ.IsOrdinalMultiplication 𝕀
        omegaTimesTwo ω two)
    (hωPlusOmega :
      ℳ.IsOrdinalAddition 𝕀
        omegaPlusOmega ω ω) :
    twoTimesOmega = ω ∧
      omegaTimesTwo = omegaPlusOmega ∧
        omegaPlusOmega ≠ ω :=
  ⟨ordinalMultiplication_two_omega
      hZF 𝕀 hω hTwo hTwoTimesOmega,
    ordinalMultiplication_omega_two_eq_addition
      hZF 𝕀 hω hTwo
      hωTimesTwo hωPlusOmega,
    ordinalAddition_omega_self_ne_omega
      hZF 𝕀 hω hωPlusOmega⟩

/-- ZF 模型中实际存在一个见证加法不交换的 `one` 与 `ω` 实例。 -/
theorem exists_ordinalAddition_noncommutative
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ) :
    ∃ ω one onePlusOmega omegaPlusOne,
      ℳ.IsOmega ω ∧
        ℳ.IsOrdinalOne one ∧
          ℳ.IsOrdinalAddition 𝕀
            onePlusOmega one ω ∧
          ℳ.IsOrdinalAddition 𝕀
            omegaPlusOne ω one ∧
          onePlusOmega = ω ∧
            omegaPlusOne ≠ ω := by
  rcases exists_omega hZF with ⟨ω, hω⟩
  rcases KP.exists_ordinalOne (ZF.modelsKP hZF) with
    ⟨one, hOne⟩
  rcases ordinalAddition_existsUnique hZF 𝕀
      one (hω.isOrdinal hZF) with
    ⟨onePlusOmega, hOnePlusOmega, _⟩
  rcases ordinalAddition_existsUnique hZF 𝕀
      ω
      (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hOne) with
    ⟨omegaPlusOne, hωPlusOne, _⟩
  have hNoncommutative :=
    ordinalAddition_not_commutative_at_omega
      hZF 𝕀 hω hOne
      hOnePlusOmega hωPlusOne
  exact ⟨ω, one, onePlusOmega, omegaPlusOne,
    hω, hOne, hOnePlusOmega, hωPlusOne,
    hNoncommutative.1, hNoncommutative.2⟩

/-- ZF 模型中实际存在一个见证乘法不交换的 `two` 与 `ω` 实例。 -/
theorem exists_ordinalMultiplication_noncommutative
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ) :
    ∃ ω two twoTimesOmega omegaTimesTwo omegaPlusOmega,
      ℳ.IsOmega ω ∧
        ℳ.IsOrdinalTwo two ∧
          ℳ.IsOrdinalMultiplication 𝕀
            twoTimesOmega two ω ∧
          ℳ.IsOrdinalMultiplication 𝕀
            omegaTimesTwo ω two ∧
          ℳ.IsOrdinalAddition 𝕀
            omegaPlusOmega ω ω ∧
          twoTimesOmega = ω ∧
            omegaTimesTwo = omegaPlusOmega ∧
              omegaPlusOmega ≠ ω := by
  rcases exists_omega hZF with ⟨ω, hω⟩
  rcases KP.exists_ordinalTwo (ZF.modelsKP hZF) with
    ⟨two, hTwo⟩
  have hωOrdinal := hω.isOrdinal hZF
  have hTwoOrdinal :=
    hTwo.isOrdinal (ZF.modelsKP hZF)
  rcases ordinalMultiplication_existsUnique hZF
      𝕀 two hωOrdinal with
    ⟨twoTimesOmega, hTwoTimesOmega, _⟩
  rcases ordinalMultiplication_existsUnique hZF
      𝕀 ω hTwoOrdinal with
    ⟨omegaTimesTwo, hωTimesTwo, _⟩
  rcases ordinalAddition_existsUnique hZF
      𝕀 ω hωOrdinal with
    ⟨omegaPlusOmega, hωPlusOmega, _⟩
  have hNoncommutative :=
    ordinalMultiplication_not_commutative_at_omega
      hZF 𝕀 hω hTwo
      hTwoTimesOmega hωTimesTwo hωPlusOmega
  exact ⟨ω, two, twoTimesOmega, omegaTimesTwo,
    omegaPlusOmega, hω, hTwo,
    hTwoTimesOmega, hωTimesTwo, hωPlusOmega,
    hNoncommutative.1, hNoncommutative.2.1,
    hNoncommutative.2.2⟩

end ZF

end SetTheory
end YesMetaZFC
