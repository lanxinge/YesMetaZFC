import YesMetaZFC.SetTheory.Ord.Arithmetic.Algebra

/-!
# 序数算术的比较与分解

本文件整理序数算术值的成员分解。加法值由左侧初段和右参数索引的尾段值组成；
这一事实是加法序和表示、唯一加法余项以及后续乘法块分解的共同基础。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure.IsOrdinalAddition

/-- 加法关系的右参数必为序数。 -/
theorem right_isOrdinal
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sum left right : ℳ.Domain}
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum left right) :
    ℳ.IsOrdinal right := by
  prove_auto

end Structure.IsOrdinalAddition

namespace Structure.IsOrdinalMultiplication

/-- 乘法关系的右参数必为序数。 -/
theorem right_isOrdinal
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {product left right : ℳ.Domain}
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left right) :
    ℳ.IsOrdinal right := by
  prove_auto

end Structure.IsOrdinalMultiplication

namespace Structure.IsOrdinalExponentiation

/-- 幂关系的指数参数必为序数。 -/
theorem exponent_isOrdinal
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {power base exponent : ℳ.Domain}
    (hPower :
      ℳ.IsOrdinalExponentiation 𝕀 power base exponent) :
    ℳ.IsOrdinal exponent := by
  prove_auto

end Structure.IsOrdinalExponentiation

namespace Definitional
namespace Project
namespace UnarySchema

/-- 当前加法值的成员由左初段或更早的加法值给出。 -/
private def ordinalAdditionMembership
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .forallE <| .imp
    (Formula.isOrdinalAddition 𝒞
      Term.newest (.bound 2) (.bound 1)) <|
    .forallE <| .iff (.mem Term.newest (.bound 1)) <|
      .disj (.mem Term.newest (.bound 3)) <|
        Formula.existsMem (.bound 2) <|
          Formula.isOrdinalAddition 𝒞
            (.bound 1) (.bound 4) Term.newest
  freeClosed := by
    simp [Formula.isOrdinalAddition, Formula.related,
      Formula.existsMem, Formula.FreeClosed,
      Term.newest]
    constructor
    · apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]
    · apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

/-- 当前乘法值的成员按右参数分解为唯一块中的加法余项。 -/
private def ordinalMultiplicationMembership
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .forallE <| .imp
    (Formula.isOrdinalMultiplication 𝒞
      Term.newest (.bound 2) (.bound 1)) <|
    .forallE <| .iff (.mem Term.newest (.bound 1)) <|
      Formula.existsMem (.bound 2) <| .existsE <|
        .conj
          (Formula.isOrdinalMultiplication 𝒞
            Term.newest (.bound 5) (.bound 1))
          (Formula.existsMem (.bound 5) <|
            Formula.isOrdinalAddition 𝒞
              (.bound 3) (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.isOrdinalMultiplication,
      Formula.isOrdinalAddition, Formula.related,
      Formula.existsMem, Formula.FreeClosed,
      Term.newest]
    constructor
    · apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]
    · constructor
      · apply Formula.related_freeClosed_of_closed <;>
          simp [TermVector.FreeClosed, TermVector.singleton]
      · apply Formula.related_freeClosed_of_closed <;>
          simp [TermVector.FreeClosed, TermVector.singleton]

/-- 当前候选满足固定目标不大于对应的加法值。 -/
private def ordinalAdditionUpperBound
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalAddition 𝒞
      Term.newest (.bound 2) (.bound 1))
    (.disj (Formula.extensionalEq (.bound 3) Term.newest)
      (.mem (.bound 3) Term.newest))
  freeClosed := by
    simp [Formula.isOrdinalAddition, Formula.related,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]
    apply Formula.related_freeClosed_of_closed <;>
      simp [TermVector.FreeClosed, TermVector.singleton]

/-- 当前候选的后继乘法块严格越过固定被除数。 -/
private def ordinalMultiplicationUpperBlock
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := .existsE <| .conj
    (Formula.isSuccessor Term.newest (.bound 1)) <|
    .existsE <| .conj
      (Formula.isOrdinalMultiplication 𝒞
        Term.newest (.bound 3) (.bound 1))
      (.mem (.bound 4) Term.newest)
  freeClosed := by
    simp [Formula.isSuccessor,
      Formula.isOrdinalMultiplication, Formula.related,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]
    apply Formula.related_freeClosed_of_closed <;>
      simp [TermVector.FreeClosed, TermVector.singleton]

end UnarySchema

namespace Formula

private theorem satisfies_ordinalAdditionMembership_iff
    {ℳ : Structure.{u}}
    {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 1)
    (right : ℳ.Domain) :
    satisfies (env.push right)
        (UnarySchema.ordinalAdditionMembership 𝒞).body ↔
      ∀ sum,
        ℳ.IsOrdinalAddition 𝕀
            sum (env.bound 0) right →
          ∀ value,
            ℳ.mem value sum ↔
              ℳ.mem value (env.bound 0) ∨
                ∃ index, ℳ.mem index right ∧
                  ℳ.IsOrdinalAddition 𝕀
                    value (env.bound 0) index := by
  simp only [UnarySchema.ordinalAdditionMembership,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_disj_iff, satisfies_existsMem_iff,
    satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

private theorem satisfies_ordinalMultiplicationMembership_iff
    {ℳ : Structure.{u}}
    {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 1)
    (right : ℳ.Domain) :
    satisfies (env.push right)
        (UnarySchema.ordinalMultiplicationMembership 𝒞).body ↔
      ∀ product,
        ℳ.IsOrdinalMultiplication 𝕀
            product (env.bound 0) right →
          ∀ value,
            ℳ.mem value product ↔
              ∃ index, ℳ.mem index right ∧
                ∃ block,
                  ℳ.IsOrdinalMultiplication 𝕀
                    block (env.bound 0) index ∧
                  ∃ remainder, ℳ.mem remainder (env.bound 0) ∧
                    ℳ.IsOrdinalAddition 𝕀
                      value block remainder := by
  simp only [UnarySchema.ordinalMultiplicationMembership,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_existsMem_iff, satisfies_exists_iff,
    satisfies_conj_iff,
    satisfies_isOrdinalMultiplication_iff 𝕀 hExt,
    satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Definitional.Term.eval_newest]
  rfl

private theorem satisfies_ordinalAdditionUpperBound_iff
    {ℳ : Structure.{u}}
    {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (candidate : ℳ.Domain) :
    satisfies (env.push candidate)
        (UnarySchema.ordinalAdditionUpperBound 𝒞).body ↔
      ∃ sum,
        ℳ.IsOrdinalAddition 𝕀
            sum (env.bound 0) candidate ∧
          (env.bound 1 = sum ∨ ℳ.mem (env.bound 1) sum) := by
  simp only [UnarySchema.ordinalAdditionUpperBound,
    satisfies_exists_iff, satisfies_conj_iff, satisfies_disj_iff,
    satisfies_mem_iff,
    satisfies_isOrdinalAddition_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest]
  rfl

private theorem satisfies_ordinalMultiplicationUpperBlock_iff
    {ℳ : Structure.{u}}
    {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (candidate : ℳ.Domain) :
    satisfies (env.push candidate)
        (UnarySchema.ordinalMultiplicationUpperBlock 𝒞).body ↔
      ∃ successor,
        ℳ.SuccessorOf successor candidate ∧
          ∃ product,
            ℳ.IsOrdinalMultiplication 𝕀
                product (env.bound 0) successor ∧
              ℳ.mem (env.bound 1) product := by
  simp only [UnarySchema.ordinalMultiplicationUpperBlock,
    satisfies_exists_iff, satisfies_conj_iff, satisfies_mem_iff,
    satisfies_isSuccessor_iff,
    satisfies_isOrdinalMultiplication_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Definitional.Term.eval_newest]
  rfl

end Formula

end Project
end Definitional

namespace ZF

/--
`left + right` 的成员恰为 `left` 的成员，或某个更早加法值 `left + index`。
-/
theorem ordinalAddition_mem_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left right value : ℳ.Domain}
    (hRight : ℳ.IsOrdinal right)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum left right) :
    ℳ.mem value sum ↔
      ℳ.mem value left ∨
        ∃ index, ℳ.mem index right ∧
          ℳ.IsOrdinalAddition 𝕀 value left index := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∀ currentSum,
      ℳ.IsOrdinalAddition 𝕀 currentSum left current →
        ∀ member,
          ℳ.mem member currentSum ↔
            ℳ.mem member left ∨
              ∃ index, ℳ.mem index current ∧
                ℳ.IsOrdinalAddition 𝕀 member left index
  have hProperty : property right := by
    apply hRight.induction property
    · rcases exists_separation hZF
          (Definitional.Project.UnarySchema.ordinalAdditionMembership 𝒞).neg
          env right with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp [Definitional.Project.UnarySchema.neg, property,
        Definitional.Project.Formula.satisfies_neg_iff,
        Definitional.Project.Formula.satisfies_ordinalAdditionMembership_iff
          𝕀 hZF.1]
      intro _
      rfl
    · intro current hCurrent hPrevious currentSum hCurrentSum member
      rcases hCurrent.classify hZF.1 with
        hEmpty | hSuccessor | hLimit
      · have hCurrentSumEq :=
          (ordinalAddition_zero_iff
            hZF 𝕀 hEmpty).mp hCurrentSum
        constructor
        · intro hMember
          exact Or.inl <| hCurrentSumEq ▸ hMember
        · intro hMember
          rcases hMember with hMemberLeft | hEarlier
          · exact hCurrentSumEq.symm ▸ hMemberLeft
          · rcases hEarlier with ⟨index, hIndex, _⟩
            exact False.elim (hEmpty index hIndex)
      · rcases hSuccessor with
          ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
        rcases (ordinalAddition_successor_iff
            hZF 𝕀
            hPredecessorOrdinal hSuccessor).mp hCurrentSum with
          ⟨previousSum, hPreviousSum, hCurrentSuccessor⟩
        have hPredecessorMem : ℳ.mem predecessor current :=
          (hSuccessor predecessor).mpr
            (Or.inr fun _ => Iff.rfl)
        have hPreviousMembership :=
          hPrevious predecessor hPredecessorMem
            previousSum hPreviousSum
        constructor
        · intro hMember
          rcases (hCurrentSuccessor member).mp hMember with
            hMemberPrevious | hSame
          · rcases (hPreviousMembership member).mp
                hMemberPrevious with
              hMemberLeft | ⟨index, hIndex, hIndexValue⟩
            · exact Or.inl hMemberLeft
            · exact Or.inr
                ⟨index,
                  (hSuccessor index).mpr (Or.inl hIndex),
                  hIndexValue⟩
          · have hMemberEq :=
              hZF.1.eq_of_same_members
                member previousSum hSame
            subst member
            exact Or.inr
              ⟨predecessor, hPredecessorMem, hPreviousSum⟩
        · intro hMember
          rcases hMember with
            hMemberLeft | ⟨index, hIndex, hIndexValue⟩
          · exact (hCurrentSuccessor member).mpr <| Or.inl <|
              (hPreviousMembership member).mpr
                (Or.inl hMemberLeft)
          · rcases (hSuccessor index).mp hIndex with
              hIndexPredecessor | hSame
            · exact (hCurrentSuccessor member).mpr <| Or.inl <|
                (hPreviousMembership member).mpr <| Or.inr
                  ⟨index, hIndexPredecessor, hIndexValue⟩
            · have hIndexEq :=
                hZF.1.eq_of_same_members
                  index predecessor hSame
              subst index
              rcases ordinalAddition_existsUnique hZF
                  𝕀 left hPredecessorOrdinal with
                ⟨_, _, hUnique⟩
              have hMemberEq : member = previousSum :=
                (hUnique member hIndexValue).trans
                  (hUnique previousSum hPreviousSum).symm
              subst member
              exact (hCurrentSuccessor previousSum).mpr
                (Or.inr fun _ => Iff.rfl)
      · rcases (ordinalAddition_limit_iff
            hZF 𝕀 hLimit).mp hCurrentSum with
          ⟨range, hRange, hUnion⟩
        constructor
        · intro hMember
          rcases (hUnion member).mp hMember with
            ⟨rangeValue, hRangeValue, hMemberRange⟩
          rcases (hRange rangeValue).mp hRangeValue with
            ⟨index, hIndex, hIndexValue⟩
          rcases (hPrevious index hIndex
              rangeValue hIndexValue member).mp hMemberRange with
            hMemberLeft | ⟨earlier, hEarlierIndex, hEarlierValue⟩
          · exact Or.inl hMemberLeft
          · exact Or.inr
              ⟨earlier,
                hLimit.1.transitive index hIndex
                  earlier hEarlierIndex,
                hEarlierValue⟩
        · intro hMember
          rcases hMember with
            hMemberLeft | ⟨index, hIndex, hIndexValue⟩
          · rcases hLimit.2.1 with ⟨index, hIndex⟩
            rcases ordinalAddition_existsUnique hZF
                𝕀 left (hLimit.1.mem hIndex) with
              ⟨rangeValue, hRangeValue, _⟩
            have hMemberRange :
                ℳ.mem member rangeValue :=
              (hPrevious index hIndex
                rangeValue hRangeValue member).mpr
                (Or.inl hMemberLeft)
            exact (hUnion member).mpr
              ⟨rangeValue,
                (hRange rangeValue).mpr
                  ⟨index, hIndex, hRangeValue⟩,
                hMemberRange⟩
          · rcases hLimit.2.2 index hIndex with
              ⟨larger, hLarger, hIndexLarger⟩
            rcases ordinalAddition_existsUnique hZF
                𝕀 left (hLimit.1.mem hLarger) with
              ⟨rangeValue, hRangeValue, _⟩
            have hMemberRange :
                ℳ.mem member rangeValue :=
              (hPrevious larger hLarger
                rangeValue hRangeValue member).mpr <| Or.inr
                  ⟨index, hIndexLarger, hIndexValue⟩
            exact (hUnion member).mpr
              ⟨rangeValue,
                (hRange rangeValue).mpr
                  ⟨larger, hLarger, hRangeValue⟩,
                hMemberRange⟩
  exact hProperty sum hSum value

/-- 序数加法值不小于左参数。 -/
theorem ordinalAddition_left_eq_or_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left right : ℳ.Domain}
    (hRight : ℳ.IsOrdinal right)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum left right) :
    left = sum ∨ ℳ.mem left sum := by
  by_cases hRightEmpty : ∀ value, ¬ ℳ.mem value right
  · exact Or.inl <|
      ((ordinalAddition_zero_iff
        hZF 𝕀 hRightEmpty).mp hSum).symm
  · have hRightNonempty : ∃ value, ℳ.mem value right := by
      apply Classical.byContradiction
      intro hNoMember
      apply hRightEmpty
      intro value hValue
      exact hNoMember ⟨value, hValue⟩
    rcases KP.exists_empty (ZF.modelsKP hZF) with
      ⟨zero, hZero⟩
    have hZeroOrdinal : ℳ.IsOrdinal zero :=
      Structure.IsOrdinal.of_no_members hZero
    have hZeroRight : ℳ.mem zero right :=
      hRight.empty_mem_of_nonempty
        (ZF.modelsKP hZF) hRightNonempty hZero
    have hLeftPlusZero :
        ℳ.IsOrdinalAddition 𝕀 left left zero :=
      (ordinalAddition_zero_iff
        hZF 𝕀 hZero).mpr rfl
    exact Or.inr <| (ordinalAddition_mem_iff
      hZF 𝕀 hRight hSum).mpr <| Or.inr
        ⟨zero, hZeroRight, hLeftPlusZero⟩

/-- 固定左参数的序数加法可在右侧消去。 -/
theorem ordinalAddition_right_injective
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left first second : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hFirst : ℳ.IsOrdinal first) (hSecond : ℳ.IsOrdinal second)
    (hFirstSum :
      ℳ.IsOrdinalAddition 𝕀 sum left first)
    (hSecondSum :
      ℳ.IsOrdinalAddition 𝕀 sum left second) :
    first = second := by
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hFirst hSecond
      (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF)
        first second) with
    hSame | hFirstSecond | hSecondFirst
  · exact hZF.1.eq_of_same_members first second hSame
  · have hSelf :=
      ordinalAddition_isIncreasingOnOrdinals
        hZF 𝕀 hLeft
        first second hFirst hSecond hFirstSecond
        sum sum hFirstSum hSecondSum
    exact False.elim <|
      (ordinalAddition_isOrdinal hZF 𝕀
        hLeft hFirst hFirstSum).wellOrder.linear.irrefl
        sum hSelf hSelf
  · have hSelf :=
      ordinalAddition_isIncreasingOnOrdinals
        hZF 𝕀 hLeft
        second first hSecond hFirst hSecondFirst
        sum sum hSecondSum hFirstSum
    exact False.elim <|
      (ordinalAddition_isOrdinal hZF 𝕀
        hLeft hSecond hSecondSum).wellOrder.linear.irrefl
        sum hSelf hSelf

/-- 左初段的每个成员都小于任意加法尾段值。 -/
theorem ordinalAddition_left_member_mem_value
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left index value member : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hIndex : ℳ.IsOrdinal index)
    (hMember : ℳ.mem member left)
    (hValue :
      ℳ.IsOrdinalAddition 𝕀 value left index) :
    ℳ.mem member value := by
  have hValueOrdinal :=
    ordinalAddition_isOrdinal hZF 𝕀
      hLeft hIndex hValue
  rcases ordinalAddition_left_eq_or_mem
      hZF 𝕀 hIndex hValue with
    hEqual | hLeftValue
  · simpa [hEqual] using hMember
  · exact hValueOrdinal.transitive left hLeftValue member hMember

/-- 加法尾段值不可能严格小于左初段中的成员。 -/
theorem ordinalAddition_value_not_mem_left_member
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left index value member : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hIndex : ℳ.IsOrdinal index)
    (hMember : ℳ.mem member left)
    (hValue :
      ℳ.IsOrdinalAddition 𝕀 value left index) :
    ¬ ℳ.mem value member := by
  intro hValueMember
  have hMemberOrdinal := hLeft.mem hMember
  have hValueOrdinal :=
    ordinalAddition_isOrdinal hZF 𝕀
      hLeft hIndex hValue
  have hMemberValue :=
    ordinalAddition_left_member_mem_value
      hZF 𝕀 hLeft hIndex hMember hValue
  have hSelf :=
    hValueOrdinal.transitive
      member hMemberValue value hValueMember
  exact hValueOrdinal.wellOrder.linear.irrefl
    value hSelf hSelf

/-- 固定左参数后，加法值之间的严格次序正好反映右参数次序。 -/
theorem ordinalAddition_values_mem_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left firstIndex secondIndex firstValue secondValue : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hFirstIndex : ℳ.IsOrdinal firstIndex)
    (hSecondIndex : ℳ.IsOrdinal secondIndex)
    (hFirstValue :
      ℳ.IsOrdinalAddition 𝕀 firstValue left firstIndex)
    (hSecondValue :
      ℳ.IsOrdinalAddition 𝕀 secondValue left secondIndex) :
    ℳ.mem firstValue secondValue ↔
      ℳ.mem firstIndex secondIndex := by
  constructor
  · intro hFirstSecond
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hFirstIndex hSecondIndex
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          firstIndex secondIndex) with
      hSame | hIndexOrder | hReverse
    · have hIndexEq :=
        hZF.1.eq_of_same_members firstIndex secondIndex hSame
      subst secondIndex
      rcases ordinalAddition_existsUnique hZF
          𝕀 left hFirstIndex with
        ⟨_, _, hUnique⟩
      have hValueEq : firstValue = secondValue :=
        (hUnique firstValue hFirstValue).trans
          (hUnique secondValue hSecondValue).symm
      subst secondValue
      exact False.elim <|
        (ordinalAddition_isOrdinal hZF 𝕀
          hLeft hFirstIndex hFirstValue).wellOrder.linear.irrefl
          firstValue hFirstSecond hFirstSecond
    · exact hIndexOrder
    · have hSecondFirst :=
        ordinalAddition_isIncreasingOnOrdinals
          hZF 𝕀 hLeft
          secondIndex firstIndex
          hSecondIndex hFirstIndex hReverse
          secondValue firstValue hSecondValue hFirstValue
      have hSelf :=
        (ordinalAddition_isOrdinal hZF 𝕀
          hLeft hSecondIndex hSecondValue).transitive
          firstValue hFirstSecond secondValue hSecondFirst
      exact False.elim <|
        (ordinalAddition_isOrdinal hZF 𝕀
          hLeft hSecondIndex hSecondValue).wellOrder.linear.irrefl
          secondValue hSelf hSelf
  · intro hIndexOrder
    exact ordinalAddition_isIncreasingOnOrdinals
      hZF 𝕀 hLeft
      firstIndex secondIndex
      hFirstIndex hSecondIndex hIndexOrder
      firstValue secondValue hFirstValue hSecondValue

/-- 底数大于一时，固定底数的序数幂可在指数处消去。 -/
theorem ordinalExponentiation_exponent_injective
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power base one first second : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base) (hOne : ℳ.IsOrdinalOne one)
    (hOneBase : ℳ.mem one base)
    (hFirst : ℳ.IsOrdinal first) (hSecond : ℳ.IsOrdinal second)
    (hFirstPower :
      ℳ.IsOrdinalExponentiation 𝕀 power base first)
    (hSecondPower :
      ℳ.IsOrdinalExponentiation 𝕀 power base second) :
    first = second := by
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hFirst hSecond
      (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF)
        first second) with
    hSame | hFirstSecond | hSecondFirst
  · exact hZF.1.eq_of_same_members first second hSame
  · have hSelf :=
      ordinalExponentiation_isIncreasingOnOrdinals
        hZF 𝕀 hBase hOne hOneBase
        first second hFirst hSecond hFirstSecond
        power power hFirstPower hSecondPower
    exact False.elim <|
      (ordinalExponentiation_isOrdinal hZF 𝕀
        hBase hFirst hFirstPower).wellOrder.linear.irrefl
        power hSelf hSelf
  · have hSelf :=
      ordinalExponentiation_isIncreasingOnOrdinals
        hZF 𝕀 hBase hOne hOneBase
        second first hSecond hFirst hSecondFirst
        power power hSecondPower hFirstPower
    exact False.elim <|
      (ordinalExponentiation_isOrdinal hZF 𝕀
        hBase hFirst hFirstPower).wellOrder.linear.irrefl
        power hSelf hSelf

/-- 底数大于一时，幂值之间的严格次序恰好反映指数次序。 -/
theorem ordinalExponentiation_values_mem_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base one first second firstPower secondPower : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base) (hOne : ℳ.IsOrdinalOne one)
    (hOneBase : ℳ.mem one base)
    (hFirst : ℳ.IsOrdinal first) (hSecond : ℳ.IsOrdinal second)
    (hFirstPower :
      ℳ.IsOrdinalExponentiation 𝕀 firstPower base first)
    (hSecondPower :
      ℳ.IsOrdinalExponentiation 𝕀 secondPower base second) :
    ℳ.mem firstPower secondPower ↔ ℳ.mem first second := by
  constructor
  · intro hPowerOrder
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hFirst hSecond
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          first second) with
      hSame | hIndexOrder | hReverse
    · have hIndexEq :=
        hZF.1.eq_of_same_members first second hSame
      subst second
      rcases ordinalExponentiation_existsUnique hZF
          𝕀 hBase hFirst with
        ⟨_, _, hUnique⟩
      have hPowerEq : firstPower = secondPower :=
        (hUnique firstPower hFirstPower).trans
          (hUnique secondPower hSecondPower).symm
      subst secondPower
      exact False.elim <|
        (ordinalExponentiation_isOrdinal hZF 𝕀
          hBase hFirst hFirstPower).wellOrder.linear.irrefl
          firstPower hPowerOrder hPowerOrder
    · exact hIndexOrder
    · have hReversePower :=
        ordinalExponentiation_isIncreasingOnOrdinals
          hZF 𝕀 hBase hOne hOneBase
          second first hSecond hFirst hReverse
          secondPower firstPower hSecondPower hFirstPower
      have hSelf :=
        (ordinalExponentiation_isOrdinal hZF 𝕀
          hBase hSecond hSecondPower).transitive
          firstPower hPowerOrder secondPower hReversePower
      exact False.elim <|
        (ordinalExponentiation_isOrdinal hZF 𝕀
          hBase hSecond hSecondPower).wellOrder.linear.irrefl
          secondPower hSelf hSelf
  · intro hIndexOrder
    exact
      ordinalExponentiation_isIncreasingOnOrdinals
        hZF 𝕀 hBase hOne hOneBase
        first second hFirst hSecond hIndexOrder
        firstPower secondPower hFirstPower hSecondPower

/--
若 `left < right`，则存在唯一的右余项 `remainder` 使
`left + remainder = right`。
-/
theorem ordinalAddition_existsUnique_rightRemainder
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hRight : ℳ.IsOrdinal right)
    (hLeftRight : ℳ.mem left right) :
    ∃ remainder,
      ℳ.IsOrdinalAddition 𝕀 right left remainder ∧
        ∀ other,
          ℳ.IsOrdinalAddition 𝕀 right left other →
            other = remainder := by
  rcases KP.exists_successor (ZF.modelsKP hZF) right with
    ⟨rightSuccessor, hRightSuccessor⟩
  have hRightSuccessorOrdinal : ℳ.IsOrdinal rightSuccessor :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hRight hRightSuccessor
  let env : Env ℳ 2 := {
    bound := fun
      | 0 => left
      | 1 => right
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.ordinalAdditionUpperBound 𝒞)
      env rightSuccessor with
    ⟨candidates, hCandidates⟩
  have hCandidatesSemantic :
      ∀ candidate,
        ℳ.mem candidate candidates ↔
          ℳ.mem candidate rightSuccessor ∧
            ∃ sum,
              ℳ.IsOrdinalAddition 𝕀 sum left candidate ∧
                (right = sum ∨ ℳ.mem right sum) := by
    intro candidate
    rw [hCandidates candidate]
    constructor
    · rintro ⟨hBound, hCandidate⟩
      exact ⟨hBound,
        (Definitional.Project.Formula.satisfies_ordinalAdditionUpperBound_iff
          𝕀 hZF.1 env candidate).mp hCandidate⟩
    · rintro ⟨hBound, hCandidate⟩
      exact ⟨hBound,
        (Definitional.Project.Formula.satisfies_ordinalAdditionUpperBound_iff
          𝕀 hZF.1 env candidate).mpr hCandidate⟩
  have hCandidatesSubset :
      ℳ.MemberSubset candidates rightSuccessor := by
    intro candidate hCandidate
    exact (hCandidatesSemantic candidate).mp hCandidate |>.1
  have hCandidatesNonempty :
      ∃ candidate, ℳ.mem candidate candidates := by
    rcases ordinalAddition_existsUnique hZF
        𝕀 left hRight with
      ⟨sum, hSum, _⟩
    have hRightLeSum :=
      ordinalAddition_right_eq_or_mem hZF
        𝕀 hLeft hRight hSum
    exact
      ⟨right,
        (hCandidatesSemantic right).mpr
          ⟨(hRightSuccessor right).mpr
              (Or.inr fun _ => Iff.rfl),
            sum, hSum, hRightLeSum⟩⟩
  rcases hRightSuccessorOrdinal.wellOrder.least
      candidates hCandidatesSubset hCandidatesNonempty with
    ⟨remainder, hRemainderCandidate, hLeast⟩
  have hRemainderData :=
    (hCandidatesSemantic remainder).mp hRemainderCandidate
  rcases hRemainderData.2 with
    ⟨sum, hSum, hRightSum | hRightSum⟩
  · subst sum
    refine ⟨remainder, hSum, ?_⟩
    intro other hOther
    exact ordinalAddition_right_injective
      hZF 𝕀 hLeft
      (Structure.IsOrdinalAddition.right_isOrdinal hOther)
      (Structure.IsOrdinalAddition.right_isOrdinal hSum)
      hOther hSum
  · rcases (ordinalAddition_mem_iff
        hZF 𝕀
        (Structure.IsOrdinalAddition.right_isOrdinal hSum)
        hSum).mp hRightSum with
      hRightLeft | ⟨earlier, hEarlier, hEarlierSum⟩
    · have hSelf :=
        hRight.transitive left hLeftRight right hRightLeft
      exact False.elim <|
        hRight.wellOrder.linear.irrefl right hSelf hSelf
    · have hEarlierCandidate : ℳ.mem earlier candidates :=
        (hCandidatesSemantic earlier).mpr
          ⟨hRightSuccessorOrdinal.transitive
              remainder hRemainderData.1 earlier hEarlier,
            right, hEarlierSum, Or.inl rfl⟩
      rcases hLeast earlier hEarlierCandidate with
        hSame | hRemainderEarlier
      · have hEarlierEq :=
          hZF.1.eq_of_same_members remainder earlier hSame
        subst earlier
        exact False.elim <|
          hRightSuccessorOrdinal.wellOrder.linear.irrefl
            remainder hRemainderData.1 hEarlier
      · have hSelf :=
          hRightSuccessorOrdinal.wellOrder.linear.trans
            remainder hRemainderData.1
            earlier
              ((hCandidatesSemantic earlier).mp
                hEarlierCandidate).1
            remainder hRemainderData.1
            hRemainderEarlier hEarlier
        exact False.elim <|
          hRightSuccessorOrdinal.wellOrder.linear.irrefl
            remainder hRemainderData.1 hSelf

/--
`left · right` 的成员恰位于某个 `index ∈ right` 块中，并且是
`left · index + remainder`，其中 `remainder ∈ left`。
-/
theorem ordinalMultiplication_mem_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left right value : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hRight : ℳ.IsOrdinal right)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left right) :
    ℳ.mem value product ↔
      ∃ index, ℳ.mem index right ∧
        ∃ block,
          ℳ.IsOrdinalMultiplication 𝕀 block left index ∧
            ∃ remainder, ℳ.mem remainder left ∧
              ℳ.IsOrdinalAddition 𝕀
                value block remainder := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∀ currentProduct,
      ℳ.IsOrdinalMultiplication 𝕀
          currentProduct left current →
        ∀ member,
          ℳ.mem member currentProduct ↔
            ∃ index, ℳ.mem index current ∧
              ∃ block,
                ℳ.IsOrdinalMultiplication 𝕀
                    block left index ∧
                  ∃ remainder, ℳ.mem remainder left ∧
                    ℳ.IsOrdinalAddition 𝕀
                      member block remainder
  have hProperty : property right := by
    apply hRight.induction property
    · rcases exists_separation hZF
          (Definitional.Project.UnarySchema.ordinalMultiplicationMembership 𝒞).neg
          env right with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp [Definitional.Project.UnarySchema.neg, property,
        Definitional.Project.Formula.satisfies_neg_iff,
        Definitional.Project.Formula.satisfies_ordinalMultiplicationMembership_iff
          𝕀 hZF.1]
      intro _
      rfl
    · intro current hCurrent hPrevious currentProduct
        hCurrentProduct member
      rcases hCurrent.classify hZF.1 with
        hEmpty | hSuccessor | hLimit
      · have hCurrentProductEmpty :=
          (ordinalMultiplication_zero_iff
            hZF 𝕀 hLeft hEmpty).mp hCurrentProduct
        constructor
        · exact fun hMember =>
            False.elim (hCurrentProductEmpty member hMember)
        · rintro ⟨index, hIndex, _⟩
          exact False.elim (hEmpty index hIndex)
      · rcases hSuccessor with
          ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
        rcases (ordinalMultiplication_successor_iff
            hZF 𝕀 hLeft
            hPredecessorOrdinal hSuccessor).mp hCurrentProduct with
          ⟨previousProduct, hPreviousProduct, hCurrentAddition⟩
        have hPredecessorMem : ℳ.mem predecessor current :=
          (hSuccessor predecessor).mpr
            (Or.inr fun _ => Iff.rfl)
        have hPreviousMembership :=
          hPrevious predecessor hPredecessorMem
            previousProduct hPreviousProduct
        have hCurrentMembership :
            ℳ.mem member currentProduct ↔
              ℳ.mem member previousProduct ∨
                ∃ remainder, ℳ.mem remainder left ∧
                  ℳ.IsOrdinalAddition 𝕀
                    member previousProduct remainder :=
          ordinalAddition_mem_iff hZF 𝕀
            (value := member) hLeft hCurrentAddition
        constructor
        · intro hMember
          rcases (hCurrentMembership.mp hMember) with
            hMemberPrevious |
              ⟨remainder, hRemainder, hRemainderValue⟩
          · rcases (hPreviousMembership member).mp hMemberPrevious with
              ⟨index, hIndex, block, hBlock,
                remainder, hRemainder, hValue⟩
            exact
              ⟨index, (hSuccessor index).mpr (Or.inl hIndex),
                block, hBlock, remainder, hRemainder, hValue⟩
          · exact
              ⟨predecessor, hPredecessorMem,
                previousProduct, hPreviousProduct,
                remainder, hRemainder, hRemainderValue⟩
        · rintro ⟨index, hIndex, block, hBlock,
            remainder, hRemainder, hValue⟩
          rcases (hSuccessor index).mp hIndex with
            hIndexPredecessor | hSame
          · apply hCurrentMembership.mpr
            apply Or.inl
            exact (hPreviousMembership member).mpr
              ⟨index, hIndexPredecessor, block, hBlock,
                remainder, hRemainder, hValue⟩
          · have hIndexEq :=
              hZF.1.eq_of_same_members index predecessor hSame
            subst index
            rcases ordinalMultiplication_existsUnique hZF
                𝕀 left hPredecessorOrdinal with
              ⟨_, _, hUnique⟩
            have hBlockEq : block = previousProduct :=
              (hUnique block hBlock).trans
                (hUnique previousProduct hPreviousProduct).symm
            subst block
            exact hCurrentMembership.mpr <| Or.inr
              ⟨remainder, hRemainder, hValue⟩
      · rcases (ordinalMultiplication_limit_iff
            hZF 𝕀 hLeft hLimit).mp hCurrentProduct with
          ⟨range, hRange, hUnion⟩
        constructor
        · intro hMember
          rcases (hUnion member).mp hMember with
            ⟨rangeValue, hRangeValue, hMemberRange⟩
          rcases (hRange rangeValue).mp hRangeValue with
            ⟨index, hIndex, hIndexValue⟩
          rcases (hPrevious index hIndex
              rangeValue hIndexValue member).mp hMemberRange with
            ⟨earlier, hEarlierIndex, block, hBlock,
              remainder, hRemainder, hValue⟩
          exact
            ⟨earlier,
              hLimit.1.transitive index hIndex
                earlier hEarlierIndex,
              block, hBlock, remainder, hRemainder, hValue⟩
        · rintro ⟨index, hIndex, block, hBlock,
            remainder, hRemainder, hValue⟩
          rcases hLimit.2.2 index hIndex with
            ⟨larger, hLarger, hIndexLarger⟩
          rcases ordinalMultiplication_existsUnique hZF
              𝕀 left (hLimit.1.mem hLarger) with
            ⟨rangeValue, hRangeValue, _⟩
          have hMemberRange : ℳ.mem member rangeValue :=
            (hPrevious larger hLarger
              rangeValue hRangeValue member).mpr
              ⟨index, hIndexLarger, block, hBlock,
                remainder, hRemainder, hValue⟩
          exact (hUnion member).mpr
            ⟨rangeValue,
              (hRange rangeValue).mpr
                ⟨larger, hLarger, hRangeValue⟩,
              hMemberRange⟩
  exact hProperty product hProduct value

/-- 序数上的“等于或隶属”关系具有传递性。 -/
theorem eqOrMem_trans
    {ℳ : Structure.{u}} {left middle right : ℳ.Domain}
    (hRight : ℳ.IsOrdinal right)
    (hLeftMiddle : left = middle ∨ ℳ.mem left middle)
    (hMiddleRight : middle = right ∨ ℳ.mem middle right) :
    left = right ∨ ℳ.mem left right := by
  prove_auto

/-- 较早乘法块中的每个值都严格小于较晚块中的每个值。 -/
theorem ordinalMultiplication_block_lt_of_index_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left smallerIndex largerIndex smallerBlock largerBlock
      smallerRemainder largerRemainder
      smallerValue largerValue : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hLeftNonempty : ∃ member, ℳ.mem member left)
    (hSmallerIndex : ℳ.IsOrdinal smallerIndex)
    (hLargerIndex : ℳ.IsOrdinal largerIndex)
    (hIndexOrder : ℳ.mem smallerIndex largerIndex)
    (hSmallerBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        smallerBlock left smallerIndex)
    (hLargerBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        largerBlock left largerIndex)
    (hSmallerRemainder : ℳ.mem smallerRemainder left)
    (hLargerRemainder : ℳ.mem largerRemainder left)
    (hSmallerValue :
      ℳ.IsOrdinalAddition 𝕀
        smallerValue smallerBlock smallerRemainder)
    (hLargerValue :
      ℳ.IsOrdinalAddition 𝕀
        largerValue largerBlock largerRemainder) :
    ℳ.mem smallerValue largerValue := by
  rcases KP.exists_successor (ZF.modelsKP hZF) smallerIndex with
    ⟨smallerSuccessor, hSmallerSuccessor⟩
  have hSmallerSuccessorOrdinal : ℳ.IsOrdinal smallerSuccessor :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hSmallerIndex hSmallerSuccessor
  rcases ordinalMultiplication_existsUnique hZF
      𝕀 left hSmallerSuccessorOrdinal with
    ⟨successorProduct, hSuccessorProduct, _⟩
  have hSmallerIndexSuccessor :
      ℳ.mem smallerIndex smallerSuccessor :=
    (hSmallerSuccessor smallerIndex).mpr
      (Or.inr fun _ => Iff.rfl)
  have hSmallerValueSuccessorProduct :
      ℳ.mem smallerValue successorProduct :=
    (ordinalMultiplication_mem_iff hZF 𝕀
      hLeft hSmallerSuccessorOrdinal hSuccessorProduct).mpr
      ⟨smallerIndex, hSmallerIndexSuccessor,
        smallerBlock, hSmallerBlock,
        smallerRemainder, hSmallerRemainder, hSmallerValue⟩
  have hSuccessorSubset :
      ℳ.MemberSubset smallerSuccessor largerIndex := by
    intro member hMember
    rcases (hSmallerSuccessor member).mp hMember with
      hMemberSmaller | hSame
    · exact hLargerIndex.transitive
        smallerIndex hIndexOrder member hMemberSmaller
    · have hMemberEq :=
        hZF.1.eq_of_same_members member smallerIndex hSame
      simpa [hMemberEq] using hIndexOrder
  have hSuccessorLeLarger :
      smallerSuccessor = largerIndex ∨
        ℳ.mem smallerSuccessor largerIndex := by
    by_cases hSame :
        ℳ.SameMembers smallerSuccessor largerIndex
    · exact Or.inl <|
        hZF.1.eq_of_same_members _ _ hSame
    · exact Or.inr <| Structure.IsOrdinal.mem_of_properSubset
        hZF.1 hSmallerSuccessorOrdinal hLargerIndex
        ⟨hSuccessorSubset, hSame⟩
        (KP.exists_difference (ZF.modelsKP hZF)
          smallerSuccessor largerIndex)
  have hLargerBlockOrdinal :=
    ordinalMultiplication_isOrdinal hZF 𝕀
      hLeft hLargerIndex hLargerBlock
  have hSuccessorProductLeBlock :
      successorProduct = largerBlock ∨
        ℳ.mem successorProduct largerBlock := by
    rcases hSuccessorLeLarger with hEqual | hMember
    · subst largerIndex
      rcases ordinalMultiplication_existsUnique hZF
          𝕀 left hSmallerSuccessorOrdinal with
        ⟨_, _, hUnique⟩
      exact Or.inl <|
        (hUnique successorProduct hSuccessorProduct).trans
          (hUnique largerBlock hLargerBlock).symm
    · exact Or.inr <|
        ordinalMultiplication_isIncreasingOnOrdinals
          hZF 𝕀 hLeft hLeftNonempty
          smallerSuccessor largerIndex
          hSmallerSuccessorOrdinal hLargerIndex hMember
          successorProduct largerBlock
          hSuccessorProduct hLargerBlock
  have hLargerRemainderOrdinal : ℳ.IsOrdinal largerRemainder :=
    hLeft.mem hLargerRemainder
  have hBlockLeValue :
      largerBlock = largerValue ∨
        ℳ.mem largerBlock largerValue :=
    ordinalAddition_left_eq_or_mem hZF 𝕀
      hLargerRemainderOrdinal hLargerValue
  have hLargerValueOrdinal :=
    ordinalAddition_isOrdinal hZF 𝕀
      hLargerBlockOrdinal hLargerRemainderOrdinal hLargerValue
  have hSuccessorProductLeValue :=
    eqOrMem_trans hLargerValueOrdinal
      hSuccessorProductLeBlock hBlockLeValue
  rcases hSuccessorProductLeValue with hEqual | hMember
  · simpa [hEqual] using hSmallerValueSuccessorProduct
  · exact hLargerValueOrdinal.transitive
      successorProduct hMember
      smallerValue hSmallerValueSuccessorProduct

/-- 乘法分块值的次序正好是块指标优先、余项次之的右字典序。 -/
theorem ordinalMultiplication_block_values_mem_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left firstIndex secondIndex firstBlock secondBlock
      firstRemainder secondRemainder firstValue secondValue : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hLeftNonempty : ∃ member, ℳ.mem member left)
    (hFirstIndex : ℳ.IsOrdinal firstIndex)
    (hSecondIndex : ℳ.IsOrdinal secondIndex)
    (hFirstBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        firstBlock left firstIndex)
    (hSecondBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        secondBlock left secondIndex)
    (hFirstRemainder : ℳ.mem firstRemainder left)
    (hSecondRemainder : ℳ.mem secondRemainder left)
    (hFirstValue :
      ℳ.IsOrdinalAddition 𝕀
        firstValue firstBlock firstRemainder)
    (hSecondValue :
      ℳ.IsOrdinalAddition 𝕀
        secondValue secondBlock secondRemainder) :
    ℳ.mem firstValue secondValue ↔
      ℳ.mem firstIndex secondIndex ∨
        (firstIndex = secondIndex ∧
          ℳ.mem firstRemainder secondRemainder) := by
  constructor
  · intro hValueOrder
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hFirstIndex hSecondIndex
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          firstIndex secondIndex) with
      hSame | hIndexOrder | hReverse
    · have hIndexEq :=
        hZF.1.eq_of_same_members firstIndex secondIndex hSame
      subst secondIndex
      rcases ordinalMultiplication_existsUnique hZF
          𝕀 left hFirstIndex with
        ⟨_, _, hUnique⟩
      have hBlockEq : firstBlock = secondBlock :=
        (hUnique firstBlock hFirstBlock).trans
          (hUnique secondBlock hSecondBlock).symm
      subst secondBlock
      exact Or.inr ⟨rfl,
        (ordinalAddition_values_mem_iff
          hZF 𝕀
          (ordinalMultiplication_isOrdinal hZF 𝕀
            hLeft hFirstIndex hFirstBlock)
          (hLeft.mem hFirstRemainder)
          (hLeft.mem hSecondRemainder)
          hFirstValue hSecondValue).mp hValueOrder⟩
    · exact Or.inl hIndexOrder
    · have hReverseValue :=
        ordinalMultiplication_block_lt_of_index_mem
          hZF 𝕀 hLeft hLeftNonempty
          hSecondIndex hFirstIndex hReverse
          hSecondBlock hFirstBlock
          hSecondRemainder hFirstRemainder
          hSecondValue hFirstValue
      have hSecondValueOrdinal :=
        ordinalAddition_isOrdinal hZF 𝕀
          (ordinalMultiplication_isOrdinal hZF 𝕀
            hLeft hSecondIndex hSecondBlock)
          (hLeft.mem hSecondRemainder) hSecondValue
      have hSelf :=
        hSecondValueOrdinal.transitive
          firstValue hValueOrder secondValue hReverseValue
      exact False.elim <|
        hSecondValueOrdinal.wellOrder.linear.irrefl
          secondValue hSelf hSelf
  · rintro (hIndexOrder | ⟨hIndexEq, hRemainderOrder⟩)
    · exact ordinalMultiplication_block_lt_of_index_mem
        hZF 𝕀 hLeft hLeftNonempty
        hFirstIndex hSecondIndex hIndexOrder
        hFirstBlock hSecondBlock
        hFirstRemainder hSecondRemainder
        hFirstValue hSecondValue
    · subst secondIndex
      rcases ordinalMultiplication_existsUnique hZF
          𝕀 left hFirstIndex with
        ⟨_, _, hUnique⟩
      have hBlockEq : firstBlock = secondBlock :=
        (hUnique firstBlock hFirstBlock).trans
          (hUnique secondBlock hSecondBlock).symm
      subst secondBlock
      exact (ordinalAddition_values_mem_iff
        hZF 𝕀
        (ordinalMultiplication_isOrdinal hZF 𝕀
          hLeft hFirstIndex hFirstBlock)
        (hLeft.mem hFirstRemainder)
        (hLeft.mem hSecondRemainder)
        hFirstValue hSecondValue).mpr hRemainderOrder

/-- 乘法分块表示的块指标与块内余项都是唯一的。 -/
theorem ordinalMultiplication_block_coordinates_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left firstIndex secondIndex firstBlock secondBlock
      firstRemainder secondRemainder value : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hLeftNonempty : ∃ member, ℳ.mem member left)
    (hFirstIndex : ℳ.IsOrdinal firstIndex)
    (hSecondIndex : ℳ.IsOrdinal secondIndex)
    (hFirstBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        firstBlock left firstIndex)
    (hSecondBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        secondBlock left secondIndex)
    (hFirstRemainder : ℳ.mem firstRemainder left)
    (hSecondRemainder : ℳ.mem secondRemainder left)
    (hFirstValue :
      ℳ.IsOrdinalAddition 𝕀
        value firstBlock firstRemainder)
    (hSecondValue :
      ℳ.IsOrdinalAddition 𝕀
        value secondBlock secondRemainder) :
    firstIndex = secondIndex ∧ firstRemainder = secondRemainder := by
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hFirstIndex hSecondIndex
      (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF)
        firstIndex secondIndex) with
    hSame | hFirstSecond | hSecondFirst
  · have hIndexEq :=
      hZF.1.eq_of_same_members firstIndex secondIndex hSame
    subst secondIndex
    rcases ordinalMultiplication_existsUnique hZF
        𝕀 left hFirstIndex with
      ⟨_, _, hUnique⟩
    have hBlockEq : firstBlock = secondBlock :=
      (hUnique firstBlock hFirstBlock).trans
        (hUnique secondBlock hSecondBlock).symm
    subst secondBlock
    exact ⟨rfl,
      ordinalAddition_right_injective
        hZF 𝕀
        (ordinalMultiplication_isOrdinal hZF 𝕀
          hLeft hFirstIndex hFirstBlock)
        (hLeft.mem hFirstRemainder)
        (hLeft.mem hSecondRemainder)
        hFirstValue hSecondValue⟩
  · have hSelf :=
      ordinalMultiplication_block_lt_of_index_mem
        hZF 𝕀 hLeft hLeftNonempty
        hFirstIndex hSecondIndex hFirstSecond
        hFirstBlock hSecondBlock
        hFirstRemainder hSecondRemainder
        hFirstValue hSecondValue
    exact False.elim <|
      (ordinalAddition_isOrdinal hZF 𝕀
        (ordinalMultiplication_isOrdinal hZF 𝕀
          hLeft hFirstIndex hFirstBlock)
        (hLeft.mem hFirstRemainder) hFirstValue).wellOrder.linear.irrefl
        value hSelf hSelf
  · have hSelf :=
      ordinalMultiplication_block_lt_of_index_mem
        hZF 𝕀 hLeft hLeftNonempty
        hSecondIndex hFirstIndex hSecondFirst
        hSecondBlock hFirstBlock
        hSecondRemainder hFirstRemainder
        hSecondValue hFirstValue
    exact False.elim <|
      (ordinalAddition_isOrdinal hZF 𝕀
        (ordinalMultiplication_isOrdinal hZF 𝕀
          hLeft hFirstIndex hFirstBlock)
        (hLeft.mem hFirstRemainder) hFirstValue).wellOrder.linear.irrefl
        value hSelf hSelf

/--
非零序数除数给出唯一的商余对：
`dividend = divisor · quotient + remainder` 且 `remainder < divisor`。
-/
theorem ordinalDivision_existsUnique_pair
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {dividend divisor : ℳ.Domain}
    (hDividend : ℳ.IsOrdinal dividend)
    (hDivisor : ℳ.IsOrdinal divisor)
    (hDivisorNonempty : ∃ member, ℳ.mem member divisor) :
    ∃ quotient remainder,
      ℳ.IsOrdinalDivision 𝕀
          dividend divisor quotient remainder ∧
        ∀ otherQuotient otherRemainder,
          ℳ.IsOrdinalDivision 𝕀
              dividend divisor otherQuotient otherRemainder →
            otherQuotient = quotient ∧
              otherRemainder = remainder := by
  rcases KP.exists_successor (ZF.modelsKP hZF) dividend with
    ⟨dividendSuccessor, hDividendSuccessor⟩
  have hDividendSuccessorOrdinal : ℳ.IsOrdinal dividendSuccessor :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hDividend hDividendSuccessor
  let env : Env ℳ 2 := {
    bound := fun
      | 0 => divisor
      | 1 => dividend
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.ordinalMultiplicationUpperBlock 𝒞)
      env dividendSuccessor with
    ⟨candidates, hCandidates⟩
  have hCandidatesSemantic :
      ∀ candidate,
        ℳ.mem candidate candidates ↔
          ℳ.mem candidate dividendSuccessor ∧
            ∃ successor,
              ℳ.SuccessorOf successor candidate ∧
                ∃ product,
                  ℳ.IsOrdinalMultiplication 𝕀
                      product divisor successor ∧
                    ℳ.mem dividend product := by
    intro candidate
    rw [hCandidates candidate]
    constructor
    · rintro ⟨hBound, hCandidate⟩
      exact ⟨hBound,
        (Definitional.Project.Formula.satisfies_ordinalMultiplicationUpperBlock_iff
          𝕀 hZF.1 env candidate).mp hCandidate⟩
    · rintro ⟨hBound, hCandidate⟩
      exact ⟨hBound,
        (Definitional.Project.Formula.satisfies_ordinalMultiplicationUpperBlock_iff
          𝕀 hZF.1 env candidate).mpr hCandidate⟩
  have hCandidatesSubset :
      ℳ.MemberSubset candidates dividendSuccessor := by
    intro candidate hCandidate
    exact (hCandidatesSemantic candidate).mp hCandidate |>.1
  have hCandidatesNonempty :
      ∃ candidate, ℳ.mem candidate candidates := by
    rcases ordinalMultiplication_existsUnique hZF
        𝕀 divisor hDividend with
      ⟨dividendBlock, hDividendBlock, _⟩
    rcases ordinalMultiplication_existsUnique hZF
        𝕀 divisor hDividendSuccessorOrdinal with
      ⟨successorProduct, hSuccessorProduct, _⟩
    have hDividendBlockSuccessor :
        ℳ.mem dividendBlock successorProduct :=
      ordinalMultiplication_isIncreasingOnOrdinals
        hZF 𝕀 hDivisor hDivisorNonempty
        dividend dividendSuccessor
        hDividend hDividendSuccessorOrdinal
        ((hDividendSuccessor dividend).mpr
          (Or.inr fun _ => Iff.rfl))
        dividendBlock successorProduct
        hDividendBlock hSuccessorProduct
    have hDividendLeBlock :=
      ordinalMultiplication_right_eq_or_mem
        hZF 𝕀 hDivisor hDivisorNonempty
        hDividend hDividendBlock
    have hDividendProduct :
        ℳ.mem dividend successorProduct := by
      rcases hDividendLeBlock with hEqual | hMember
      · simpa [hEqual] using hDividendBlockSuccessor
      · have hSuccessorProductOrdinal :=
          ordinalMultiplication_isOrdinal hZF 𝕀
            hDivisor hDividendSuccessorOrdinal hSuccessorProduct
        exact hSuccessorProductOrdinal.transitive
          dividendBlock hDividendBlockSuccessor dividend hMember
    exact
      ⟨dividend,
        (hCandidatesSemantic dividend).mpr
          ⟨(hDividendSuccessor dividend).mpr
              (Or.inr fun _ => Iff.rfl),
            dividendSuccessor, hDividendSuccessor,
            successorProduct, hSuccessorProduct,
            hDividendProduct⟩⟩
  rcases hDividendSuccessorOrdinal.wellOrder.least
      candidates hCandidatesSubset hCandidatesNonempty with
    ⟨quotient, hQuotientCandidate, hLeast⟩
  have hQuotientData :=
    (hCandidatesSemantic quotient).mp hQuotientCandidate
  rcases hQuotientData.2 with
    ⟨quotientSuccessor, hQuotientSuccessor,
      quotientSuccessorProduct,
      hQuotientSuccessorProduct,
      hDividendProduct⟩
  have hQuotientSuccessorOrdinal : ℳ.IsOrdinal quotientSuccessor :=
    Structure.IsOrdinalMultiplication.right_isOrdinal
      hQuotientSuccessorProduct
  rcases (ordinalMultiplication_mem_iff
      hZF 𝕀 hDivisor hQuotientSuccessorOrdinal
      hQuotientSuccessorProduct).mp hDividendProduct with
    ⟨index, hIndexSuccessor, block, hBlock,
      remainder, hRemainder, hDividendDecomposition⟩
  have hIndexEq : index = quotient := by
    rcases (hQuotientSuccessor index).mp hIndexSuccessor with
      hIndexQuotient | hSame
    · rcases KP.exists_successor (ZF.modelsKP hZF) index with
        ⟨indexSuccessor, hIndexSuccessorRelation⟩
      have hIndexOrdinal :=
        Structure.IsOrdinalMultiplication.right_isOrdinal hBlock
      have hIndexSuccessorOrdinal : ℳ.IsOrdinal indexSuccessor :=
        KP.successor_isOrdinal (ZF.modelsKP hZF)
          hIndexOrdinal hIndexSuccessorRelation
      rcases ordinalMultiplication_existsUnique hZF
          𝕀 divisor hIndexSuccessorOrdinal with
        ⟨indexSuccessorProduct, hIndexSuccessorProduct, _⟩
      have hDividendIndexSuccessor :
          ℳ.mem dividend indexSuccessorProduct :=
        (ordinalMultiplication_mem_iff
          hZF 𝕀 hDivisor hIndexSuccessorOrdinal
          hIndexSuccessorProduct).mpr
          ⟨index,
            (hIndexSuccessorRelation index).mpr
              (Or.inr fun _ => Iff.rfl),
            block, hBlock, remainder, hRemainder,
            hDividendDecomposition⟩
      have hIndexCandidate : ℳ.mem index candidates :=
        (hCandidatesSemantic index).mpr
          ⟨hDividendSuccessorOrdinal.transitive
              quotient hQuotientData.1 index hIndexQuotient,
            indexSuccessor, hIndexSuccessorRelation,
            indexSuccessorProduct, hIndexSuccessorProduct,
            hDividendIndexSuccessor⟩
      rcases hLeast index hIndexCandidate with
        hQuotientIndex | hQuotientIndex
      · have hEqual :=
          hZF.1.eq_of_same_members quotient index hQuotientIndex
        subst index
        exact False.elim <|
          hDividendSuccessorOrdinal.wellOrder.linear.irrefl
            quotient hQuotientData.1 hIndexQuotient
      · have hSelf :=
          hDividendSuccessorOrdinal.wellOrder.linear.trans
            quotient hQuotientData.1
            index
              ((hCandidatesSemantic index).mp hIndexCandidate).1
            quotient hQuotientData.1
            hQuotientIndex hIndexQuotient
        exact False.elim <|
          hDividendSuccessorOrdinal.wellOrder.linear.irrefl
            quotient hQuotientData.1 hSelf
    · exact hZF.1.eq_of_same_members index quotient hSame
  subst index
  have hQuotientOrdinal :=
    Structure.IsOrdinalMultiplication.right_isOrdinal hBlock
  refine
    ⟨quotient, remainder,
      ⟨hQuotientOrdinal, hRemainder,
        block, hBlock, hDividendDecomposition⟩,
      ?_⟩
  intro otherQuotient otherRemainder hOther
  rcases hOther with
    ⟨hOtherQuotient, hOtherRemainder,
      otherBlock, hOtherBlock, hOtherDecomposition⟩
  have hCoordinates :=
    ordinalMultiplication_block_coordinates_unique
      hZF 𝕀 hDivisor hDivisorNonempty
      hOtherQuotient hQuotientOrdinal
      hOtherBlock hBlock
      hOtherRemainder hRemainder
      hOtherDecomposition hDividendDecomposition
  exact hCoordinates

/-- 非零序数除数给出文献形式的唯一商和唯一余项。 -/
theorem ordinalDivision_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {dividend divisor : ℳ.Domain}
    (hDividend : ℳ.IsOrdinal dividend)
    (hDivisor : ℳ.IsOrdinal divisor)
    (hDivisorNonempty : ∃ member, ℳ.mem member divisor) :
    ∃ quotient,
      (∃ remainder,
        ℳ.IsOrdinalDivision 𝕀
            dividend divisor quotient remainder ∧
          ∀ otherRemainder,
            ℳ.IsOrdinalDivision 𝕀
                dividend divisor quotient otherRemainder →
              otherRemainder = remainder) ∧
      ∀ otherQuotient,
        (∃ otherRemainder,
          ℳ.IsOrdinalDivision 𝕀
            dividend divisor otherQuotient otherRemainder) →
          otherQuotient = quotient := by
  rcases ordinalDivision_existsUnique_pair
      hZF 𝕀 hDividend hDivisor hDivisorNonempty with
    ⟨quotient, remainder, hDivision, hUnique⟩
  refine ⟨quotient, ?_, ?_⟩
  · refine ⟨remainder, hDivision, ?_⟩
    intro otherRemainder hOther
    exact (hUnique quotient otherRemainder hOther).2
  · intro otherQuotient hOther
    rcases hOther with ⟨otherRemainder, hOther⟩
    exact (hUnique otherQuotient otherRemainder hOther).1

end ZF

end SetTheory
end YesMetaZFC
