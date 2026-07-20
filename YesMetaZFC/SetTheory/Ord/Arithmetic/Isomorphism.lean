import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison

/-!
# 序数算术的序同构表示

本文件形式化序数加法与乘法的外延序型解释。严格序同构显式给出正反映射及关系等价；
加法源端使用不交并，乘法源端使用第二坐标优先的右字典序积。
-/

namespace YesMetaZFC
namespace SetTheory

universe u v

/-- 两个严格关系之间的显式序同构。 -/
structure StrictOrderIsomorphism
    {Source : Type u} {Target : Type v}
    (sourceRelation : Source → Source → Prop)
    (targetRelation : Target → Target → Prop) where
  toFun : Source → Target
  invFun : Target → Source
  left_inv : ∀ source, invFun (toFun source) = source
  right_inv : ∀ target, toFun (invFun target) = target
  map_rel_iff :
    ∀ first second,
      sourceRelation first second ↔
        targetRelation (toFun first) (toFun second)

namespace Structure

/-- 序数的成员所成的载体类型。 -/
abbrev OrdinalSegment (ℳ : Structure.{u}) (α : ℳ.Domain) :=
  { value : ℳ.Domain // ℳ.mem value α }

/-- 序数成员类型上的严格隶属序。 -/
def OrdinalMembershipRelation (ℳ : Structure.{u})
    {α : ℳ.Domain}
    (first second : ℳ.OrdinalSegment α) : Prop :=
  ℳ.mem first.1 second.1

/-- 两个序数成员序的不交序和关系。 -/
def OrdinalSumRelation (ℳ : Structure.{u})
    (left right : ℳ.Domain)
    (first second :
      Sum (ℳ.OrdinalSegment left) (ℳ.OrdinalSegment right)) : Prop :=
  match first, second with
  | .inl first, .inl second => ℳ.mem first.1 second.1
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr first, .inr second => ℳ.mem first.1 second.1

/-- 两个序数成员序的第二坐标优先右字典序。 -/
def OrdinalRightLexicographicRelation (ℳ : Structure.{u})
    (left right : ℳ.Domain)
    (first second :
      ℳ.OrdinalSegment left × ℳ.OrdinalSegment right) : Prop :=
  ℳ.mem first.2.1 second.2.1 ∨
    (first.2.1 = second.2.1 ∧
      ℳ.mem first.1.1 second.1.1)

end Structure

namespace ZF

/-- `left + right` 与 `left`、`right` 的不交序和严格序同构。 -/
noncomputable def ordinalAddition_strictOrderIsomorphism
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hRight : ℳ.IsOrdinal right)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum left right) :
    StrictOrderIsomorphism
      (ℳ.OrdinalSumRelation left right)
      (ℳ.OrdinalMembershipRelation
        (α := sum)) := by
  classical
  let tailExistence :
      ∀ index : ℳ.OrdinalSegment right,
        ∃ value,
          ℳ.IsOrdinalAddition 𝕀 value left index.1 ∧
            ∀ other,
              ℳ.IsOrdinalAddition 𝕀 other left index.1 →
                other = value :=
    fun index =>
      ordinalAddition_existsUnique hZF 𝕀 left
        (hRight.mem index.2)
  let tailValue : ℳ.OrdinalSegment right → ℳ.Domain :=
    fun index => Classical.choose (tailExistence index)
  have hTailValue (index : ℳ.OrdinalSegment right) :
      ℳ.IsOrdinalAddition 𝕀
        (tailValue index) left index.1 :=
    (Classical.choose_spec (tailExistence index)).1
  let forward :
      Sum (ℳ.OrdinalSegment left) (ℳ.OrdinalSegment right) →
        ℳ.OrdinalSegment sum :=
    fun point =>
      match point with
      | .inl member =>
          ⟨member.1,
            (ordinalAddition_mem_iff
              hZF 𝕀 hRight hSum).mpr
              (Or.inl member.2)⟩
      | .inr index =>
          ⟨tailValue index,
            (ordinalAddition_mem_iff
              hZF 𝕀 hRight hSum).mpr
              (Or.inr ⟨index.1, index.2, hTailValue index⟩)⟩
  have hForwardSurjective :
      ∀ target : ℳ.OrdinalSegment sum,
        ∃ source, forward source = target := by
    intro target
    rcases (ordinalAddition_mem_iff
        hZF 𝕀 hRight hSum).mp target.2 with
      hTargetLeft | ⟨index, hIndex, hIndexValue⟩
    · refine ⟨Sum.inl ⟨target.1, hTargetLeft⟩, ?_⟩
      apply Subtype.ext
      rfl
    · let sourceIndex : ℳ.OrdinalSegment right := ⟨index, hIndex⟩
      have hTargetEq :
          target.1 = tailValue sourceIndex :=
        (Classical.choose_spec (tailExistence sourceIndex)).2
          target.1 hIndexValue
      refine ⟨Sum.inr sourceIndex, ?_⟩
      apply Subtype.ext
      exact hTargetEq.symm
  have hForwardInjective :
      ∀ first second, forward first = forward second →
        first = second := by
    intro first second hEqual
    rcases first with first | first <;>
      rcases second with second | second
    · have hValueEq : first.1 = second.1 := by
        simpa [forward] using congrArg Subtype.val hEqual
      exact congrArg Sum.inl (Subtype.ext hValueEq)
    · have hValueEq : first.1 = tailValue second := by
        simpa [forward] using congrArg Subtype.val hEqual
      have hSelf : ℳ.mem (tailValue second) (tailValue second) := by
        simpa [hValueEq] using
          ordinalAddition_left_member_mem_value
            hZF 𝕀 hLeft
            (hRight.mem second.2) first.2 (hTailValue second)
      have hTailOrdinal :=
        ordinalAddition_isOrdinal hZF 𝕀
          hLeft (hRight.mem second.2) (hTailValue second)
      exact False.elim <|
        hTailOrdinal.wellOrder.linear.irrefl
          (tailValue second) hSelf hSelf
    · have hValueEq : tailValue first = second.1 := by
        simpa [forward] using congrArg Subtype.val hEqual
      have hSelf : ℳ.mem (tailValue first) (tailValue first) := by
        simpa [hValueEq] using
          ordinalAddition_left_member_mem_value
            hZF 𝕀 hLeft
            (hRight.mem first.2) second.2 (hTailValue first)
      have hTailOrdinal :=
        ordinalAddition_isOrdinal hZF 𝕀
          hLeft (hRight.mem first.2) (hTailValue first)
      exact False.elim <|
        hTailOrdinal.wellOrder.linear.irrefl
          (tailValue first) hSelf hSelf
    · have hValueEq : tailValue first = tailValue second := by
        simpa [forward] using congrArg Subtype.val hEqual
      have hSecondAtFirst :
          ℳ.IsOrdinalAddition 𝕀
            (tailValue first) left second.1 := by
        simpa [hValueEq] using hTailValue second
      have hIndexEq : first.1 = second.1 :=
        ordinalAddition_right_injective
          hZF 𝕀 hLeft
          (hRight.mem first.2) (hRight.mem second.2)
          (hTailValue first) hSecondAtFirst
      exact congrArg Sum.inr (Subtype.ext hIndexEq)
  have hForwardRelation :
      ∀ first second,
        ℳ.OrdinalSumRelation left right first second ↔
          ℳ.OrdinalMembershipRelation
            (forward first) (forward second) := by
    intro first second
    rcases first with first | first <;>
      rcases second with second | second
    · rfl
    · change True ↔ ℳ.mem first.1 (tailValue second)
      constructor
      · intro _
        exact ordinalAddition_left_member_mem_value
          hZF 𝕀 hLeft
          (hRight.mem second.2) first.2 (hTailValue second)
      · intro _
        trivial
    · change False ↔ ℳ.mem (tailValue first) second.1
      constructor
      · intro hFalse
        exact False.elim hFalse
      · exact ordinalAddition_value_not_mem_left_member
          hZF 𝕀 hLeft
          (hRight.mem first.2) second.2 (hTailValue first)
    · change ℳ.mem first.1 second.1 ↔
        ℳ.mem (tailValue first) (tailValue second)
      exact (ordinalAddition_values_mem_iff
        hZF 𝕀 hLeft
        (hRight.mem first.2) (hRight.mem second.2)
        (hTailValue first) (hTailValue second)).symm
  let inverse : ℳ.OrdinalSegment sum →
      Sum (ℳ.OrdinalSegment left) (ℳ.OrdinalSegment right) :=
    fun target => Classical.choose (hForwardSurjective target)
  refine {
    toFun := forward
    invFun := inverse
    left_inv := ?_
    right_inv := ?_
    map_rel_iff := hForwardRelation
  }
  · intro source
    apply hForwardInjective
    exact Classical.choose_spec (hForwardSurjective (forward source))
  · intro target
    exact Classical.choose_spec (hForwardSurjective target)

/-- `left · right` 与 `left × right` 的右字典序严格序同构。 -/
noncomputable def ordinalMultiplication_strictOrderIsomorphism
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hRight : ℳ.IsOrdinal right)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left right) :
    StrictOrderIsomorphism
      (ℳ.OrdinalRightLexicographicRelation left right)
      (ℳ.OrdinalMembershipRelation
        (α := product)) := by
  classical
  by_cases hLeftEmpty : ∀ member, ¬ ℳ.mem member left
  · have hProductEmpty :
        ∀ member, ¬ ℳ.mem member product :=
      ordinalMultiplication_empty_left
        hZF 𝕀 hLeftEmpty
        right hRight product hProduct
    let sourceFalse :
        ℳ.OrdinalSegment left × ℳ.OrdinalSegment right → False :=
      fun source => hLeftEmpty source.1.1 source.1.2
    let targetFalse : ℳ.OrdinalSegment product → False :=
      fun target => hProductEmpty target.1 target.2
    exact {
      toFun := fun source => False.elim (sourceFalse source)
      invFun := fun target => False.elim (targetFalse target)
      left_inv := fun source => False.elim (sourceFalse source)
      right_inv := fun target => False.elim (targetFalse target)
      map_rel_iff := fun first _ => False.elim (sourceFalse first)
    }
  · have hLeftNonempty : ∃ member, ℳ.mem member left := by
      apply Classical.byContradiction
      intro hNoMember
      apply hLeftEmpty
      intro member hMember
      exact hNoMember ⟨member, hMember⟩
    let blockExistence :
        ∀ index : ℳ.OrdinalSegment right,
          ∃ block,
            ℳ.IsOrdinalMultiplication 𝕀
                block left index.1 ∧
              ∀ other,
                ℳ.IsOrdinalMultiplication 𝕀
                    other left index.1 →
                  other = block :=
      fun index =>
        ordinalMultiplication_existsUnique
          hZF 𝕀 left (hRight.mem index.2)
    let blockValue : ℳ.OrdinalSegment right → ℳ.Domain :=
      fun index => Classical.choose (blockExistence index)
    have hBlockValue (index : ℳ.OrdinalSegment right) :
        ℳ.IsOrdinalMultiplication 𝕀
          (blockValue index) left index.1 :=
      (Classical.choose_spec (blockExistence index)).1
    let pointExistence :
        ∀ point : ℳ.OrdinalSegment left × ℳ.OrdinalSegment right,
          ∃ value,
            ℳ.IsOrdinalAddition 𝕀
                value (blockValue point.2) point.1.1 ∧
              ∀ other,
                ℳ.IsOrdinalAddition 𝕀
                    other (blockValue point.2) point.1.1 →
                  other = value :=
      fun point =>
        ordinalAddition_existsUnique hZF 𝕀
          (blockValue point.2) (hLeft.mem point.1.2)
    let pointValue :
        ℳ.OrdinalSegment left × ℳ.OrdinalSegment right → ℳ.Domain :=
      fun point => Classical.choose (pointExistence point)
    have hPointValue
        (point : ℳ.OrdinalSegment left × ℳ.OrdinalSegment right) :
        ℳ.IsOrdinalAddition 𝕀
          (pointValue point) (blockValue point.2) point.1.1 :=
      (Classical.choose_spec (pointExistence point)).1
    let forward :
        ℳ.OrdinalSegment left × ℳ.OrdinalSegment right →
          ℳ.OrdinalSegment product :=
      fun point =>
        ⟨pointValue point,
          (ordinalMultiplication_mem_iff
            hZF 𝕀 hLeft hRight hProduct).mpr
            ⟨point.2.1, point.2.2,
              blockValue point.2, hBlockValue point.2,
              point.1.1, point.1.2, hPointValue point⟩⟩
    have hForwardSurjective :
        ∀ target : ℳ.OrdinalSegment product,
          ∃ source, forward source = target := by
      intro target
      rcases (ordinalMultiplication_mem_iff
          hZF 𝕀 hLeft hRight hProduct).mp target.2 with
        ⟨index, hIndex, block, hBlock,
          remainder, hRemainder, hTargetValue⟩
      let source :
          ℳ.OrdinalSegment left × ℳ.OrdinalSegment right :=
        (⟨remainder, hRemainder⟩, ⟨index, hIndex⟩)
      have hBlockEq :
          block = blockValue source.2 :=
        (Classical.choose_spec (blockExistence source.2)).2
          block hBlock
      have hTargetAtSelected :
          ℳ.IsOrdinalAddition 𝕀
            target.1 (blockValue source.2) source.1.1 := by
        simpa [source, hBlockEq] using hTargetValue
      have hTargetEq :
          target.1 = pointValue source :=
        (Classical.choose_spec (pointExistence source)).2
          target.1 hTargetAtSelected
      refine ⟨source, ?_⟩
      apply Subtype.ext
      exact hTargetEq.symm
    have hForwardInjective :
        ∀ first second, forward first = forward second →
          first = second := by
      intro first second hEqual
      have hValueEq : pointValue first = pointValue second := by
        simpa [forward] using congrArg Subtype.val hEqual
      have hSecondAtFirst :
          ℳ.IsOrdinalAddition 𝕀
            (pointValue first) (blockValue second.2) second.1.1 := by
        simpa [hValueEq] using hPointValue second
      have hCoordinates :=
        ordinalMultiplication_block_coordinates_unique
          hZF 𝕀 hLeft hLeftNonempty
          (hRight.mem first.2.2) (hRight.mem second.2.2)
          (hBlockValue first.2) (hBlockValue second.2)
          first.1.2 second.1.2
          (hPointValue first) hSecondAtFirst
      apply Prod.ext
      · exact Subtype.ext hCoordinates.2
      · exact Subtype.ext hCoordinates.1
    have hForwardRelation :
        ∀ first second,
          ℳ.OrdinalRightLexicographicRelation left right first second ↔
            ℳ.OrdinalMembershipRelation
              (forward first) (forward second) := by
      intro first second
      change
        (ℳ.mem first.2.1 second.2.1 ∨
          (first.2.1 = second.2.1 ∧
            ℳ.mem first.1.1 second.1.1)) ↔
          ℳ.mem (pointValue first) (pointValue second)
      exact (ordinalMultiplication_block_values_mem_iff
        hZF 𝕀 hLeft hLeftNonempty
        (hRight.mem first.2.2) (hRight.mem second.2.2)
        (hBlockValue first.2) (hBlockValue second.2)
        first.1.2 second.1.2
        (hPointValue first) (hPointValue second)).symm
    let inverse : ℳ.OrdinalSegment product →
        ℳ.OrdinalSegment left × ℳ.OrdinalSegment right :=
      fun target => Classical.choose (hForwardSurjective target)
    refine {
      toFun := forward
      invFun := inverse
      left_inv := ?_
      right_inv := ?_
      map_rel_iff := hForwardRelation
    }
    · intro source
      apply hForwardInjective
      exact Classical.choose_spec (hForwardSurjective (forward source))
    · intro target
      exact Classical.choose_spec (hForwardSurjective target)

end ZF

end SetTheory
end YesMetaZFC
