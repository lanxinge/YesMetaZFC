import YesMetaZFC.SetTheory.Card.Properties.Basic
import YesMetaZFC.SetTheory.Card.Cofinality.Boundedness
import YesMetaZFC.SetTheory.Card.OrdinalCardinality
/-!
# 奇异基数的族并刻画
本层形式化定理 3.10：一个具有共尾度见证的无限基数是奇异的，当且仅当它能写成少于
自身个、且每个成员基数都严格小于自身的集合族之并。集合族、值域、并集与各成员的
基数见证均保留为模型内部对象。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/--
`family` 是长度严格小于 `κ` 的基数指标族，其并为 `κ`，且每个成员的基数严格小于
`κ`。
-/
def IsSmallCardinalityUnionFamily {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (family length κ : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 length ∧
    ℳ.mem length κ ∧
      ℳ.IsSequenceOfLength 𝕀 family length ∧
        ∃ range,
          ℳ.IsRangeOf 𝕀 range family ∧
            ℳ.IsUnionOf κ range ∧
              ∀ index, ℳ.mem index length →
                ∀ set, ℳ.PairMember 𝕀 index set family →
                  ∃ μ,
                    ℳ.IsCardinalOf 𝕀 μ set ∧
                      ℳ.mem μ κ
namespace IsSingularCardinal
/--
定理 3.10：具有共尾度见证的基数是奇异的，当且仅当它是一个较小基数指标族的并，
且族中每个集合的基数都严格小于它。
-/
theorem iff_exists_smallCardinalityUnionFamily
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {κ cf : ℳ.Domain} (hκ : ℳ.IsCardinal 𝕀 κ) (hCofinality : ℳ.IsCofinality 𝕀 cf κ) :
    ℳ.IsSingularCardinal 𝕀 κ ↔
      ∃ length family,
        ℳ.IsSmallCardinalityUnionFamily
          𝕀 family length κ := by
  constructor
  · intro hSingular
    rcases hSingular.2 with
      ⟨otherCf, hOtherCfκ, hOtherCofinality⟩
    have hCfEq : cf = otherCf := by
      exact hCofinality.eq hOtherCofinality
    have hCfκ : ℳ.mem cf κ := by
      simpa [hCfEq] using hOtherCfκ
    rcases hCofinality.hasCofinalSequence with
      ⟨family, hFamily⟩
    rcases hFamily.isLimit.2.2 with
      ⟨range, hRange, hUnion⟩
    refine ⟨cf, family, hCofinality.isCardinal,
      hCfκ, hFamily.isIncreasing.1.1,
      range, hRange, hUnion, ?_⟩
    intro index hIndex set hIndexSet
    have hSetκ :
        ℳ.mem set κ :=
      hFamily.value_mem hIndex hIndexSet
    rcases ZF.ordinalCardinal_existsUnique
        hZF 𝕀 (hκ.1.mem hSetκ) with
      ⟨μ, hμ, _⟩
    refine ⟨μ, hμ, ?_⟩
    have hμEquinumerous := hμ.2
    rcases hμEquinumerous with
      ⟨μToSet, hμToSet⟩
    rcases ZF.exists_inclusionInjection hZF 𝕀 (hκ.1.transitive set hSetκ) with
      ⟨setToκ, hSetToκ⟩
    rcases ZF.exists_compositionInjection hZF 𝕀
        hμToSet.1 hSetToκ with
      ⟨μToκ, hμToκ⟩
    rcases hμ.1.eq_or_mem_of_cardinalLessOrEqual
        hZF 𝕀 hκ ⟨μToκ, hμToκ⟩ with
      hEq | hμκ
    · subst μ
      exact False.elim <|
        hκ.2 set hSetκ <| (show ℳ.Equinumerous 𝕀 κ set from
            ⟨μToSet, hμToSet⟩).symm hZF 𝕀
    · exact hμκ
  · rintro ⟨length, family, _hLengthCardinal,
      hLengthκ, hFamily, range, hRange, hUnion, hSmall⟩
    rcases hCofinality.hasCofinalSequence with
      ⟨cofinalSequence, hCofinalSequence⟩
    have hCfLeκ :
        ℳ.CardinalLessOrEqual 𝕀 cf κ :=
      ⟨cofinalSequence,
        hCofinalSequence.isSetInjectionFromTo hZF 𝕀⟩
    rcases hCofinality.isCardinal.eq_or_mem_of_cardinalLessOrEqual
        hZF 𝕀 hκ hCfLeκ with
      hCfEq | hCfκ
    · have hLengthCf :
          ℳ.mem length cf := by
        simpa [hCfEq] using hLengthκ
      have hEachBounded :
          ∀ index, ℳ.mem index length →
            ∀ set, ℳ.PairMember 𝕀 index set family →
              ℳ.IsBoundedSubsetOfOrdinal set κ := by
        intro index hIndex set hIndexSet
        rcases hSmall index hIndex set hIndexSet with
          ⟨μ, hμ, hμκ⟩
        have hμCf :
            ℳ.mem μ cf := by
          simpa [hCfEq] using hμκ
        apply hCofinality.bounded_of_cardinality_mem
          hZF 𝕀
        · intro value hValue
          exact (hUnion value).mpr
            ⟨set, (hRange set).mpr
              ⟨index, hIndexSet⟩, hValue⟩
        · exact hμ
        · exact hμCf
      have hκBounded :=
        hCofinality.familyUnion_bounded_of_length_mem
          hZF 𝕀 hLengthCf hFamily hRange hUnion hEachBounded
      exact False.elim <|
        Structure.IsBoundedSubsetOfOrdinal.not_self
          hCofinalSequence.isLimitOrdinal hκBounded
    · exact ⟨hκ, cf, hCfκ, hCofinality⟩
end IsSingularCardinal
end Structure
end SetTheory
end YesMetaZFC
