import YesMetaZFC.SetTheory.Card.Properties.Basic
import YesMetaZFC.SetTheory.Card.Cofinality.Composition
import YesMetaZFC.SetTheory.Card.Cofinality.LimitLength
/-!
# 共尾度的正则性
本层证明引理 3.8：任意极限序数的共尾度都是正则基数。证明先排除最小共尾序列具有
零长度或后继长度，再用恒等函数图构造共尾度上的共尾序列。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure.IsCofinality
/-- 引理 3.8：任意极限序数的共尾度都是正则基数。 -/
theorem isRegularCardinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {α κ : ℳ.Domain} (hκ : ℳ.IsCofinality 𝕀 κ α) :
    ℳ.IsRegularCardinal 𝕀 κ := by
  change ℳ.IsCofinality 𝕀 κ κ
  rcases hκ.hasCofinalSequence with
    ⟨outer, hOuter⟩
  have hκLimit :
      ℳ.IsLimitOrdinal κ :=
    hOuter.length_isLimitOrdinal hZF
  refine ⟨hκ.isCardinal,
    hκLimit.hasCofinalOrdinalSequence_self hZF 𝕀, ?_⟩
  intro length hLength
  rcases hLength with ⟨inner, hInner⟩
  rcases hOuter.exists_composition hZF 𝕀 hInner with
    ⟨composition, hComposition⟩
  exact hκ.minimal ⟨composition, hComposition⟩
end Structure.IsCofinality
end SetTheory
end YesMetaZFC
