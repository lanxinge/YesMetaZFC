import YesMetaZFC.SetTheory.ProductConstruction

/-!
# 带标签不交并

固定两个不同标签，把左右集合分别映到 `tag × set` 的有序对编码行，再取二元并。
坐标编码的单射性保证两行不交。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `union` 是由两个不同标签编码出的不交并。 -/
def IsTaggedUnion {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (union leftTag rightTag left right : ℳ.Domain) : Prop :=
  ∃ leftCopy rightCopy,
    (∀ pair, ℳ.mem pair leftCopy ↔
      ∃ value, ℳ.mem value left ∧
        𝕀.Codes pair leftTag value) ∧
    (∀ pair, ℳ.mem pair rightCopy ↔
      ∃ value, ℳ.mem value right ∧
        𝕀.Codes pair rightTag value) ∧
    ℳ.IsDisjoint leftCopy rightCopy ∧
    ℳ.IsUnionOfTwo union leftCopy rightCopy

end Structure

namespace ZF

/-- 给定不同标签时，任意两个集合都有相应的带标签不交并。 -/
theorem exists_taggedUnion
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {leftTag rightTag : ℳ.Domain}
    (hTags : leftTag ≠ rightTag)
    (left right : ℳ.Domain) :
    ∃ union, ℳ.IsTaggedUnion 𝕀
      union leftTag rightTag left right := by
  rcases exists_cartesianRow hZF 𝕀 leftTag left with
    ⟨leftCopy, hLeftCopy⟩
  rcases exists_cartesianRow hZF 𝕀 rightTag right with
    ⟨rightCopy, hRightCopy⟩
  rcases KP.exists_unionOfTwo (modelsKP hZF) leftCopy rightCopy with
    ⟨union, hUnion⟩
  refine ⟨union, leftCopy, rightCopy,
    hLeftCopy, hRightCopy, ?_, hUnion⟩
  intro pair hBoth
  rcases (hLeftCopy pair).mp hBoth.1 with
    ⟨leftValue, _, hLeftCode⟩
  rcases (hRightCopy pair).mp hBoth.2 with
    ⟨rightValue, _, hRightCode⟩
  exact hTags <| (𝕀.injective hLeftCode hRightCode).1

end ZF

end SetTheory
end YesMetaZFC
