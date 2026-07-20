import YesMetaZFC.SetTheory.Card.Aleph.Basic
import YesMetaZFC.SetTheory.Card.CantorBernstein

/-!
# Aleph 数的存在性基础

本层收集 Aleph 枚举所需的基数存在性与上确界闭包定理。Hartogs 构造及基数后继存在性
将在同一层继续建立。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure.IsUnionOf

/--
基数组成的集合族之并仍是基数。

若某个更小序数 `β` 与并集等势，则把逆向双射限制到包含 `β` 的成员基数 `κ`，得到
`κ` 到 `β` 的单射；另一方面 `β ∈ κ` 给出恒等包含单射。Cantor--Bernstein 随即推出
`β` 与 `κ` 等势，违背 `κ` 的初始序数性。
-/
theorem isCardinal_of_members
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {supremum family : ℳ.Domain}
    (hUnion : ℳ.IsUnionOf supremum family)
    (hCardinals :
      ∀ κ, ℳ.mem κ family → ℳ.IsCardinal 𝕀 κ) :
    ℳ.IsCardinal 𝕀 supremum := by
  have hSupremumOrdinal : ℳ.IsOrdinal supremum :=
    Structure.IsOrdinal.of_union (ZF.modelsKP hZF) hUnion
      fun κ hκ => (hCardinals κ hκ).1
  refine ⟨hSupremumOrdinal, ?_⟩
  intro β hβSupremum hβEquinumerous
  rcases (hUnion β).mp hβSupremum with
    ⟨κ, hκFamily, hβκ⟩
  have hκCardinal := hCardinals κ hκFamily
  have hκSubsetSupremum : ℳ.MemberSubset κ supremum := by
    intro value hValue
    exact (hUnion value).mpr ⟨κ, hκFamily, hValue⟩
  rcases hβEquinumerous.symm hZF 𝕀 with
    ⟨supremumToβ, hSupremumToβ⟩
  rcases ZF.exists_restriction hZF 𝕀 supremumToβ κ with
    ⟨κToβ, hκToβRestriction⟩
  have hκToβInjection :
      ℳ.IsSetInjectionFromTo 𝕀 κToβ κ β := by
    refine ⟨hκToβRestriction.isSetFunctionFromTo
      hSupremumToβ.1.1 hκSubsetSupremum, ?_⟩
    intro first second output hFirst hSecond
    exact hSupremumToβ.1.2 first second output
      ((hκToβRestriction.2 first output).mp hFirst).2
      ((hκToβRestriction.2 second output).mp hSecond).2
  rcases ZF.exists_identityBijection hZF 𝕀 β with
    ⟨identity, hIdentity⟩
  have hβSubsetκ : ℳ.MemberSubset β κ :=
    hκCardinal.1.transitive β hβκ
  have hβToκInjection :
      ℳ.IsSetInjectionFromTo 𝕀 identity β κ := by
    refine ⟨⟨hIdentity.1.1.1, hIdentity.1.1.2.1, ?_⟩,
      hIdentity.1.2⟩
    intro input hInput
    rcases hIdentity.1.1.2.2 input hInput with
      ⟨output, hOutput, hPair⟩
    exact ⟨output, hβSubsetκ output hOutput, hPair⟩
  exact hκCardinal.2 β hβκ <|
    ZF.equinumerous_of_injections hZF 𝕀
      hβToκInjection hκToβInjection

end Structure.IsUnionOf

end SetTheory
end YesMetaZFC
