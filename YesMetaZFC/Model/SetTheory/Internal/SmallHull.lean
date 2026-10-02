import YesMetaZFC.Model.SetTheory.Internal.ElementaryHull
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # κ 小种子的实际 Σ₁ 隶属子结构

构造完整内部初等壳后忘掉多余结构码，保留凝聚与 Σ₁ 绝对性所需的接口。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem s1_hull_l (hZFC : M.Models ZFC) {ω κ U A} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ) (hn : ∃ x, M.mem x U)
    (hA : M.MemberSubset A U) (ha : M.CardinalLessOrEqual I A κ) :
    ∃ X, S1_sub_d X U ∧ M.MemberSubset A X ∧ M.CardinalLessOrEqual I X κ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨c, R, hm, hr⟩ := smdl_membership_l I hZF hn
  obtain ⟨X, d, S, hs, hAX, hx, he⟩ := selem_hull_bound_l I hZFC hω hκ hm hA ha
  exact ⟨X, selem_sigma1_sub_l I hZF hω ⟨hm, hr⟩ hs he, hAX, hx⟩

end YesMetaZFC.SetTheory.Internal
