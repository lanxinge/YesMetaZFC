import YesMetaZFC.SetTheory.Card.InfiniteBound

/-! # 无限基数运算界在 ω 上的实例 -/
namespace YesMetaZFC.SetTheory.ZF
universe u
variable {M : Structure.{u}} {𝒞 : Definitional.Project.OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem countable_product_l (hZF : M.Models ZF) {ω X Y W} (hω : M.IsOmega ω)
    (hX : M.CardinalLessOrEqual I X ω) (hY : M.CardinalLessOrEqual I Y ω)
    (hW : M.IsCartesianProduct I W X Y) : M.CardinalLessOrEqual I W ω := by
  obtain ⟨F, hF⟩ := exists_identityBijection hZF I ω
  exact infinite_product_l I hZF hω ⟨omega_cardinal_l I hZF hω, F, hF.1⟩ hX hY hW

theorem countable_union_two_l (hZF : M.Models ZF) {ω X Y U} (hω : M.IsOmega ω)
    (hX : M.CardinalLessOrEqual I X ω) (hY : M.CardinalLessOrEqual I Y ω)
    (hU : M.IsUnionOfTwo U X Y) : M.CardinalLessOrEqual I U ω := by
  obtain ⟨F, hF⟩ := exists_identityBijection hZF I ω
  exact infinite_union_two_l I hZF hω ⟨omega_cardinal_l I hZF hω, F, hF.1⟩ hX hY hU

end YesMetaZFC.SetTheory.ZF
