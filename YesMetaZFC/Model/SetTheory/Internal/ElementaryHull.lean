import YesMetaZFC.Model.SetTheory.Internal.Elementary
import YesMetaZFC.Model.SetTheory.Internal.Skolem

/-! # 任意内部 κ 小种子的实际初等子模型

司寇伦选择、最小闭包、有限支撑和 Tarski–Vaught 已全部实现。入口直接返回
地模型内的载体、结构码及全内部语法的初等证书，不再要求调用者补交闭性或初等性。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem selem_hull_bound_l (hZFC : M.Models ZFC) {ω κ c X R A} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ)
    (hM : Smdl_d I c X R) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A κ) :
    ∃ N d S, Ssub_d I c d X R N S ∧ M.MemberSubset A N ∧ M.CardinalLessOrEqual I N κ ∧ Selem_d I ω c d := by
  obtain ⟨u, C, S, T, D, K, N, hK, hN, hn, hu, hc⟩ := ssk_hull_bound_l I hZFC hω hκ hM hA ha
  obtain ⟨d, Q, hQ, he⟩ := selem_of_skolem_l I (ZFC.models_zf_l hZFC) hω hM hK.codes hN.2.1 hu hc
  exact ⟨N, d, Q, hQ, hN.1, hn, he⟩

/-- 可数内部初等子模型是 κ=ω 的直接实例。 -/
theorem selem_hull_l (hZFC : M.Models ZFC) {ω c X R A} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ N d S, Ssub_d I c d X R N S ∧ M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧ Selem_d I ω c d := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨F, hF⟩ := ZF.exists_identityBijection hZF I ω
  exact selem_hull_bound_l I hZFC hω ⟨ZF.omega_cardinal_l I hZF hω, F, hF.1⟩ hM hA ha

end YesMetaZFC.SetTheory.Internal
