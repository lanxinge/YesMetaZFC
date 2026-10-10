import YesMetaZFC.SetTheory.InnerModel.Condensation.Size
import YesMetaZFC.SetTheory.Collapse.Sigma1Bound
import YesMetaZFC.SetTheory.InnerModel.Jensen.Separation

/-! # GCH 的两个 Jensen 层界

唯一 Σ₁ 层值经小壳坍塌保持基数界；κ 子集则由 J 凝聚进入高度小于 κ⁺ 的层。
所有大小比较都由模型内部的集合编码单射见证。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

/-- |a|≤κ 且 κ 无限时，|Jₐ|≤κ；层值使用真实的 Σ₁ 递归图。 -/
theorem jh_cardinal_bound_l (hZFC : M.Models ZFC) {ω κ a U : M.Domain} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ)
    (ha : M.IsOrdinal a) (hc : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) a κ)
    (hU : Jh_value_d a U) : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) U κ :=
  s1_value_bound_l hZFC hω hκ ha.transitive hc (rc_value_s jh_op_s) (jh_env_l a) hU
    (fun _ h => jh_value_unique_l (ZF.models_kpi_l (ZFC.models_zf_l hZFC)) hU h)

/-- 每个构造性的 κ 子集属于 J_{κ⁺}；κ⁺ 是背景模型的实际 Hartogs 数。 -/
theorem jh_subset_bound_l (hZFC : M.Models ZFC) {ω κ θ V x : M.Domain} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ)
    (hθ : M.IsHartogsNumber (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ κ)
    (hV : Jh_value_d θ V) (hx : L_d x) (hxκ : M.MemberSubset x κ) : M.mem x V := by
  let hZF := ZFC.models_zf_l hZFC
  let hKP := ZF.modelsKP hZF
  let hM := ZF.models_kpi_l hZF
  let I := kp_pair_l hKP
  obtain ⟨a, U, ha, hU⟩ := l_finite_bound_l hM (n := 2) (Fin.cases κ (fun _ => x))
    (Fin.cases (l_ordinal_l hM hκ.1.1) (fun _ => hx))
  obtain ⟨A, hA⟩ := KP.exists_insert hKP κ x
  have hAU : M.MemberSubset A U := fun z hz => ((hA z).mp hz).elim
    (jh_value_transitive_l hM ha.2 κ (hU 0) z) (fun he => he ▸ hU 1)
  obtain ⟨G, hG⟩ := ZF.exists_identityBijection hZF I κ
  have hc := ZF.infinite_insert_l I hZF hω hκ ⟨G, hG.1⟩ hA
  obtain ⟨X, hs, hAX, hXκ⟩ := Internal.s1_hull_l I hZFC hω hκ ⟨x, hU 1⟩ hAU hc
  obtain ⟨b, B, F, hb, hf, hbx, fixed⟩ := jc_bounded_condensation_l hM ha.1 ha.2 hs
  obtain ⟨H, hH⟩ := hbx
  obtain ⟨K, hK⟩ := hXκ
  have hbθ := (hθ.2 b hb.1).mpr (ZF.exists_compositionInjection hZF I hH hK)
  have hxx := fixed κ hκ.1.1.transitive (fun z hz => hAX z ((hA z).mpr (Or.inl hz)))
    x (hAX x ((hA x).mpr (Or.inr rfl))) hxκ
  exact jh_value_transitive_l hM hV B (jh_value_mem_l hM hbθ hb.2 hV) x (hf.function.bound_l hxx).2

end YesMetaZFC.SetTheory.InnerModel
