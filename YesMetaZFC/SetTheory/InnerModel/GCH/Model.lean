import YesMetaZFC.SetTheory.InnerModel.GCH.Bounds
import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Choice
import YesMetaZFC.SetTheory.GeneralizedContinuum

/-! # 任意 ZF 模型中的 Jensen 内模型满足 GCH

在 ZF+V=L 内由 Jensen 序导出选择；凝聚给出 P(κ)⊆J_{κ⁺}，Σ₁ 层值的
基数界给出 |J_{κ⁺}|≤κ⁺。Cantor 与内部序型定理将此上界提升为实际双射。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_power_bound_l (hZF : M.Models ZF) (hVL : M.SatisfiesSentence Axioms.vl_axiom)
    {ω κ P θ : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsInfiniteCardinal (kp_pair_l (ZF.modelsKP hZF)) ω κ)
    (hP : M.IsPowerSetOf P κ) (hθ : M.IsHartogsNumber (kp_pair_l (ZF.modelsKP hZF)) θ κ) :
    M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) P θ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let hZFC := js_zfc_l hZF hVL
  let hM := ZF.models_kpi_l hZF
  have all : ∀ x : M.Domain, L_d x := (vl_sat_l (ZF.modelsKP hZF) (fun _ => κ)).mp
    ((Structure.satisfiesSentence_iff M Axioms.vl_axiom).mp hVL (fun _ => κ))
  obtain ⟨U, hU⟩ := jh_value_exists_l hM θ
  have hPU : M.MemberSubset P U := fun x hx => jh_subset_bound_l hZFC hω hκ hθ hU (all x) ((hP x).mp hx)
  obtain ⟨F, hF⟩ := ZF.exists_identityBijection hZF I κ
  have hkθ := (hθ.2 κ hκ.1.1).mpr ⟨F, hF.1⟩
  obtain ⟨G, hG⟩ := ZF.exists_inclusionInjection hZF I (hθ.1.transitive κ hkθ)
  obtain ⟨H, hH⟩ := hκ.2
  have hθi : M.IsInfiniteCardinal I ω θ := ⟨hθ.isCardinal hZF I, ZF.exists_compositionInjection hZF I hH hG⟩
  obtain ⟨J, hJ⟩ := ZF.exists_identityBijection hZF I θ
  obtain ⟨K, hK⟩ := jh_cardinal_bound_l hZFC hω hθi hθ.1 ⟨J, hJ.1⟩ hU
  obtain ⟨L, hL⟩ := ZF.exists_inclusionInjection hZF I hPU
  exact ZF.exists_compositionInjection hZF I hL hK

/-- ZF+V=L 中每个无限基数的幂集都与其后继基数实际等势。 -/
theorem js_gch_l (hZF : M.Models ZF) (hVL : M.SatisfiesSentence Axioms.vl_axiom) :
    GCH_d (kp_pair_l (ZF.modelsKP hZF)) := fun _ _ _ _ hω hκ hP hθ =>
  ZF.hartogs_power_eq_l (kp_pair_l (ZF.modelsKP hZF)) hZF hP hθ (js_power_bound_l hZF hVL hω hκ hP hθ)

theorem js_gch_sentence_l (hZF : M.Models ZF) (hVL : M.SatisfiesSentence Axioms.vl_axiom) :
    M.SatisfiesSentence (gch_sentence_l kpair_convention_l) := by
  rw [Structure.satisfiesSentence_iff]
  exact fun f => (gch_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 ⟨Fin.elim0, f⟩).mpr (js_gch_l hZF hVL)

/-- 外部只需 ZF；幂集、后继基数、双射与全部量词均在同一个实际 L 模型内解释。 -/
theorem l_model_gch_l (hZF : M.Models ZF) :
    (l_model_l (ZF.models_kpi_l hZF)).Models (ZFC_GCH kpair_convention_l) := by
  refine ⟨(l_model_zf_l hZF).1, fun s hs => ?_⟩
  rcases hs with hs | rfl
  · exact (l_model_zfc_l hZF).2 s hs
  · exact js_gch_sentence_l (l_model_zf_l hZF) (l_model_vl_l (ZF.models_kpi_l hZF))

end YesMetaZFC.SetTheory.InnerModel
