import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemCode

/-! # 模型内小 Skolem 壳的实际初始实例

只要求大小参数是含 ω 的序数。先以它的实际基数代表作闭包估计，再
恢复原序数上的双射；选择图、最小壳和双射图全部属于正则 Hχ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem sh_source_of_h_l (hZFC : M.Models ZFC) {ω χ Z : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z) (hωZ : M.mem ω Z) :
    Sh_source_d (ZF.modelsKP (ZFC.models_zf_l hZFC)) ω Z := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := ZF.h_transitive_l I hZF hZ
  obtain ⟨K₀, hK₀, finite⟩ := ZFC.h_fseq_l hZFC hω hχ hωχ hZ hωZ
  obtain ⟨W, source⟩ := ep_source_of_h_l hZFC hω (fun _ h => h) hχ hωχ hZ hωZ hωZ hK₀ finite
  intro c A R U κ f hAZ _ _ hκZ _ hm hκ hωκ hUA hf
  obtain ⟨u, C, J, T, D, K, N, g, skolem, hull, hg⟩ := ssk_hull_enum_l I hZFC hω hκ hωκ hm hUA hf
  have hC : M.mem C Z := by
    apply ZFC.h_small_closed_l I hZFC hω hχ hωχ hZ ?_ hωχ (scode_countable_l I hZF hω skolem.codes)
    intro a ha
    obtain ⟨n, F, r, code, program, hr⟩ := (skolem.codes a).mp ha
    obtain ⟨hF, _⟩ := source.program_l hZF program
    have hrZ := trans ω hωZ r (hω.transitive hZF n program.1 r hr)
    obtain ⟨p, hp, eq⟩ := source.kpair_l hZF hF hrZ
    exact kpair_unique_l M hZF.1 eq code ▸ hp
  obtain ⟨J', hJ', seq⟩ := source.sequences.space A hAZ
  have hJ : M.mem J Z := hZF.1.eq_of_same_members J' J (fun s => (seq s).trans (skolem.params s).symm) ▸ hJ'
  have hT := ZFC.h_product_l hZFC hω hχ hωχ hZ hC hωZ skolem.labels
  have hD := ZFC.h_product_l hZFC hω hχ hωχ hZ hT hJ skolem.domain
  have hK := ZFC.h_function_l hZFC hω hχ hωχ hZ hD (skolem.graph.mono_target_l I (trans A hAZ))
  have hN := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hZ hAZ N hull.2.1
  exact ⟨u, C, J, T, D, K, N, g, trans A hAZ u skolem.point, hC, hJ, hT, hD, hK, hN,
    ZFC.h_function_l hZFC hω hχ hωχ hZ hκZ (hg.1.1.mono_target_l I (trans N hN)),
    skolem, ⟨hull.1, hull.2.1, hull.2.2.1, fun B _ hUB _ => hull.2.2.2 B hUB⟩, hg⟩

end YesMetaZFC.SetTheory.LargeCardinal
