import YesMetaZFC.SetTheory.HereditaryAlgebra
import YesMetaZFC.SetTheory.Collapse.RelationMap

/-! # 遗传小模型中的实际关系塌缩

塌缩像的大小不超过关系载体；传递性把这个大小界提升为遗传大小界。
像的闭包只需极限指标。函数图的闭包复用正则 Hχ 的乘积与子集封闭。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem ZF.h_collapse_image_l (hZF : M.Models ZF) {χ H A R B F : M.Domain}
    (hχ : M.IsLimitOrdinal χ) (hH : H_d (kp_pair_l (ZF.modelsKP hZF)) χ H)
    (hA : M.mem A H) (h : Wc_iso_d A R B F) : M.mem B H := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨μ, hμ, g, hg⟩ := ZF.hmem_size_l I hZF ((hH A).mp hA)
  obtain ⟨f, hf, _⟩ := ZF.exists_inverseBijectionWithPairs hZF I (h.bijection_l (ZF.modelsKP hZF))
  exact (hH B).mpr (ZF.hmem_of_subset_l I hZF hχ h.transitive (fun _ hx => hx) hμ
    (ZF.exists_compositionInjection hZF I hf.1 hg))

theorem ZFC.h_collapse_l (hZFC : M.Models ZFC) {ω χ H A R : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    (hA : M.mem A H) (hw : Wf_rel_d A R) :
    ∃ B F, M.mem B H ∧ M.mem F H ∧ Wc_map_d A R B F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, F, h⟩ := wc_map_exists_l hZF hw
  obtain ⟨μ, hμ, g, hg⟩ := ZF.hmem_size_l I hZF ((hH A).mp hA)
  obtain ⟨f, hf⟩ := ZFC.surjection_bound_l I hZFC (fn0_function_l (ZF.modelsKP hZF) h.function) h.onto
  have hB := (hH B).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal h.transitive
    (fun _ h => h) hμ (ZF.exists_compositionInjection hZF I hf hg))
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hZF I A B
  exact ⟨B, F, hB, ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH
    (ZFC.h_product_l hZFC hω hχ hωχ hH hA hB hp) F
      (fun p hf => (hp p).mpr (h.function.1 p hf)), h⟩

end YesMetaZFC.SetTheory
