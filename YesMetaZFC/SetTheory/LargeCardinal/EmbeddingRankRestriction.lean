import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingSmallRestriction
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.HereditaryFunction

/-! # 不可达秩段上的实际限制图

任意传递源可通过已有真实枚举调用小域恢复。这里另外从正则 Hχ 源和
不可达 κ 自动构造 κ→Vκ 的枚举及其源内成员资格，消除该实例的枚举输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_h_rank_enumeration_l (hZFC : M.Models ZFC) {ω χ X κ B : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X)
    (hκX : M.mem κ X) (hωκ : M.mem ω κ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ B) :
    ∃ f, M.mem f X ∧ M.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) f κ B := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨f, hf⟩ := ZFC.inaccessible_enumeration_l I hZFC hω hωκ hr hs hB
  obtain ⟨μ, hμ, g, hg⟩ := ZF.hmem_size_l I hZF ((hX κ).mp hκX)
  obtain ⟨r, hr'⟩ := ZF.exists_inverseBijection hZF I hf
  have hBX := (hX B).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal
    (ZF.v_transitive_l I hZF hB) (fun _ h => h) hμ (ZF.exists_compositionInjection hZF I hr'.1 hg))
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hX hκX
    (hf.1.1.mono_target_l I (ZF.h_transitive_l I hZF hX B hBX)), hf⟩

theorem smap_h_rank_restriction_l (hZFC : M.Models ZFC)
    {ω κ K X R ξ K' Y S c d j p χ B : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (target : Ep_source_d (ZFC.models_zf_l hZFC) ω ξ K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d X Y j)
    (hp : M.mem p Y) (res : M.IsRestrictionOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p j κ)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X) (hωκ : M.mem ω κ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ B) : M.mem B Y ∧
      ∃ k, M.mem k Y ∧ M.IsRestrictionOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) k j B := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨f, hf, bij⟩ := ep_h_rank_enumeration_l hZFC source.omega hχ hωχ hX source.cardinal_mem hωκ hr hs hB
  exact smap_small_restriction_l hZF source target hm hn hj hp res
    (ZF.v_transitive_l (kp_pair_l (ZF.modelsKP hZF)) hZF hB) hf bij

end YesMetaZFC.SetTheory.LargeCardinal
