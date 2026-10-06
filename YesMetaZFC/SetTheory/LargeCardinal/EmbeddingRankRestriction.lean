import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingSmallRestriction
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingSetRestriction
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankClosure

/-! # 不可达秩段上的实际限制图

任意传递源可通过已有真实枚举调用小域恢复。这里另外从正则 Hχ 源和
不可达 κ 自动构造 κ→Vκ 的枚举及其源内成员资格，消除该实例的枚举输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 严格相对秩段的像及其完整初等限制同时构造，目标高度保留内部正则性。 -/
theorem ep_rank_restriction_l (hZF : M.Models ZF)
    {ω κ K X R μ K' Y S c d j a A Q α β : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hA : M.mem A X) (rank : Vr_d X α A) (regular : Sc_regular_d X α)
    (ha : Smem_d (kp_pair_l (ZF.modelsKP hZF)) a A Q) (hαβ : Rd_entry_d α β j) :
    ∃ B b T p, M.mem B Y ∧ Vr_d Y β B ∧ Sc_regular_d Y β ∧ Rd_entry_d A B j ∧
      Smem_d (kp_pair_l (ZF.modelsKP hZF)) b B T ∧
      M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) p j A ∧ Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω a b A B p := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, hB, hAB⟩ := hj.1.1.2.2 A hA
  obtain ⟨x, hx⟩ := ha.1.2.1
  obtain ⟨y, hy, hxy⟩ := hj.1.1.2.2 x (source.transitive A hA x hx)
  have hyB := ((hn.2 y B).mp ((hj.relation_l I hZF source.omega hm.1 hn.1 hxy hAB).mp
    ((hm.2 x A).mpr ⟨source.transitive A hA x hx, hA, hx⟩))).2.2
  obtain ⟨b, T, code⟩ := smdl_membership_l I hZF ⟨y, hyB⟩
  obtain ⟨p, res, elem⟩ := ep_set_restriction_l hZF source target hm hn hj ha code hAB
  exact ⟨B, b, T, p, hB, (hj.hierarchy_l hZF source.omega source.transitive target.transitive hm hn hαβ hAB).mp rank,
    (hj.regular_l hZF source.omega source.transitive target.transitive hm hn hαβ).mp regular, hAB, code, res, elem⟩

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
