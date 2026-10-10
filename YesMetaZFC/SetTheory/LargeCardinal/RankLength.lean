import YesMetaZFC.SetTheory.LargeCardinal.RankEnumerationSyntax

/-! # 为指定秩层实际选择足够长的短扩展器长度

长度同时高于临界点、秩指标和一个最小枚举的序数域，并在 V_L 中包含
整张枚举图。原构造的强度高于 L，故这些数据都进入原目标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem er_length_l (hZFC : M.Models ZFC) {ω δ X κ ν : M.Domain} (hω : M.IsOmega ω) (hωδ : M.mem ω δ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hκ : M.mem κ δ) (hν : M.mem ν δ) :
    ∃ L V μ g U, M.mem L δ ∧ M.mem κ L ∧ M.mem ν L ∧ M.mem μ L ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ν V ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L U ∧ M.mem g U ∧ Su0_d μ V g := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hδ := hr.isLimitOrdinal
  have ht := ZF.v_transitive_l I hZF hX
  have hH := ZFC.inaccessible_hereditary_l I hZFC hω hωδ hr hs hX
  obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF (hr.isCardinal.1.mem hν)
  obtain ⟨ξ, hξ, hVξ⟩ := ZFC.inaccessible_level_small_l I hZFC hω hωδ hr hs hν hV
  obtain ⟨μ, g, hμ, _, hg⟩ := ZF.small_enumeration_l I hZF hr.isCardinal hξ hVξ
  have hμX := ZF.v_ordinal_mem_l I hZF hX hμ
  have hVX := ZF.v_mem_l I hZF hV hX hν
  have hgX := ZFC.h_function_l hZFC hω hr hωδ hH hμX (hg.1.1.mono_target_l I (ht V hVX))
  obtain ⟨α, W, hα, hW, hgW⟩ := (ZF.v_limit_mem_l I hZF hX hδ.2.2 g).mp hgX
  have above a b (ha : M.mem a δ) (hb : M.mem b δ) : ∃ c, M.mem c δ ∧ M.mem a c ∧ M.mem b c := by
    rcases hδ.1.wellOrder.linear.compare a ha b hb with same | hab | hba
    · obtain ⟨c, hc, hbc⟩ := hδ.2.2 b hb
      exact ⟨c, hc, (hZF.1.eq_of_same_members a b same).symm ▸ hbc, hbc⟩
    · obtain ⟨c, hc, hbc⟩ := hδ.2.2 b hb
      exact ⟨c, hc, (hδ.1.mem hc).transitive b hbc a hab, hbc⟩
    · obtain ⟨c, hc, hac⟩ := hδ.2.2 a ha
      exact ⟨c, hc, hac, (hδ.1.mem hc).transitive a hac b hba⟩
  obtain ⟨a, ha, hκa, hνa⟩ := above κ ν hκ hν
  obtain ⟨b, hb, hμb, hαb⟩ := above μ α hμ hα
  obtain ⟨L, hL, haL, hbL⟩ := above a b ha hb
  have hLo := hδ.1.mem hL
  obtain ⟨U, hU⟩ := ZF.v_exists_l I hZF hLo
  exact ⟨L, V, μ, g, U, hL, hLo.transitive a haL κ hκa, hLo.transitive a haL ν hνa,
    hLo.transitive b hbL μ hμb, hV, hU,
    ZF.v_mono_l I hZF hW hU (hLo.transitive α (hLo.transitive b hbL α hαb)) g hgW,
    fn0_of_function_l (ZF.modelsKP hZF) hg.1.1, hg.2⟩

end YesMetaZFC.SetTheory.LargeCardinal
