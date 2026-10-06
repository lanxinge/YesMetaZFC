import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingSmallRestriction
import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

/-! # 可沿迭代传输的相对秩层枚举

初始 Vδ 中的不可达层有实际 κ 枚举；把枚举记录为有界塌缩证书后，
初等像仍带源内枚举，不要求像序数在背景中不可达或不可数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Er_level_d (X κ B : M.Domain) : Prop where
  member : M.mem B X
  hierarchy : Vr_d X κ B
  code : ∃ T f, M.mem T X ∧ M.mem f X ∧ Wc_iso_d κ T B f

theorem ep_relative_rank_l (hZFC : M.Models ZFC) {ω κ K X R δ L B : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hδ : M.IsLimitOrdinal δ)
    (hL : M.mem L δ) (hωL : M.mem ω L)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L B) : Er_level_d X L B := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hLX := ZF.v_ordinal_mem_l I hZF hX hL
  have hBX := ZF.v_mem_l I hZF hB hX hL
  obtain ⟨f, hf⟩ := ZFC.inaccessible_enumeration_l I hZFC source.omega hωL hr hs hB
  obtain ⟨D, hDX, hLD, hBD⟩ := ZF.v_joint_bound_l I hZF hX hLX hBX
  have hfX := ZF.v_relation_mem_l I hZF hX hδ hDX (F := f) (fun p hp => by
    obtain ⟨a, ha, b, hb, hab⟩ := (fn0_of_function_l (ZF.modelsKP hZF) hf.1.1).1 p hp
    exact ⟨a, hLD a ha, b, hBD b hb, hab⟩)
  obtain ⟨T, hTX, _, iso⟩ := ep_transitive_code_l hZF source (ZF.v_transitive_l I hZF hB) hfX hf
  obtain ⟨C, F, hCX, hFX, cert, _⟩ := vr_source_l hZF hX hδ hL hB
  exact ⟨hBX, ⟨C, F, hCX, hFX, fun t _ => cert t⟩, T, f, hTX, hfX, iso⟩

/-- 同时传输秩递归历史和实际枚举，保留非标准内部序数上的枚举资格。 -/
theorem Er_level_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j κ ℓ B C : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hκ : Rd_entry_d κ ℓ j) (hB : Rd_entry_d B C j) (h : Er_level_d X κ B) : Er_level_d Y ℓ C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨T, f, hT, hf, iso⟩ := h.code
  obtain ⟨T', hT', hTT⟩ := hj.1.1.2.2 T hT
  obtain ⟨f', hf', hff⟩ := hj.1.1.2.2 f hf
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 4)
    (wc_iso_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (wc_iso_delta_l ..)
    ⟨Fin.cases f (Fin.cases B (Fin.cases T (fun _ => κ))), fun _ => κ⟩
    ⟨Fin.cases f' (Fin.cases C (Fin.cases T' (fun _ => ℓ))), fun _ => ℓ⟩
    (Fin.cases hff (Fin.cases hB (Fin.cases hTT (fun _ => hκ))))
  exact ⟨hj.1.1.output_mem_of_pairMember hB, (hj.hierarchy_l hZF hω hX hY hm hn hκ hB).mp h.hierarchy,
    T', f', hT', hf', (wc_iso_sat_l hZF.1 ..).mp (tr.mp ((wc_iso_sat_l hZF.1 ..).mpr iso))⟩

/-- 同一秩层和枚举图进入严格截断；关系码在截断源中由原枚举重新分离。 -/
theorem Er_level_d.rank_l (hZF : M.Models ZF) {ω μ K X α V R κ B : M.Domain}
    (source : Ep_source_d hZF ω μ K V R) (hX : M.TransitiveSet X) (hV : M.mem V X)
    (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V)
    (h : Er_level_d X κ B) : Er_level_d V κ B := by
  obtain ⟨hB, hierarchy⟩ := rank.rank_l hZF hX hV hα hκ h.member h.hierarchy
  obtain ⟨_, f, _, hf, iso⟩ := h.code
  have hfV := rank.relation_mem_l hZF hX hV hα hκ hB hf iso.function.1
  obtain ⟨T, hT, _, code⟩ := ep_transitive_code_l hZF source iso.transitive hfV (iso.bijection_l (ZF.modelsKP hZF))
  exact ⟨hB, hierarchy, T, f, hT, hfV, code⟩

/-- 自动读取已经装配的相对秩层枚举，将序数限制恢复为整个秩层的限制。 -/
theorem Er_level_d.restriction_l (hZF : M.Models ZF)
    {ω κ K X R ξ K' Y S c d j p B : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω ξ K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (hp : M.mem p Y) (res : M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) p j κ)
    (h : Er_level_d X κ B) : M.mem B Y ∧
      ∃ k, M.mem k Y ∧ M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) k j B := by
  obtain ⟨_, f, _, hf, iso⟩ := h.code
  exact smap_small_restriction_l hZF source target hm hn hj hp res iso.transitive hf
    (iso.bijection_l (ZF.modelsKP hZF))

end YesMetaZFC.SetTheory.LargeCardinal
