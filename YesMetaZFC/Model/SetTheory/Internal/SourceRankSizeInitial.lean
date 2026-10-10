import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleClosure
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleUp
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.Card.SmallEnumeration

/-! # 初始秩模型中的全部不可达层枚举

原内部不可达性先由实际秩闭包读成背景不可达性。严格小秩层的原基数界
给出支撑以下的双射，整个支撑层用支撑自身枚举；所有图再由秩界回收。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_v_rank_size_l (hZFC : M.Models ZFC) {δ X ω L : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X)
    (h : Sc_inaccessible_d ω X L) : Sc_rank_size_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X L := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.v_transitive_l I hZF hX
  obtain ⟨above, hr, hs⟩ := sc_v_inaccessible_up_l hZF hδ hX h
  obtain ⟨_, hL, _⟩ := h
  have hLδ := ZF.v_ordinal_height_l hZF hX hr.isCardinal.1 hL
  have history {α W} (ha : M.mem α δ) (hw : V_d I α W) : M.mem W X ∧ Vr_d X α W := by
    obtain ⟨B, F, hB, hF, cert, _⟩ := vr_source_l hZF hX hδ ha hw
    exact ⟨ZF.v_mem_l I hZF hw hX ha, B, F, hB, hF, fun t _ => cert t⟩
  have owned {μ W f} (hμ : M.mem μ X) (hW : M.mem W X) (bf : M.IsSetBijectionFromTo I f μ W) : M.mem f X := by
    obtain ⟨B, hB, μb, wb⟩ := ZF.v_joint_bound_l I hZF hX hμ hW
    exact ZF.v_relation_mem_l I hZF hX hδ hB (fun p hp => by
      obtain ⟨a, ha, b, hb, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) bf.1.1).1 p hp
      exact ⟨a, μb a ha, b, wb b hb, pair⟩)
  obtain ⟨W, hw⟩ := ZF.v_exists_l I hZF hr.isCardinal.1
  obtain ⟨hW, rank⟩ := history hLδ hw
  obtain ⟨f, bf⟩ := ZFC.inaccessible_enumeration_l I hZFC hω above hr hs hw
  refine ⟨⟨W, f, hW, rank, owned hL hW bf, bf⟩, fun α hα => ?_⟩
  obtain ⟨W, hw⟩ := ZF.v_exists_l I hZF (hr.isCardinal.1.mem hα)
  obtain ⟨hW, rank⟩ := history (hδ.1.transitive L hLδ α hα) hw
  obtain ⟨ξ, hξ, bound⟩ := ZFC.inaccessible_level_small_l I hZFC hω above hr hs hα hw
  obtain ⟨μ, f, hμ, _, bf⟩ := ZF.small_enumeration_l I hZF hr.isCardinal hξ bound
  exact ⟨W, μ, f, hW, rank, hμ, owned (ht L hL μ hμ) hW bf, bf⟩

theorem sc_v_inaccessible_closure_l (hZFC : M.Models ZFC) {δ X ω : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) :
    Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X :=
  fun _ h => ⟨sc_regular_l (ZFC.models_zf_l hZFC)
    (sc_v_inaccessible_up_l (ZFC.models_zf_l hZFC) hδ hX h).2.1 X, sc_v_rank_size_l hZFC hω hδ hX h⟩

end YesMetaZFC.SetTheory.Internal
