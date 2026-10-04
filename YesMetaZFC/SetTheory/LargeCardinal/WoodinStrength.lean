import YesMetaZFC.SetTheory.LargeCardinal.ExtenderDerivedLimit
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrength
import YesMetaZFC.SetTheory.LargeCardinal.RankLength

/-! # 按指定秩自动选择短扩展器并恢复覆盖与谓词一致性

临界点随 A 固定；长度随 ν 选择。枚举域、枚举图、原强嵌入、全系统、
传递坍塌和新谓词全由既有构造生成；新嵌入同时保留完整谓词初等性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 强性证书与同一张 F、同一全系统及其实际商投影绑定。 -/
def Ep_strong_limit_d (hZF : M.Models ZF) (ω κ L X R A V F j Y : M.Domain) : Prop :=
  ∃ J O Z D p T S q c C W, Ep_system_d hZF ω κ L X R F J O Z D p T S ∧
    Di_limit_d D p T S q C W ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C W ∧ Wf_rel_d C W ∧
    Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O D p T S ∧ Ep_collapse_d hZF ω X R q c C W ∧
    Ee_factor_d hZF j Y q C W ∧ Ep_strength_d hZF ω κ L X R A V j Y q C

theorem woodin_rank_strength_l (hZFC : M.Models ZFC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧
      ∀ ν, M.mem ν δ → ∃ L K F R V Y j, M.mem L δ ∧ M.mem κ L ∧ M.mem ν L ∧ V_d I ν V ∧
        Ex_short_d hZF ω κ L F ∧ Ep_source_d hZF ω κ K X R ∧ Ep_strong_limit_d hZF ω κ L X R A V F j Y := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, all⟩ := woodin_extender_l hZFC hd
  obtain ⟨ω₀, _, hω₀, hωδ, hr, hs, _⟩ := hd
  have eqω := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  refine ⟨ω, X, hω, hX, fun A hA => ?_⟩
  obtain ⟨κ, hκ, family⟩ := all A hA
  refine ⟨κ, hκ, fun ν hν => ?_⟩
  obtain ⟨L, Vν, μ, g, U, hL, hκL, hνL, hμL, hVν, hU, hgU, hg⟩ := er_length_l hZFC hω hωδ hr hs hX hκ hν
  obtain ⟨ν₀, Y, B, j, W, k, S, F, K, _, R, hw, hLν, hLk, hS, hSY, hF, short, _, _, source, model⟩ :=
    family L hL hκL
  obtain ⟨J, O, Z, D, p, T, V, q, c, C, Q, system, limit, code, wf, elementary, collapse, factor, length⟩ := model
  obtain ⟨hY, _, _, hW, hWY, embed, crit, _, agreement⟩ := hw
  have hν₀ := v_ordinal_l I hW
  have sub : M.MemberSubset Vν W := ZF.v_mono_l I hZF hVν hW (hν₀.transitive ν (hν₀.transitive L hLν ν hνL))
  have hgY := hWY g (ZF.v_mono_l I hZF hU hW (hν₀.transitive L hLν) g hgU)
  have hωL : M.MemberSubset ω L := fun x hx => short.length.transitive κ hκL x (source.below x hx)
  have cover := er_cover_l hZFC source hX hr hs hκ embed hY crit
    (crit.ordinal_image.transitive L hLk) short.length hωL hS (hY S hSY) hF system limit
    hνL hVν (fun x hx => hWY x (sub x hx)) hμL hgY hg
  exact ⟨L, K, F, R, Vν, Y, j, hL, hκL, hνL, hVν, short, source,
    J, O, Z, D, p, T, V, q, c, C, Q, system, limit, code, wf, elementary, collapse, factor,
    ep_strength_l hZFC source hr hωδ hX (ZFC.inaccessible_hereditary_l I hZFC hω hωδ hr hs hX)
      embed hY crit (crit.ordinal_image.transitive L hLk) (hY S hSY) hF short.measures short.coherent
      system limit code collapse factor hVν length cover (fun x hx => agreement x (sub x hx))⟩

end YesMetaZFC.SetTheory.LargeCardinal
