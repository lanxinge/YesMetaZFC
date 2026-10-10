import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLimit
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFactor
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLength

/-! # 武丁派生扩展器的完整极限与原目标比较

自动选用 Vδ 本身作为源，输出同一个系统的完整内部初等极限、传递坍塌及
向原嵌入目标的实际关系因子。秩覆盖与谓词强性尚不包含在这个证书中。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_derived_limit_d (hZF : M.Models ZF) (ω κ L X R F j Y : M.Domain) : Prop := ∃ J O Z A p T S q c C V,
  Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S ∧ Di_limit_d A p T S q C V ∧
  Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧ Wf_rel_d C V ∧
  Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S ∧ Ep_collapse_d hZF ω X R q c C V ∧
  Ee_factor_d hZF j Y q C V ∧ Ep_length_d hZF ω κ L X R j Y q c C V

theorem Ep_limit_d.factor_l (hZF : M.Models ZF) {ω δ X A Y B j κ k K R L S F : M.Domain}
    (source : Ep_source_d hZF ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.MemberSubset L k) (hLo : M.IsOrdinal L) (hκL : M.mem κ L)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
    (limit : Ep_limit_d hZF ω κ L X R F) :
    Ep_derived_limit_d hZF ω κ L X R F j Y := by
  obtain ⟨J, O, Z, D, p, T, V, q, c, C, W, system, limit, code, wf, elem, collapse⟩ := limit
  have factor := ee_factor_l hZF source hV hδ h hY hc hL hS hSY hF system limit
  have comparison := ep_comparison_l hZF source.omega h source.transitive hY collapse factor
  exact ⟨J, O, Z, D, p, T, V, q, c, C, W, system, limit, code, wf, elem, collapse,
    factor, ep_length_l hZF comparison source.transitive hc hLo hκL hL
      (fun _ hα => ee_ordinal_node_l hZF source.omega hV hδ h hY hc hL hS hSY hF system limit hα)⟩

/-- 同一个标准短扩展器自动给出 Vδ 源、全部分量、完整初等极限、坍塌和原目标因子。 -/
theorem woodin_extender_l (hZFC : M.Models ZFC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω V, M.IsOmega ω ∧ V_d I δ V ∧ ∀ A, M.MemberSubset A V → ∃ κ, M.mem κ δ ∧
      ∀ L, M.mem L δ → M.mem κ L → ∃ ν N B j W k S F K E R,
        Wd_witness_d I ω δ V A κ ν N B j W k ∧ M.mem L ν ∧ M.mem L k ∧ Fseq_space_d I ω L S ∧ M.mem S N ∧
        Es_family_d I j κ L S F ∧ Ex_short_d hZF ω κ L F ∧ Ex_operator_d K S F E ∧ Ex_derived_d j S E ∧
        Ep_source_d hZF ω κ K V R ∧ Ep_derived_limit_d hZF ω κ L V R F j N := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, V, hω, hV, all⟩ := woodin_short_l hZF hd
  obtain ⟨ω₀, _, hω₀, hωδ, hr, hstrong, _⟩ := hd
  have eqω := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  refine ⟨ω, V, hω, hV, fun A hA => ?_⟩
  obtain ⟨κ, hκ, family⟩ := all A hA
  refine ⟨κ, hκ, fun L hL hκL => ?_⟩
  obtain ⟨ν, N, B, j, W, k, S, F, K, E, hw, hLν, hLk, hS, hSN, hK, hF, short, he, derived⟩ := family L hL hκL
  obtain ⟨R, source⟩ := ep_regular_source_l hZFC hω hωδ hr hV hκ
    (short.critical.1.transitive ω short.uncountable) hK
  exact ⟨ν, N, B, j, W, k, S, F, K, E, R, hw, hLν, hLk, hS, hSN, hF, short, he, derived, source,
    Ep_limit_d.factor_l hZF source hV hr.isLimitOrdinal hw.2.2.2.2.2.1 hw.1 hw.2.2.2.2.2.2.1
      (hw.2.2.2.2.2.2.1.ordinal_image.transitive L hLk) short.length short.above hS (hw.1 S hSN) hF
      (short.limit_l hZFC source)⟩

end YesMetaZFC.SetTheory.LargeCardinal
