import YesMetaZFC.SetTheory.LargeCardinal.ExtenderWellFounded
import YesMetaZFC.SetTheory.LargeCardinal.SupportConstruction

/-! # 武丁测度族的实际良基定向极限

先装配全部有限支撑源分量，再形成真实结构码，并由共同纤维证明整个极限
内部良基。源只使用自身的函数代表；其秩不受派生测度的原强嵌入定义域限制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_limit_d (hZF : M.Models ZF) (ω κ L X R F : M.Domain) : Prop := ∃ J O Z A p T S q c C V,
  Ep_system_d hZF ω κ L X R F J O Z A p T S ∧ Di_limit_d A p T S q C V ∧
  Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧ Wf_rel_d C V

/-- 单射列索引覆盖每一个有限坐标列，包括带重复坐标的原始表示。 -/
theorem ep_support_cover_l (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S m a : M.Domain}
    (hω : M.IsOmega ω) (hωL : M.MemberSubset ω L) (h : Ep_system_d hZF ω κ L X R F J O Z A p T S)
    (hm : M.mem m ω) (ha : Fn0_d m L a) : ∃ b q, M.mem b J ∧ Ei_map_d ω L a b q := by
  obtain ⟨n, b, q, _, hn, hb, hq, hqa, _⟩ := ec_join_l hZF hω hωL hm hm ha ha
  exact ⟨b, q, (h.indices b).mpr ⟨n, hn, fn0_of_function_l (ZF.modelsKP hZF) hb.1, hb.2⟩,
    m, n, hm, hn, hq, fn0_of_function_l (ZF.modelsKP hZF) hb.1, hqa⟩

theorem ep_limit_exists_l (hZFC : M.Models ZFC) {ω κ K L X R F : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_family_d ω κ L F)
    (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (complete : ∀ H f, Ef_levels_d ω κ H →
      Es_fiber_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L F H f → ∃ g, Ef_fiber_d ω κ H g)
    (hωL : M.MemberSubset ω L) : Ep_limit_d (ZFC.models_zf_l hZFC) ω κ L X R F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨J, O, Z, A, p, T, S, hs⟩ := ep_system_exists_l hZFC h hF hc hωL
  obtain ⟨z, hz, hzω⟩ := h.omega.1.1
  have hzfn : Fn0_d z L z := ⟨fun r hr => (hz r hr).elim, fun r hr => (hz r hr).elim, fun r hr => (hz r hr).elim⟩
  have hzJ := (hs.indices z).mpr ⟨z, hzω, hzfn, fun i j x hi _ => hi.elim fun r hr => (hz r hr.2).elim⟩
  obtain ⟨Q, hZ, models⟩ := hs.models
  obtain ⟨d, _, hzd⟩ := hZ.2.1 z hzJ
  obtain ⟨_, _, _, _, _, D, W, _, _, _, _, _, hm⟩ := models z d hzd
  obtain ⟨B, hBD⟩ := hm.code.2.1
  obtain ⟨u, hu⟩ := I.total z B
  have huA := (hs.nodes u).mpr ⟨z, B, hu, d, D, W, hzd, hm.code.1, hBD⟩
  obtain ⟨c, q, C, V, limit, model⟩ := di_model_exists_l hZF hs.diagram ⟨u, huA⟩
  have wf : Wf_rel_d X R := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hM, _⟩ := h.presentation
    intro Y _ hn
    obtain ⟨x, hx, least⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) hn
    exact ⟨x, hx, fun y hy hyx => least y hy (((hM.2 y x).mp hyx).2.2)⟩
  exact ⟨J, O, Z, A, p, T, S, q, c, C, V, hs, limit, model,
    ep_limit_wf_l hZF h.omega (ZFC.dc_l I hZFC h.omega) hωL hF hc complete hs limit wf⟩

/-- 同一个武丁测度族自动生成实际源、全部分量和良基极限。 -/
theorem woodin_extender_l (hZFC : M.Models ZFC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω V, M.IsOmega ω ∧ V_d I δ V ∧ ∀ A, M.MemberSubset A V → ∃ κ, M.mem κ δ ∧
      ∀ L, M.mem L δ → M.MemberSubset ω L → ∃ ν N B j W k S F K X R,
        Wd_witness_d I ω δ V A κ ν N B j W k ∧ M.mem L k ∧ Fseq_space_d I ω L S ∧
        Es_family_d I j κ L S F ∧ Es_coherent_d I ω κ L F ∧ Ep_source_d hZF ω κ K X R ∧
        Ep_limit_d hZF ω κ L X R F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, V, hω, hV, all⟩ := woodin_components_l I hZF hd
  refine ⟨ω, V, hω, hV, fun A hA => ?_⟩
  obtain ⟨κ, hκ, family⟩ := all A hA
  refine ⟨κ, hκ, fun L hL hωL => ?_⟩
  obtain ⟨ν, N, B, j, W, k, S, F, hw, hLk, hS, hF, components, coherent, complete⟩ := family L hL hωL
  have measures : Em_family_d ω κ L F := ⟨fun n a hn ha => (hF.2.1 a).mp ((hS a).mpr
      ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩), hF.1.2, fun a U ha => by
    obtain ⟨n, D, hn, hD, _, hU, _⟩ := components a U ha
    obtain ⟨m, hm, hma⟩ := (hS a).mp ((hF.2.2 a U).mp ha).1
    have en := (fn0_of_function_l (ZF.modelsKP hZF) hma).domain_eq_l hZF.1 hn
    exact ⟨n, D, en ▸ hm, hn, hD, hU⟩⟩
  have hωκ := ed_critical_omega_l I hZF hω hw.2.2.2.2.2.1 (ZF.v_transitive_l I hZF hV) hw.1 hw.2.2.2.2.2.2.1
  obtain ⟨K, X, R, source⟩ := ep_source_exists_l hZFC hω (hw.2.2.2.2.2.2.1.ordinal.transitive ω hωκ)
  exact ⟨ν, N, B, j, W, k, S, F, K, X, R, hw, hLk, hS, hF, coherent, source,
    ep_limit_exists_l hZFC source measures coherent (fun H f hH hf => (complete H f hH hf).imp fun _ hh => hh.2) hωL⟩

end YesMetaZFC.SetTheory.LargeCardinal
