import YesMetaZFC.SetTheory.LargeCardinal.Extender.WellFounded
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinExtender
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace

/-! # 武丁测度族的实际良基定向极限

先装配全部有限支撑源分量，再形成真实结构码，并由共同纤维证明整个极限
内部良基，并构造完整内部初等嵌入和传递坍塌。源只使用自身的函数代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_limit_d (hZF : M.Models ZF) (ω κ L X R F : M.Domain) : Prop := ∃ J O Z A p T S q c C V,
  Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S ∧ Di_limit_d A p T S q C V ∧
  Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧ Wf_rel_d C V ∧
  Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S ∧ Ep_collapse_d hZF ω X R q c C V

/-- 单射列索引覆盖每一个有限坐标列，包括带重复坐标的原始表示。 -/
theorem ep_support_cover_l (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S m a : M.Domain}
    (hω : M.IsOmega ω) (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (hm : M.mem m ω) (ha : Fn0_d m L a) : ∃ b q, M.mem b J ∧ Ei_map_d ω L a b q := by
  obtain ⟨n, b, q, _, hn, hb, hq, hqa, _⟩ := ec_join_l hZF hω hm hm ha ha
  exact ⟨b, q, (h.indices b).mpr ⟨n, hn, fn0_of_function_l (ZF.modelsKP hZF) hb.1, hb.2⟩,
    m, n, hm, hn, hq, fn0_of_function_l (ZF.modelsKP hZF) hb.1, hqa⟩

theorem ep_limit_exists_l (hZFC : M.Models ZFC) {ω κ K L X R F : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R) (hF : Em_family_d ω κ L F)
    (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (complete : ∀ H f, Ef_levels_d ω κ H →
      Es_fiber_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L F H f → ∃ g, Ef_fiber_d ω κ H g)
    (hωL : M.MemberSubset ω L) : Ep_limit_d (ZFC.models_zf_l hZFC) ω κ L X R F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have family := hF.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X
  have coherent := hc.source_l I X
  obtain ⟨J, O, Z, A, p, T, S, q, c, C, V, hs, limit, model, elem⟩ := ep_ultrapower_l hZF h family coherent
  have wf : Wf_rel_d X R := by
    obtain ⟨_, hM⟩ := h.code
    intro Y _ hn
    obtain ⟨x, hx, least⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) hn
    exact ⟨x, hx, fun y hy hyx => least y hy (((hM.2 y x).mp hyx).2.2)⟩
  have hw := ep_limit_wf_l hZF h.omega (ZFC.dc_l I hZFC h.omega) hωL hF hc complete hs limit wf
  exact ⟨J, O, Z, A, p, T, S, q, c, C, V, hs, limit, model, hw,
    elem, ep_collapse_l hZF h family hs limit model elem hw⟩

/-- 每个实际短扩展器都可在现有源内部函数族上自动形成良基极限。 -/
theorem Ex_short_d.limit_l (hZFC : M.Models ZFC) {ω κ L F K X R : M.Domain}
    (h : Ex_short_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R) :
    Ep_limit_d (ZFC.models_zf_l hZFC) ω κ L X R F :=
  ep_limit_exists_l hZFC source h.measures h.coherent h.countable
    (fun x hx => h.length.transitive κ h.above x (h.critical.1.transitive ω h.uncountable x hx))

end YesMetaZFC.SetTheory.LargeCardinal
