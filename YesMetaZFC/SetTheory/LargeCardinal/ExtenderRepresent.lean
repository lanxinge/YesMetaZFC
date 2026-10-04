import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLimit
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCoordinates

/-! # 任意有限种子的源函数求值都进入现有极限

重复坐标的种子先覆盖到单射支撑；源函数沿真实坐标投影复合，再由求值
交换律识别同一值。这里不把全系统扩充为另一套支撑表示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ee_represent_l (hZFC : M.Models ZFC) {ω δ X A Y B j κ k K R L S F J O Z D p T V q C W n H a f x : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X j κ k)
    (hL : M.MemberSubset L k) (hωL : M.MemberSubset ω L)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) j κ L S F)
    (system : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (hn : M.mem n ω) (hH : Ep_space_d κ n H) (ha : Fn0_d n L a)
    (hfX : M.mem f X) (hf : Fn0_d H X f) (hx : Ee_value_d j a f x) :
    ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u x := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨b, t, hbJ, m, l, _, hl, ht, hb, hba⟩ := ep_support_cover_l hZF source.omega hωL system hn ha
  have eq := hba.1.domain_eq_l hZF.1 ha
  subst m
  obtain ⟨_, hZ, models⟩ := system.models
  obtain ⟨c, _, hbc⟩ := hZ.2.1 b hbJ
  have md := models b c hbc
  obtain ⟨l', E, U, G, r, Q, S₀, _, hb', hE, hbU, hG, model⟩ := md
  have eq := hb'.domain_eq_l hZF.1 hb
  subst l'
  obtain ⟨s, hsX, hs, ss⟩ := source.projection_l hZFC hn hl ht hH hE
  obtain ⟨χ, c₀, d₀, N₀, R₀, e₀, hχ, hωχ, hN₀, hX, hm, he₀⟩ := source.presentation
  obtain ⟨g, hg, comp⟩ := smap_compose_l hZFC source.omega hχ hωχ hN₀ source.transitive hX hm he₀
    (source.space_mem_l hZF hl hE) (source.space_mem_l hZF hn hH) hsX hfX hs hf
  have pull := ep_pull_of_comp_l hH hE hs hf ss comp
  obtain ⟨Q', S', e, code, he, _, any, _⟩ := ee_component_l hZFC source hV hδ h hY hc hL hS hSY hF (models b c hbc)
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I model.code code
  obtain ⟨D₀, hD₀, hgD₀⟩ := model.map.projection.2.2 g ((hG g).mpr ⟨hg.1, comp.1⟩)
  obtain ⟨y, _, hD₀y⟩ := he.1.2.2 D₀ hD₀
  have ultra := (es_measures_l hZF source.omega hV hδ h hY hc hL hS hSY hF).at_l hZF.1 hbU hb' hE
  have hgD := model.map.representative_l I ultra.1.base_l hgD₀
  have value := any D₀ y g hD₀y hgD
  have eq := ee_pull_l hZFC source hV hδ h hY hc hL hn hl ht
    (hSY a ((hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩))
    (hSY b ((hS b).mpr ⟨l, hl, fn0_function_l (ZF.modelsKP hZF) hb⟩)) hb hba hfX pull hx value
  obtain ⟨u, hu⟩ := I.total b D₀
  have huD := (system.nodes u).mpr ⟨b, D₀, hu, c, Q, S₀, hbc, model.code.1, hD₀⟩
  obtain ⟨E₀, hE₀, huE₀⟩ := limit.projection.2.1 u huD
  exact ⟨E₀, u, hE₀, huE₀, b, D₀, g, hu, hgD, eq.symm ▸ value⟩

end YesMetaZFC.SetTheory.LargeCardinal
