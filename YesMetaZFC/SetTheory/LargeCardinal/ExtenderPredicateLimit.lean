import YesMetaZFC.SetTheory.LargeCardinal.ExtenderPredicateComponent
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderConstant

/-! # 同一个有限支撑极限的完整谓词初等性

逐分量扩张关系，沿既有过渡图应用完整 Łoś，再由通用定向极限定理装配。
最后用实际种子求值识别常值箭头，证明原来的那张嵌入保持全部谓词公式码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_predicate_limit_l {ω δ κ k K L X R A Y B j c₀ R₀ c₁ R₁ S F J O Z D p T V q c C W g t : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hδ : M.IsRegularCardinal I δ) (hωδ : M.mem ω δ)
    (hV : V_d I δ X) (hH : H_d I δ X)
    (hx : Spred_d I c₀ X A R₀) (hy : Spred_d I c₁ Y B R₁) (hj : Smap_d I ω c₀ c₁ X Y j)
    (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k) (hL : M.MemberSubset L k)
    (hSY : M.MemberSubset S Y) (family : Es_family_d I j κ L S F)
    (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (system : Ep_system_d hZF ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (model : Smdl_d I c C W) (hg : M.IsSetInjectionFromTo I g C Y)
    (any : ∀ u a H f E y, Rd_entry_d u E q → KPair_d M u a H → M.mem f H →
      Rd_entry_d E y g → Ee_value_d j a f y)
    (ht : M.IsSetInjectionFromTo I t X C) (constants : Ep_constants_d X q t) :
    ∃ d W', Smdl_d I d C W' ∧ Smap_d I ω c₀ d X C t ∧
      ∀ E H y z, Rd_entry_d E y g → Rd_entry_d H z g → (Rd_entry_d E H W' ↔ Rd_entry_d y z R₁) := by
  obtain ⟨d, W', md, rel⟩ := smdl_pull_l hZF model.2.1 hg.1 R₁
  obtain ⟨V', changed, newLimit, _⟩ := di_relation_change_l hZF system.diagram limit md
  have component a b (hab : Rd_entry_d a b Z) := ep_predicate_component_l hZFC source hδ hωδ hV hH
    hx hy hj hY hc hL hSY family hF coherent system limit model hg rel any hab
  obtain ⟨Q, hz, models⟩ := system.models
  have elementary : Di_elementary_d I ω O D p T V' := by
    intro a b e H U f N W st₀ st₁ hab
    obtain ⟨ha, hb, s, m, n, hm, hn, hs, hnb, hsa⟩ := (system.order_spec a b).mp hab
    obtain ⟨a₀, _, haa⟩ := hz.2.1 a ha
    obtain ⟨b₀, _, hbb⟩ := hz.2.1 b hb
    obtain ⟨m', Q₀, U₀, G₀, r₀, H₀, T₀, e₀, V₀, v₀, _, hma, hQ₀, haU, hG₀, old₀, new₀, full₀, _, vr₀, vs₀⟩ := component a a₀ haa
    obtain ⟨n', Q₁, U₁, G₁, r₁, H₁, T₁, e₁, V₁, v₁, _, hnb', hQ₁, hbU, hG₁, old₁, new₁, full₁, _, vr₁, vs₁⟩ := component b b₀ hbb
    have eqm := hma.domain_eq_l hZF.1 hsa.1
    have eqn := hnb'.domain_eq_l hZF.1 hnb
    subst m' n'
    obtain ⟨_, _, _, inj⟩ := (system.indices b).mp hb
    obtain ⟨v, H₀', T₀', H₁', T₁', code₀, code₁, hv, _, _, vs, _⟩ := ep_map_l hZFC source (hF.source_l hZF X) (coherent.source_l I X)
      hm hn hs hnb inj hsa (models a a₀ haa) (models b b₀ hbb)
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I code₀ old₀.code
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I code₁ old₁.code
    have he := ep_predicate_map_l hZFC source hF coherent hm hn hs hnb hsa hQ₀ hQ₁ haU hbU
      hG₀ hG₁ new₀ new₁ full₀ full₁ hx.1 hv vs
    obtain ⟨s₀, _, he₀, _, ss₀, _⟩ := ep_tag_change_l hZF source.omega system changed newLimit st₀ haa old₀.code new₀.code vr₀ vs₀
    obtain ⟨_, s₁, _, he₁, _, ss₁⟩ := ep_tag_change_l hZF source.omega system changed newLimit st₁ hbb old₁.code new₁.code vr₁ vs₁
    obtain ⟨w, hw, ws⟩ := smap_comp_l I hZF he₀ he
    obtain ⟨u, hu, us⟩ := smap_comp_l I hZF hw he₁
    refine ⟨u, hu, fun x y => ⟨?_, ?_⟩⟩
    · intro hxy
      obtain ⟨hx, E, hxE, hEy⟩ := (us x y).mp hxy
      obtain ⟨_, B, hxB, hBE⟩ := (ws x E).mp hxE
      exact ⟨hx, ((ss₁ E y).mp hEy).1,
        (system.toEp_graph_d.arrow_l ((ss₀ x B).mp hxB).2 ((ss₁ E y).mp hEy).2).mpr
          ⟨((st₀.2.1 x).mp hx).1, ((st₁.2.1 y).mp ((ss₁ E y).mp hEy).1).1, ((vs B E).mp hBE).2.2⟩⟩
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨B, hpx, hat⟩ := system.toEp_graph_d.label_l (((st₀.2.1 x).mp hx).2)
      obtain ⟨E, hpy, hbt⟩ := system.toEp_graph_d.label_l (((st₁.2.1 y).mp hy).2)
      have hBE := (vs B E).mpr ⟨(ep_at_read_l hz haa old₀.code.1).mp hat,
        (ep_at_read_l hz hbb old₁.code.1).mp hbt, ((system.toEp_graph_d.arrow_l hpx hpy).mp hxy).2.2⟩
      exact (us x y).mpr ⟨hx, E, (ws x E).mpr ⟨hx, B, (ss₀ x B).mpr ⟨hx, hpx⟩, hBE⟩,
        (ss₁ E y).mpr ⟨hy, hpy⟩⟩
  obtain ⟨E, hE⟩ := model.2.1
  obtain ⟨u, hu⟩ := (limit.range E).mp hE
  obtain ⟨a, ha, hua⟩ := system.diagram.index.2.1 u (limit.projection.bound_l hu).1
  obtain ⟨b, _, hab⟩ := hz.2.1 a ha
  obtain ⟨n, Q, U, G, r, H, V₀, e, V₁, v, hn, ha, hQ, haU, hG, old, new, full, hv, vr, vs⟩ := component a b hab
  obtain ⟨f, N, W₀, stage⟩ := di_stage_exists_l hZF changed hua
  obtain ⟨_, s, _, he, _, ss⟩ := ep_tag_change_l hZF source.omega system changed newLimit stage hab old.code new.code vr vs
  obtain ⟨w, hw, ws⟩ := di_elementary_limit_l hZF source.omega changed newLimit elementary stage md
  obtain ⟨v', he', vs'⟩ := smap_comp_l I hZF he hw
  have eqv : v' = v := by
    apply he'.1.1.1.1.eq_of_pairMember_iff hZF.1 hv.1.1.1
    intro E E'
    refine (vs' E E').trans (?_ : _ ↔ Rd_entry_d E E' v)
    rw [vs E E']
    apply and_congr_right
    intro hE
    refine ⟨fun ⟨u, hEu, huE⟩ => ⟨u, ((ss E u).mp hEu).2, ((ws u E').mp huE).2⟩, ?_⟩
    rintro ⟨u, hp, huE⟩
    have huD := (system.nodes u).mpr ⟨a, E, hp, b, H, V₀, hab, old.code.1, hE⟩
    have huN := (stage.2.1 u).mpr ⟨huD, (system.index u a E hp).mpr huD⟩
    exact ⟨u, (ss E u).mpr ⟨huN, hp⟩, (ws u E').mpr ⟨huN, huE⟩⟩
  subst v'
  obtain ⟨b₀, hm₀⟩ := source.code
  have ultra := hF.at_l hZF.1 haU ha hQ
  obtain ⟨P, U', hP, hU', _, restricted⟩ := rs_restrict_model_l hZF source.omega source.transitive hm₀ source.theory (source.space_mem_l hZF hn hQ) (ultra.source_l hZF X) hG old
  obtain ⟨i, hi, is⟩ := rs_constant_embedding_l hZF source.omega source.transitive hm₀ source.theory
    (source.space_mem_l hZF hn hQ) hP hU' hG restricted
  have hi' := rp_full_constant_l hZFC source.omega ultra hx.1 new full hi.1 is
  obtain ⟨t', ht', ts⟩ := smap_comp_l I hZF hi' he'
  have constant x E y (hxE : Rd_entry_d x E t) (hEy : Rd_entry_d E y g) : Rd_entry_d x y j := by
    obtain ⟨u, a, H, f, Q, hQX, hf, hs, hfH, hp, huE⟩ := constants x E hxE
    obtain ⟨z, _, hxz⟩ := hj.1.1.2.2 x (ht.1.input_mem_of_pairMember hxE)
    exact (ed_constant_value_l hZF source.omega ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩ source.transitive hY hQX hf hs hxz
      (any u a H f E y huE hp hfH hEy)).symm ▸ hxz
  have eqt : t' = t := by
    apply (fn0_of_function_l (ZF.modelsKP hZF) ht'.1.1).ext_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) ht.1)
    intro x hxX
    obtain ⟨E, _, hxE⟩ := ht'.1.1.2.2 x hxX
    obtain ⟨H', _, hxH⟩ := ht.1.2.2 x hxX
    obtain ⟨y, _, hEy⟩ := hg.1.2.2 E (ht'.1.1.output_mem_of_pairMember hxE)
    obtain ⟨z, _, hHz⟩ := hg.1.2.2 H' (ht.1.output_mem_of_pairMember hxH)
    obtain ⟨_, B, hxB, hBE⟩ := (ts x E).mp hxE
    obtain ⟨_, f, hf, hs, hfr⟩ := (is x B).mp hxB
    obtain ⟨_, u, hp, huE⟩ := (vs B E).mp hBE
    have value := any u a B f E y huE hp (old.map.representative_l I ultra.1.base_l hfr) hEy
    have eyz := ed_constant_value_l hZF source.omega ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩ source.transitive hY
      (source.space_mem_l hZF hn hQ) (source.function_l hZF (source.space_mem_l hZF hn hQ) ((hG f).mp hf).1 ((hG f).mp hf).2)
      hs (constant x H' z hxH hHz) value
    exact ⟨E, hxE, (hg.2 E H' z (eyz ▸ hEy) hHz).symm ▸ hxH⟩
  exact ⟨d, W', md, eqt ▸ ht', rel⟩

end YesMetaZFC.SetTheory.LargeCardinal
