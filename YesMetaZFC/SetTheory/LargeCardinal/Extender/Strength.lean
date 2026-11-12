import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.DerivedPredicate
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Coordinates
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.Model.SetTheory.ReducedPower.FullEmbedding
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedGraph
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.Card.Cantor
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Length
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RankCover
import YesMetaZFC.Model.SetTheory.Embedding.Range

/-! # 在既有分量上扩张谓词

商类和代表投影原封保留；新关系沿规范分量映射拉回。Vδ=Hδ 的实际
小定义域闭性证明原代表族已经完整，随后可调用任意关系的 Łoś 定理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_predicate_component_l {ω δ κ k K L X R A Y B j c₀ R₀ c₁ R₁ S F J O Z D p T V q c C W g W' a b : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hδ : M.IsRegularCardinal I δ) (hωδ : M.mem ω δ)
    (hV : V_d I δ X) (hH : H_d I δ X)
    (hx : Spred_d I c₀ X A R₀) (hy : Spred_d I c₁ Y B R₁) (hj : Smap_d I ω c₀ c₁ X Y j)
    (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k) (hL : M.MemberSubset L k)
    (hSY : M.MemberSubset S Y) (family : Es_family_d I j κ L S F)
    (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (model : Smdl_d I c C W) (hg : M.IsSetInjectionFromTo I g C Y)
    (rel : ∀ E H y z, Rd_entry_d E y g → Rd_entry_d H z g → (Rd_entry_d E H W' ↔ Rd_entry_d y z R₁))
    (any : ∀ u a H f E y, Rd_entry_d u E q → KPair_d M u a H → M.mem f H →
      Rd_entry_d E y g → Ee_value_d j a f y) (hab : Rd_entry_d a b Z) :
    ∃ n Q U G r H V₀ e V₁ v, M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n Q ∧ Rd_entry_d a U F ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d Q X f) ∧ Rp_model_d I Q X U R b G r H V₀ ∧
      Rp_model_d I Q X U R₀ e G r H V₁ ∧ (∀ f, Fn0_d Q X f → M.mem f G) ∧
      M.IsSetInjectionFromTo I v H C ∧
      (∀ E H x y, Rd_entry_d E x v → Rd_entry_d H y v → (Rd_entry_d E H V₁ ↔ Rd_entry_d x y W')) ∧
      ∀ E E', Rd_entry_d E E' v ↔ M.mem E H ∧ ∃ u, KPair_d M u a E ∧ Rd_entry_d u E' q := by
  have embed : Spred_emb_d I ω X A Y B j := ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩
  have models := system.components
  obtain ⟨n, Q, U, G, r, H, V₀, hn, ha, hQ, haU, hG, hm⟩ := models a b hab
  obtain ⟨v, hv, vs⟩ := ep_stage_embedding_l hZF source.omega system.toEg_graph_d system.diagram limit
    (system.toEp_graph_d.elementary_l hZF source (hF.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) (coherent.source_l I X)) model hab hm.code
  obtain ⟨e, V₁, code, vr⟩ := smdl_pull_l hZF hm.code.2.1 hv.1.1 W'
  obtain ⟨haS, m, Q₀, ha₀, hQ₀, hu⟩ := (family.2.2 a U).mp haU
  have eq := ha₀.domain_eq_l hZF.1 ha
  subst m
  have eq := hZF.1.eq_of_same_members Q₀ Q (fun s => (hQ₀ s).trans (hQ s).symm)
  subst Q₀
  have hQX := source.space_mem_l hZF hn hQ
  obtain ⟨Q', _, hjQ⟩ := hj.1.1.2.2 Q hQX
  have hωκ := ed_critical_omega_l I hZF source.omega embed source.transitive hY hc
  have haQ := es_seed_l I hZF source.omega embed source.transitive hY
    (hc.fixed n (hc.ordinal.transitive ω hωκ n hn)) hc.image hjQ hQ hL (hSY a haS) ha
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF Q
  have hPX := source.transitive P (v_power_mem_l I hV hδ.isLimitOrdinal hQX hP)
  have sf f (hf : M.mem f G) := source.function_l hZF ((hG f).mp hf).1 ((hG f).mp hf).2
  have ultra := hF.at_l hZF.1 haU ha hQ
  have newModel : Rp_model_d I Q X U R₀ e G r H V₁ := ⟨hm.map, code, by
    intro f f' E E' hf hf'
    obtain ⟨x, _, hEx⟩ := hv.1.1.2.2 E (hm.map.projection.output_mem_of_pairMember hf)
    obtain ⟨x', _, hEx'⟩ := hv.1.1.2.2 E' (hm.map.projection.output_mem_of_pairMember hf')
    obtain ⟨y, _, hxy⟩ := hg.1.2.2 x (hv.1.1.output_mem_of_pairMember hEx)
    obtain ⟨y', _, hxy'⟩ := hg.1.2.2 x' (hv.1.1.output_mem_of_pairMember hEx')
    obtain ⟨_, u, hp, hux⟩ := (vs E x).mp hEx
    obtain ⟨_, u', hp', hux'⟩ := (vs E' x').mp hEx'
    have ey := any u a E f x y hux hp (hm.map.representative_l I ultra.1.base_l hf) hxy
    have ey' := any u' a E' f' x' y' hux' hp' (hm.map.representative_l I ultra.1.base_l hf') hxy'
    exact (vr E E' x x' hEx hEx').trans ((rel x x' y y' hxy hxy').trans
      (ed_predicate_evaluation_l hZF source.omega hx hy hj source.transitive hY hjQ haQ hP hPX hu
        (sf f (hm.map.projection.input_mem_of_pairMember hf))
        (sf f' (hm.map.projection.input_mem_of_pairMember hf')) ey ey').symm)⟩
  exact ⟨n, Q, U, G, r, H, V₀, e, V₁, v, hn, ha, hQ, haU, hG, hm, newModel,
    fun f hf => (hG f).mpr ⟨ZFC.h_function_l hZFC source.omega hδ hωδ hH hQX
      (fn0_function_l (ZF.modelsKP hZF) hf), hf⟩, hv.1, vr, vs⟩

/-- 原过渡图在扩张关系下仍对全部内部代码初等。 -/
theorem ep_predicate_map_l {ω κ K L X R F a b m n s Q₀ Q₁ U V G₀ G₁ r₀ r₁ H₀ H₁ c₀ c₁ T₀ T₁ j c S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (hm : M.mem m ω) (hn : M.mem n ω) (hs : Fn0_d m n s) (hb : Fn0_d n L b) (ha : Cp0_d m n L s b a)
    (hQ₀ : Ep_space_d κ m Q₀) (hQ₁ : Ep_space_d κ n Q₁) (haU : Rd_entry_d a U F) (hbV : Rd_entry_d b V F)
    (hG₀ : ∀ f, M.mem f G₀ ↔ M.mem f X ∧ Fn0_d Q₀ X f) (hG₁ : ∀ f, M.mem f G₁ ↔ M.mem f X ∧ Fn0_d Q₁ X f)
    (hp : Rp_model_d I Q₀ X U S c₀ G₀ r₀ H₀ T₀) (hq : Rp_model_d I Q₁ X V S c₁ G₁ r₁ H₁ T₁)
    (full₀ : ∀ f, Fn0_d Q₀ X f → M.mem f G₀) (full₁ : ∀ f, Fn0_d Q₁ X f → M.mem f G₁)
    (code : Smdl_d I c X S) (hj : M.IsSetInjectionFromTo I j H₀ H₁)
    (spec : ∀ E H, Rd_entry_d E H j ↔ M.mem E H₀ ∧ M.mem H H₁ ∧ Ep_arrow_d ω κ L X a b E H) :
    Smap_d I ω c₀ c₁ H₀ H₁ j := by
  obtain ⟨t, K', _, ht, ts, hK, ks⟩ := source.family_l hZF hm hn hs hQ₀ hQ₁ hG₀ hG₁
  obtain ⟨P₀, hP₀⟩ := ZF.exists_powerSet hZF Q₀
  obtain ⟨P₁, hP₁⟩ := ZF.exists_powerSet hZF Q₁
  have push : Push_d Q₀ Q₁ P₀ P₁ U V t := ⟨ht, fun E hE => by
    obtain ⟨H, hH, eq⟩ := coherent m n s b a U V E hm hn hs hb ha hbV haU
      (fun r hr => (hQ₀ r).mp ((hP₀ E).mp hE r hr))
    exact ⟨H, (hP₁ H).mpr (fun v hv => (hQ₁ v).mpr ((hH v).mp hv).1), fun v => (hH v).trans
      ⟨fun ⟨hv, r, hr, hvr⟩ => ⟨(hQ₁ v).mpr hv, r, hr, (ts v r).mpr ⟨(hQ₁ v).mpr hv, hvr⟩⟩,
        fun ⟨hv, r, hr, hvr⟩ => ⟨(hQ₁ v).mp hv, r, hr, ((ts v r).mp hvr).2⟩⟩, eq⟩⟩
  have hu := hF.at_l hZF.1 haU ha.1 hQ₀
  have hv := hF.at_l hZF.1 hbV hb hQ₁
  apply rp_full_embedding_l hZFC source.omega code hP₀ hu hv push hp hq full₀ full₁ hK
    (fun f g hfg => ((ks f g).mp hfg).2.2) hj
  intro f g E H hfg hf hg
  exact (spec E H).mpr ⟨hp.map.projection.output_mem_of_pairMember hf, hq.map.projection.output_mem_of_pairMember hg,
    m, n, s, f, g, hm, hn, hs, hb, ha, hp.map.representative_l I hu.1.base_l hf,
    hq.map.representative_l I hv.1.base_l hg, ep_pull_of_comp_l hQ₀ hQ₁ ht
      (hp.map.functions f (hK.input_mem_of_pairMember hfg)) ts ((ks f g).mp hfg).2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一个有限支撑极限的完整谓词初等性

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hδ : M.IsRegularCardinal I δ) (hωδ : M.mem ω δ)
    (hV : V_d I δ X) (hH : H_d I δ X)
    (hx : Spred_d I c₀ X A R₀) (hy : Spred_d I c₁ Y B R₁) (hj : Smap_d I ω c₀ c₁ X Y j)
    (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k) (hL : M.MemberSubset L k)
    (hSY : M.MemberSubset S Y) (family : Es_family_d I j κ L S F)
    (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
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
  obtain ⟨Q, hz⟩ := system.codes
  have models := system.components
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
    obtain ⟨v, H₀', T₀', H₁', T₁', code₀, code₁, hv, _, _, vs, _⟩ := ep_map_l hZF source (hF.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) (coherent.source_l I X)
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
  obtain ⟨P, U', hP, hU', _, restricted⟩ := rs_restrict_model_l hZF source.omega source.transitive hm₀ source.theory (source.space_mem_l hZF hn hQ) (ultra.source_l (ZF.modelsKP hZF) (ZF.exists_powerSet hZF Q) X) hG old
  obtain ⟨i, hi, is⟩ := rs_constant_embedding_l hZF source.omega source.transitive hm₀ source.theory (source.uniform_l hZF hn hQ)
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
      (source.space_mem_l hZF hn hQ) (source.function_l hZF ((hG f).mp hf).1 ((hG f).mp hf).2)
      hs (constant x H' z hxH hHz) value
    exact ⟨E, hxE, (hg.2 E H' z (eyz ▸ hEy) hHz).symm ▸ hxH⟩
  exact ⟨d, W', md, eqt ▸ ht', rel⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 不可达支撑长度处的真实强度上界

若目标包含 L 的全部子集，则它们都属于原 P(κ) 的像，因而都有处处取值于
P(κ) 的源代表。这些有限支撑节点全在 V_L 中；原商投影与坍缩的复合于是
把 V_L 的一个子集满射到 P(L)，与 |V_L|=L 及 Cantor 定理矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_inaccessible_bound_l {ω κ K L X R F J O Z A p T S q C W b d N V i t e P Γ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hm : Smem_d I b X R) (hn : Smem_d I d N V) (hN : M.TransitiveSet N) (hi : Smap_d I ω b d X N i)
    (constants : Ep_constants_d X q t) (wc : Wc_graph_d C W e) (bij : M.IsSetBijectionFromTo I e C N)
    (comp : ∀ x y, Rd_entry_d x y i ↔ M.mem x X ∧ ∃ E, Rd_entry_d x E t ∧ Rd_entry_d E y e)
    (hP : M.IsPowerSetOf P κ) (hPX : M.mem P X) (hκi : Rd_entry_d κ Γ i) (hLΓ : M.MemberSubset L Γ)
    (hκL : M.mem κ L) (hωL : M.mem ω L) (hr : M.IsRegularCardinal I L) (hs : M.IsStrongLimitCardinal I L) :
    ∃ x, M.MemberSubset x L ∧ ¬ M.mem x N := by
  classical
  apply Classical.byContradiction
  intro missing
  have all x (hx : M.MemberSubset x L) : M.mem x N :=
    Classical.byContradiction (fun hn => missing ⟨x, hx, hn⟩)
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hr.isCardinal.1
  obtain ⟨R', rank⟩ := ep_regular_source_l hZFC source.omega hωL hr hB hκL source.below (source.finite_l (ZF.modelsKP hZF))
  obtain ⟨c, code⟩ := rank.code
  have hPB := v_power_mem_l I hB hr.isLimitOrdinal rank.cardinal_mem hP
  obtain ⟨U, hU, hKU, hPU⟩ := v_joint_bound_l I hB rank.finite.mem_l hPB
  have node_rank u (node : Eb_node_d ω κ L K P J X X u) : M.mem u B := by
    obtain ⟨a, _, f, _, pair, n, hn, D, _, ha, space, ff⟩ := node
    have haB := sc_finite_function_l (ZF.modelsKP hZF) source.omega rank.transitive (rank.algebra_l (ZF.modelsKP hZF)).pair (rank.algebra_l (ZF.modelsKP hZF)).union rank.omega_mem
      (ZF.v_ordinal_subset_l I hZF hB) hn ha
    have hfB := v_relation_mem_l I hB hr.isLimitOrdinal hU (fun p hp => by
      obtain ⟨s, hd, x, hx, pair⟩ := ff.1 p hp
      exact ⟨s, hKU s (space.1 s hd), x, hPU x hx, pair⟩)
    obtain ⟨v, hv, vp⟩ := (rank.algebra_l (ZF.modelsKP hZF)).kpair_l haB hfB
    exact kpair_unique_l M hZF.1 vp pair ▸ hv
  -- 完整初等性只用于原幂集的源量词刻画。
  obtain ⟨P', _, hPP⟩ := hi.1.1.2.2 P hPX
  have power := hi.power_l hZF source.omega source.transitive hN hm hn hκi hPP
    (fun x => ⟨fun hx => ⟨source.transitive P hPX x hx, (hP x).mp hx⟩, fun ⟨_, hx⟩ => (hP x).mpr hx⟩)
  obtain ⟨_, H, hPH, hHP⟩ := (comp P P').mp hPP
  obtain ⟨u, a, D, f, Q, _, sf, fc, hfD, pair, huH⟩ := constants P H hPH
  have fv : Ep_repr_d q a f H := ⟨u, D, pair, hfD, huH⟩
  obtain ⟨_, n, hnω, ha, Q', space, ff⟩ := fv.source_l hZF family system limit
  have eq := (sf.function_l source.transitive).domain_eq_l hZF.1 ff
  subst Q'
  obtain ⟨PL, hPL⟩ := ZF.exists_powerSet hZF L
  -- 分离只收集原投影实际求值为 L 子集的节点，不另造求值关系。
  let ρ : Env M 10 := ⟨Fin.cases PL (Fin.cases e (Fin.cases q (Fin.cases X (Fin.cases J
    (Fin.cases P (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω))))))))), fun _ => ω⟩
  let φ : UnarySchema 10 := {
    body := .conj
      (eb_node_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 4) .newest)
      (Formula.existsMem (.bound 1) (.existsE (.conj (eb_value_m (.bound 5) (.bound 2) .newest)
        (rd_entry0_m .newest (.bound 1) (.bound 4))))) }
  obtain ⟨D₀, ds⟩ := ZF.separation_exists_d hZF φ ρ B
  have spec u : M.mem u D₀ ↔ M.mem u B ∧ Eb_node_d ω κ L K P J X X u ∧
      ∃ x, M.mem x PL ∧ ∃ E, Eb_value_d q u E ∧ Rd_entry_d E x e := by
    simpa only [φ, Formula.satisfies_conj_iff, eb_node_sat_l hZF.1, Formula.satisfies_existsMem_iff,
      Formula.satisfies_exists_iff, eb_value_sat_l hZF.1, rd_entry0_sat_l hZF.1] using! ds u
  obtain ⟨v, vf, vs⟩ := eb_projection_l hZF source family system limit (source.transitive P hPX)
    (fun u hu => ((spec u).mp hu).2.1)
  obtain ⟨g, gf, gs⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) vf) bij.1.1
  have into u x (hux : Rd_entry_d u x g) : M.mem x PL := by
    obtain ⟨hu, E, huE, hEx⟩ := (gs u x).mp hux
    obtain ⟨_, _, y, hy, H', value, hHy⟩ := (spec u).mp hu
    have h := (vs u H').mpr ⟨hu, value⟩
    have eq := (fn0_function_l (ZF.modelsKP hZF) vf).1.2 u H' E h huE
    exact bij.1.1.1.2 E y x (eq ▸ hHy) hEx ▸ hy
  have onto x (hx : M.mem x PL) : ∃ u, M.mem u D₀ ∧ Rd_entry_d u x g := by
    have hxN := all x ((hPL x).mp hx)
    obtain ⟨E, _, hEx⟩ := bij.2 x hxN
    have hxP := (power x).mpr ⟨hxN, fun y hy => hLΓ y ((hPL x).mp hx y hy)⟩
    have edge := (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHP).mpr hxP
    obtain ⟨m, a', D', f', hm, haJ, ha', hd, hf, fn, value⟩ :=
      ep_repr_bounded_l hZF source family system limit hnω ha space ff fc fv hPX edge
    obtain ⟨u', pair'⟩ := (I).total a' f'
    have node : Eb_node_d ω κ L K P J X X u' := ⟨a', haJ, f', hf, pair', m, hm, D',
      source.space_mem_l hZF hm hd, ha', (eb_space_iff_l (ZF.modelsKP hZF) (source.finite_l (ZF.modelsKP hZF)) hm).mpr hd, fn⟩
    have hu := (spec u').mpr ⟨node_rank u' node, node, x, hx, E, ⟨a', f', pair', value⟩, hEx⟩
    exact ⟨u', hu, (gs u' x).mpr ⟨hu, E, (vs u' E).mpr ⟨hu, a', f', pair', value⟩, hEx⟩⟩
  obtain ⟨r, rb⟩ := ZFC.inaccessible_enumeration_l I hZFC source.omega hωL hr hs hB
  obtain ⟨s, sb⟩ := ZF.exists_inverseBijection hZF I rb
  obtain ⟨t', ti⟩ := ZF.exists_inclusionInjection hZF I (fun u hu => ((spec u).mp hu).1)
  have small := ZF.exists_compositionInjection hZF I ti sb.1
  have bound := ZF.ordinal_image_bound_l I hZF hr.isCardinal.1 small
    (fn0_function_l (ZF.modelsKP hZF) ((fn0_of_function_l (ZF.modelsKP hZF) gf).retarget_l into)) onto
  have cantor := ZF.cardinalLess_powerSet hZF I hPL
  exact cantor.2 (ZF.equinumerous_of_cardinalLessOrEqual hZF I cantor.1 bound)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定秩层的覆盖与原谓词一致性恢复

在已证明的原因子像中实际覆盖 Vν 后，传递坍塌固定整个 Vν。目标谓词
由原因子的真实逆像集合构造；交换三角给出源谓词保持，固定性给出秩层一致。
完整谓词 Łoś 经同像比较传递到同一个坍塌嵌入，保留全部内部公式码的初等性。
常值图与坍缩图随证书保留；不可达支撑处的代表计数给出同一目标的缺失子集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_strength_d (hZF : M.Models ZF) (ω κ L X R A V j Y q c₀ C W : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ c d N S B i k κ', Smem_d I c X R ∧ Smem_d I d N S ∧ M.TransitiveSet N ∧ Smap_d I ω c d X N i ∧
    Spred_emb_d I ω X A N B i ∧
    Wd_crit_d I X i κ κ' ∧ M.MemberSubset L κ' ∧ M.MemberSubset V N ∧ M.MemberSubset B N ∧
    M.IsSetInjectionFromTo I k N Y ∧
    (∀ x y u v, Rd_entry_d x u k → Rd_entry_d y v k → (M.mem x y ↔ M.mem u v)) ∧
    (∀ y, (∃ z, Rd_entry_d z y k) ↔ ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u y) ∧
    (∀ x, M.mem x V → Rd_entry_d x x k) ∧
    (∀ x y z, Rd_entry_d x y i → (Rd_entry_d y z k ↔ Rd_entry_d x z j)) ∧
    (∀ x y, Rd_entry_d x y i → (M.mem x A ↔ M.mem y B)) ∧
    (∀ x, M.mem x V → (M.mem x A ↔ M.mem x B)) ∧
    Ep_realizer_d hZF ω X q c c₀ C W d N i ∧ ∃ x, M.MemberSubset x L ∧ ¬ M.mem x N

section Construction
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_strength_l {ω δ κ κ₀ K L X R A Y B j S F J O Z D p T V₀ q c C W ν V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hδ : M.IsRegularCardinal I δ) (hωδ : M.mem ω δ)
    (hVX : V_d I δ X) (hHX : H_d I δ X) (h : Spred_emb_d I ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d I X j κ κ₀) (hL : M.MemberSubset L κ₀)
    (hκL : M.mem κ L) (hωL : M.mem ω L) (rL : M.IsRegularCardinal I L) (sL : M.IsStrongLimitCardinal I L)
    (hSY : M.MemberSubset S Y) (family : Es_family_d I j κ L S F)
    (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z D p T V₀) (limit : Di_limit_d D p T V₀ q C W)
    (model : Smdl_d I c C W) (collapse : Ep_collapse_d hZF ω X R q c C W) (factor : Ee_factor_d hZF j Y q C W)
    (hV : V_d I ν V) (length : Ep_length_d hZF ω κ L X R j Y q c C W)
    (cover : ∀ x, M.mem x V → ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u x)
    (agree : ∀ x, M.mem x V → (M.mem x A ↔ M.mem x B)) : Ep_strength_d hZF ω κ L X R A V j Y q c C W := by
  obtain ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩ := h
  have embed : Spred_emb_d I ω X A Y B j := ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩
  obtain ⟨g, hg, gs, _, any⟩ := factor
  obtain ⟨_, _, t, _, _, _, _, _, _, _, ht, constants, _⟩ := collapse
  obtain ⟨d₀, W₀, expanded, full, fr⟩ := ep_predicate_limit_l hZFC source hδ hωδ hVX hHX hx hy hj hY hc hL
    hSY family hF coherent system limit model hg any ht.1 constants
  obtain ⟨b, d, N, S, i, k, κ', hm, hn, ht, hi, hk, rel, range, triangle, _, _, crit, bound, realizer⟩ := length
  obtain ⟨t', e', ht', ct, wc, bij, he', comp⟩ := realizer
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  have missing := ep_inaccessible_bound_l hZFC source (hF.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) system limit hm hn ht hi ct wc bij comp hP
    (v_power_mem_l I hVX hδ.isLimitOrdinal source.cardinal_mem hP) crit.image bound hκL hωL rL sL
  obtain ⟨hVN, fixed⟩ := mem_embedding_fixed_l hZF ht hk rel (v_transitive_l I hV)
    (fun x hx => (range x).mpr (cover x hx))
  let ρ := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push k
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m (.bound 1) .newest (.bound 2)) }
  obtain ⟨B', bs⟩ := ZF.separation_exists_d hZF φ ρ N
  have spec x : M.mem x B' ↔ M.mem x N ∧ ∃ y, M.mem y B ∧ Rd_entry_d x y k := by
    simpa only [φ, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] using! bs x
  have predicate x y (hxy : Rd_entry_d x y k) : M.mem x B' ↔ M.mem y B := (spec x).trans
    ⟨fun ⟨_, z, hz, hxz⟩ => hk.1.1.2 x z y hxz hxy ▸ hz,
      fun hy => ⟨hk.1.input_mem_of_pairMember hxy, y, hy, hxy⟩⟩
  have hBN : M.MemberSubset B' N := fun x hx => ((spec x).mp hx).1
  obtain ⟨e, U, pred⟩ := spred_exists_l I hZF ⟨κ', hi.1.1.output_mem_of_pairMember crit.image⟩ hBN
  have pr x y u v (hx : Rd_entry_d x u k) (hy' : Rd_entry_d y v k) : Rd_entry_d x y U ↔ Rd_entry_d u v R₁ := by
    have eq : x = y ↔ u = v := ⟨fun h => hk.1.1.2 y u v (h ▸ hx) hy', fun h => hk.2 x y v (h ▸ hx) hy'⟩
    have left : Rd_entry_d x y U ↔ M.mem x y ∨ x = y ∧ M.mem x B' :=
      (pred.2.2 x y).trans ⟨fun h => h.2.2, fun h =>
        ⟨hk.1.input_mem_of_pairMember hx, hk.1.input_mem_of_pairMember hy', h⟩⟩
    have right : Rd_entry_d u v R₁ ↔ M.mem u v ∨ u = v ∧ M.mem u B :=
      (hy.2.2 u v).trans ⟨fun h => h.2.2, fun h =>
        ⟨hk.1.output_mem_of_pairMember hx, hk.1.output_mem_of_pairMember hy', h⟩⟩
    exact left.trans ((or_congr (rel x y u v hx hy') (and_congr eq (predicate x u hx))).trans right.symm)
  have same y : (∃ E, Rd_entry_d E y g) ↔ ∃ x, Rd_entry_d x y k := by
    refine ⟨fun ⟨E, hEy⟩ => ?_, fun hy => ?_⟩
    · obtain ⟨hE, u, hu, hv⟩ := (gs E y).mp hEy
      exact (range y).mpr ⟨E, u, hE, hu, hv⟩
    · obtain ⟨E, u, hE, hu, hv⟩ := (range y).mp hy
      exact ⟨E, (gs E y).mpr ⟨hE, u, hu, hv⟩⟩
  have full' := smap_same_range_l hZF source.omega full hi.1.1 hg hk expanded pred.1 same
    (fun E H z w y y' hEy hHy hzy hwy => (fr E H y y' hEy hHy).trans (pr z w y y' hzy hwy).symm)
    (fun x E z y hxE hxz hEy => by
      obtain ⟨u, a, H, f, Q, hQ, hf, hs, hfH, hp, huE⟩ := constants x E hxE
      obtain ⟨y', _, hxy⟩ := hj.1.1.2.2 x (hi.1.1.input_mem_of_pairMember hxz)
      have eq := ed_constant_value_l hZF source.omega embed source.transitive hY hQ hf hs hxy
        (any u a H f E y huE hp hfH hEy)
      exact (triangle x z y hxz).mpr (eq.symm ▸ hxy))
  refine ⟨b, d, N, S, B', i, k, κ', hm, hn, ht, hi, ⟨c₀, R₀, e, U, hx, pred, full'⟩, crit, bound, hVN,
    fun x hx => ((spec x).mp hx).1, hk, rel, range, fixed, triangle, ?_, ?_,
    ⟨t', e', ht', ct, wc, bij, he', comp⟩, missing⟩
  · intro x y hxy
    obtain ⟨z, _, hyz⟩ := hk.1.2.2 y (hi.1.1.output_mem_of_pairMember hxy)
    exact (spred_predicate_l I hZF source.omega embed ((triangle x y z hxy).mp hyz)).trans (predicate y z hyz).symm
  · intro x hx
    exact (agree x hx).trans (predicate x x (fixed x hx)).symm

end Construction
end YesMetaZFC.SetTheory.LargeCardinal
